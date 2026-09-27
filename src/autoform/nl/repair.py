"""Counterexample adjudication and bounded repair of refuted English properties.

    check ─► checks.json ─► adjudicate ─► adjudication.json ─► prove (original + repaired)

For every REFUTED_MODEL / REFUTED_RUNTIME statement:

1. Deterministic gates narrow what the judge may say (`gates`):
     REFUTED_RUNTIME only                   ⇒ INCOMPLETE_MODEL (forced): the model disagrees
                                               with the real code;
     the model's outcome is a hole/outOfFuel ⇒ INCOMPLETE_MODEL (forced);
     the real code satisfies the statement
       on every checked input (runtime_agrees) ⇒ INCOMPLETE_MODEL (forced);
     otherwise REAL_BUG, BAD_SPEC, plus
       MISSING_PRECONDITION  only if the witness lies outside the inputs the docs/tests use
                             (or no such domain is known),
       ABSTRACTION_ARTIFACT  only if the real code was not run;
     the losing reading of a rival group (INTENT_SELECTION) cannot be REAL_BUG.
2. The judge (COUNTEREXAMPLE_CLASSIFICATION) picks among the allowed classes, shown the
   counterexample, the English, the Lean statement and the function source.
3. REAL_BUG is a *finding* only if cross-validated: the property has evidence other than
   "implementation" AND its intent is confident (the chosen reading of its rival group with
   probability ≥ 0.8, or, with no rival, a PROPERTY_JUDGMENT that is not
   UNSUPPORTED_BY_EVIDENCE/TOO_STRONG). Otherwise it is a *suspected bug* for review. A
   REAL_BUG is never repaired away.
4. BAD_SPEC / MISSING_PRECONDITION ⇒ repair candidates (`candidates`): the English restated
   under a precondition taken from the code's own guards, the docstring, or the input domain
   the tests use; a weakening (one direction of an "exactly when", allowing the exception
   the model raised); or REJECT. A precondition that mentions a witness value not found in
   the code, docs, tests or English is never offered. PRECONDITION_SELECTION picks among
   preconditions, REPAIR_SELECTION among repair kinds; the chosen restatement goes through
   formalize → check again (prove later), at most `rounds` rounds. Each repaired property
   and statement keeps a `parent` link.
5. INCOMPLETE_MODEL ⇒ MODEL_DEFECT_CLASSIFICATION and a report entry pointing at the model;
   the model stage owns model repairs.

The judge never sets a status: classes, repairs and findings are readings of what the
kernel and the real executions established.
"""
from __future__ import annotations

import ast
import json
import re
from dataclasses import asdict
from pathlib import Path

from ..harness.judge import COUNTEREXAMPLE_CLASSES
from .judge import (EST_FORMALIZE_USD, INTENT_THRESHOLD, external_evidence, full_state, make_judge,
                    record_skips)
from .schema import FILES

REFUTED = ('REFUTED_MODEL', 'REFUTED_RUNTIME')
ROUNDS = 2
NEG = {'==': '!=', '!=': '==', '<': '>=', '>=': '<', '>': '<=', '<=': '>', 'is': 'is not', 'is not': 'is',
       'in': 'not in', 'not in': 'in'}
OPS = {ast.Eq: '==', ast.NotEq: '!=', ast.Lt: '<', ast.LtE: '<=', ast.Gt: '>', ast.GtE: '>=', ast.Is: 'is',
       ast.IsNot: 'is not', ast.In: 'in', ast.NotIn: 'not in'}
DOC_CONSTRAINT = [
    re.compile(r'\b(?P<p>\w+)\s+(?:must|should|has to|is expected to)\s+be\s+(?P<c>non-?negative|positive|'
               r'non-?zero|not zero)\b', re.I),
    re.compile(r'\b(?P<c>non-?negative|positive|non-?zero)\s+(?:integer\s+|number\s+|value\s+)?(?P<p>\w+)\b', re.I),
]
DOC_PRE = {'nonnegative': '{p} >= 0', 'non-negative': '{p} >= 0', 'positive': '{p} > 0', 'nonzero': '{p} != 0',
           'non-zero': '{p} != 0', 'not zero': '{p} != 0'}


def margin(probs: dict) -> float:
    """Top-1 minus top-2 probability; near 0 the judge could not separate its options."""
    top = sorted((probs or {}).values(), reverse=True) + [0.0, 0.0]
    return round(top[0] - top[1], 4)


def _d(x):
    return asdict(x) if hasattr(x, '__dataclass_fields__') else dict(x)


# --- facts about the function ---------------------------------------------------------

def param_names(fn: dict) -> list:
    return [p['name'] for p in fn.get('params') or []]


def tested_values(fn: dict) -> dict:
    """param name → literal argument values used by the tests / doctest examples."""
    name = fn.get('source_name') or fn['name'].rsplit('.', 1)[-1]
    names = param_names(fn)
    texts = [t.get('text') or '' for t in fn.get('tests') or []]
    texts += [ln.strip()[3:].strip() for ln in (fn.get('doc') or '').splitlines() if ln.strip().startswith('>>>')]
    out: dict = {}
    for text in texts:
        try:
            tree = ast.parse(text.strip())
        except SyntaxError:
            continue
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            callee = node.func.id if isinstance(node.func, ast.Name) else \
                node.func.attr if isinstance(node.func, ast.Attribute) else None
            if callee != name:
                continue
            for i, a in enumerate(node.args):
                try:
                    v = ast.literal_eval(a)
                except (ValueError, TypeError, SyntaxError):
                    continue
                if i < len(names):
                    out.setdefault(names[i], []).append(v)
            for kw in node.keywords:
                try:
                    out.setdefault(kw.arg, []).append(ast.literal_eval(kw.value))
                except (ValueError, TypeError, SyntaxError):
                    continue
    return out


def doc_constraints(fn: dict) -> list:
    """[(param, precondition text)] stated by the docstring ("b must be nonzero")."""
    names, out = set(param_names(fn)), []
    for pat in DOC_CONSTRAINT:
        for m in pat.finditer(fn.get('doc') or ''):
            p, c = m.group('p'), m.group('c').lower()
            form = DOC_PRE.get(c) or DOC_PRE.get(c.replace('-', ''))
            if p in names and form:
                pre = form.format(p=p)
                if (p, pre) not in out:
                    out.append((p, pre))
    return out


def _holds(pre: str, env: dict):
    try:
        return bool(eval(pre, {'__builtins__': {}}, dict(env)))   # noqa: S307 - our own tiny expressions
    except Exception:  # noqa: BLE001
        return None


def witness_domain(inputs: dict, fn: dict) -> tuple:
    """(inside, reason): is the witness within what the docs/tests use? None = unknown."""
    inputs = inputs or {}
    tested = tested_values(fn)
    reasons, known = [], False
    for p, pre in doc_constraints(fn):
        if p in inputs:
            known = True
            if _holds(pre, {p: inputs[p]}) is False:
                return False, f'the docstring requires {pre}; the witness has {p} = {inputs[p]!r}'
    for p, vals in tested.items():
        if p not in inputs:
            continue
        known = True
        v = inputs[p]
        kinds = {type(x).__name__ for x in vals}
        if type(v).__name__ not in kinds:
            return False, f'tests pass {p} only as {"/".join(sorted(kinds))}; the witness has {v!r}'
        nums = [x for x in vals if isinstance(x, (int, float)) and not isinstance(x, bool)]
        if nums and isinstance(v, (int, float)) and not isinstance(v, bool) and not (min(nums) <= v <= max(nums)):
            return False, f'tests use {p} in [{min(nums)}, {max(nums)}]; the witness has {p} = {v}'
        if not isinstance(v, (int, float)) and v not in vals:
            return False, f'tests use {p} only as {sorted(map(repr, vals))}; the witness has {p} = {v!r}'
        reasons.append(f'{p} = {v!r} is within the tested values of {p}')
    if not known:
        return None, 'no documented or tested input domain'
    return True, '; '.join(reasons) or 'within the documented domain'


def model_kind(model_outcome) -> str:
    text = str(model_outcome or '')
    if re.search(r'\bhole\b', text):
        return 'hole'
    if 'outOfFuel' in text or 'out of fuel' in text:
        return 'out_of_fuel'
    if re.search(r'\bexn\b', text):
        return 'exception'
    return 'value' if text else 'unknown'


def raised(model_outcome) -> str | None:
    m = re.search(r'exn\s*\(?\s*(?:Autoform\.Core\.)?(?:Val)?\.str\s+"([^"]+)"', str(model_outcome or ''))
    return m.group(1) if m else None


# --- gates ----------------------------------------------------------------------------

def gates(check: dict, fn: dict, sel_row: dict | None = None) -> tuple:
    """(allowed classes, facts): deterministic facts first, the judge chooses among the rest."""
    ce = check.get('counterexample') or {}
    kind = model_kind(ce.get('model'))
    facts = dict(status=check['status'], model_outcome_kind=kind, runtime_agrees=check.get('runtime_agrees'))
    if check['status'] == 'REFUTED_RUNTIME':
        facts['gate'] = 'refuted on the real code only: the model disagrees with the code'
        return ['INCOMPLETE_MODEL'], facts
    if kind in ('hole', 'out_of_fuel'):
        facts['gate'] = f'the model reached {kind.replace("_", " ")} at the witness'
        return ['INCOMPLETE_MODEL'], facts
    if check.get('runtime_agrees') is True:
        facts['gate'] = 'the real code satisfies the statement on every checked input; the model does not'
        return ['INCOMPLETE_MODEL'], facts
    inside, why = witness_domain(ce.get('inputs'), fn)
    facts.update(witness_in_domain=inside, domain=why)
    allowed = ['REAL_BUG', 'BAD_SPEC']
    if inside is not True:
        allowed.append('MISSING_PRECONDITION')
    runtime = str(ce.get('runtime') or '')
    if check.get('runtime_agrees') is None and (not runtime or runtime.startswith('not run')):
        allowed.append('ABSTRACTION_ARTIFACT')
    intent = (sel_row or {}).get('intent') or {}
    if intent and not intent.get('chosen'):
        allowed.remove('REAL_BUG')
        facts['intent'] = 'a rival reading was chosen as the intent: this one cannot be a real bug'
    return allowed, facts


def classification_prior(prop: dict, sel_row: dict | None, facts: dict) -> dict:
    prior = {k: 0.1 for k in COUNTEREXAMPLE_CLASSES}
    if external_evidence(prop.get('evidence')):
        prior['REAL_BUG'] += 0.3
    else:
        prior['BAD_SPEC'] += 0.3
    j = ((sel_row or {}).get('judgment') or {}).get('probabilities') or {}
    prior['BAD_SPEC'] += 0.3 * (j.get('TOO_STRONG', 0) + j.get('UNSUPPORTED_BY_EVIDENCE', 0))
    intent = (sel_row or {}).get('intent') or {}
    if intent.get('chosen') and intent.get('probability', 0) >= INTENT_THRESHOLD:
        prior['REAL_BUG'] += 0.2
    if facts.get('witness_in_domain') is False:
        prior['MISSING_PRECONDITION'] += 0.35
    return prior


def intent_confident(sel_row: dict | None) -> tuple:
    """The cross-validation rule's intent half: (ok, why)."""
    if not sel_row:
        return False, 'the property was never judged'
    intent = sel_row.get('intent')
    if intent:
        ok = intent.get('chosen') and intent.get('probability', 0) >= INTENT_THRESHOLD
        return bool(ok), (f"chosen intent of its rival group with p={intent.get('probability')}" if intent.get('chosen')
                          else 'a rival reading was chosen as the intent') + ('' if ok else
                                                                             f' (needs ≥ {INTENT_THRESHOLD})')
    label = (sel_row.get('judgment') or {}).get('label')
    ok = label not in ('UNSUPPORTED_BY_EVIDENCE', 'TOO_STRONG')
    return ok, f'no rival reading; judged {label}'


def allowed_defects(facts: dict) -> list:
    kind = facts.get('model_outcome_kind')
    if kind == 'out_of_fuel':
        return ['FUEL_BOUND']
    if kind == 'hole':
        return ['UNMODELED_CONSTRUCT', 'FRONTEND_MISTRANSLATION']
    return ['SEMANTICS_MISMATCH', 'FRONTEND_MISTRANSLATION']


# --- repair candidates ------------------------------------------------------------------

def _neg(cond: ast.expr) -> str:
    if isinstance(cond, ast.Compare) and len(cond.ops) == 1 and type(cond.ops[0]) in OPS:
        return f"{ast.unparse(cond.left)} {NEG[OPS[type(cond.ops[0])]]} {ast.unparse(cond.comparators[0])}"
    if isinstance(cond, ast.UnaryOp) and isinstance(cond.op, ast.Not):
        return ast.unparse(cond.operand)
    return f'not ({ast.unparse(cond)})'


def guard_preconditions(fn: dict) -> list:
    """Preconditions the code itself states: `if C: raise` ⇒ not C; `assert C` ⇒ C; an early
    return `if C: return …` ⇒ both C and not C (the property may be about either path)."""
    names, out = set(param_names(fn)), []
    try:
        tree = ast.parse((fn.get('source') or '').strip() or 'pass')
    except SyntaxError:
        for m in re.finditer(r'\bif\s*\((.+?)\)\s*(?:\{|return|goto)', fn.get('source') or ''):
            cond = m.group(1).strip()
            if set(re.findall(r'[A-Za-z_]\w*', cond)) & names:
                out += [('code guard', f'!({cond})'), ('code guard', cond)]
        return out

    def mentions(node):
        return {n.id for n in ast.walk(node) if isinstance(n, ast.Name)} & names

    for node in ast.walk(tree):
        if isinstance(node, ast.If) and mentions(node.test):
            first = node.body[0] if node.body else None
            if isinstance(first, ast.Raise):
                out.append(('code guard', _neg(node.test)))
            elif isinstance(first, ast.Return):
                out += [('code guard', _neg(node.test)), ('code guard', ast.unparse(node.test))]
        elif isinstance(node, ast.Assert) and mentions(node.test):
            out.append(('code guard', ast.unparse(node.test)))
    seen, uniq = set(), []
    for item in out:
        if item[1] not in seen:
            seen.add(item[1])
            uniq.append(item)
    return uniq


def domain_preconditions(fn: dict) -> list:
    out = [('docstring', pre) for _, pre in doc_constraints(fn)]
    for p, vals in tested_values(fn).items():
        nums = [x for x in vals if isinstance(x, int) and not isinstance(x, bool)]
        if len(nums) < 2:
            continue
        if min(nums) > 0:
            out.append(('tested domain', f'{p} > 0'))
        elif min(nums) >= 0:
            out.append(('tested domain', f'{p} >= 0'))
        out.append(('tested domain', f'{min(nums)} <= {p} <= {max(nums)}'))
    return out


def _literals(text: str) -> set:
    text = text or ''
    nums = {m.group(0).lstrip('+') for m in re.finditer(r'(?<![\w.])[-+]?\d+(?![\w.])', text)}
    return nums | {a or b for a, b in re.findall(r'"([^"]*)"|\'([^\']*)\'', text)}


def witness_constants(pre: str, inputs: dict, fn: dict, english: str) -> list:
    """Witness values a precondition mentions that no evidence mentions (an overfit patch)."""
    allowed = _literals(fn.get('source') or '') | _literals(fn.get('doc') or '') | _literals(english) | \
        {v for t in fn.get('tests') or [] for v in _literals(t.get('text') or '')} | {'0', '1'}
    used = _literals(pre)
    bad = []
    for v in (inputs or {}).values():
        s = str(v)
        if s in used and s not in allowed:
            bad.append(s)
    return bad


def candidates(stmt: dict, prop: dict, check: dict, fn: dict, cls: str) -> tuple:
    """(repair options, dropped): each option restates the English; none mentions a witness
    constant without evidence."""
    english = prop.get('text') or stmt.get('english') or ''
    ce = check.get('counterexample') or {}
    inputs = ce.get('inputs') or {}
    out, dropped = [dict(id='REJECT', kind='reject', evidence='none',
                         text='Reject the property: it does not describe intended behavior.', english=None)], []
    existing = {stmt.get('pre') or ''}
    pres = guard_preconditions(fn) + domain_preconditions(fn)
    for i, (source, pre) in enumerate(pres):
        bad = witness_constants(pre, inputs, fn, english)
        if bad:
            dropped.append(dict(precondition=pre, reason=f'mentions witness value(s) {bad} found in no evidence'))
            continue
        if pre in existing:
            continue
        existing.add(pre)
        if _holds(pre, inputs) is True:
            dropped.append(dict(precondition=pre, reason='the witness satisfies it: it would not exclude the '
                                                         'counterexample'))
            continue
        out.append(dict(id=f'PRECONDITION_{i}', kind='precondition', evidence=source, precondition=pre,
                        text=f'Add precondition from the {source}: {pre}',
                        english=f'Assuming {pre}: {english}'))
    t = english
    for pat, a, b in ((r'\bexactly when\b', 'whenever', 'only when'),
                      (r'\bif and only if\b', 'if', 'only if'), (r'\biff\b', 'if', 'only if')):
        if re.search(pat, t, re.I):
            out.append(dict(id='WEAKEN_IF', kind='weaken', evidence='none', english=re.sub(pat, a, t, flags=re.I),
                            text='Keep one direction: ' + re.sub(pat, a, t, flags=re.I)))
            out.append(dict(id='WEAKEN_ONLY_IF', kind='weaken', evidence='none',
                            english=re.sub(pat, b, t, flags=re.I),
                            text='Keep the other direction: ' + re.sub(pat, b, t, flags=re.I)))
            break
    exc = raised(ce.get('model'))
    if exc and exc not in english:
        out.append(dict(id='ALLOW_EXCEPTION', kind='exceptions', evidence='none',
                        english=english.rstrip('. ') + f', unless it raises {exc}.',
                        text=f'Treat raising {exc} as permitted behavior (the function signals invalid input).'))
    return out[:16], dropped


def repair_prior(option: dict, cls: str) -> float:
    fit = {'reject': {'BAD_SPEC': 0.45, 'MISSING_PRECONDITION': 0.1},
           'weaken': {'BAD_SPEC': 0.5, 'MISSING_PRECONDITION': 0.1},
           'precondition': {'MISSING_PRECONDITION': 0.7, 'BAD_SPEC': 0.2},
           'exceptions': {'MISSING_PRECONDITION': 0.4, 'BAD_SPEC': 0.3}}.get(option['kind'], {}).get(cls, 0.05)
    support = {'docstring': 0.3, 'code guard': 0.25, 'tested domain': 0.2}.get(option.get('evidence'), 0)
    return round(max(0.01, fit + support), 4)


# --- the stage --------------------------------------------------------------------------

def adjudicate(translation: dict, statements: list, checks: list, out_dir, *, judge='auto', english=None,
               selection=None, models=None, formalize_fn=None, check_fn=None, budget_usd=None, rounds=ROUNDS,
               domain_size=64, runtime=True) -> dict:
    """Classify every refuted statement, repair where the class allows it; write adjudication.json."""
    from .formalize import statement_id
    from .pipeline import metered
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    jd, info = make_judge(judge, out, 'adjudicate')
    fns = {f['name']: f for f in map(_d, translation.get('functions') or [])}
    props = {(s['function'], _d(p)['id']): _d(p) for s in map(_d, english or []) for p in s.get('properties') or []}
    summaries = {s['function']: s.get('summary', '') for s in map(_d, english or [])}
    sel = {(r['function'], r['property']): r for r in (selection or {}).get('properties', [])}
    models_by = {m['function']: m for m in map(_d, models or [])}
    by_check = {c['statement']: c for c in map(_d, checks or [])}
    records, new_stmts, new_checks, new_props, lineage, skipped = [], [], [], [], {}, []
    frontier = [s for s in map(_d, statements or []) if (by_check.get(s['id']) or {}).get('status') in REFUTED]
    spent = 0.0
    for round_no in range(1, rounds + 2):
        todo = []                      # (parent record, new property, function)
        for stmt in frontier:
            fn = fns.get(stmt['function'])
            if fn is None:
                continue
            chk = by_check[stmt['id']]
            key = (stmt['function'], stmt.get('property'))
            prop = props.get(key) or dict(id=stmt.get('property'), text=stmt.get('english', ''), evidence=[])
            row = sel.get(key) or sel.get((stmt['function'], (lineage.get(stmt['id']) or {}).get('root_property')))
            allowed, facts = gates(chk, fn, row)
            ce = chk.get('counterexample') or {}
            state = dict(full_state(fn), english=prop.get('text', stmt.get('english')),
                         evidence=prop.get('evidence') or [], lean_precondition=stmt.get('pre'),
                         lean_postcondition=stmt.get('post'), check_status=chk['status'],
                         counterexample=dict(inputs=ce.get('inputs'), model_outcome=ce.get('model'),
                                             real_code_outcome=ce.get('runtime')),
                         input_domain=facts.get('domain'))
            d = jd.classify_counterexample(state, allowed, classification_prior(prop, row, facts),
                                           dict(statement=stmt['id'], round=round_no))
            rec = dict(statement=stmt['id'], function=stmt['function'], property=stmt.get('property'),
                       round=round_no, status=chk['status'], english=prop.get('text', stmt.get('english')),
                       evidence=prop.get('evidence') or [], counterexample=ce, allowed=allowed, facts=facts,
                       classification=d['chosen'], probabilities=d['probabilities'], forced=bool(d.get('forced')),
                       margin=margin(d['probabilities']),
                       decision=d['decision_id'], parent=(lineage.get(stmt['id']) or {}).get('parent'))
            records.append(rec)
            cls = d['chosen']
            if cls == 'INCOMPLETE_MODEL':
                dallowed = allowed_defects(facts)
                prior = {k: 0.1 + (0.4 if k == ('UNMODELED_CONSTRUCT' if facts['model_outcome_kind'] == 'hole'
                                                else 'SEMANTICS_MISMATCH') else 0) for k in dallowed}
                dd = jd.classify_model_defect(dict(state, gate=facts.get('gate')), dallowed, prior,
                                              dict(statement=stmt['id']))
                m = models_by.get(stmt['function'])
                rec['model_defect'] = dict(classification=dd['chosen'], allowed=dallowed,
                                           probabilities=dd['probabilities'], forced=bool(dd.get('forced')),
                                           decision=dd['decision_id'], gate=facts.get('gate'),
                                           model=(m or {}).get('lean_name') or translation.get('call_template'),
                                           model_status=(m or {}).get('status'),
                                           owner='model stage' if m else 'translation')
                rec['disposition'] = 'model_defect'
                continue
            if cls == 'REAL_BUG':
                ext = external_evidence(prop.get('evidence'))
                ok_intent, why = intent_confident(row)
                rec['cross_validation'] = dict(external_evidence=ext, intent_confident=ok_intent, intent=why)
                rec['disposition'] = 'finding' if ext and ok_intent else 'suspected_bug'
                continue
            if cls in ('ENVIRONMENT_MISMATCH', 'ABSTRACTION_ARTIFACT'):
                rec['disposition'] = cls.lower()
                continue
            if round_no > rounds:
                rec['disposition'] = 'repair_limit'
                continue
            options, dropped = candidates(stmt, prop, chk, fn, cls)
            prior = {o['id']: repair_prior(o, cls) for o in options}
            pres = [o for o in options if o['kind'] == 'precondition']
            rec['repair'] = dict(offered=[o['id'] for o in options], dropped=dropped)
            if cls == 'MISSING_PRECONDITION' and len(pres) >= 2:
                pp = jd.select_precondition(state, pres, {o['id']: prior[o['id']] for o in pres},
                                            dict(statement=stmt['id'], classification=cls))
                rec['repair']['precondition'] = dict(chosen=pp['chosen'], decision=pp['decision_id'],
                                                     probabilities=pp['probabilities'])
                options = [o for o in options if o['kind'] != 'precondition' or o['id'] == pp['chosen']]
            pick = jd.rank_repairs(state, options, {o['id']: prior[o['id']] for o in options},
                                   dict(statement=stmt['id'], classification=cls))
            chosen = next(o for o in options if o['id'] == pick['chosen'])
            rec['repair'].update(chosen=chosen['id'], kind=chosen['kind'], text=chosen['text'],
                                 english=chosen.get('english'), decision=pick['decision_id'],
                                 options=[o['id'] for o in options], probabilities=pick['probabilities'],
                                 margin=margin(pick['probabilities']))
            if chosen['kind'] == 'reject':
                rec['disposition'] = 'rejected_by_repair'
                continue
            dup = [p for (f, _), p in props.items() if f == stmt['function']
                   and ' '.join(p.get('text', '').split()) == ' '.join(chosen['english'].split())]
            if dup:
                rec['disposition'] = 'repair_duplicates_existing'
                rec['repair']['duplicate_of'] = dup[0]['id']
                continue
            if budget_usd is not None and spent + EST_FORMALIZE_USD > budget_usd:
                rec['disposition'] = 'repair_skipped_budget'
                rec['repair']['skipped'] = f'budget: ${spent:.2f} spent of ${budget_usd:.2f}'
                skipped.append(dict(function=stmt['function'], property=stmt.get('property'),
                                    reason=rec['repair']['skipped']))
                continue
            new_id = f"{stmt.get('property')}_r{round_no}"
            root = (lineage.get(stmt['id']) or {}).get('root', stmt['id'])
            root_prop = (lineage.get(stmt['id']) or {}).get('root_property', stmt.get('property'))
            newp = dict(id=new_id, text=chosen['english'], kind=prop.get('kind', 'postcondition'),
                        evidence=list(prop.get('evidence') or []) + [f"repair:{chosen['kind']}"
                                                                      + (f" ({chosen['evidence']})"
                                                                         if chosen.get('evidence') != 'none' else '')],
                        parent=stmt.get('property'))
            sid = statement_id(stmt['function'], new_id)
            rec['repaired_by'] = sid
            rec['disposition'] = 'repaired'
            lineage[sid] = dict(parent=stmt['id'], root=root, root_property=root_prop, round=round_no,
                                repair_kind=chosen['kind'], repair=chosen['id'])
            props[(stmt['function'], new_id)] = newp
            new_props.append(dict(newp, function=stmt['function'], statement=sid, round=round_no))
            todo.append((rec, newp, stmt['function']))
        if not todo or formalize_fn is None or check_fn is None:
            break
        work = out / 'repair' / f'round{round_no}'
        work.mkdir(parents=True, exist_ok=True)
        specs: dict = {}
        for _, p, f in todo:
            specs.setdefault(f, dict(function=f, summary=summaries.get(f, ''), properties=[], model='repair'))
            specs[f]['properties'].append({k: p[k] for k in ('id', 'text', 'kind', 'evidence')})
        with metered() as box:
            got = [_d(s) for s in formalize_fn(translation, list(specs.values()), work) or []]
        spent += box[0]
        for s in got:
            s['parent'] = lineage.get(s['id'], {}).get('parent')
        res = [_d(c) for c in check_fn(translation, got, work, domain_size=domain_size, runtime=runtime) or []]
        new_stmts += got
        new_checks += res
        by_check.update({c['statement']: c for c in res})
        frontier = [s for s in got if (by_check.get(s['id']) or {}).get('status') in REFUTED]
        if not frontier:
            break
    record_skips(out, 'adjudicate', skipped)
    findings = [r['statement'] for r in records if r.get('disposition') == 'finding']
    result = dict(judge=info, rounds=rounds, records=records, statements=new_stmts, checks=new_checks,
                  properties=new_props, lineage=lineage, findings=findings, cost_usd=round(spent, 4),
                  counts={k: sum(1 for r in records if r.get('disposition') == k) for k in
                          sorted({r.get('disposition') for r in records if r.get('disposition')})})
    (out / FILES['adjudication']).write_text(json.dumps(result, indent=1, ensure_ascii=False, default=str))
    return result
