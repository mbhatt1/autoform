"""Selection with a budget: the typed-decision judge (SemIf/OpenJev) ranks English properties.

    describe ─► english.json ─► select ─► selection.json ─► formalize (selected, in utility order)

For each function the judge sees the *interface* view only — name, signature, docstring,
tests, callers — never the body: shown `return True`, a judge rates "always returns True" as
the intended contract (see autoform.harness.pipeline._state). It makes three decisions:

  PROPERTY_JUDGMENT     per property: USEFUL_PROPERTY | SECURITY_RELEVANT | TRIVIAL | …
  PROPERTY_SELECTION    listwise: which property is most worth proving
  INTENT_SELECTION      among mutually incompatible properties (same call and domain,
                        different outcome), which reading is intended

A utility combines them with deterministic facts (evidence other than "implementation" up,
security relevance up, trivial/vacuous down, the losing reading of a rival group down). A
global `--budget-usd` is then allocated across functions in priority order (utility, damped
by the property's rank inside its function so one function cannot take everything); what
does not fit, or exceeds `--max-properties-per-function`, is recorded as skipped, with the
reason. The formalize and prove stages then spend in that order and stop when the money is
gone (`formalize_within_budget`, `order_by_utility`).

The judge never sets a status. Its decisions choose what to try first; every status still
comes from Lean (elaboration, `decide +kernel`, kernel-checked proofs) or a real execution.

Decisions are appended to decisions-<stage>.jsonl; `finalize_decisions` joins them with the
verifier outcomes into decisions.jsonl and exports JEVBench rows (jevbench.jsonl).

Backends (`--judge`): semif (SemIf, ~/semif/.venv), heuristic (deterministic priors, offline),
replay:PATH (a previous decisions.jsonl), auto (semif if installed, else heuristic).
"""
from __future__ import annotations

import json
import os
import re
from dataclasses import asdict
from pathlib import Path

from ..harness import bench
from ..harness.judge import CLAIM_JUDGMENTS, DecisionLog, Judge, make_scorer
from .schema import FILES

INTENT_THRESHOLD = 0.8          # as in the harness: a confident intent pick
RANK_DAMPING = 0.85             # priority = utility * RANK_DAMPING ** (rank inside the function)
EST_FORMALIZE_USD = float(os.environ.get('AUTOFORM_EST_FORMALIZE_USD', 0.05))
EST_PROVE_USD = float(os.environ.get('AUTOFORM_EST_PROVE_USD', 0.60))

EVIDENCE_WEIGHTS = {'tests': 0.5, 'docstring': 0.4, 'caller': 0.3, 'comments': 0.2, 'name': 0.15}
SECURITY = re.compile(r'\b(auth\w*|permission\w*|privilege\w*|admin|root|password\w*|token\w*|secret\w*|'
                      r'saniti[sz]\w*|escap\w*|inject\w*|owner\w*|access|allow\w*|den(y|ies|ied)|role\w*|'
                      r'signature|verif\w*|encrypt\w*|decrypt\w*|hash\w*|csrf|xss|sql|traversal|'
                      r'overflow\w*|out[- ]of[- ]bounds|untrusted|valid(ate|ates|ation|ated)?)\b', re.I)
TRIVIAL = re.compile(r'(returns a value of type|twice with the same arguments|same arguments gives the same|'
                     r'returns an? (integer|int|string|str|bool|boolean|float|value|number|result)\s*\.?$|'
                     r'does not (crash|raise an unexpected))', re.I)

_SCORERS: dict = {}


# --- the judge -----------------------------------------------------------------------

class StageJudge(Judge):
    """harness.judge.Judge with stage-prefixed decision ids (several stages share one run)."""

    def __init__(self, scorer, log, stage, temperature=None):
        super().__init__(scorer, log, temperature)
        self.stage = stage

    def _next(self, task):
        self.counter += 1
        return f'D_{self.stage}_{self.counter:04d}_{task}'


def scorer_for(spec: str):
    """(scorer, note). One scorer per spec per process: SemIf loads its weights once."""
    requested = spec or 'auto'
    if requested in _SCORERS:
        return _SCORERS[requested]
    spec, note = requested, ''
    if spec == 'auto':
        py = Path(os.environ.get('AUTOFORM_SEMIF_PYTHON', Path.home() / 'semif/.venv/bin/python'))
        spec = 'semif' if py.exists() else 'heuristic'
        note = f'auto: {spec}'
    try:
        scorer = make_scorer(spec)
    except (RuntimeError, OSError) as exc:
        if spec != 'semif':
            raise
        scorer, note = make_scorer('heuristic'), f'semif unavailable ({exc}); fell back to heuristic'
    _SCORERS[requested] = (scorer, note)
    return scorer, note


def make_judge(spec: str, out: Path, stage: str):
    scorer, note = scorer_for(spec)
    log = DecisionLog(Path(out) / f'decisions-{stage}.jsonl')
    return StageJudge(scorer, log, stage), dict(requested=spec, backend=scorer.name, note=note,
                                                metadata=getattr(scorer, 'metadata', {}))


# --- the interface view -------------------------------------------------------------

def _d(x):
    return asdict(x) if hasattr(x, '__dataclass_fields__') else dict(x)


def signature(fn: dict) -> str:
    params = ', '.join(p['name'] + (f": {p.get('integer_type') or p.get('sort')}" if p.get('sort') not in
                                    (None, 'any') or p.get('integer_type') else '') for p in fn.get('params') or [])
    return f"{fn.get('source_name') or fn['name']}({params}) -> {fn.get('returns', 'any')}"


def interface_state(fn: dict) -> dict:
    """What intent questions may see: no implementation."""
    return dict(function=signature(fn), file=fn.get('file', ''), documentation=(fn.get('doc') or '')[:400],
                tests=[f"{t.get('location', '')}: {(t.get('text') or '')[:160]}" for t in (fn.get('tests') or [])[:8]],
                callers=list(fn.get('callers') or [])[:8])


def full_state(fn: dict) -> dict:
    """Counterexample questions (is the code or the claim wrong?) need the implementation."""
    return dict(interface_state(fn), implementation=(fn.get('source') or '')[:2000])


# --- deterministic facts ----------------------------------------------------------------

def evidence_kinds(evidence) -> set:
    out = set()
    for e in evidence or []:
        e = str(e).strip().lower()
        for k in EVIDENCE_WEIGHTS:
            if e.startswith(k) or (k == 'tests' and e.startswith('test')):
                out.add(k)
    return out


def evidence_score(evidence) -> float:
    return round(min(1.0, sum(EVIDENCE_WEIGHTS[k] for k in evidence_kinds(evidence))), 4)


def external_evidence(evidence) -> list:
    """Evidence other than the implementation (the finding rule needs some)."""
    return [e for e in evidence or [] if str(e).strip()
            and not str(e).lower().startswith(('implementation', 'repair'))]


def security_relevant(prop: dict, fn: dict) -> bool:
    return bool(SECURITY.search(prop.get('text', '')) or SECURITY.search(fn.get('source_name') or fn['name'])
                or SECURITY.search(fn.get('doc') or ''))


def judgment_prior(prop: dict, fn: dict) -> dict:
    """The heuristic judge's answer to PROPERTY_JUDGMENT (and SemIf's fallback prior)."""
    p = {k: 0.1 for k in CLAIM_JUDGMENTS}
    ev = evidence_score(prop.get('evidence'))
    text = prop.get('text', '')
    if ev:
        p['USEFUL_PROPERTY'] += 0.2 + 0.3 * ev
    else:
        p['UNSUPPORTED_BY_EVIDENCE'] += 0.25
    if prop.get('kind') in ('postcondition', 'exception', 'invariant') and not TRIVIAL.search(text):
        p['USEFUL_PROPERTY'] += 0.15
    if security_relevant(prop, fn) and SECURITY.search(text + ' ' + (fn.get('source_name') or '')):
        p['SECURITY_RELEVANT'] += 0.45
    if TRIVIAL.search(text):
        p['TRIVIAL'] += 0.5
    if prop.get('kind') == 'example':
        p['TOO_WEAK'] += 0.15
    return p


# --- rival readings -----------------------------------------------------------------

_CALL = r'(?P<call>[A-Za-z_][\w.]*\s*\([^()]*\))'
_PATTERNS = [
    re.compile(r'^(?:if|when|whenever)\s+(?P<cond>.+?),\s*' + _CALL + r'\s+(?P<verb>returns|raises|is)\s+(?P<out>.+?)\.?$', re.I),
    re.compile(r'^(?P<cond>for (?:all|any|every)\b[^,]*),\s*' + _CALL + r'\s+(?P<verb>returns|raises|is)\s+(?P<out>.+?)\.?$', re.I),
    re.compile(r'^' + _CALL + r'\s+(?P<verb>returns|raises|is)\s+(?P<out>.+?)(?:\s+(?:if|when)\s+(?P<cond>.+?))?\.?$', re.I),
]
_VAGUE_OUT = re.compile(r'^(an? |the )?(integer|int|string|str|bool|boolean|float|value|number|result|'
                        r'non-?negative|positive|negative)\b', re.I)


def _norm(s: str) -> str:
    return re.sub(r'\s+', ' ', (s or '').strip().lower().rstrip('.'))


def parse_outcome(text: str):
    """(key, verb, outcome) for 'If C, f(x) returns V' / 'For all …, f(x) returns V' / 'f(1) returns 2'."""
    t = ' '.join(text.split())
    for pat in _PATTERNS:
        m = pat.match(t)
        if m:
            call = re.sub(r'\s+', '', m.group('call'))
            return (_norm(m.group('cond') or ''), call.lower()), m.group('verb').lower(), _norm(m.group('out'))
    return None


def incompatible(a: dict, b: dict) -> bool:
    pa, pb = parse_outcome(a.get('text', '')), parse_outcome(b.get('text', ''))
    if not pa or not pb or pa[0] != pb[0]:
        return False
    (_, va, oa), (_, vb, ob) = pa, pb
    if oa == ob and va == vb:
        return False
    if va != vb and 'raises' in (va, vb):
        return True           # one reading returns, the other raises, on the same inputs
    if _VAGUE_OUT.match(oa) or _VAGUE_OUT.match(ob):
        return False          # "returns an integer" is compatible with "returns a + b"
    return True


def rival_groups(props: list) -> list:
    """Connected components of the incompatibility relation (size ≥ 2)."""
    groups, seen = [], set()
    for i, p in enumerate(props):
        if i in seen:
            continue
        comp, todo = {i}, [i]
        while todo:
            k = todo.pop()
            for j, q in enumerate(props):
                if j not in comp and incompatible(props[k], q):
                    comp.add(j)
                    todo.append(j)
        if len(comp) > 1:
            seen |= comp
            groups.append(sorted(comp))
    return groups


# --- utility and budget ----------------------------------------------------------------

def utility(prop: dict, judgment: dict, select_p: float, n: int, intent: dict | None, security: bool) -> float:
    """U = .30·Useful + .25·Security + .20·Selection + .20·Evidence + .10·Nontrivial
           − .10·Unsupported − .05·TooStrong − .10·implementation-only ± intent."""
    j = judgment or {}
    nontrivial = 1 - j.get('TRIVIAL', 0) - j.get('LIKELY_VACUOUS', 0)
    sec = max(j.get('SECURITY_RELEVANT', 0), 0.5 if security else 0)
    u = (0.30 * j.get('USEFUL_PROPERTY', 0) + 0.25 * sec + 0.20 * min(1.0, select_p * max(n, 1))
         + 0.20 * evidence_score(prop.get('evidence')) + 0.10 * nontrivial
         - 0.10 * j.get('UNSUPPORTED_BY_EVIDENCE', 0) - 0.05 * j.get('TOO_STRONG', 0)
         - 0.10 * (not external_evidence(prop.get('evidence'))))
    if intent:
        u += 0.10 if intent.get('chosen') else -0.15
    return round(u, 4)


def estimate(prove: bool) -> dict:
    per = EST_FORMALIZE_USD + (EST_PROVE_USD if prove else 0.0)
    return dict(formalize_usd=EST_FORMALIZE_USD, prove_usd=EST_PROVE_USD if prove else 0.0, per_property_usd=per)


def allocate(rows: list, budget_usd, max_per_function, est: dict) -> float:
    """Mark rows selected/skipped in priority order; return the planned spend.

    Priority is utility damped by the property's rank inside its function. Rows are taken
    greedily; the first row whose estimate does not fit stops the allocation (everything
    after it is skipped for budget), so a cheap low-utility property never jumps the queue."""
    by_fn: dict = {}
    for r in sorted(rows, key=lambda r: -r['utility']):
        by_fn.setdefault(r['function'], []).append(r)
    for items in by_fn.values():
        for rank, r in enumerate(items):
            r['rank'] = rank
            r['priority'] = round(r['utility'] * RANK_DAMPING ** rank, 4)
    planned, stopped = 0.0, False
    order = sorted(rows, key=lambda r: (-r['priority'], r['function'], r['property']))
    for i, r in enumerate(order):
        r['order'] = i
        r['est_cost_usd'] = est['per_property_usd']
        # The cap trims implementation-only guesses; a property the docs or tests state is
        # never dropped by it (it can still lose to the budget, in priority order).
        if max_per_function is not None and r['rank'] >= max_per_function and not r.get('external'):
            r.update(selected=False, skip_reason=f"max-properties-per-function {max_per_function} "
                                                 f"(rank {r['rank'] + 1} in its function)")
            continue
        if stopped or (budget_usd is not None and planned + r['est_cost_usd'] > budget_usd + 1e-9):
            stopped = True
            r.update(selected=False, skip_reason=f"budget: estimated ${planned + r['est_cost_usd']:.2f} would exceed "
                                                 f"${budget_usd:.2f} (utility {r['utility']})")
            continue
        planned += r['est_cost_usd']
        r.update(selected=True, skip_reason=None)
    rows.sort(key=lambda r: r['order'])
    return round(planned, 4)


# --- the select stage -------------------------------------------------------------------

def select(translation: dict, english: list, out_dir, *, judge='auto', budget_usd=None,
           max_properties_per_function=None, prove=True) -> dict:
    """Judge, rank and budget every English property; write selection.json."""
    from .formalize import statement_id
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    jd, info = make_judge(judge, out, 'select')
    fns = {f['name']: f for f in map(_d, translation.get('functions') or [])}
    rows, per_fn = [], []
    for spec in map(_d, english or []):
        fn = fns.get(spec['function'])
        props = [_d(p) for p in spec.get('properties') or []]
        if fn is None or not props:
            continue
        state = interface_state(fn)
        texts = [f"{p['text']}\n(kind: {p.get('kind')}; evidence: {', '.join(map(str, p.get('evidence') or [])) or 'none'})"
                 for p in props]
        ctx = [dict(function=fn['name'], property=p['id'], statement=statement_id(fn['name'], p['id'])) for p in props]
        decisions = jd.judge_claims(state, texts, [judgment_prior(p, fn) for p in props], ctx)
        judged = {p['id']: d for p, d in zip(props, decisions)}
        sel = jd.select(state, [dict(id=p['id'], text=t) for p, t in zip(props, texts)],
                        {p['id']: 0.2 + 0.5 * judged[p['id']]['probabilities'].get('USEFUL_PROPERTY', 0)
                         + 0.5 * judged[p['id']]['probabilities'].get('SECURITY_RELEVANT', 0) for p in props},
                        dict(function=fn['name'])) if len(props) > 1 else {props[0]['id']: 1.0}
        intents, fn_intents = {}, []
        for gi, group in enumerate(rival_groups(props)):
            members = [props[i] for i in group]
            d = jd.intent(state, [dict(id=p['id'], text=texts[i]) for i, p in zip(group, members)],
                          {p['id']: sel.get(p['id'], 0.1) + 0.1 for p in members},
                          dict(function=fn['name'], group=[p['id'] for p in members]))
            fn_intents.append(dict(group=[p['id'] for p in members], chosen=d['chosen'],
                                   probabilities=d['probabilities'], decision=d['decision_id']))
            for p in members:
                intents[p['id']] = dict(group=gi, chosen=p['id'] == d['chosen'],
                                        probability=round(d['probabilities'].get(p['id'], 0), 4),
                                        rivals=[q['id'] for q in members if q is not p], decision=d['decision_id'])
        per_fn.append(dict(function=fn['name'], rival_groups=[i['group'] for i in fn_intents], intent=fn_intents))
        for p in props:
            probs = judged[p['id']]['probabilities']
            sec = security_relevant(p, fn)
            rows.append(dict(function=fn['name'], source_name=fn.get('source_name'), property=p['id'],
                             statement=statement_id(fn['name'], p['id']), text=p['text'], kind=p.get('kind'),
                             evidence=p.get('evidence') or [],
                             external=bool(external_evidence(p.get('evidence'))),
                             judgment=dict(label=max(probs, key=probs.get), probabilities=probs,
                                           decision=judged[p['id']]['decision_id']),
                             selection_probability=round(sel.get(p['id'], 0), 4), intent=intents.get(p['id']),
                             security=sec,
                             utility=utility(p, probs, sel.get(p['id'], 0), len(props), intents.get(p['id']), sec)))
    est = estimate(prove)
    planned = allocate(rows, budget_usd, max_properties_per_function, est)
    result = dict(judge=info, budget_usd=budget_usd, max_properties_per_function=max_properties_per_function,
                  estimates=est, planned_usd=planned, functions=per_fn, properties=rows,
                  selected=sum(r['selected'] for r in rows), skipped=sum(not r['selected'] for r in rows))
    (out / FILES['selection']).write_text(json.dumps(result, indent=1, ensure_ascii=False, default=str))
    return result


# --- spending in utility order -------------------------------------------------------

def selected_english(english: list, selection: dict) -> list:
    """english.json restricted to the selected properties, functions and properties in priority order."""
    order = {(r['function'], r['property']): r['order'] for r in selection.get('properties', []) if r['selected']}
    specs = []
    for spec in map(_d, english or []):
        props = sorted((_d(p) for p in spec.get('properties') or [] if (spec['function'], _d(p)['id']) in order),
                       key=lambda p: order[(spec['function'], p['id'])])
        if props:
            specs.append(dict(spec, properties=props))
    specs.sort(key=lambda s: order[(s['function'], s['properties'][0]['id'])])
    return specs


def record_skips(out: Path, stage: str, items: list):
    """Append budget/cap skips to budget.json (the report's "spent vs budget" section)."""
    f = Path(out) / FILES['budget']
    data = json.loads(f.read_text()) if f.is_file() else {'skipped': []}
    data['skipped'] = [s for s in data['skipped'] if s.get('stage') != stage] + [dict(s, stage=stage) for s in items]
    f.write_text(json.dumps(data, indent=1, ensure_ascii=False))


def formalize_within_budget(fn, translation: dict, english: list, out_dir, selection: dict, budget_usd,
                            wave: int = 3, **kw) -> list:
    """Run the formalize stage function on the selected properties in priority order, `wave`
    at a time, and stop once the spend reaches `budget_usd`. Writes statements.json."""
    from .pipeline import metered
    from .schema import dump
    out = Path(out_dir)
    order = {(r['function'], r['property']): r['order'] for r in selection.get('properties', [])}
    queue = sorted(((s, p) for s in selected_english(english, selection) for p in s['properties']),
                   key=lambda sp: order[(sp[0]['function'], sp[1]['id'])])
    statements, skipped = [], []
    with metered() as box:
        for start in range(0, len(queue), max(1, wave)):
            if budget_usd is not None and box[0] >= budget_usd:
                skipped = [dict(function=s['function'], property=p['id'],
                                reason=f'budget spent before formalize (${box[0]:.2f} of ${budget_usd:.2f})')
                           for s, p in queue[start:]]
                break
            batch: dict = {}
            for s, p in queue[start:start + wave]:
                batch.setdefault(s['function'], dict(s, properties=[]))['properties'].append(p)
            statements += [_d(x) for x in fn(translation, list(batch.values()), out, **kw) or []]
    dump(statements, out / FILES['statements'])
    record_skips(out, 'formalize', skipped)
    return statements


def utilities(out: Path) -> dict:
    """statement id → utility (repaired statements inherit their root's)."""
    sel = _json(out / FILES['selection']) or {}
    u = {r['statement']: r['utility'] for r in sel.get('properties', [])}
    adj = _json(out / FILES['adjudication']) or {}
    for s in adj.get('statements', []):
        u.setdefault(s['id'], u.get((adj.get('lineage') or {}).get(s['id'], {}).get('root'), 0))
    return u


def order_by_utility(statements: list, out: Path) -> list:
    u = utilities(out)
    return sorted((_d(s) for s in statements or []), key=lambda s: -u.get(s['id'], 0))


def _json(path: Path):
    try:
        return json.loads(Path(path).read_text()) if Path(path).is_file() else None
    except ValueError:
        return None


def _jsonl(path: Path) -> list:
    if not Path(path).is_file():
        return []
    return [json.loads(line) for line in Path(path).read_text().splitlines() if line.strip()]


# --- decision log + JEVBench -------------------------------------------------------------

HARNESS_STATUS = {'PROVED': 'PROVED', 'BOUNDED_HOLDS': 'BOUNDED_PROVED', 'REFUTED_MODEL': 'REFUTED'}


def statement_outcome(sid: str, checks: dict, proofs: dict) -> dict:
    c, p = checks.get(sid) or {}, proofs.get(sid) or {}
    status = 'PROVED' if p.get('status') == 'PROVED' else c.get('status')
    return dict(nl_status=status, status=HARNESS_STATUS.get(status, status), check=c.get('status'),
                proof=p.get('status'), detail=(c.get('detail') or '')[:160])


def label(entry: dict) -> dict:
    """bench.label where its rules apply to this flow, plus the rules this flow adds."""
    task, out = entry['task'], entry.get('outcome') or {}
    if entry.get('forced'):
        return dict(kind='forced')
    if task == 'PROPERTY_JUDGMENT':
        if out.get('skipped'):
            return dict(kind='unlabeled', reason='not verified: ' + out['skipped'])
        if out.get('nl_status') == 'UNCHECKABLE':
            # "No domain point meets the precondition" may be a vacuous property or just a
            # finite domain that misses the one input it is about: not settled.
            return dict(kind='unlabeled', reason='unchecked: ' + (out.get('detail') or '')[:80])
        if out.get('nl_status') == 'REFUTED_RUNTIME' or out.get('classification') == 'INCOMPLETE_MODEL':
            return dict(kind='unlabeled', reason='the refutation is attributed to the model, not the property')
    if task in ('COUNTEREXAMPLE_CLASSIFICATION', 'REPAIR_SELECTION', 'PRECONDITION_SELECTION'):
        if out.get('repair_nl_status') == 'REFUTED_RUNTIME':
            return dict(kind='unlabeled', reason='the repaired statement fails on the real code but not the '
                                                 'model: a model defect, not evidence about the repair')
        if out.get('repair_elaborates') is False:
            return dict(kind='unlabeled', reason='the repaired English did not formalize')
        if out.get('repair_skipped'):
            return dict(kind='unlabeled', reason='repair not verified: ' + out['repair_skipped'])
    return bench.label(entry)


def finalize_decisions(out_dir) -> dict:
    """decisions-*.jsonl + verifier outcomes → decisions.jsonl, jevbench.jsonl; returns counts."""
    out = Path(out_dir)
    entries = []
    for stage in ('select', 'adjudicate'):
        entries += _jsonl(out / f'decisions-{stage}.jsonl')
    checks = {c['statement']: c for c in (_json(out / FILES['checks']) or [])}
    proofs = {p['statement']: p for p in (_json(out / FILES['proofs']) or [])}
    sel = _json(out / FILES['selection']) or {}
    adj = _json(out / FILES['adjudication']) or {}
    checks.update({c['statement']: c for c in adj.get('checks', [])})
    stmts = {s['id']: s for s in (_json(out / FILES['statements']) or []) + adj.get('statements', [])}
    skipped_by_prop = {r['statement']: r['skip_reason'] for r in sel.get('properties', []) if not r['selected']}
    for s in (_json(out / FILES['budget']) or {}).get('skipped', []):
        if s.get('stage') == 'formalize':
            from .formalize import statement_id
            skipped_by_prop[statement_id(s['function'], s['property'])] = s['reason']
    records = {r['statement']: r for r in adj.get('records', [])}
    for e in entries:
        ctx = e.get('context') or {}
        sid = ctx.get('statement')
        if not sid:
            continue
        o = statement_outcome(sid, checks, proofs)
        if sid in skipped_by_prop:
            o['skipped'] = skipped_by_prop[sid]
        elif sid not in stmts:
            o['skipped'] = 'not formalized'
        rec = records.get(sid) or {}
        if rec:
            o.update(classification=rec.get('classification'), disposition=rec.get('disposition'))
            rep = rec.get('repair') or {}
            o.update(repair_chosen=rep.get('chosen'), repair_kind=rep.get('kind'))
            child = rec.get('repaired_by')
            if child:
                ro = statement_outcome(child, checks, proofs)
                o.update(repair_status=ro['status'], repair_nl_status=ro['nl_status'],
                         repair_elaborates=bool((stmts.get(child) or {}).get('elaborates')))
            elif rep.get('skipped'):
                o['repair_skipped'] = rep['skipped']
        e['outcome'] = o
    (out / FILES['decisions']).write_text(''.join(json.dumps(e, default=str, ensure_ascii=False) + '\n'
                                                  for e in entries))
    rows = []
    for e in entries:
        lab = label(e)
        if lab['kind'] == 'forced':
            continue
        rows.append(dict(id=e['decision_id'], task=e['task'], state=e.get('state'), question=e.get('question'),
                         options=[dict(id=i, description=d) for i, d in
                                  zip(e.get('options', []), e.get('option_descriptions', []))],
                         model_choice=e.get('chosen'), option_logits=e.get('option_logits'),
                         backend=e.get('backend'), label=lab, outcome=e.get('outcome')))
    (out / FILES['jevbench']).write_text(''.join(json.dumps(r, default=str, ensure_ascii=False) + '\n' for r in rows))
    kinds: dict = {}
    for r in rows:
        kinds[r['label']['kind']] = kinds.get(r['label']['kind'], 0) + 1
    tasks: dict = {}
    for e in entries:
        tasks[e['task']] = tasks.get(e['task'], 0) + 1
    return dict(decisions=len(entries), forced=sum(1 for e in entries if e.get('forced')), by_task=tasks,
                jevbench_rows=len(rows), labels=kinds)
