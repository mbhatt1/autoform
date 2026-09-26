"""Counterexample-guided refinement with bounded, penalized repair.

    C_0 → Verify(C_0) → witness → Judge.classify → [REAL_BUG: stop, report]
                                               → [else: repairs r_1..r_k → Judge.rank → C_1 → Verify …]

Anti-overfitting rules (design §29–30):
  * at most `max_refinements` rounds;
  * Complexity(C_{i+1}) ≤ Complexity(C_i) + δ; larger repairs are never offered;
  * a repair may not mention the witness's concrete values unless those constants
    already occur in the program or its evidence (no `x ≠ 42` patches);
  * every repair that adds an assumption is scored down, and prose assumptions make
    the eventual result ASSUMPTION_DEPENDENT rather than PROVED;
  * a counterexample classified REAL_BUG is never repaired away — the claim stays
    REFUTED and becomes a finding.
"""
from __future__ import annotations

import copy

from . import claims as C
from .judge import COUNTEREXAMPLE_CLASSES

DELTA = 12
MAX_REFINEMENTS = 5


def value_sort(model_outcome: str):
    for sort, key in (('int', 'Val.int'), ('bool', 'Val.bool'), ('str', 'Val.str'), ('float', 'Val.float')):
        if 'EResult.val' in (model_outcome or '') and key in model_outcome:
            return sort
    return None


def explain(claim, witness, program) -> str:
    """One sentence a judge can read: what the claim required and what the model did."""
    outcome = witness.get('model_outcome') or 'unknown'
    kind = witness.get('outcome_kind')
    got = {'value': 'returned ' + outcome.replace('Autoform.Core.', ''), 'exception': 'raised an exception',
           'undefined_behavior': 'reached undefined behavior (' + outcome.split('"')[1] + ')' if '"' in outcome
           else 'reached undefined behavior', 'hole': 'reached an unmodeled construct',
           'out_of_fuel': 'did not finish within the evaluation budget'}.get(kind, outcome)
    return (f"The claim requires {C.render_claim(claim, program).split(': ', 1)[-1]}; "
            f"with inputs {witness.get('inputs')} the function {got}.")


def allowed_classes(result: dict, fn, native_match, claim=None) -> list:
    """Deterministic facts first: narrow what the judge may choose between."""
    kind = (result.get('witness') or {}).get('outcome_kind')
    got = value_sort((result.get('witness') or {}).get('model_outcome'))
    if claim and kind == 'value' and claim.get('result_sort') and got and got != claim['result_sort']:
        return ['PROPERTY_TOO_STRONG']  # the claim assumed a result of another sort
    if kind == 'undefined_behavior':
        # The model states the behavior is undefined: either the code has a defect or
        # callers must never supply such inputs. Neither reading blames the model.
        return ['REAL_BUG', 'MISSING_PRECONDITION']
    if kind in ('hole', 'out_of_fuel'):
        return ['MODEL_INCOMPLETE']
    if native_match is False:
        return ['MODEL_INCOMPLETE']  # the model and the real runtime disagree at the witness
    classes = ['REAL_BUG', 'PROPERTY_TOO_STRONG', 'MISSING_PRECONDITION']
    if fn.calls and any(not c.resolved for c in fn.calls):
        classes.append('ENVIRONMENT_ASSUMPTION')
    if result.get('domain_size', 0) and native_match is None:
        classes.append('SOLVER_ARTIFACT')
    return classes


def classification_prior(claim, result, ctx, native_match) -> dict:
    prior = {k: 0.1 for k in COUNTEREXAMPLE_CLASSES}
    judged = ((claim.get('judgment') or {}).get('probabilities') or {})
    intended = judged.get('USEFUL_PROPERTY', 0) + judged.get('SECURITY_RELEVANT', 0)
    prior['REAL_BUG'] += 0.5 * intended
    prior['PROPERTY_TOO_STRONG'] += 0.5 * (judged.get('TOO_STRONG', 0) + judged.get('UNSUPPORTED_BY_EVIDENCE', 0))
    if claim['category'] == 'security' and ctx['security_relevant']:
        prior['REAL_BUG'] += 0.1
    if claim['provenance'].get('generator') == 'template' and not ctx['security_relevant']:
        prior['PROPERTY_TOO_STRONG'] += 0.4
    if any(e['type'] == 'guard' for e in ctx['evidence']):
        prior['MISSING_PRECONDITION'] += 0.2
    if C.independent_sources(claim) >= 2:
        prior['REAL_BUG'] += 0.2
    if (result.get('witness') or {}).get('outcome_kind') == 'undefined_behavior':
        prior['MISSING_PRECONDITION'] += 0.3
    if native_match is True:
        prior['REAL_BUG'] += 0.1
        prior['SOLVER_ARTIFACT'] = 0.02
    return prior


def _guard_atoms(fn, params_by_name):
    """Comparisons over parameters that the function itself branches on."""
    out = []
    names = {p.name: p.id for p in fn.params}
    ops = {'==': 'EQ', '!=': 'NEQ', '<': 'LT', '<=': 'LTE', '>': 'GT', '>=': 'GTE'}
    for br in fn.branches:
        cond = br.condition
        if not isinstance(cond, dict) or cond.get('k') != 'binop' or cond.get('op') not in ops:
            continue
        sides = []
        for side in (cond.get('a'), cond.get('b')):
            if isinstance(side, dict) and side.get('k') == 'name' and side.get('v') in names:
                sides.append({'param': names[side['v']]})
            elif isinstance(side, dict) and side.get('k') in ('int', 'str', 'bool') and 'v' in side:
                sides.append({'lit': side['v']})
            else:
                sides = None
                break
        if sides and any('param' in s for s in sides):
            atom = {'op': ops[cond['op']], 'args': sides}
            out += [atom, {'op': 'NOT', 'args': [atom]}]
    return out


def repairs(claim, result, fn, ctx) -> list:
    """Candidate repairs of a refuted claim, each a complete new claim."""
    base = C.complexity(claim)
    witness = (result.get('witness') or {}).get('inputs', {})
    out = []

    def add(rid, text, new, kind, new_assumptions=0, evidence='none'):
        for key in list(new):
            if key not in C.CLAIM_KEYS:
                del new[key]
        new.pop('id', None)
        new.pop('status', None)
        new['parent'] = claim['id']
        new['provenance'] = dict(claim['provenance'], repair=kind, repaired_from=claim['id'])
        new['evidence'] = claim['evidence'] + [{'type': 'counterexample', 'location': claim['id']}]
        if kind != 'reject' and C.complexity(new) > base + DELTA:
            return
        out.append(dict(id=rid, text=text, claim=new, kind=kind, new_assumptions=new_assumptions,
                        evidence=evidence))

    out.append(dict(id='REJECT', text='Reject the property: it does not describe intended behavior.',
                    claim=None, kind='reject', new_assumptions=0))
    prop = claim['property']
    # Weaken: an IFF becomes the one direction that survived, an AND drops a conjunct.
    if prop.get('op') == 'IFF':
        a, b = prop['args']
        for i, (x, y) in enumerate(((a, b), (b, a))):
            new = copy.deepcopy(claim)
            new['property'] = {'op': 'IMPLIES', 'args': [x, y]}
            add(f'WEAKEN_DIRECTION_{i}', 'Keep only one direction: ' +
                C.render(new['property'], {p.id: p.name for p in fn.params}), new, 'weaken')
    if prop.get('op') == 'AND':
        for i, _ in enumerate(prop['args']):
            new = copy.deepcopy(claim)
            rest = [a for j, a in enumerate(prop['args']) if j != i]
            new['property'] = rest[0] if len(rest) == 1 else {'op': 'AND', 'args': rest}
            add(f'DROP_CONJUNCT_{i}', 'Drop one conjunct: ' +
                C.render(new['property'], {p.id: p.name for p in fn.params}), new, 'weaken')
    # Exceptions: an exception at the witness may be the intended outcome.
    if (result.get('witness') or {}).get('outcome_kind') == 'exception' and claim.get('on_exception') != 'allowed':
        new = copy.deepcopy(claim)
        new['on_exception'] = 'allowed'
        add('ALLOW_EXCEPTIONS', 'Treat a raised exception as permitted behavior (the function signals '
            'invalid input by raising).', new, 'exceptions')
    # Preconditions from the function's own guards (evidence-backed, not witness-shaped).
    for i, atom in enumerate(_guard_atoms(fn, witness)):
        new = copy.deepcopy(claim)
        new['preconditions'] = claim['preconditions'] + [atom]
        add(f'GUARD_PRECONDITION_{i}', 'Add precondition taken from a branch in the code: ' +
            C.render(atom, {p.id: p.name for p in fn.params}), new, 'precondition', evidence='code guard')
    # Relational preconditions between parameters (no constants from the witness).
    params = [b['param'] for b in claim['forall'] if b['domain'] == 'int']
    if len(params) >= 2:
        for rel in ('NEQ', 'LT'):
            atom = {'op': rel, 'args': [{'param': params[0]}, {'param': params[1]}]}
            new = copy.deepcopy(claim)
            new['preconditions'] = claim['preconditions'] + [atom]
            add(f'REL_PRECONDITION_{rel}', 'Add precondition (no supporting evidence): ' +
                C.render(atom, {p.id: p.name for p in fn.params}), new, 'precondition')
    # Undefined-behavior guards derived from the function's own arithmetic and declared types.
    from .cpir import UWIDTHS, WIDTHS, integer_range
    by_name = {p.name: p for p in fn.params}
    bound = {b['param'] for b in claim['forall']}
    for i, e in enumerate(fn.arith):
        def t(x):
            return {'param': by_name[x].id} if isinstance(x, str) else {'lit': x}
        if any(isinstance(x, str) and (x not in by_name or by_name[x].id not in bound) for x in (e['a'], e['b'])):
            continue
        if e['op'] in ('<<', '>>', '>>>') and isinstance(e['b'], str):
            owner = by_name[e['a']] if isinstance(e['a'], str) else None
            wtype = e.get('type') or (owner.integer_type if owner else '')
            width = WIDTHS.get(wtype) or UWIDTHS.get(wtype)
            if width:
                atom = {'op': 'AND', 'args': [{'op': 'GTE', 'args': [t(e['b']), {'lit': 0}]},
                                              {'op': 'LT', 'args': [t(e['b']), {'lit': width}]}]}
                new = copy.deepcopy(claim)
                new['preconditions'] = claim['preconditions'] + [atom]
                add(f'SHIFT_IN_RANGE_{i}', f"Add precondition: shift amount {e['b']} in [0, {width})", new,
                    'precondition', evidence='declared operand width')
        elif e['op'] in ('+', '-', '*'):
            rng = integer_range(e.get('type', '')) or integer_range(fn.return_integer_type) or next(
                (integer_range(by_name[x].integer_type) for x in (e['a'], e['b'])
                 if isinstance(x, str) and integer_range(by_name[x].integer_type)), None)
            if rng:
                expr = {'op': {'+': 'ADD', '-': 'SUB', '*': 'MUL'}[e['op']], 'args': [t(e['a']), t(e['b'])]}
                atom = {'op': 'AND', 'args': [{'op': 'GTE', 'args': [expr, {'lit': rng[0]}]},
                                              {'op': 'LTE', 'args': [expr, {'lit': rng[1]}]}]}
                new = copy.deepcopy(claim)
                new['preconditions'] = claim['preconditions'] + [atom]
                add(f'NO_OVERFLOW_{i}', f"Add precondition: {e['a']} {e['op']} {e['b']} does not overflow "
                    f"[{rng[0]}, {rng[1]}]", new, 'precondition', evidence='declared operand width')
    # Nonzero divisors: only for parameters the code actually divides by.
    for e in fn.arith:
        if e['op'] in ('/', '//', '%') and isinstance(e['b'], str) and e['b'] in by_name \
                and by_name[e['b']].id in bound:
            atom = {'op': 'NEQ', 'args': [{'param': by_name[e['b']].id}, {'lit': 0}]}
            new = copy.deepcopy(claim)
            new['preconditions'] = claim['preconditions'] + [atom]
            add(f"NONZERO_{e['b']}", f"Add precondition: divisor {e['b']} ≠ 0", new, 'precondition',
                evidence='divisor in code')
    # Environment: assume an unmodeled external behaves as needed (heavily penalized).
    for ext in ctx['externals']:
        if ext['semantics'] in ('UNSUPPORTED', 'NONDETERMINISTIC'):
            new = copy.deepcopy(claim)
            new['assumptions'] = claim['assumptions'] + [f"`{ext['name']}` behaves as the caller expects"]
            add(f"ASSUME_{ext['name']}", f"Add assumption about `{ext['name']}` (environment).", new,
                'assumption', new_assumptions=1)
    return out[:16]


def repair_prior(repair, claim, ce_class) -> dict:
    """RepairScore = Fit − λ·Complexity − μ·NewAssumptions (fit comes from the class)."""
    fit = {'reject': {'PROPERTY_TOO_STRONG': 0.5, 'REAL_BUG': 0.2},
           'weaken': {'PROPERTY_TOO_STRONG': 0.6},
           'precondition': {'MISSING_PRECONDITION': 0.7, 'PROPERTY_TOO_STRONG': 0.2},
           'exceptions': {'MISSING_PRECONDITION': 0.5, 'PROPERTY_TOO_STRONG': 0.3},
           'assumption': {'ENVIRONMENT_ASSUMPTION': 0.6}}.get(repair['kind'], {}).get(ce_class, 0.05)
    growth = (C.complexity(repair['claim']) - C.complexity(claim)) if repair['claim'] else 0
    support = 0.25 if repair.get('evidence', 'none') != 'none' else -0.2 if repair['kind'] == 'precondition' else 0
    return max(0.01, fit + support - 0.02 * max(growth, 0) - 0.25 * repair['new_assumptions'])
