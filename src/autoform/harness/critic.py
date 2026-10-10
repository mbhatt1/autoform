"""Deterministic claim critic: reject bad candidates before any solver time is spent.

Checks are logical, over the claim alone (with the program abstracted away):
  * tautology      — the property holds for every parameter, result and outcome;
                     proving it would say nothing about the program;
  * contradiction  — the property fails for every result and outcome;
  * vacuity        — no sampled input satisfies the preconditions;
  * duplicate      — same canonical claim;
  * dominated      — another candidate with the same scope implies it (kept, ranked lower).
A claim passing the critic is only *worth trying*, never true.
"""
from __future__ import annotations

import itertools

from . import claims as C

OUTCOMES = ({'outcome:RETURNS': True, 'outcome:THROWS': False, 'outcome:TERMINATES': True},
            {'outcome:RETURNS': False, 'outcome:THROWS': True, 'outcome:TERMINATES': True},
            {'outcome:RETURNS': False, 'outcome:THROWS': False, 'outcome:TERMINATES': False})


def _results(sort, literals):
    if sort is None:
        return [None]
    return C.sample_values(sort, literals)


def _truth_table(claim, literals):
    """Yield (pre_holds, prop_value) over params × results × outcomes; None if undefined."""
    for env in C.assignments(claim, literals, limit=512):
        try:
            pre = all(C.eval_formula(p, env) for p in claim['preconditions'])
        except (C.Undefined, TypeError, KeyError):
            pre = None
        for result in _results(claim.get('result_sort'), literals):
            for outcome in OUTCOMES:
                if result is not None and not outcome['outcome:RETURNS']:
                    continue  # a result exists only on normal return
                scope = dict(env, **outcome)
                if result is not None:
                    scope['result'] = result
                try:
                    yield pre, C.eval_formula(claim['property'], scope)
                except (C.Undefined, TypeError, KeyError):
                    yield pre, None


def review(claim, fn) -> list:
    """Return a list of findings; any finding with severity 'reject' drops the claim."""
    findings = []
    if claim['structural']:
        return findings
    lits = [v for vals in fn.literals.values() for v in vals]
    table = list(_truth_table(claim, lits))
    defined = [(p, v) for p, v in table if p is not None and v is not None]
    if table and not any(p for p, _ in table if p is not None):
        findings.append(dict(check='vacuous_precondition', severity='reject',
                             detail='no sampled input satisfies the preconditions'))
    live = [v for p, v in defined if p]
    undefined = any(v is None for p, v in table if p)
    if live and all(live) and not undefined:
        findings.append(dict(check='tautology', severity='reject',
                             detail='holds for every input, result and outcome; independent of the program'))
    if live and not any(live):
        findings.append(dict(check='contradiction', severity='reject',
                             detail='fails for every result and outcome; cannot describe any program'))
    if C.complexity(claim) > 40:
        findings.append(dict(check='complexity', severity='warn', detail='large claim; low readability'))
    return findings


def implies(a, b, literals) -> bool:
    """a ⇒ b on every sampled point (same scope and quantification)."""
    if a['scope'] != b['scope'] or a['forall'] != b['forall'] or a['structural'] or b['structural']:
        return False
    if a.get('on_exception') != b.get('on_exception'):
        return False
    sort = a.get('result_sort') or b.get('result_sort')
    if a.get('result_sort') and b.get('result_sort') and a['result_sort'] != b['result_sort']:
        return False
    seen = False
    for env in C.assignments(a, literals, limit=512):
        for result in _results(sort, literals):
            for outcome in OUTCOMES:
                if result is not None and not outcome['outcome:RETURNS']:
                    continue
                scope = dict(env, **outcome)
                if result is not None:
                    scope['result'] = result
                try:
                    pa = all(C.eval_formula(p, scope) for p in a['preconditions']) and \
                        C.eval_formula(a['property'], scope)
                    pb = all(C.eval_formula(p, scope) for p in b['preconditions']) <= \
                        C.eval_formula(b['property'], scope)
                except (C.Undefined, TypeError, KeyError):
                    return False
                if pa and not pb:
                    return False
                seen = seen or pa
    return seen


def rivals(a, b, literals) -> bool:
    """No function can satisfy both: at some input, no result value meets both claims.

    Rival claims are competing readings of the same behavior; at most one can be the
    intended contract, so only one of them may later count as a finding."""
    if (a['scope'] != b['scope'] or a['structural'] or b['structural']
            or not (C.mentions_result(a['property']) and C.mentions_result(b['property']))
            or a.get('result_sort') != b.get('result_sort') or a['forall'] != b['forall']):
        return False
    outcome = OUTCOMES[0]
    for env in C.assignments(a, literals, limit=512):
        both = False
        for result in _results(a['result_sort'], literals):
            scope = dict(env, result=result, **outcome)
            try:
                ok_a = not all(C.eval_formula(p, scope) for p in a['preconditions']) or C.eval_formula(a['property'], scope)
                ok_b = not all(C.eval_formula(p, scope) for p in b['preconditions']) or C.eval_formula(b['property'], scope)
            except (C.Undefined, TypeError, KeyError):
                return False
            if ok_a and ok_b:
                both = True
                break
        if not both:
            return True
    return False


def rival_groups(accepted, program) -> list:
    """Connected components of the rivalry relation (groups of size ≥ 2)."""
    parent = {c['id']: c['id'] for c in accepted}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for a, b in itertools.combinations(accepted, 2):
        fn = program.by_id[a['scope']['target']]
        lits = [v for vals in fn.literals.values() for v in vals]
        if rivals(a, b, lits):
            parent[find(a['id'])] = find(b['id'])
    groups = {}
    for c in accepted:
        groups.setdefault(find(c['id']), []).append(c)
    return [g for g in groups.values() if len(g) > 1]


def screen(candidates, program):
    """Validate, deduplicate, critique. Returns (accepted, rejected)."""
    accepted, rejected, seen = [], [], {}
    for raw in candidates:
        try:
            claim = C.validate(raw, program)
        except C.ClaimError as exc:
            rejected.append(dict(claim=raw, stage='validation', reason=str(exc)))
            continue
        if claim['id'] in seen:
            seen[claim['id']]['evidence'] += [e for e in claim['evidence']
                                              if e not in seen[claim['id']]['evidence']]
            rejected.append(dict(claim=claim, stage='duplicate', reason='duplicate of ' + claim['id']))
            continue
        fn = program.by_id[claim['scope']['target']]
        findings = review(claim, fn)
        claim['critic'] = findings
        if any(f['severity'] == 'reject' for f in findings):
            rejected.append(dict(claim=claim, stage='critic',
                                 reason='; '.join(f['check'] for f in findings if f['severity'] == 'reject')))
            continue
        seen[claim['id']] = claim
        accepted.append(claim)
    for a, b in itertools.permutations(accepted, 2):
        fn = program.by_id[a['scope']['target']]
        lits = [v for vals in fn.literals.values() for v in vals]
        if implies(a, b, lits) and not implies(b, a, lits):
            b.setdefault('dominated_by', []).append(a['id'])
    return accepted, rejected
