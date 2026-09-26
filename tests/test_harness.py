"""The formalization harness: generator → judge → verifier, with the judge outside the TCB.

Most tests are pure Python. The Lean-backed end-to-end test runs with AUTOFORM_TEST_LEAN=1
against the checked-in PipelineSecurityVulnerable model.
"""
from __future__ import annotations

import json
import os
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))

from autoform.harness import cegis, claims as C, compiler, cpir, critic, judge, report, bench  # noqa: E402
from autoform.harness import verifier  # noqa: E402
from autoform.harness.environment import Environment  # noqa: E402
from autoform.harness.evidence import context  # noqa: E402
from autoform.harness.generator import TemplateGenerator  # noqa: E402


def fn_ast(name, params, body, types=None, itypes=None, ret='ANY', rtype=''):
    return dict(name=name, file='m.py', sourceName=name.rsplit('.', 1)[-1], params=params,
                paramTypes=types or ['ANY'] * len(params), paramIntegerTypes=itypes or [''] * len(params),
                returnType=ret, returnIntegerType=rtype, body=body)


N = lambda v: {'k': 'name', 'v': v}  # noqa: E731
AUTH = fn_ast('m.py:<module>.authorize', ['owner', 'caller'],
              {'k': 'ret', 'e': {'k': 'binop', 'op': '==', 'a': N('owner'), 'b': N('caller')}},
              ret='__builtin.bool')
ADD = fn_ast('add', ['a', 'b'], {'k': 'ret', 'e': {'k': 'unop', 'op': 'cast:i64', 'a': {
    'k': 'binop', 'op': 'num:c:i64:+', 'a': N('a'), 'b': N('b')}}}, itypes=['i64', 'i64'], rtype='i64')
DIV = fn_ast('div', ['a', 'b'], {'k': 'ret', 'e': {'k': 'binop', 'op': '//', 'a': N('a'), 'b': N('b')}})
# `verify_token` runs on only one branch, so the final `write_acl` is reachable without it.
GRANT = fn_ast('grant', ['user', 'fast'], {'k': 'seq',
    'a': {'k': 'ifte', 'c': N('fast'),
          't': {'k': 'skip'},
          'e': {'k': 'exprS', 'e': {'k': 'call', 'f': 'verify_token', 'args': [N('user')]}}},
    'b': {'k': 'exprS', 'e': {'k': 'call', 'f': 'write_acl', 'args': [N('user')]}}})


def program(tmp_path, functions, module='M'):
    path = tmp_path / f'ast-{module}.json'
    path.write_text(json.dumps(functions))
    return cpir.build(path, module)


def auth_claim(p, prop, forall=None, pre=()):
    fn = p.by_name['m.py:<module>.authorize']
    o, c = fn.params
    return dict(scope={'kind': 'function', 'target': fn.id}, category='security',
                forall=forall if forall is not None else [{'param': o.id, 'domain': 'int'},
                                                          {'param': c.id, 'domain': 'int'}],
                preconditions=list(pre), property=prop, evidence=[{'type': 'test', 'location': 't.py:1'}])


def eq_result_true(p):
    fn = p.by_name['m.py:<module>.authorize']
    o, c = fn.params
    return {'op': 'IFF', 'args': [{'op': 'EQ', 'args': [{'result': True}, {'lit': True}]},
                                  {'op': 'EQ', 'args': [{'param': o.id}, {'param': c.id}]}]}


# --- CPIR -------------------------------------------------------------------------------

def test_cpir_ids_are_deterministic_and_sorted(tmp_path):
    a = program(tmp_path, [ADD, AUTH])
    b = program(tmp_path, [AUTH, ADD])
    assert [(f.id, f.name) for f in a.functions] == [(f.id, f.name) for f in b.functions]
    assert a.by_name['add'].id == 'F_0001'
    assert a.by_name['add'].arith == [dict(op='+', a='a', b='b', type='i64')]


def test_claim_id_survives_positional_id_shifts(tmp_path):
    p1 = program(tmp_path, [AUTH])
    p2 = program(tmp_path, [ADD, AUTH])  # authorize is now F_0002, its params V_0003/V_0004
    c1 = C.validate(auth_claim(p1, eq_result_true(p1)), p1)
    c2 = C.validate(auth_claim(p2, eq_result_true(p2)), p2)
    assert c1['scope']['target'] != c2['scope']['target']
    assert c1['id'] == c2['id']


# --- the claim grammar rejects hallucinated or ill-typed claims ------------------------

@pytest.mark.parametrize('mutate, message', [
    (lambda c: c['scope'].update(target='F_9999'), 'scope'),
    (lambda c: c['property']['args'][1]['args'].__setitem__(0, {'param': 'V_0099'}), 'unknown'),
    (lambda c: c.update(forall=c['forall'][:1]), 'quantify every parameter'),
    (lambda c: c.update(property={'op': 'EXPLOITABLE'}), 'outside the claim grammar'),
    (lambda c: c.update(property={'op': 'LT', 'args': [{'result': True}, {'lit': 'x'}]}), 'int'),
    (lambda c: c.update(property={'op': 'EQ', 'args': [{'result': True}, {'result': True}]}), 'reflexive'),
    (lambda c: c.update(verified=True), 'unknown claim fields'),
])
def test_validation_rejects(tmp_path, mutate, message):
    p = program(tmp_path, [AUTH])
    claim = auth_claim(p, eq_result_true(p))
    mutate(claim)
    with pytest.raises(C.ClaimError, match=message):
        C.validate(claim, p)


def test_structural_claims_must_name_mentioned_callees(tmp_path):
    p = program(tmp_path, [GRANT])
    fn = p.by_name['grant']
    base = dict(scope={'kind': 'function', 'target': fn.id}, category='security')
    C.validate(dict(base, property={'op': 'BEFORE', 'first': 'verify_token', 'then': 'write_acl'}), p)
    with pytest.raises(C.ClaimError, match='never mentions'):
        C.validate(dict(base, property={'op': 'BEFORE', 'first': 'check_admin', 'then': 'write_acl'}), p)


# --- critic ------------------------------------------------------------------------------

def test_critic_rejects_tautology_contradiction_and_vacuity(tmp_path):
    p = program(tmp_path, [AUTH])
    fn = p.by_name['m.py:<module>.authorize']
    o, c = fn.params
    eq = {'op': 'EQ', 'args': [{'param': o.id}, {'param': c.id}]}
    taut = auth_claim(p, {'op': 'OR', 'args': [eq, {'op': 'NOT', 'args': [eq]}]})
    contra = auth_claim(p, {'op': 'AND', 'args': [{'op': 'EQ', 'args': [{'result': True}, {'lit': True}]},
                                                  {'op': 'EQ', 'args': [{'result': True}, {'lit': False}]}]})
    vacuous = auth_claim(p, eq_result_true(p), pre=[{'op': 'LT', 'args': [{'param': o.id}, {'param': o.id}]}])
    good = auth_claim(p, eq_result_true(p))
    accepted, rejected = critic.screen([taut, contra, vacuous, good, dict(good)], p)
    reasons = sorted(r['reason'] for r in rejected)
    assert [a['id'] for a in accepted] == [C.validate(good, p)['id']]
    assert any('tautology' in r for r in reasons)
    assert any('contradiction' in r for r in reasons)
    assert any('vacuous' in r for r in reasons)
    assert any(r.startswith('duplicate') for r in reasons)


# --- compiler ----------------------------------------------------------------------------

def test_compiler_emits_outcome_match_and_typed_domain(tmp_path):
    p = program(tmp_path, [ADD])
    fn = p.by_name['add']
    a, b = fn.params
    claim = C.validate(dict(scope={'kind': 'function', 'target': fn.id},
                            forall=[{'param': a.id, 'domain': 'int'}, {'param': b.id, 'domain': 'int'}],
                            property={'op': 'EQ', 'args': [{'result': True},
                                                           {'op': 'ADD', 'args': [{'param': a.id}, {'param': b.id}]}]}),
                       p)
    ob = compiler.Obligation(claim, fn, p, 'M', fuel=64)
    prop = ob.prop()
    assert 'runFunc Autoform.Generated.M.program 64 "add"' in prop
    assert '| .val (.int res) => ((x0_a + x1_b) = res)' in prop
    assert '| .exn _ => False' in prop and '| _ => False' in prop   # holes and exceptions violate
    flat = {v for point in ob.points for v in point}
    assert 2 ** 63 - 1 in flat and -2 ** 63 in flat and max(flat) <= 2 ** 63 - 1


def test_lean_strings_are_escaped():
    assert compiler.lean_str('a"b\\c\n') == '"a\\"b\\\\c\\n"'


# --- judge: typed decisions, logged, forced where facts decide -------------------------

def test_heuristic_judge_logs_and_forces(tmp_path):
    log = judge.DecisionLog(tmp_path / 'd.jsonl')
    j = judge.Judge(judge.HeuristicScorer(), log)
    d = j.classify_counterexample({'x': 1}, ['MODEL_INCOMPLETE'], {}, {'claim': 'C_1'})
    assert d['forced'] and d['chosen'] == 'MODEL_INCOMPLETE' and d['backend'] == 'forced'
    d = j.classify_counterexample({'x': 1}, ['REAL_BUG', 'PROPERTY_TOO_STRONG'],
                                  {'REAL_BUG': 0.1, 'PROPERTY_TOO_STRONG': 0.9}, {'claim': 'C_1'})
    assert d['chosen'] == 'PROPERTY_TOO_STRONG'
    assert abs(sum(d['probabilities'].values()) - 1) < 1e-9
    assert len((tmp_path / 'd.jsonl').read_text().splitlines()) == 2


def test_replay_judge_reproduces_recorded_scores(tmp_path):
    rows = [dict(id='r', state={'s': 1}, question='q?', options=[dict(id='A', description='a'),
                                                                  dict(id='B', description='b')])]
    record = dict(key=judge.row_key(rows[0]), option_ids=['A', 'B'], option_logits=[0.0, 3.0])
    path = tmp_path / 'replay.jsonl'
    path.write_text(json.dumps(record) + '\n')
    out = judge.ReplayScorer(path).score(rows)
    assert out[0]['probabilities'][1] > 0.9 and not out[0].get('replay_miss')


def test_semif_scorer_reports_missing_install(monkeypatch, tmp_path):
    monkeypatch.setenv('AUTOFORM_SEMIF_PYTHON', str(tmp_path / 'nope/python'))
    with pytest.raises(RuntimeError, match='SemIf interpreter not found'):
        judge.SemIfScorer()


# --- CEGIS: deterministic facts gate the judge; repairs never use witness constants ------

def test_counterexample_classes_are_gated_by_facts(tmp_path):
    p = program(tmp_path, [ADD])
    fn = p.by_name['add']
    ub = dict(witness=dict(outcome_kind='undefined_behavior'))
    hole = dict(witness=dict(outcome_kind='hole'))
    value = dict(witness=dict(outcome_kind='value'), domain_size=36)
    assert cegis.allowed_classes(ub, fn, None) == ['REAL_BUG', 'MISSING_PRECONDITION']
    assert cegis.allowed_classes(hole, fn, None) == ['MODEL_INCOMPLETE']
    assert cegis.allowed_classes(value, fn, False) == ['MODEL_INCOMPLETE']   # native disagrees with model
    assert 'REAL_BUG' in cegis.allowed_classes(value, fn, True)


def test_repairs_come_from_code_not_from_the_witness(tmp_path):
    p = program(tmp_path, [ADD, DIV])
    env = Environment(ROOT)
    for name, expect in (('add', 'NO_OVERFLOW_0'), ('div', 'NONZERO_b')):
        fn = p.by_name[name]
        a, b = fn.params
        claim = C.validate(dict(scope={'kind': 'function', 'target': fn.id},
                                forall=[{'param': a.id, 'domain': 'int'}, {'param': b.id, 'domain': 'int'}],
                                property={'op': 'EQ', 'args': [{'result': True}, {'param': a.id}]},
                                provenance={'generator': 'template'}), p)
        result = dict(witness=dict(inputs={'a': 12345, 'b': -777}, outcome_kind='value'))
        options = cegis.repairs(claim, result, fn, context(p, env, fn))
        ids = [o['id'] for o in options]
        assert expect in ids and 'REJECT' in ids
        for o in options:
            if o['claim']:
                text = json.dumps(o['claim'])
                assert '12345' not in text and '-777' not in text
                C.validate(o['claim'], p)      # every repair is itself a valid claim
                assert o['claim']['parent'] == claim['id']


# --- structural backend ----------------------------------------------------------------

def test_must_precede_finds_the_unchecked_path(tmp_path):
    p = program(tmp_path, [GRANT])
    fn = p.by_name['grant']
    backend = verifier.StructuralBackend({'grant': GRANT['body']})
    claim = C.validate(dict(scope={'kind': 'function', 'target': fn.id}, category='security',
                            property={'op': 'BEFORE', 'first': 'verify_token', 'then': 'write_acl'}), p)
    r = backend.verify(claim, fn)
    assert r['status'] == 'REFUTED' and 'without a preceding verify_token' in r['witness']['path']
    checked = {'k': 'seq', 'a': {'k': 'exprS', 'e': {'k': 'call', 'f': 'verify_token', 'args': []}},
               'b': GRANT['body']['b']}
    assert verifier._must_precede(checked, 'verify_token', 'write_acl')[0]
    # BEFORE is call order: a check whose result is ignored still precedes (see docs/harness.md).
    ignored = {'k': 'seq', 'a': {'k': 'ifte', 'c': {'k': 'call', 'f': 'verify_token', 'args': []},
                                 't': {'k': 'skip'}, 'e': {'k': 'skip'}}, 'b': GRANT['body']['b']}
    assert verifier._must_precede(ignored, 'verify_token', 'write_acl')[0]


# --- templates + routing -----------------------------------------------------------------

def test_templates_are_valid_and_routable(tmp_path):
    p = program(tmp_path, [AUTH, ADD, GRANT])
    env = Environment(ROOT)
    for fn in p.functions:
        cands = TemplateGenerator().generate(p, fn, context(p, env, fn))
        accepted, rejected = critic.screen(cands, p)
        assert not [r for r in rejected if r['stage'] == 'validation'], rejected
        for c in accepted:
            backends = [b['id'] for b in verifier.feasible_backends(c)]
            assert backends == (['cpir-structural'] if c['structural'] else ['lean-kernel'])


# --- report diff and bench labels --------------------------------------------------------

def test_formalization_diff_reports_lost_proofs():
    def rec(cid, status):
        return dict(id=cid, selected=True, status=status, text=cid, result={}, reason=None)
    old = dict(claims=[rec('C_a', 'PROVED'), rec('C_b', 'BOUNDED_PROVED')], critical_assumptions=[])
    new = dict(claims=[rec('C_a', 'PROVED'), rec('C_b', 'REFUTED'), rec('C_c', 'PROVED')],
               critical_assumptions=[])
    d = report.diff(old, new)
    assert [a['id'] for a, _ in d['lost']] == ['C_b']
    assert [a['id'] for a, _ in d['preserved']] == ['C_a']
    assert [c['id'] for c in d['new']] == ['C_c']
    assert '✗ 1 previously established claims lost' in report.diff_markdown(d)


def test_bench_labels_only_what_verification_settles():
    held = dict(task='REPAIR_SELECTION', chosen='NO_OVERFLOW_0', outcome=dict(repair_status='BOUNDED_PROVED'))
    again = dict(task='REPAIR_SELECTION', chosen='X', outcome=dict(repair_status='REFUTED'))
    bug = dict(task='COUNTEREXAMPLE_CLASSIFICATION', chosen='REAL_BUG', outcome=dict(status='REFUTED'))
    assert bench.label(held) == dict(kind='single', label='NO_OVERFLOW_0')
    assert bench.label(again)['kind'] == 'negative'
    assert bench.label(bug)['kind'] == 'unlabeled'          # intent needs a human


# --- end to end, Lean-backed ---------------------------------------------------------------

@pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_LEAN') != '1', reason='set AUTOFORM_TEST_LEAN=1')
def test_harness_refutes_the_vulnerable_policy_with_a_kernel_witness(tmp_path):
    from autoform.harness.pipeline import Harness, Options
    src = tmp_path / 'src'
    src.mkdir()
    (src / 'policy.py').write_text('def authorize(owner, caller):\n    return True\n')
    h = Harness(Options(root=ROOT, module='PipelineSecurityVulnerable', source=src, out=tmp_path / 'out',
                        judge='heuristic', cache=None, top_k=20,
                        ast=ROOT / 'ast-PipelineSecurityVulnerable.json'))
    data = h.run()
    by_text = {r['text']: r for r in data['claims'] if r['selected']}
    owner_only = by_text['authorize: ∀ owner:int caller:int. ((true = result) ↔ (owner = caller))']
    assert owner_only['status'] == 'REFUTED'
    assert owner_only['certificate']['certificate']['theorems'][0].startswith('refute_')
    assert owner_only['counterexample']['native_agrees'] is True
    assert by_text['authorize: ∀ owner:int caller:int. returns']['status'] == 'PROVED'
    assert (tmp_path / 'out/report.md').is_file() and (tmp_path / 'out/jevbench.jsonl').is_file()
