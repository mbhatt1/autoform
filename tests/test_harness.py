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
    d = j.classify_counterexample({'x': 1}, ['INCOMPLETE_MODEL'], {}, {'claim': 'C_1'})
    assert d['forced'] and d['chosen'] == 'INCOMPLETE_MODEL' and d['backend'] == 'forced'
    d = j.classify_counterexample({'x': 1}, ['REAL_BUG', 'BAD_SPEC'],
                                  {'REAL_BUG': 0.1, 'BAD_SPEC': 0.9}, {'claim': 'C_1'})
    assert d['chosen'] == 'BAD_SPEC'
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
    assert cegis.allowed_classes(hole, fn, None) == ['INCOMPLETE_MODEL']
    assert cegis.allowed_classes(value, fn, False) == ['INCOMPLETE_MODEL']   # native disagrees with model
    assert 'REAL_BUG' in cegis.allowed_classes(value, fn, True)
    assert 'ABSTRACTION_ARTIFACT' in cegis.allowed_classes(value, fn, None)
    assert 'ABSTRACTION_ARTIFACT' not in cegis.allowed_classes(value, fn, True)   # reproduced natively


def test_counterexample_vocabulary_matches_the_design():
    assert list(judge.COUNTEREXAMPLE_CLASSES) == ['REAL_BUG', 'BAD_SPEC', 'MISSING_PRECONDITION', 'INCOMPLETE_MODEL',
                                                  'ENVIRONMENT_MISMATCH', 'ABSTRACTION_ARTIFACT']
    # MODEL_INCOMPLETE is a verifier status, never a judge class (and vice versa).
    assert 'MODEL_INCOMPLETE' in verifier.STATUSES and 'MODEL_INCOMPLETE' not in judge.COUNTEREXAMPLE_CLASSES
    assert 'INCOMPLETE_MODEL' not in verifier.STATUSES
    classes = set(judge.COUNTEREXAMPLE_CLASSES)
    for kind in ('reject', 'weaken', 'precondition', 'exceptions', 'assumption'):
        repair = dict(kind=kind, claim=None, new_assumptions=0)
        assert {cegis.repair_prior(repair, {}, c) for c in classes} != {0.05}   # every kind fits some class


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
    too_strong = dict(task='PROPERTY_JUDGMENT', chosen='USEFUL_PROPERTY',
                      outcome=dict(status='REFUTED', classification='BAD_SPEC'))
    assert bench.label(too_strong) == dict(kind='acceptable', labels=['TOO_STRONG'])


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
    # Every established selected claim carries a proof-value judgment; it never changed a status.
    held = [r for r in data['claims'] if r['selected'] and r['status'] in report.HELD]
    assert held and all(r['proof_value']['label'] in judge.PROOF_VALUES for r in held)
    assert data['proof_values'] and sum(data['proof_values'].values()) == len(held)
    tasks = {json.loads(line)['task'] for line in (tmp_path / 'out/decisions.jsonl').read_text().splitlines()}
    assert 'PROOF_VALUE_JUDGMENT' in tasks


# --- new typed decisions: precondition selection, model defects, proof value ---------------

def stub_harness(tmp_path, functions, judge_spec='heuristic'):
    """A Harness without Lean: the judge-facing stages run on hand-written verifier results."""
    from autoform.harness import ledger
    from autoform.harness.pipeline import Harness, Options
    p = program(tmp_path, functions)
    h = Harness.__new__(Harness)
    h.o = Options(root=ROOT, module='M', native=False)
    h.program = p
    h.env = Environment(ROOT)
    h.log = judge.DecisionLog(tmp_path / 'decisions.jsonl')
    h.judge = judge.Judge(judge.make_scorer(judge_spec), h.log)
    h.ledger = ledger.AssumptionLedger()
    h.claims, h.review, h.rejected = {}, [], []
    h.contexts = {f.id: context(p, h.env, f) for f in p.functions}
    return h


def add_claim(h, name, prop, result, **extra):
    fn = h.program.by_name[name]
    claim = C.validate(dict(scope={'kind': 'function', 'target': fn.id}, category=extra.pop('category', 'functional'),
                            forall=[{'param': x.id, 'domain': 'int'} for x in fn.params], property=prop,
                            provenance={'generator': 'template'}, **extra), h.program)
    h.register(claim, fn, result)
    return claim['id']


def sum_prop(h):
    a, b = h.program.by_name['add'].params
    return {'op': 'EQ', 'args': [{'result': True}, {'op': 'ADD', 'args': [{'param': a.id}, {'param': b.id}]}]}


UB = dict(status='REFUTED', domain_size=36, witness=dict(inputs={'a': 1, 'b': 2},
          model_outcome='Autoform.Core.EResult.hole "ub:signed-overflow"', outcome_kind='undefined_behavior'))


def decisions(h, task):
    return [e for e in h.log.entries if e['task'] == task]


def test_precondition_selection_runs_before_repair_selection(tmp_path):
    h = stub_harness(tmp_path, [ADD])
    cid = add_claim(h, 'add', sum_prop(h), dict(UB))
    fresh = h.adjudicate(cid, 1)
    rec = h.claims[cid]
    assert rec['counterexample']['classification'] == 'MISSING_PRECONDITION'
    [pre] = decisions(h, 'PRECONDITION_SELECTION')
    assert sorted(pre['options']) == ['NO_OVERFLOW_0', 'REL_PRECONDITION_LT', 'REL_PRECONDITION_NEQ']
    assert pre['chosen'] == 'NO_OVERFLOW_0'                  # evidence-backed (declared width) wins
    [rep] = decisions(h, 'REPAIR_SELECTION')
    assert rep['options'] == ['REJECT', 'NO_OVERFLOW_0']      # only the selected precondition competes
    assert rec['repair']['precondition']['chosen'] == 'NO_OVERFLOW_0'
    assert rec['repair']['precondition']['decision'] == pre['decision_id']
    assert rec['repair']['chosen'] == 'NO_OVERFLOW_0' and rec['repair']['kind'] == 'precondition'
    assert fresh == [rec['repaired_by']] and h.claims[fresh[0]]['result']['status'] == 'PENDING'


def test_precondition_selection_is_replayable(tmp_path):
    (tmp_path / 'a').mkdir()
    h = stub_harness(tmp_path / 'a', [ADD])
    cid = add_claim(h, 'add', sum_prop(h), dict(UB))
    h.adjudicate(cid, 1)
    rows = []
    for e in h.log.entries:
        if e['task'] == 'PRECONDITION_SELECTION':   # flip the recorded scores
            e = dict(e, option_logits=[5.0 if o == 'REL_PRECONDITION_NEQ' else 0.0 for o in e['options']])
        rows.append(json.dumps(e))
    replay = tmp_path / 'replay.jsonl'
    replay.write_text('\n'.join(rows) + '\n')
    (tmp_path / 'b').mkdir()
    h2 = stub_harness(tmp_path / 'b', [ADD], judge_spec=f'replay:{replay}')
    cid2 = add_claim(h2, 'add', sum_prop(h2), dict(UB))
    h2.adjudicate(cid2, 1)
    [pre] = decisions(h2, 'PRECONDITION_SELECTION')
    assert pre['chosen'] == 'REL_PRECONDITION_NEQ' and not pre['replay_miss']
    [rep] = decisions(h2, 'REPAIR_SELECTION')
    assert 'REL_PRECONDITION_NEQ' in rep['options'] and 'NO_OVERFLOW_0' not in rep['options']


def test_no_precondition_selection_unless_missing_precondition(tmp_path):
    h = stub_harness(tmp_path, [DIV])
    a, _ = h.program.by_name['div'].params
    cid = add_claim(h, 'div', {'op': 'EQ', 'args': [{'result': True}, {'param': a.id}]},
                    dict(status='REFUTED', domain_size=36, witness=dict(inputs={'a': 3, 'b': 2}, outcome_kind='value',
                                                                         model_outcome='EResult.val (Val.int 1)')))
    h.adjudicate(cid, 1)
    assert h.claims[cid]['counterexample']['classification'] == 'BAD_SPEC'
    assert not decisions(h, 'PRECONDITION_SELECTION')
    [rep] = decisions(h, 'REPAIR_SELECTION')
    assert {'NONZERO_b', 'REL_PRECONDITION_NEQ', 'REL_PRECONDITION_LT'} <= set(rep['options'])
    assert 'precondition' not in h.claims[cid]['repair']


def test_model_defect_gates(tmp_path):
    p = program(tmp_path, [ADD, GRANT])
    add, grant = p.by_name['add'], p.by_name['grant']
    hole = lambda label: dict(witness=dict(outcome_kind='hole',  # noqa: E731
                                           model_outcome=f'Autoform.Core.EResult.hole "{label}"'))
    assert cegis.hole_label('Autoform.Core.EResult.hole "binop:**"') == 'binop:**'
    assert cegis.hole_label('Autoform.Core.EResult.val (Val.int 3)') is None
    assert cegis.allowed_defects('INCONSISTENT_MODEL', {}, add, None) == ['EVALUATOR_KERNEL_DISAGREEMENT']
    assert cegis.allowed_defects('MODEL_INCOMPLETE', dict(witness=dict(outcome_kind='out_of_fuel')), add, None) \
        == ['FUEL_BOUND']
    assert cegis.allowed_defects('MODEL_INCOMPLETE', hole('binop:**'), add, None) == \
        ['UNMODELED_CONSTRUCT', 'FRONTEND_MISTRANSLATION']
    unsupported = ['verify_token', 'write_acl']
    assert cegis.allowed_defects('MODEL_INCOMPLETE', hole('call:verify_token'), grant, None, unsupported) == \
        ['EXTERNAL_UNMODELED', 'FRONTEND_MISTRANSLATION']
    # A named hole never admits a semantics or fuel reading, even when natives disagree.
    assert cegis.allowed_defects('MODEL_INCOMPLETE', hole('call:verify_token:not-callable'), grant, False,
                                 unsupported) == ['UNMODELED_CONSTRUCT', 'FRONTEND_MISTRANSLATION']
    value = dict(witness=dict(outcome_kind='value', model_outcome='EResult.val (Val.int 1)'))
    assert cegis.allowed_defects('MODEL_INCOMPLETE', value, add, False) == ['SEMANTICS_MISMATCH',
                                                                           'FRONTEND_MISTRANSLATION']
    assert 'SEMANTICS_MISMATCH' not in cegis.allowed_defects('MODEL_INCOMPLETE', value, add, True)
    assert 'EXTERNAL_UNMODELED' in cegis.allowed_defects('MODEL_INCOMPLETE', value, grant, None, unsupported)
    for allowed in (['FUEL_BOUND'], ['SEMANTICS_MISMATCH', 'FRONTEND_MISTRANSLATION']):
        assert set(cegis.defect_prior(allowed, value, False)) == set(allowed)


def test_model_defects_are_diagnosed_reported_and_queued(tmp_path):
    h = stub_harness(tmp_path, [ADD])
    a, b = h.program.by_name['add'].params
    ge = lambda x: {'op': 'GTE', 'args': [{'result': True}, {'param': x.id}]}  # noqa: E731
    named = add_claim(h, 'add', sum_prop(h), dict(status='MODEL_INCOMPLETE', witness=dict(
        inputs={'a': 1, 'b': 2}, outcome_kind='hole', model_outcome='Autoform.Core.EResult.hole "binop:**"')))
    fuel = add_claim(h, 'add', ge(a), dict(status='MODEL_INCOMPLETE', witness=dict(
        inputs={'a': 1, 'b': 2}, outcome_kind='out_of_fuel', model_outcome='Autoform.Core.EResult.outOfFuel')))
    split = add_claim(h, 'add', ge(b), dict(status='INCONSISTENT_MODEL', witness_candidate=[1, 2]))
    refuted = add_claim(h, 'add', {'op': 'GTE', 'args': [{'result': True}, {'lit': 0}]}, dict(UB))
    h.diagnose()
    d = {cid: h.claims[cid].get('model_defect') for cid in (named, fuel, split, refuted)}
    assert d[named]['classification'] == 'UNMODELED_CONSTRUCT' and not d[named]['forced']
    assert d[named]['hole_label'] == 'binop:**'
    assert d[fuel] == dict(d[fuel], classification='FUEL_BOUND', forced=True)
    assert d[split] == dict(d[split], classification='EVALUATOR_KERNEL_DISAGREEMENT', forced=True)
    assert d[refuted] is None
    # statuses are the verifier's, untouched
    assert [h.claims[c]['result']['status'] for c in (named, fuel, split)] == \
        ['MODEL_INCOMPLETE', 'MODEL_INCOMPLETE', 'INCONSISTENT_MODEL']
    queued = {x['claim']: x['classification'] for x in h.review if x['kind'] == 'model defect'}
    assert queued == {named: 'UNMODELED_CONSTRUCT', fuel: 'FUEL_BOUND', split: 'EVALUATOR_KERNEL_DISAGREEMENT'}
    [judged] = [e for e in decisions(h, 'MODEL_DEFECT_CLASSIFICATION') if not e.get('forced')]
    assert judged['options'] == ['UNMODELED_CONSTRUCT', 'FRONTEND_MISTRANSLATION']
    assert 'implementation' in judged['state']      # blame questions see the code


def test_counterexample_attributed_to_the_model_gets_a_defect_class(tmp_path):
    h = stub_harness(tmp_path, [ADD])
    cid = add_claim(h, 'add', sum_prop(h), dict(status='REFUTED', witness=dict(
        inputs={'a': 1, 'b': 2}, outcome_kind='hole', model_outcome='Autoform.Core.EResult.hole "cast:i64"')))
    assert h.adjudicate(cid, 1) == []
    rec = h.claims[cid]
    assert rec['counterexample']['classification'] == 'INCOMPLETE_MODEL'   # the judge's class (forced)
    assert rec['result']['status'] == 'MODEL_INCOMPLETE'                   # the status, set by rule
    h.diagnose()
    assert rec['model_defect']['allowed'] == ['UNMODELED_CONSTRUCT', 'FRONTEND_MISTRANSLATION']


def test_proof_value_uses_the_interface_view_and_never_sets_status(tmp_path):
    h = stub_harness(tmp_path, [ADD])
    a, _ = h.program.by_name['add'].params
    plain = add_claim(h, 'add', sum_prop(h), dict(status='PROVED'))
    repaired = add_claim(h, 'add', {'op': 'GTE', 'args': [{'result': True}, {'param': a.id}]},
                         dict(status='BOUNDED_PROVED', domain_size=36), parent='C_parent')
    refuted = add_claim(h, 'add', {'op': 'GTE', 'args': [{'result': True}, {'lit': 0}]}, dict(UB))
    h.judge_proof_values()
    rows = decisions(h, 'PROOF_VALUE_JUDGMENT')
    assert len(rows) == 2 and all('implementation' not in r['state'] for r in rows)
    assert set(rows[0]['options']) == set(judge.PROOF_VALUES)
    assert h.claims[plain]['proof_value']['label'] == 'ROUTINE'
    assert h.claims[repaired]['proof_value']['label'] == 'WEAKER_THAN_INTENDED'
    assert 'proof_value' not in h.claims[refuted]
    assert [h.claims[c]['result']['status'] for c in (plain, repaired)] == ['PROVED', 'BOUNDED_PROVED']


def test_report_card_shows_defect_value_and_precondition():
    r = dict(id='C_1', status='BOUNDED_PROVED', text='t', function='f', file='m.py', category='functional',
             subtype='x', backend='lean-kernel', evidence=[], assumptions=[], result={},
             confidence=dict(intent_confidence=0.5, model_confidence=1.0, proof_confidence=0.5),
             proof_value=dict(label='ROUTINE', probabilities={'ROUTINE': 0.7}),
             model_defect=dict(classification='FUEL_BOUND', forced=True, allowed=['FUEL_BOUND'], hole_label=None),
             repair=dict(text='Add precondition', precondition=dict(chosen='NO_OVERFLOW_0',
                                                                    options=['NO_OVERFLOW_0', 'REL_PRECONDITION_LT'])))
    text = '\n'.join(report.card(r))
    assert 'Proof value (judge; not a status): ROUTINE' in text
    assert 'Model defect: **FUEL_BOUND** — forced by verifier facts' in text
    assert 'Precondition chosen: NO_OVERFLOW_0' in text


def test_bench_labels_for_new_tasks():
    L = bench.label
    pre = lambda chosen, **o: dict(task='PRECONDITION_SELECTION', chosen=chosen, outcome=o)  # noqa: E731
    assert L(pre('P', repair_chosen='P', repair_status='BOUNDED_PROVED'))['kind'] == 'single'
    assert L(pre('P', repair_chosen='P', repair_status='REFUTED')) == dict(
        L(pre('P', repair_chosen='P', repair_status='REFUTED')), kind='negative', label='P')
    untested = L(pre('P', repair_chosen='REJECT', repair_status=None))
    assert untested['kind'] == 'unlabeled' and 'never verified' in untested['reason']
    ass = lambda chosen, **o: dict(task='ASSUMPTION_ACCEPTABILITY', chosen=chosen, outcome=o)  # noqa: E731
    assert L(ass('ACCEPTABLE', repair_status='REFUTED')) == dict(
        L(ass('ACCEPTABLE', repair_status='REFUTED')), kind='negative', label='ACCEPTABLE')
    unneeded = L(ass('ACCEPTABLE', repair_status='ASSUMPTION_DEPENDENT', assumption_free_sibling='C_s'))
    assert unneeded['kind'] == 'single' and unneeded['label'] == 'UNACCEPTABLE' and 'C_s' in unneeded['reason']
    assert L(ass('NEEDS_HUMAN_REVIEW', repair_status='ASSUMPTION_DEPENDENT'))['kind'] == 'unlabeled'
    assert L(ass('UNACCEPTABLE', repair_status=None, disposition='repair_refused'))['kind'] == 'unlabeled'
    for task in ('MODEL_DEFECT_CLASSIFICATION', 'PROOF_VALUE_JUDGMENT', 'INTENT_SELECTION', 'PROPERTY_SELECTION'):
        lab = L(dict(task=task, chosen='X', outcome=dict(status='PROVED')))
        assert lab['kind'] == 'unlabeled' and lab['reason']
    assert L(dict(task='MODEL_DEFECT_CLASSIFICATION', chosen='FUEL_BOUND', forced=True)) == dict(kind='forced')
    assert set(bench.TASKS) == {'PROPERTY_JUDGMENT', 'PROPERTY_SELECTION', 'INTENT_SELECTION',
                                'PRECONDITION_SELECTION', 'COUNTEREXAMPLE_CLASSIFICATION',
                                'MODEL_DEFECT_CLASSIFICATION', 'REPAIR_SELECTION', 'BACKEND_SELECTION',
                                'ASSUMPTION_ACCEPTABILITY', 'PROOF_VALUE_JUDGMENT'}


def test_assumption_free_sibling(tmp_path):
    h = stub_harness(tmp_path, [ADD])
    parent = add_claim(h, 'add', sum_prop(h), dict(UB))
    with_assumption = add_claim(h, 'add', sum_prop(h), dict(status='ASSUMPTION_DEPENDENT'),
                                assumptions=['`x` behaves'], parent=parent)
    rec = h.claims[parent]
    rec['repaired_by'] = with_assumption
    rec['repair'] = dict(chosen='ASSUME_x', kind='assumption', core=None)
    assert h.assumption_free_sibling(parent, rec) is None
    a, _ = h.program.by_name['add'].params
    sibling = add_claim(h, 'add', {'op': 'GTE', 'args': [{'result': True}, {'param': a.id}]},
                        dict(status='PROVED'), parent=parent)
    assert h.assumption_free_sibling(parent, rec) == sibling


def test_a_precondition_already_assumed_is_not_offered_again(tmp_path):
    shr = fn_ast('shr', ['a', 'b'], {'k': 'ret', 'e': {'k': 'binop', 'op': 'num:c:i32:>>', 'a': N('a'), 'b': N('b')}},
                 itypes=['i32', 'i32'], rtype='i32')
    p = program(tmp_path, [shr])
    fn = p.by_name['shr']
    a, b = fn.params
    claim = C.validate(dict(scope={'kind': 'function', 'target': fn.id},
                            forall=[{'param': a.id, 'domain': 'int'}, {'param': b.id, 'domain': 'int'}],
                            property={'op': 'GTE', 'args': [{'result': True}, {'lit': 0}]},
                            provenance={'generator': 'template'}), p)
    ctx = context(p, Environment(ROOT), fn)
    result = dict(witness=dict(inputs={'a': -1, 'b': 0}, outcome_kind='value'))
    [shift] = [o for o in cegis.repairs(claim, result, fn, ctx) if o['id'].startswith('SHIFT_IN_RANGE')]
    repaired = C.validate(shift['claim'], p)
    assert not [o for o in cegis.repairs(repaired, result, fn, ctx) if o['id'].startswith('SHIFT_IN_RANGE')]


# --- prover agent: the kernel, not the agent, decides ------------------------------------

from autoform.harness import prover  # noqa: E402


class _ScriptedAgent:
    """Stands in for the model: replies with a fixed text, whatever the prompt says."""
    name = 'scripted'

    def __init__(self, reply):
        self.reply = reply

    def run(self, prompt, cwd):
        return self.reply, 0.0


def _job(statement='theorem t (a b : Nat) : a + b = b + a'):
    return prover.Job(name='t', prefix='import Autoform.Lang.Core.Semantics\n', statement=statement)


def test_jobs_from_file_and_blueprints(tmp_path):
    f = tmp_path / 'x.lean'
    f.write_text('import Std\n/-- commutes -/\ntheorem a (n : Nat) : n + 0 = n := by\n  sorry\n\n'
                 'theorem b : True := trivial\n\ntheorem c : 1 = 1 := sorry\n')
    jobs = prover.jobs_from_file(f)
    assert [j.name for j in jobs] == ['a', 'c'] and jobs[0].blueprint == 'commutes'
    assert [j.name for j in prover.jobs_from_file(f, ['b'])] == ['b']


@pytest.mark.parametrize('reply', [
    '<proof>by\n  sorry</proof>',                                # forbidden construct
    '<proof>by\n  native_decide</proof>',
    '<proof>FAILED</proof><reason>too hard</reason>',
])
def test_prover_rejects_without_lean(tmp_path, reply):
    r = prover.prove(_job(), ROOT, tmp_path, agent=_ScriptedAgent(reply), attempts=1)
    assert r.status == 'FAILED'


@pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_LEAN') != '1', reason='set AUTOFORM_TEST_LEAN=1')
def test_prover_accepts_only_kernel_checked_proofs_of_the_original_statement(tmp_path):
    good = prover.prove(_job(), ROOT, tmp_path / 'good',
                        agent=_ScriptedAgent('<proof>by\n  exact Nat.add_comm a b</proof>'), attempts=1)
    assert good.status == 'PROVED' and set(good.axioms) <= prover.ALLOWED_AXIOMS
    wrong = prover.prove(_job(), ROOT, tmp_path / 'wrong',
                         agent=_ScriptedAgent('<proof>by\n  rfl</proof>'), attempts=1)
    assert wrong.status == 'FAILED' and 'independent check failed' in wrong.reason
    # A helper that restates the goal as an axiom-free lemma is fine; one that smuggles an
    # axiom is caught by the forbidden-token screen before Lean even runs.
    cheat = prover.prove(_job(), ROOT, tmp_path / 'cheat', attempts=1, agent=_ScriptedAgent(
        '<helpers>axiom magic : ∀ a b : Nat, a + b = b + a</helpers><proof>by\n  exact magic a b</proof>'))
    assert cheat.status == 'FAILED'


def test_prover_restore_rolls_back_only_lean_inputs_and_keeps_a_copy(tmp_path):
    import subprocess
    from autoform.harness import prover as P
    root = tmp_path / 'repo'
    (root / 'Lib').mkdir(parents=True)
    (root / 'Lib' / 'A.lean').write_text('def a := 1\n')
    (root / 'tool.py').write_text('x = 1\n')
    (root / 'notes.lean').write_text('-- user draft\n')
    git = lambda *a: subprocess.run(['git', '-C', str(root), *a], check=True, capture_output=True)
    git('init', '-q')
    git('add', '.')
    git('-c', 'user.email=t@t', '-c', 'user.name=t', 'commit', '-qm', 'init')
    (root / 'notes.lean').write_text('-- user draft, edited before\n')      # dirty before the attempt
    before = P.snapshot(root)
    # during the attempt: a Lean input is tampered with, a Python file is edited, the draft is reverted
    (root / 'Lib' / 'A.lean').write_text('axiom cheat : False\n')
    (root / 'tool.py').write_text('x = 2  # concurrent edit\n')
    git('checkout', '--', 'notes.lean')
    restored, untracked, other = P.restore(root, before, tmp_path / 'backup')
    assert restored == ['Lib/A.lean', 'notes.lean'] and untracked == [] and other == ['tool.py']
    assert (root / 'Lib' / 'A.lean').read_text() == 'def a := 1\n'
    assert (root / 'notes.lean').read_text() == '-- user draft, edited before\n'
    assert (root / 'tool.py').read_text() == 'x = 2  # concurrent edit\n'           # never touched
    assert (tmp_path / 'backup' / 'Lib' / 'A.lean').read_text() == 'axiom cheat : False\n'
