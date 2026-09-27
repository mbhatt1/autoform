"""Selection with a budget, counterexample adjudication and repair (autoform.nl.judge / repair).

All tests use the `heuristic` or `replay:` judge and stub stages; no Lean, no model calls.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))

from autoform.nl import judge as J, llm, pipeline, repair as R  # noqa: E402
from autoform.nl.formalize import statement_id  # noqa: E402
from autoform.nl.schema import FILES, CheckResult, Statement, dump  # noqa: E402

FIXTURE = ROOT / 'tests/fixtures/nl/translation-PipelinePython.json'
ADD = 'numbers.py:<module>.add'
QUO = 'numbers.py:<module>.quotient'
TESTS = [{'location': 'tests/test_numbers.py:3', 'text': 'assert add(2, 3) == 5'},
         {'location': 'tests/test_numbers.py:4', 'text': 'assert add(10, 4) == 14'}]


def translation():
    t = json.loads(FIXTURE.read_text())
    t['lean_root'] = str(ROOT)
    for f in t['functions']:
        if f['name'] == ADD:
            f.update(doc='Return the sum of a and b.', tests=TESTS)
        if f['name'] == QUO:
            f.update(source='def quotient(a, b):\n    if b == 0:\n        raise ZeroDivisionError("b")\n'
                            '    return a // b\n', doc='Floor division; b must be nonzero.')
    return t


def P(pid, text, kind='postcondition', evidence=('docstring',)):
    return {'id': pid, 'text': text, 'kind': kind, 'evidence': list(evidence)}


ENGLISH = [
    {'function': ADD, 'summary': 'Adds.', 'properties': [
        P('p1', 'For all integers a and b, add(a, b) returns a + b.'),
        P('p2', 'For all integers a and b, add(a, b) returns a - b.', evidence=['implementation']),
        P('p3', 'For all integers a and b, add(a, b) returns a non-negative integer.', evidence=['tests:t.py:3']),
        P('p4', 'add(a, b) returns a value of type int.', evidence=['implementation']),
        P('p5', 'For all integers a and b, add(a, b) equals add(b, a).', 'invariant'),
        P('p6', 'add(2, 3) returns 6.', 'example')]},
    {'function': QUO, 'summary': 'Divides.', 'properties': [
        P('p1', 'If b is 0, quotient(a, b) raises ZeroDivisionError.', 'exception'),
        P('p2', 'For integers a and b, quotient(a, b) returns the floor of a / b.')]},
]


def rows(sel, fn=ADD):
    return {r['property']: r for r in sel['properties'] if r['function'] == fn}


# --- ranking ------------------------------------------------------------------------

def test_ranking_prefers_evidence_and_penalizes_trivial_and_rival_losers(tmp_path):
    sel = J.select(translation(), ENGLISH, tmp_path, judge='heuristic')
    r = rows(sel)
    assert r['p1']['utility'] > r['p2']['utility']          # docstring beats implementation-only
    assert r['p4']['judgment']['label'] == 'TRIVIAL'
    assert r['p4']['utility'] < min(r[k]['utility'] for k in ('p1', 'p3', 'p5', 'p6'))
    assert r['p2']['utility'] < r['p1']['utility'] - 0.2       # the losing rival reading
    # p1 and p2 are rival readings of the same call on the same domain; p3 ("a non-negative
    # integer") is compatible with either and is not in the group.
    assert sel['functions'][0]['rival_groups'] == [['p1', 'p2']]
    assert r['p1']['intent']['chosen'] and not r['p2']['intent']['chosen'] and r['p3']['intent'] is None
    tasks = [json.loads(line)['task'] for line in (tmp_path / 'decisions-select.jsonl').read_text().splitlines()]
    assert tasks.count('PROPERTY_JUDGMENT') == 8 and 'PROPERTY_SELECTION' in tasks and 'INTENT_SELECTION' in tasks
    # The interface view never shows the body.
    first = json.loads((tmp_path / 'decisions-select.jsonl').read_text().splitlines()[0])
    assert 'implementation' not in first['state'] and first['state']['documentation']


def test_rival_detection():
    assert J.incompatible(P('a', 'If b is 0, quotient(a, b) raises ZeroDivisionError.'),
                          P('b', 'If b is 0, quotient(a, b) returns 0.'))
    assert not J.incompatible(P('a', 'For all integers a and b, add(a, b) returns a + b.'),
                              P('b', 'For all strings a and b, add(a, b) returns a - b.'))   # other domain
    assert not J.incompatible(P('a', 'add(a, b) returns a + b.'), P('b', 'add(a, b) returns an integer.'))


def test_security_relevance_raises_utility():
    t = translation()
    fn = dict(t['functions'][0], name='m.authorize', source_name='authorize', doc='')
    sec = J.judgment_prior(P('x', 'authorize(owner, caller) returns True only when owner equals caller.'), fn)
    assert sec['SECURITY_RELEVANT'] > 0.5


def test_replay_judge_reproduces_selection(tmp_path):
    first = J.select(translation(), ENGLISH, tmp_path / 'a', judge='heuristic')
    J._SCORERS.pop('replay:' + str(tmp_path / 'a/decisions-select.jsonl'), None)
    again = J.select(translation(), ENGLISH, tmp_path / 'b', judge='replay:' + str(tmp_path / 'a/decisions-select.jsonl'))
    assert [(r['property'], r['utility'], r['order']) for r in first['properties']] == \
        [(r['property'], r['utility'], r['order']) for r in again['properties']]
    log = [json.loads(x) for x in (tmp_path / 'b/decisions-select.jsonl').read_text().splitlines()]
    assert log and all(e['backend'] == 'replay' and not e['replay_miss'] for e in log)


# --- budget ---------------------------------------------------------------------------

def test_budget_allocation_stops_and_records_reasons(tmp_path, monkeypatch):
    monkeypatch.setattr(J, 'PROVE_SHARE', 0.0)
    est = J.estimate(True)['per_property_usd']
    sel = J.select(translation(), ENGLISH, tmp_path, judge='heuristic', budget_usd=3 * est + 0.01)
    chosen = [r for r in sel['properties'] if r['selected']]
    assert len(chosen) == 3 and sel['planned_usd'] <= 3 * est + 0.01
    # Taken strictly in priority order: everything after the first miss is skipped for budget.
    assert [r['order'] for r in chosen] == [0, 1, 2]
    assert all(r['skip_reason'].startswith('budget') for r in sel['properties'] if not r['selected'])
    # Rank damping spreads the budget: the top property of each function is in.
    assert {r['function'] for r in chosen} == {ADD, QUO}


def test_selection_keeps_a_proving_reserve(tmp_path, monkeypatch):
    monkeypatch.setattr(J, 'PROVE_SHARE', 0.5)
    est = J.estimate(True)['per_property_usd']
    sel = J.select(translation(), ENGLISH, tmp_path, judge='heuristic', budget_usd=6 * est + 0.02)
    assert sel['prove_reserve_usd'] == round((6 * est + 0.02) * 0.5, 4)
    assert sel['selected'] == 3 and sel['planned_usd'] <= 6 * est + 0.02 - sel['prove_reserve_usd']
    # without proving nothing is held back
    sel = J.select(translation(), ENGLISH, tmp_path, judge='heuristic', budget_usd=6 * est + 0.02, prove=False)
    assert sel['prove_reserve_usd'] == 0.0 and sel['selected'] == 6


def test_max_properties_per_function(tmp_path):
    sel = J.select(translation(), ENGLISH, tmp_path, judge='heuristic', max_properties_per_function=2)
    r = rows(sel)
    # The cap trims implementation-only properties; documented (docstring/test) ones are exempt.
    internal = {k: x for k, x in r.items() if not x['external']}
    assert all(x['selected'] for x in r.values() if x['external'])
    assert all('max-properties-per-function 2' in x['skip_reason'] for x in r.values() if not x['selected'])
    assert all(x['rank'] >= 2 for x in r.values() if not x['selected'])
    assert all(x['selected'] for x in internal.values() if x['rank'] < 2)


def test_formalize_stops_when_budget_is_spent(tmp_path, monkeypatch):
    monkeypatch.setattr(llm, 'ask', lambda *a, **k: ('', 0.4))
    calls = []

    def formalize(translation, english, out, **kw):
        out_stmts = []
        for spec in english:
            for p in spec['properties']:
                llm.ask('formalize')
                calls.append(p['id'])
                out_stmts.append(Statement(statement_id(spec['function'], p['id']), spec['function'], p['id'],
                                           p['text'], 'True', [], 'true', 'true', elaborates=True))
        return out_stmts

    sel = J.select(translation(), ENGLISH, tmp_path, judge='heuristic')
    got = J.formalize_within_budget(formalize, translation(), ENGLISH, tmp_path, sel, budget_usd=1.0, wave=2)
    assert len(got) == 4 and len(calls) == 4                    # 2 waves × $0.8 ≥ $1.0: stop
    order = [r['property'] for r in sel['properties']]
    assert [s['id'] for s in got] == [statement_id(r['function'], r['property']) for r in sel['properties'][:4]]
    budget = json.loads((tmp_path / FILES['budget']).read_text())
    assert len(budget['skipped']) == len(order) - 4
    assert all(s['stage'] == 'formalize' and 'budget spent' in s['reason'] for s in budget['skipped'])


# --- gates -------------------------------------------------------------------------------

def fn_add():
    return next(f for f in translation()['functions'] if f['name'] == ADD)


def ce(inputs, model='EResult.val (Val.int (-1))', runtime='returns -1 (int)'):
    return {'inputs': inputs, 'model': model, 'runtime': runtime}


def test_gates_force_incomplete_model():
    f = fn_add()
    allowed, facts = R.gates({'status': 'REFUTED_RUNTIME', 'counterexample': ce({'a': 1, 'b': 2})}, f)
    assert allowed == ['INCOMPLETE_MODEL'] and 'real code only' in facts['gate']
    hole = ce({'a': 1, 'b': 2}, model='Autoform.Core.EResult.hole "call:foo"')
    assert R.gates({'status': 'REFUTED_MODEL', 'counterexample': hole}, f)[0] == ['INCOMPLETE_MODEL']
    agrees = {'status': 'REFUTED_MODEL', 'counterexample': ce({'a': 1, 'b': 2}), 'runtime_agrees': True}
    assert R.gates(agrees, f)[0] == ['INCOMPLETE_MODEL']


def test_gates_missing_precondition_only_outside_tested_domain():
    f = fn_add()
    inside = {'status': 'REFUTED_MODEL', 'counterexample': ce({'a': 3, 'b': 3}), 'runtime_agrees': False}
    outside = {'status': 'REFUTED_MODEL', 'counterexample': ce({'a': -1, 'b': 3}), 'runtime_agrees': False}
    assert R.gates(inside, f)[0] == ['REAL_BUG', 'BAD_SPEC']
    allowed, facts = R.gates(outside, f)
    assert allowed == ['REAL_BUG', 'BAD_SPEC', 'MISSING_PRECONDITION'] and '[2, 10]' in facts['domain']
    loser = {'intent': {'chosen': False, 'probability': 0.1}}
    assert 'REAL_BUG' not in R.gates(outside, f, loser)[0]
    notrun = {'status': 'REFUTED_MODEL', 'counterexample': ce({'a': -1, 'b': 3}, runtime='not run: no runtime')}
    assert 'ABSTRACTION_ARTIFACT' in R.gates(notrun, f)[0]
    # Strings: inside only if the tests use that very value.
    g = dict(f, source_name='is_admin', params=[{'name': 'user', 'sort': 'str'}],
             tests=[{'location': 't', 'text': 'assert is_admin("admin")'}])
    refuted = lambda v: {'status': 'REFUTED_MODEL', 'counterexample': ce({'user': v}), 'runtime_agrees': False}  # noqa
    assert 'MISSING_PRECONDITION' in R.gates(refuted('root'), g)[0]
    assert 'MISSING_PRECONDITION' not in R.gates(refuted('admin'), g)[0]


def test_docstring_domain_counts():
    q = next(f for f in translation()['functions'] if f['name'] == QUO)
    assert R.doc_constraints(q) == [('b', 'b != 0')]
    assert R.witness_domain({'a': 1, 'b': 0}, q)[0] is False


# --- repair candidates ---------------------------------------------------------------------

def test_repair_candidates_from_guards_docs_and_tests_never_witness_constants():
    q = next(f for f in translation()['functions'] if f['name'] == QUO)
    stmt = {'id': 's', 'english': 'quotient(a, b) returns a // b.', 'pre': 'true'}
    chk = {'status': 'REFUTED_MODEL', 'counterexample': ce({'a': 17, 'b': 0},
                                                           model='EResult.exn (Val.str "ZeroDivisionError")')}
    opts, dropped = R.candidates(stmt, P('p2', stmt['english']), chk, q, 'MISSING_PRECONDITION')
    pres = {o['precondition']: o['evidence'] for o in opts if o['kind'] == 'precondition'}
    assert pres == {'b != 0': 'code guard'}           # the docstring says the same; deduplicated
    assert any(o['id'] == 'ALLOW_EXCEPTION' and 'ZeroDivisionError' in o['english'] for o in opts)
    assert opts[0]['id'] == 'REJECT'
    assert not any('17' in (o.get('english') or '') for o in opts)
    # A guard the code itself states may mention the witness value (it is evidence) ...
    f = dict(q, source='def quotient(a, b):\n    if a == 17:\n        return 0\n    return a // b\n', doc='')
    opts, dropped = R.candidates(stmt, P('p2', stmt['english']), chk, f, 'MISSING_PRECONDITION')
    assert {o['precondition'] for o in opts if o['kind'] == 'precondition'} == {'a != 17'}
    assert any(d['precondition'] == 'a == 17' and 'witness satisfies' in d['reason'] for d in dropped)
    # ... a precondition mentioning a witness value no evidence mentions never is.
    assert R.witness_constants('a != 17', {'a': 17}, dict(q, source='', doc=''), 'x') == ['17']
    assert R.witness_constants('a != 17', {'a': 17}, dict(q, source='if a == 17: pass', doc=''), 'x') == []


def test_weaken_iff():
    f = fn_add()
    stmt = {'id': 's', 'english': 'add(a, b) returns True exactly when a equals b.', 'pre': 'true'}
    opts, _ = R.candidates(stmt, P('p', stmt['english']), {'status': 'REFUTED_MODEL', 'counterexample': ce({})},
                           f, 'BAD_SPEC')
    texts = {o['english'] for o in opts if o['kind'] == 'weaken'}
    assert texts == {'add(a, b) returns True whenever a equals b.', 'add(a, b) returns True only when a equals b.'}


# --- the repair loop -------------------------------------------------------------------------

class Loop:
    """formalize/check stubs: every repaired statement is refuted again, outside the tests."""

    def __init__(self, holds=()):
        self.holds, self.formalized = set(holds), []

    def formalize(self, translation, english, out, **kw):
        out_stmts = []
        for spec in english:
            for p in spec['properties']:
                self.formalized.append(p['id'])
                out_stmts.append(Statement(statement_id(spec['function'], p['id']), spec['function'], p['id'],
                                           p['text'], 'True', [], 'true', 'true', elaborates=True))
        return out_stmts

    def check(self, translation, statements, out, domain_size=64, runtime=True):
        out = []
        for s in statements:
            s = s if isinstance(s, dict) else s.__dict__
            ok = s['property'] in self.holds
            out.append(CheckResult(s['id'], 'BOUNDED_HOLDS' if ok else 'REFUTED_MODEL', 64, runtime_agrees=ok,
                                   counterexample=None if ok else ce({'a': -5, 'b': -7})))
        return out


def base_statement(pid='p3'):
    return Statement(statement_id(ADD, pid), ADD, pid, 'x', 'True', [], 'true', 'true', elaborates=True)


def test_repair_loop_terminates_and_links_parents(tmp_path):
    loop = Loop()
    english = [{'function': ADD, 'summary': '', 'properties': [P('p3', 'add(a, b) returns a non-negative value.',
                                                                 evidence=['implementation'])]}]
    res = R.adjudicate(translation(), [base_statement()],
                       [CheckResult(statement_id(ADD, 'p3'), 'REFUTED_MODEL', 64, runtime_agrees=False,
                                    counterexample=ce({'a': -1, 'b': 0}))],
                       tmp_path, judge='heuristic', english=english, formalize_fn=loop.formalize,
                       check_fn=loop.check, rounds=2)
    assert loop.formalized == ['p3_r1', 'p3_r1_r2']              # at most 2 rounds
    assert [r['disposition'] for r in res['records']] == ['repaired', 'repaired', 'repair_limit']
    sid1, sid2 = statement_id(ADD, 'p3_r1'), statement_id(ADD, 'p3_r1_r2')
    assert res['lineage'][sid1]['parent'] == statement_id(ADD, 'p3')
    assert res['lineage'][sid2] == dict(res['lineage'][sid2], parent=sid1, root=statement_id(ADD, 'p3'))
    assert [p['parent'] for p in res['properties']] == ['p3', 'p3_r1']
    assert all(s['parent'] for s in res['statements'])
    for rec in res['records'][:2]:
        assert rec['classification'] in ('BAD_SPEC', 'MISSING_PRECONDITION')
        assert rec['repair']['kind'] == 'precondition'
        assert '-1' not in rec['repair']['english'] and '-5' not in rec['repair']['english']


def test_real_bug_needs_cross_validation(tmp_path):
    t = translation()
    stmts = [base_statement('p6'), base_statement('p2')]
    chk = [CheckResult(s.id, 'REFUTED_MODEL', 1, runtime_agrees=False,
                       counterexample=ce({'a': 3, 'b': 3}, runtime='returns 6 (int)')) for s in stmts]
    english = [{'function': ADD, 'summary': '', 'properties': [
        P('p6', 'add(3, 3) returns 7.', 'example', evidence=['docstring']),
        P('p2', 'add(a, b) returns a * b.', evidence=['implementation'])]}]
    sel = J.select(t, english, tmp_path, judge='heuristic')
    res = R.adjudicate(t, stmts, chk, tmp_path, judge='heuristic', english=english, selection=sel)
    by = {r['property']: r for r in res['records']}
    assert by['p6']['classification'] == 'REAL_BUG' and by['p6']['disposition'] == 'finding'
    assert by['p6']['cross_validation']['external_evidence'] == ['docstring']
    assert res['findings'] == [statement_id(ADD, 'p6')]
    assert by['p2']['disposition'] != 'finding'


def test_runtime_only_refutation_points_at_the_model(tmp_path):
    s = base_statement('p5')
    res = R.adjudicate(translation(), [s], [CheckResult(s.id, 'REFUTED_RUNTIME', 64,
                                                        counterexample=ce({'a': 1, 'b': 2}))],
                       tmp_path, judge='heuristic',
                       models=[{'function': ADD, 'lean_name': 'Autoform.NLModel.M.add', 'status': 'VALIDATED'}])
    rec = res['records'][0]
    assert rec['forced'] and rec['classification'] == 'INCOMPLETE_MODEL' and rec['disposition'] == 'model_defect'
    assert rec['model_defect']['model'] == 'Autoform.NLModel.M.add' and rec['model_defect']['owner'] == 'model stage'
    assert rec['model_defect']['classification'] in ('SEMANTICS_MISMATCH', 'FRONTEND_MISTRANSLATION')


# --- pipeline + report + JEVBench ------------------------------------------------------------

class Stubs(Loop):
    def __init__(self):
        super().__init__(holds={'p1', 'p3_r1', 'p5'})
        self.calls = []

    def impl(self, name):
        fn = {'select': J.select, 'adjudicate': R.adjudicate}.get(name) or getattr(self, name)

        def run(*a, **k):
            self.calls.append(name)
            return fn(*a, **k)
        return run

    def translate(self, source, module, lean_root, out, **kw):
        t = translation()
        dump(t, Path(out) / FILES['translation'])
        return t

    def describe(self, translation, out, functions=None, **kw):
        return ENGLISH

    def check(self, translation, statements, out, domain_size=64, runtime=True):
        res = []
        for s in statements:
            s = s if isinstance(s, dict) else s.__dict__
            p = s['property']
            if s['function'] == ADD and p in self.holds:
                res.append(CheckResult(s['id'], 'BOUNDED_HOLDS', 64, runtime_agrees=True))
            elif s['function'] == ADD and p == 'p6':
                res.append(CheckResult(s['id'], 'REFUTED_MODEL', 1, runtime_agrees=False,
                                       counterexample=ce({}, 'EResult.val (Val.int 5)', 'returns 5 (int)')))
            elif s['function'] == ADD and p == 'p5':
                res.append(CheckResult(s['id'], 'REFUTED_RUNTIME', 64, counterexample=ce({'a': 1, 'b': 2})))
            elif s['function'] == ADD:
                res.append(CheckResult(s['id'], 'REFUTED_MODEL', 64, runtime_agrees=False,
                                       counterexample=ce({'a': -1, 'b': 0})))
            else:
                res.append(CheckResult(s['id'], 'BOUNDED_HOLDS', 64, runtime_agrees=True))
        return res

    def prove(self, translation, statements, checks, out, budget_usd=None, **kw):
        from autoform.nl.schema import ProofResult
        self.proved_order = [s['id'] for s in statements]
        ok = {c['statement'] for c in checks if c['status'] == 'BOUNDED_HOLDS'}
        return [ProofResult(s['id'], 'PROVED' if s['id'] in ok else 'SKIPPED', cost_usd=0.0) for s in statements]


def test_pipeline_with_judge_reports_lineage_budget_and_findings(tmp_path, monkeypatch):
    monkeypatch.setattr(J, 'PROVE_SHARE', 0.0)
    stubs = Stubs()
    stubs.holds = {'p1', 'p3_r1', 'p2_r1', 'p4', 'p4_r1'}
    monkeypatch.setattr(pipeline, '_impl', stubs.impl)
    src = tmp_path / 'src'
    src.mkdir()
    (src / 'numbers.py').write_text('def add(a, b):\n    return a + b\n')
    out = tmp_path / 'run'
    est = J.estimate(True)['per_property_usd']
    res = pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT, deep=True, judge='heuristic',
                       budget_usd=7 * est + 0.01)
    st = res['run']['stages']
    assert list(st)[:7] == ['translate', 'describe', 'select', 'formalize', 'check', 'adjudicate', 'prove']
    assert all(st[s]['status'] == 'ok' for s in ('select', 'formalize', 'check', 'adjudicate', 'prove')), st
    rep = json.loads((out / 'report.json').read_text())
    sel = json.loads((out / FILES['selection']).read_text())
    assert sel['selected'] == 7 and sel['skipped'] == 1
    # Findings follow the cross-validated rule.
    bugs = rep['findings']['potential_bugs']
    assert [b['id'] for b in bugs] == [statement_id(ADD, 'p6')] and bugs[0]['classification'] == 'REAL_BUG'
    assert any(x['id'] == statement_id(ADD, 'p5') for x in rep['findings']['model_defects'])
    # p3 is stated by a test and refuted: the judge repaired it, but the contradiction with the
    # documented behaviour must still be listed (a repair never hides it).
    sus = {x['id']: x for x in rep['findings']['suspected_bugs']}
    assert sus[statement_id(ADD, 'p3')]['documented_intent_contradicted'] is True
    # Repair lineage: the refuted p3 was restated under a precondition and the restatement holds.
    add = next(f for f in rep['functions'] if f['name'] == ADD)
    by = {p['id']: p for p in add['properties']}
    child = by[statement_id(ADD, 'p3')]['adjudication']['repaired_by']
    assert by[child]['parent'] == statement_id(ADD, 'p3') and by[child]['check']['status'] == 'BOUNDED_HOLDS'
    assert by[child]['lineage'] == [statement_id(ADD, 'p3'), child]
    assert by[child]['proof']['status'] == 'PROVED'
    assert len(add['budget_skips']) + sum(len(f.get('budget_skips', [])) for f in rep['functions']
                                          if f['name'] != ADD) == 1
    md = (out / 'report.md').read_text()
    assert '## Spent vs budget' in md and 'repaired from' in md and 'counterexample reading' in md
    assert 'skipped at selection: 1' in md
    # Proving runs in utility order.
    u = J.utilities(out)
    assert stubs.proved_order == sorted(stubs.proved_order, key=lambda s: -u.get(s, 0))
    # Decision log + JEVBench.
    decisions = [json.loads(x) for x in (out / FILES['decisions']).read_text().splitlines()]
    assert all('outcome' in d for d in decisions if (d.get('context') or {}).get('statement'))
    bench = [json.loads(x) for x in (out / FILES['jevbench']).read_text().splitlines()]
    tasks = {b['task'] for b in bench}
    assert {'PROPERTY_JUDGMENT', 'COUNTEREXAMPLE_CLASSIFICATION', 'REPAIR_SELECTION'} <= tasks
    rs = [b for b in bench if b['task'] == 'REPAIR_SELECTION' and b['outcome'].get('repair_status') in ('PROVED', 'BOUNDED_PROVED')]
    assert rs and all(b['label']['kind'] == 'single' for b in rs)
    skipped = [b for b in bench if b['task'] == 'PROPERTY_JUDGMENT' and b['outcome'].get('skipped')]
    assert skipped and all(b['label']['kind'] == 'unlabeled' for b in skipped)
    assert res['run']['decisions']['jevbench_rows'] == len(bench)
    # Unchanged inputs: nothing reruns, judge stages included.
    stubs.calls.clear()
    pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT, deep=True, judge='heuristic',
                 budget_usd=7 * est + 0.01)
    assert stubs.calls == []


def test_label_rules_for_the_new_flow():
    base = dict(task='PROPERTY_JUDGMENT', chosen='USEFUL_PROPERTY')
    assert J.label(dict(base, outcome={'skipped': 'budget: …'}))['kind'] == 'unlabeled'
    assert J.label(dict(base, outcome={'nl_status': 'UNCHECKABLE', 'detail': 'vacuous: no domain point'}))['kind'] \
        == 'unlabeled'
    assert J.label(dict(base, outcome={'status': 'BOUNDED_PROVED'}))['kind'] == 'acceptable'
    ce_ = dict(task='COUNTEREXAMPLE_CLASSIFICATION', chosen='BAD_SPEC')
    assert J.label(dict(ce_, outcome={'repair_status': 'REFUTED', 'repair_nl_status': 'REFUTED_MODEL'}))['kind'] == \
        'negative'
    assert J.label(dict(ce_, outcome={'repair_nl_status': 'REFUTED_RUNTIME'}))['kind'] == 'unlabeled'
    assert J.label(dict(ce_, forced=True))['kind'] == 'forced'


def test_ill_typed_counterexample_is_not_a_documented_contradiction():
    from autoform.nl.report import ill_typed
    assert ill_typed({'model': 'Autoform.Core.EResult.exn (Autoform.Core.Val.str "TypeError")',
                      'runtime': 'raises TypeError'})
    assert ill_typed({'model': '.exn (.str "TypeError")'})
    assert not ill_typed({'model': '.exn (.str "TypeError")', 'runtime': 'returned 3'})
    assert not ill_typed({'model': '.exn (.str "KeyError")', 'runtime': 'raises KeyError'})
    assert not ill_typed({'model': '.val (.int 99)', 'runtime': 'returned 99'})


def test_undefined_behaviour_witness_is_a_bug_not_a_model_gap():
    from autoform.nl import repair as R
    ub = {'status': 'REFUTED_MODEL', 'runtime_agrees': None,
          'counterexample': {'inputs': {'x': 18446744073709551615},
                             'model': 'Autoform.Core.EResult.hole "ub:shift count out of range"'}}
    allowed, facts = R.gates(ub, {'name': 'int_sqrt64', 'params': [{'name': 'x'}]})
    assert 'INCOMPLETE_MODEL' not in allowed and 'REAL_BUG' in allowed
    assert facts['model_outcome_kind'] == 'undefined_behavior' and 'shift count out of range' in facts['gate']
    assert allowed == ['REAL_BUG']              # no documented domain: the declared type is the domain
    documented = {'name': 'f', 'params': [{'name': 'x'}], 'tests': [{'text': 'f(1)\nf(2)'}]}
    assert R.gates(ub, documented)[0] == ['REAL_BUG', 'MISSING_PRECONDITION']   # the tests only use 1 and 2
    gap = dict(ub, counterexample=dict(ub['counterexample'], model='Autoform.Core.EResult.hole "stmt:UNKNOWN"'))
    assert R.gates(gap, {'name': 'int_sqrt64', 'params': [{'name': 'x'}]})[0] == ['INCOMPLETE_MODEL']
