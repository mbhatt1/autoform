"""`scripts/pr_mode.py` and `autoform pr`: per-function evidence for a change.

The unit tests feed the level derivation hand-built artifacts, so the one rule that
matters -- a function is reported at the level its own artifacts reach and never above
-- is pinned without Joern or Lean. The end-to-end tests run the script on the fixture
history `scripts/pr_fixture.py` builds, with no Joern and no Lean on the path, so they
check what the report says when the chain cannot run. The last test runs the real chain
and is gated on `AUTOFORM_TEST_JOERN=1`.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

from conftest import ROOT, SCRIPTS, load

ROOT = Path(ROOT)
pr_mode = load(str(Path(SCRIPTS) / 'pr_mode.py'), 'af_pr_mode')
pr_fixture = load(str(Path(SCRIPTS) / 'pr_fixture.py'), 'af_pr_fixture')
# The Rust leg's entry points: `load` has put scripts/ on sys.path, and these are the same
# module objects pr_mode imports lazily, so a monkeypatched attribute reaches the leg.
import rust_aeneas  # noqa: E402
import rust_regress  # noqa: E402

needs_git = pytest.mark.skipif(shutil.which('git') is None, reason='git is required')


# ------------------------------------------------------------ changed functions

def test_python_functions_are_named_the_way_the_exporter_names_them():
    source = b'''
class C:
    @staticmethod
    def m(x):
        def inner(y):
            return y
        return inner(x)

def f(a):
    return a
'''
    found, error = pr_mode.python_functions(source, 'pkg/mod.py')
    assert error is None
    assert sorted(found) == ['pkg/mod.py:<module>.C.m', 'pkg/mod.py:<module>.C.m.inner',
                             'pkg/mod.py:<module>.f']
    assert found['pkg/mod.py:<module>.C.m']['start'] == 3   # the decorator line
    assert found['pkg/mod.py:<module>.C.m']['end'] == 7
    assert found['pkg/mod.py:<module>.f']['start'] == 9


def test_a_syntax_error_is_reported_not_swallowed():
    found, error = pr_mode.python_functions(b'def (:\n', 'bad.py')
    assert found is None and 'bad.py' in error and 'SyntaxError' in error


@needs_git
def test_changed_functions_come_from_the_ast_diff_of_both_commits(tmp_path):
    history = pr_fixture.make_history(tmp_path / 'repo')
    detected = pr_mode.changed_functions(history['repo'], history['base'], history['head'])
    by_name = {f['name']: f for f in detected['functions']}
    assert by_name['numbers.py:<module>.quotient']['change'] == 'modified'
    assert by_name['numbers.py:<module>.quotient']['line'] == 4
    assert {n for n, f in by_name.items() if f['change'] == 'added'} == {
        'numbers.py:<module>.clamp', 'numbers.py:<module>.label',
        'numbers.py:<module>.first', 'numbers.py:<module>.raw'}
    # `add` and `fraction` are byte-identical at both commits: not changed, not reported.
    assert 'numbers.py:<module>.add' not in by_name
    assert 'numbers.py:<module>.fraction' not in by_name
    assert detected['removed'] == [] and detected['errors'] == []
    assert all(f['detection'] == 'python-ast' for f in detected['functions'])


@needs_git
def test_the_working_tree_is_the_default_head_and_untracked_files_count(tmp_path):
    history = pr_fixture.make_history(tmp_path / 'repo')
    repo = Path(history['repo'])
    (repo / 'numbers.py').write_text('def add(a, b):\n    return b + a\n')
    (repo / 'extra.py').write_text('def twice(x):\n    return 2 * x\n')
    detected = pr_mode.changed_functions(repo, history['head'], None)
    names = {(f['name'], f['change']) for f in detected['functions']}
    assert ('numbers.py:<module>.add', 'modified') in names
    assert ('extra.py:<module>.twice', 'added') in names
    removed = {f['name'] for f in detected['removed']}
    assert 'numbers.py:<module>.clamp' in removed and 'numbers.py:<module>.raw' in removed


@needs_git
def test_a_whitespace_only_edit_changes_no_function(tmp_path):
    history = pr_fixture.make_history(tmp_path / 'repo')
    repo = Path(history['repo'])
    text = (repo / 'numbers.py').read_text()
    (repo / 'numbers.py').write_text(text.replace('return a + b', 'return  a + b  # same'))
    detected = pr_mode.changed_functions(repo, history['head'], None)
    assert detected['functions'] == [] and detected['removed'] == []
    assert detected['files'][0]['analysed'] == 'python-ast'


@needs_git
def test_files_outside_subdir_and_non_code_files_are_listed_not_analysed(tmp_path):
    history = pr_fixture.make_history(tmp_path / 'repo')
    repo = Path(history['repo'])
    (repo / 'README.md').write_text('notes\n')
    (repo / 'lib').mkdir()
    (repo / 'lib' / 'm.py').write_text('def g():\n    return 1\n')
    detected = pr_mode.changed_functions(repo, history['head'], None, subdir='lib')
    files = {f['path']: f for f in detected['files']}
    assert files['README.md']['analysed'] is False
    assert files['lib/m.py']['analysed'] == 'python-ast'
    assert [f['name'] for f in detected['functions']] == ['m.py:<module>.g']
    assert detected['functions'][0]['path'] == 'lib/m.py'


# ------------------------------------------------------------------ selection

def fn(name, body=None):
    return {'name': name, 'file': name.split(':')[0], 'params': [],
            'body': body if body is not None else {'k': 'ret', 'e': {'k': 'int', 'v': 1}}}


def call(name):
    return {'k': 'ret', 'e': {'k': 'call', 'f': name, 'args': []}}


def mcall(method):
    return {'k': 'ret', 'e': {'k': 'mcall', 'recv': {'k': 'name', 'v': 'self'}, 'm': method, 'args': []}}


AST = [fn('m.py:<module>.f', call('g')), fn('m.py:<module>.g', call('h')), fn('m.py:<module>.h'),
       fn('m.py:<module>.C.m', mcall('k')), fn('m.py:<module>.C.k'), fn('m.py:<module>.C'),
       fn('m.py:<module>.unrelated'), fn('<module-objects>:<module>'), fn('m.py:<module>')]


def test_selection_keeps_callees_to_a_fixed_point_and_the_module_entries():
    selected, closure, missing = pr_mode.select_functions(AST, ['m.py:<module>.f'])
    names = [f['name'] for f in selected]
    assert names == ['m.py:<module>.f', 'm.py:<module>.g', 'm.py:<module>.h',
                     '<module-objects>:<module>', 'm.py:<module>']
    assert closure == ['m.py:<module>.g', 'm.py:<module>.h'] and missing == []


def test_selection_keeps_enclosing_scopes_and_method_callees():
    selected, closure, missing = pr_mode.select_functions(AST, ['m.py:<module>.C.m', 'm.py:<module>.gone'])
    names = {f['name'] for f in selected}
    assert {'m.py:<module>.C.m', 'm.py:<module>.C.k', 'm.py:<module>.C'} <= names
    assert 'm.py:<module>.unrelated' not in names and 'm.py:<module>.f' not in names
    assert closure == ['m.py:<module>.C.k']
    assert missing == ['m.py:<module>.gone']


# ------------------------------------------------------------------- evidence

def changed(name, line=1):
    return {'name': name, 'path': 'm.py', 'file': 'm.py', 'change': 'modified', 'line': line,
            'end_line': line + 1, 'detection': 'python-ast', 'language': 'python'}


HOLE = fn('m.py:<module>.holed', {'k': 'ret', 'e': {'k': 'hole', 'label': 'lit:bytes'}})
NAMES = ['proved', 'agreed', 'blocked', 'diverged', 'refuted', 'budget', 'holed', 'absent']
FUNCTIONS = [fn(f'm.py:<module>.{n}') for n in NAMES if n not in ('holed', 'absent')] + [HOLE]
CONFORMANCE = {
    'divergences': 1,
    'coverage': {'by_status': {f'm.py:<module>.{n}': 'compared' for n in NAMES} |
                 {'m.py:<module>.blocked': 'blocked (value model): float'}},
    'runtime_cases': [{'name': f'm.py:<module>.{n}', 'comparison': 'agree'} for n in NAMES
                      if n not in ('blocked', 'holed')] +
                     [{'name': 'm.py:<module>.diverged', 'comparison': 'diverge'}],
    'divergence_detail': [{'function': 'm.py:<module>.diverged', 'args': '(1)'}],
}
SPECS = {'build_clean': True,
         'specs': [{'id': 'conform_proved', 'subject': 'm.py:<module>.proved', 'status': 'proved', 'proved': True},
                   {'id': 'law_refuted', 'subject': 'm.py:<module>.refuted', 'status': 'refuted',
                    'proved': False, 'reason': 'counterexample in the fuzzed domain'}],
         'budget_excluded': [{'theorem': 'conform_budget', 'subject': 'm.py:<module>.budget',
                              'reason': 'over 300 s'}]}
MUTATION = {'theorems': {'conform_proved': {'killed': 3, 'survived': 1, 'verdict': 'VACUOUS'}}}
STAGES = {'export': {'status': 'passed'}, 'render': {'status': 'passed'}, 'build': {'status': 'passed'},
          'oracle': {'status': 'passed'}, 'specs': {'status': 'passed'}, 'mutation': {'status': 'passed'}}
EXPORTER = {'status': 'available', 'reason': ''}


def levels(**overrides):
    args = dict(changed=[changed(f'm.py:<module>.{n}') for n in NAMES], selected=FUNCTIONS,
                conformance=CONFORMANCE, specs=SPECS, mutation=MUTATION, stages=STAGES,
                module='Probe', exporter=EXPORTER)
    args.update(overrides)
    results = pr_mode.evidence(**args)
    return {r['name'].rsplit('.', 1)[-1]: r for r in results}


def test_each_function_gets_the_level_its_own_artifacts_reach():
    got = levels()
    assert got['proved']['level'] == 'proved'
    assert 'conform_proved' in got['proved']['reason']
    assert {a['kind'] for a in got['proved']['artifacts']} == {'ast', 'render', 'conformance', 'theorem',
                                                               'specs', 'mutation'}
    assert got['proved']['mutation'] == {'killed': 3, 'survived': 1, 'verdicts': {'conform_proved': 'VACUOUS'}}
    assert got['agreed']['level'] == 'oracle-agreed' and 'no theorem was emitted' in got['agreed']['reason']
    assert got['blocked']['level'] == 'translated' and 'float' in got['blocked']['reason']
    assert got['diverged']['level'] == 'refuted'
    assert got['diverged']['artifacts'][-1] == {'kind': 'divergence', 'path': 'conformance.json',
                                                'divergence_detail': [0]}
    assert got['refuted']['level'] == 'refuted' and 'law_refuted' in got['refuted']['reason']
    assert got['budget']['level'] == 'oracle-agreed' and 'over 300 s' in got['budget']['reason']
    assert got['holed']['level'] == 'hole' and got['holed']['holes'] == ['lit:bytes']
    assert got['absent']['level'] == 'none' and 'exported no function' in got['absent']['reason']


def test_a_verdict_replayed_from_the_oracle_cache_counts_and_says_so():
    """`differential.py` reports a replayed verdict as `compared: cached from <time>`. Its
    key binds the model, the cases and the runtime source (`oracle_cache.plan`), so it is
    the same evidence a fresh comparison would be: the function reaches `oracle-agreed`
    (and `proved` when its theorem is), and the record says the verdict was replayed."""
    stamp = '2026-10-19T12:00:00Z'
    cached = dict(CONFORMANCE, coverage={'by_status': {
        name: (status + ': cached from ' + stamp if status == 'compared' else status)
        for name, status in CONFORMANCE['coverage']['by_status'].items()}})
    got = levels(conformance=cached)
    assert got['proved']['level'] == 'proved' and got['agreed']['level'] == 'oracle-agreed'
    for name in ('proved', 'agreed'):
        assert got[name]['oracle']['cached_from'] == stamp
        assert got[name]['oracle']['status'] == 'compared: cached from ' + stamp
        assert 'replayed from the oracle cache, computed ' + stamp in got[name]['reason']
    assert 'cached_from' not in levels()['agreed']['oracle']
    # Only a replayed *comparison* counts: a replayed all-inconclusive status does not.
    got = levels(conformance=dict(CONFORMANCE, coverage={'by_status': {
        'm.py:<module>.agreed': 'cases built, all inconclusive: cached from ' + stamp}}))
    assert got['agreed']['level'] == 'translated'


def test_a_level_is_never_rounded_up_when_a_stage_did_not_run():
    # No exporter output: nothing is known about anybody.
    got = levels(exporter={'status': 'unavailable', 'reason': 'no Joern frontend at /nowhere'},
                 selected=[], conformance=None, specs=None, mutation=None)
    assert {r['level'] for r in got.values()} == {'none'}
    assert all('no Joern frontend' in r['reason'] for r in got.values())
    # Rendered but never type-checked: a hole is still a hole, a hole-free function is nothing yet.
    got = levels(stages={'render': {'status': 'passed'},
                         'build': {'status': 'skipped', 'reason': 'lake is not on PATH'}},
                 conformance=None, specs=None, mutation=None)
    assert got['holed']['level'] == 'hole'
    assert got['proved']['level'] == 'none' and 'lake is not on PATH' in got['proved']['reason']
    # Proof stage skipped: the oracle's agreement stands, nothing is proved.
    got = levels(specs=None, mutation=None,
                 stages=dict(STAGES, specs={'status': 'skipped', 'reason': 'the oracle recorded 1 divergence(s)'}))
    assert got['proved']['level'] == 'oracle-agreed'
    assert 'proof stage skipped: the oracle recorded 1 divergence' in got['proved']['reason']
    # A theorem that is emitted but not built clean is not a proof.
    got = levels(specs=dict(SPECS, build_clean=False))
    assert got['proved']['level'] == 'oracle-agreed'


# -------------------------------------------------------------------- outputs

def report_for(results):
    return {'tool_version': '0.1.0', 'module': 'Probe', 'report_dir': '/tmp/x',
            'repository': {'uri': 'file:///tmp/repo', 'path': '/tmp/repo', 'subdir': '.'},
            'base': {'ref': 'base', 'commit': 'a' * 40}, 'head': {'ref': None, 'commit': None},
            'detection': 'python-ast', 'exporter': EXPORTER, 'files': [], 'errors': [],
            'selection': {'changed': [], 'selected': [], 'closure': [], 'missing': []},
            'stages': STAGES, 'functions': results, 'removed': [], 'summary': {}}


def test_sarif_has_one_result_per_function_and_passes_the_code_scanning_checks():
    results = list(levels().values())
    document = pr_mode.sarif_document(report_for(results))
    assert document['version'] == '2.1.0'
    assert pr_mode.validate_sarif(document) == []
    run = document['runs'][0]
    assert len(run['results']) == len(results)
    by_rule = {}
    for result in run['results']:
        by_rule.setdefault(result['ruleId'], []).append(result)
        assert result['message']['text'].startswith(result['properties']['function'] + ': ')
        assert result['locations'][0]['physicalLocation']['artifactLocation']['uri'] == 'm.py'
    assert {r['level'] for r in by_rule['autoform/refuted']} == {'error'}
    assert {r['level'] for r in by_rule['autoform/hole']} == {'warning'}
    assert {r['level'] for r in by_rule['autoform/proved']} == {'note'}
    assert run['versionControlProvenance'][0]['revisionId'] == 'working-tree'


def test_sarif_validation_rejects_what_github_would():
    document = pr_mode.sarif_document(report_for(list(levels().values())))
    result = document['runs'][0]['results'][0]
    result['level'] = 'fatal'
    result['locations'][0]['physicalLocation']['artifactLocation']['uri'] = '/abs/m.py'
    result['locations'][0]['physicalLocation']['region']['startLine'] = 0
    document['runs'][0]['results'][1]['ruleId'] = 'autoform/unknown'
    problems = pr_mode.validate_sarif(document)
    assert any('level' in p for p in problems)
    assert any('relative path' in p for p in problems)
    assert any('startLine' in p for p in problems)
    assert any('not in tool.driver.rules' in p for p in problems)
    assert pr_mode.validate_sarif({'version': '2.0.0'}) == ["version must be '2.1.0'", 'runs must be a non-empty list']


def test_sarif_carries_what_a_consumer_other_than_github_needs():
    """The SARIF 2.1.0 required properties (sarifLog version/runs, run.tool.driver.name,
    reportingDescriptor.id, result.message), plus what an internal SARIF consumer resolves
    and identifies a run by: the tool version, rules in tool.driver, every result's
    ruleId among them, a percent-encoded relative uri under %SRCROOT%, and an absolute
    repositoryUri."""
    record = dict(levels()['proved'], path='src/a dir/m é.py')
    document = pr_mode.sarif_document(report_for([record]))
    assert document['$schema'].endswith('sarif-schema-2.1.0.json') and document['version'] == '2.1.0'
    (run,) = document['runs']
    driver = run['tool']['driver']
    assert driver['name'] == 'autoform' and driver['version'] == driver['semanticVersion'] == '0.1.0'
    ids = [rule['id'] for rule in driver['rules']]
    assert len(ids) == len(set(ids)) and all(rule['shortDescription']['text'] for rule in driver['rules'])
    assert set(ids) == {f'autoform/{level}' for level in pr_mode.LEVELS} | {'autoform/behaviour-changed'}
    (result,) = run['results']
    assert ids[result['ruleIndex']] == result['ruleId'] == 'autoform/proved' and result['message']['text']
    location = result['locations'][0]['physicalLocation']['artifactLocation']
    assert location == {'uri': 'src/a%20dir/m%20%C3%A9.py', 'uriBaseId': '%SRCROOT%'}
    assert run['versionControlProvenance'][0]['repositoryUri'] == 'file:///tmp/repo'
    assert pr_mode.validate_sarif(document) == []

    broken = json.loads(json.dumps(document))
    del broken['runs'][0]['tool']['driver']['version'], broken['runs'][0]['tool']['driver']['semanticVersion']
    location = broken['runs'][0]['results'][0]['locations'][0]['physicalLocation']['artifactLocation']
    location['uri'], location['uriBaseId'] = 'src/a dir/m.py', None
    broken['runs'][0]['versionControlProvenance'][0]['repositoryUri'] = 'git@host:group/repo.git'
    assert sorted(pr_mode.validate_sarif(broken)) == sorted([
        'tool.driver.version is required',
        'versionControlProvenance.repositoryUri must be an absolute URI',
        'result 0: artifactLocation.uri must be percent-encoded',
        'result 0: a relative artifactLocation.uri needs uriBaseId %SRCROOT%'])


@needs_git
@pytest.mark.parametrize('remote, uri', [
    ('https://ci-job-token:s3cret@git.example.test/group/repo.git', 'https://git.example.test/group/repo.git'),
    ('ssh://git@git.example.test:2222/group/repo.git', 'ssh://git.example.test:2222/group/repo.git'),
    ('git@git.example.test:group/repo.git', 'ssh://git.example.test/group/repo.git'),
    ('git.example.test:/srv/git/repo.git', 'ssh://git.example.test/srv/git/repo.git'),
    ('/srv/git/repo.git', 'file:///srv/git/repo.git'),
])
def test_the_repository_uri_is_absolute_and_credential_free_for_any_git_remote(tmp_path, remote, uri):
    history = pr_fixture.make_history(tmp_path / 'repo')
    pr_fixture.git(history['repo'], 'remote', 'add', 'origin', remote)
    assert pr_mode._origin(history['repo']) == uri


def test_markdown_names_every_function_level_and_skipped_stage():
    report = report_for(list(levels().values()))
    report['stages'] = dict(STAGES, mutation={'status': 'skipped', 'reason': '--mutants 0'})
    report['removed'] = [{'name': 'm.py:<module>.old'}]
    report['selection']['missing'] = ['m.py:<module>.absent']
    text = pr_mode.markdown_comment(report)
    for name in NAMES:
        assert f'`m.py:<module>.{name}`' in text
    for level in pr_mode.LEVELS:
        assert f'| {level} |' in text and f'**{level}**' in text
    assert 'Mutation gate: VACUOUS (3 killed, 1 survived)' in text
    assert '| mutation | skipped |  | --mutants 0 |' in text
    assert 'Removed at head (nothing to verify): `m.py:<module>.old`' in text
    assert 'did not export: `m.py:<module>.absent`' in text
    assert 'Levels never round up' in text


# ------------------------------------------------------------------ behaviour

SET = 'm.py:<module>.C.__setitem__'
ROW = {'function': SET, 'args': '(int 1, int 1)', 'detail': 'cpython raised ValueError, lean returned unit',
       'lean_repr': 'Autoform.Core.EResult.val (Autoform.Core.Val.unit)', 'origin': 'test-suite',
       'observation': {'outcome': ['exn', 'ValueError'], 'self': ['ref', 0],
                       'heap': [['m.py:<module>.C', [['getsizeof', ['fn', 't.py:<module>.t.<lambda>2']],
                                                     ['_C__maxsize', ['int', 3]]], None]]}}
NOISE = {'function': 'm.py:<module>.C.__init__', 'args': '(int 2, unit)',
         'detail': 'cpython=unit lean=unit; heap graph=some false',
         'lean_repr': 'Autoform.Core.EResult.val (Autoform.Core.Val.unit)',
         'observation': {'outcome': ['val', ['unit']]}}


def cases(name, agree=0, diverge=0, inconclusive=0):
    return ([{'name': name, 'comparison': 'agree'}] * agree + [{'name': name, 'comparison': 'diverge'}] * diverge
            + [{'name': name, 'comparison': 'inconclusive'}] * inconclusive)


def behave(rows, control=None, extra_cases=(), changed_names=(SET, 'm.py:<module>.C.__init__', 'm.py:<module>.C.get'),
           notes=None):
    cross = {'runtime_cases': list(extra_cases), 'divergence_detail': rows,
             'coverage': {'by_status': {}}}
    out, suppressed = pr_mode.behaviour_results(
        [changed(n) for n in changed_names], cross, control, notes or {})
    return out, suppressed


def test_a_changed_input_is_reported_with_the_call_and_both_results():
    out, suppressed = behave([ROW], extra_cases=cases(SET, agree=4, diverge=1))
    row = out[SET]
    assert row['status'] == 'changed' and suppressed == 0
    item, = row['counter_inputs']
    assert item['call'] == 'C.__setitem__(int 1, int 1)'
    assert item['base_model'] == 'returns unit'
    assert item['head_runtime'] == 'raises ValueError'
    assert 'getsizeof=<lambda>2' in item['receiver'] and 'C{' in item['receiver']


def test_at_most_three_counter_inputs_are_kept_and_all_are_counted():
    rows = [dict(ROW, args=f'(int {n}, int 1)') for n in range(5)]
    out, _ = behave(rows, extra_cases=cases(SET, diverge=5))
    assert len(out[SET]['counter_inputs']) == 3 and out[SET]['diverging'] == 5


def test_unchanged_states_the_number_of_cases_and_is_not_a_proof():
    out, _ = behave([], extra_cases=cases(SET, agree=7))
    row = out[SET]
    assert row['status'] == 'unchanged-on-inputs' and row['compared'] == 7
    assert '7 case(s) compared' in row['reason'] and 'not a proof' in row['reason']


def test_all_inconclusive_is_not_compared_with_the_reason_never_unchanged():
    out, _ = behave([], extra_cases=cases(SET, inconclusive=9))
    row = out[SET]
    assert row['status'] == 'not-compared' and row['compared'] == 0
    assert '9 inconclusive' in row['reason']
    assert out['m.py:<module>.C.get']['status'] == 'not-compared'


def test_a_function_without_a_base_model_is_not_compared_with_its_note():
    out, _ = behave([], extra_cases=cases(SET, agree=2), notes={SET: 'added at head, no base behaviour'})
    assert out[SET] == {'status': 'not-compared', 'reason': 'added at head, no base behaviour', 'compared': 0,
                        'counter_inputs': [], 'suppressed_as_model_noise': 0}


def test_divergences_the_same_base_control_also_has_are_suppressed_and_counted():
    init = 'm.py:<module>.C.__init__'
    out, suppressed = behave([NOISE, NOISE, ROW], control={'divergence_detail': [NOISE, NOISE]},
                             extra_cases=cases(init, diverge=2) + cases(SET, diverge=1))
    assert suppressed == 2
    assert out[init]['status'] == 'not-compared' and out[init]['suppressed_as_model_noise'] == 2
    assert 'model noise' in out[init]['reason']
    assert out[SET]['status'] == 'changed'
    # one control row cancels one cross row, not all of them
    out, suppressed = behave([NOISE, NOISE], control={'divergence_detail': [NOISE]},
                             extra_cases=cases(init, diverge=2))
    assert suppressed == 1 and out[init]['status'] == 'changed' and out[init]['diverging'] == 1
    # no control run: nothing is filtered
    out, suppressed = behave([NOISE], control=None, extra_cases=cases(init, diverge=1))
    assert suppressed == 0 and out[init]['status'] == 'changed'


def with_behaviour(_unused=None):
    results = [dict(r) for r in levels().values()][:2]
    first, second = results[0]['name'], results[1]['name']
    results[0]['behaviour'] = pr_mode.behaviour_results(
        [changed(first)], {'runtime_cases': cases(first, diverge=1),
                           'divergence_detail': [dict(ROW, function=first)]}, None, {})[0][first]
    results[1]['behaviour'] = pr_mode.behaviour_results(
        [changed(second)], {'runtime_cases': cases(second, inconclusive=3)}, None, {})[0][second]
    report = report_for(results)
    report['behaviour'] = {'suppressed_as_model_noise': 4,
                           'summary': {'changed': 1, 'unchanged-on-inputs': 0, 'not-compared': 1}}
    return report, results


def test_sarif_carries_the_behaviour_rule_with_the_input_and_both_results():
    report, results = with_behaviour(None)
    document = pr_mode.sarif_document(report)
    assert pr_mode.validate_sarif(document) == []
    run = document['runs'][0]
    assert 'autoform/behaviour-changed' in [r['id'] for r in run['tool']['driver']['rules']]
    found = [r for r in run['results'] if r['ruleId'] == 'autoform/behaviour-changed']
    assert len(found) == 1 and found[0]['level'] == 'warning'
    text = found[0]['message']['text']
    assert 'proved(int 1, int 1)' in text and 'getsizeof=<lambda>2' in text
    assert 'base model returns unit' in text and 'head runtime raises ValueError' in text
    assert len(run['results']) == len(results) + 1


def test_markdown_has_the_behaviour_section_and_names_the_suppression():
    report, results = with_behaviour(None)
    text = pr_mode.markdown_comment(report)
    assert '### PR verdict' in text
    # The PR verdict leads; the level is named as the head model's conformance.
    assert text.index('### PR verdict') < text.index('### Head model conformance')
    assert '| function | change | head model conformance |' in text
    assert 'behaviour: changed' in text and 'head runtime raises ValueError' in text
    assert 'suppressed-as-model-noise: 4' in text
    assert '| not-compared |' in text and '3 inconclusive' in text


def test_a_report_without_behaviour_has_no_behaviour_section_or_result():
    report = report_for(list(levels().values()))
    text = pr_mode.markdown_comment(report)
    assert 'Behaviour changes' not in text and 'behaviour: changed' not in text
    assert 'PR verdict' in text and 'Not run' in text
    assert all(r['ruleId'] != 'autoform/behaviour-changed'
               for r in pr_mode.sarif_document(report)['runs'][0]['results'])


def test_the_exit_code_ignores_behaviour_changes_unless_asked():
    source = (ROOT / 'scripts/pr_mode.py').read_text()
    assert 'elif report["summary"]["refuted"] or ("behaviour-changed" in args.fail_on and changed_behaviour):' in source
    # Exit 3 (no evidence) exists only under --fail-on and comes after 1 and 2.
    start = source.index('def run(')
    assert source.index('exit_code = 2\n', start) < source.index('exit_code = 1\n', start) \
        < source.index('exit_code = EXIT_INCONCLUSIVE', start)
    assert 'if not set(fail_on) & set(FAIL_ON):\n        return None' in source


def test_the_test_overlay_replaces_the_base_tests_with_the_heads(tmp_path):
    base, head = tmp_path / 'base', tmp_path / 'head'
    for tree, mark in ((base, 'old'), (head, 'new')):
        (tree / 'src').mkdir(parents=True)
        (tree / 'src/lib.py').write_text(mark)
        (tree / 'tests').mkdir()
        (tree / 'tests/test_a.py').write_text(mark)
    (base / 'tests/test_gone.py').write_text('old')
    assert pr_mode.build_hybrid(base, head) == ['tests']
    assert (base / 'src/lib.py').read_text() == 'old'
    assert (base / 'tests/test_a.py').read_text() == 'new' and not (base / 'tests/test_gone.py').exists()


def test_behaviour_routes_each_function_by_its_file_extension(monkeypatch):
    """A language is compared when the oracle has a cross-revision backend for it and its
    toolchain is present (`runtime_backends.CROSS_REVISION_INPUTS`); one run compares one
    language, and every other function is `not-compared` with the reason."""
    backends = pr_mode._backends()
    monkeypatch.setattr(backends.shutil, 'which', lambda tool: '/usr/bin/' + tool)
    jav = lambda n, f='src/main/java/p/A.java': dict(changed(n), file=f, path=f, language=pr_mode.source_language(f))
    assert [pr_mode.source_language(p) for p in ('a.py', 'A.java', 'B.kt', 'c.go', 'd.ts', 'e.mjs', 'f.c',
                                                 'z.h', 'x.cpp', 'g.rb', None)] == \
        ['python', 'java', 'kotlin', 'go', 'ts', 'js', 'c', 'c-header', 'cpp', 'other', 'other']
    language, notes = pr_mode.behaviour_plan([jav('p.A.f:int(int)'), jav('p.A.g:int(int)'), changed(SET),
                                              jav('main', 'cmd/main.go'), jav('run', 'bin/run.rb')])
    assert language == 'java'
    assert set(notes) == {SET, 'main', 'run'}
    assert 'compared java' in notes[SET] and 'compared java' in notes['main']
    assert 'no cross-revision runtime backend' in notes['run']
    assert pr_mode.behaviour_plan([changed(SET)]) == ('python', {})
    assert pr_mode.behaviour_plan([jav('lib.ts::program:f', 'lib.ts')]) == ('ts', {})
    assert pr_mode.behaviour_plan([jav('calc.Clamp', 'calc/calc.go')]) == ('go', {})
    monkeypatch.setattr(backends.shutil, 'which', lambda tool: None)
    language, notes = pr_mode.behaviour_plan([jav('p.A.f:int(int)')])
    assert language is None and 'javac' in notes['p.A.f:int(int)']
    language, notes = pr_mode.behaviour_plan([jav('lib.ts::program:f', 'lib.ts')])
    assert language is None and 'node not on PATH' in notes['lib.ts::program:f']


def test_an_archived_revision_gets_the_working_trees_installed_packages(tmp_path):
    """`git archive` carries no `node_modules`; the runtime must still load modules that
    import a package, so the working tree's are linked in at the same paths (never walked
    into, and never over a path the archive has)."""
    repo, tree = tmp_path / 'repo', tmp_path / 'tree'
    for rel in ('node_modules/dep', 'packages/a/node_modules/dep2', 'packages/a/node_modules/x/node_modules/y',
                'only-installed/node_modules/z', '.git/node_modules/no'):
        (repo / rel).mkdir(parents=True)
    (tree / 'packages/a').mkdir(parents=True)
    linked = pr_mode.link_installed_dependencies(repo, tree)
    assert linked == ['node_modules', 'packages/a/node_modules']
    assert (tree / 'node_modules/dep').is_dir() and (tree / 'packages/a/node_modules/dep2').is_dir()
    assert (tree / 'node_modules').resolve() == (repo / 'node_modules').resolve()
    assert not (tree / 'only-installed').exists()
    # None at the root: the nearest one above the checkout, as Node would reach it.
    outer = tmp_path / 'outer'
    (outer / 'node_modules/up').mkdir(parents=True)
    (outer / 'checkout/src').mkdir(parents=True)
    (tmp_path / 'tree2').mkdir()
    assert pr_mode.link_installed_dependencies(outer / 'checkout', tmp_path / 'tree2') == \
        [str((outer / 'node_modules').resolve())]
    assert (tmp_path / 'tree2/node_modules/up').is_dir()


def test_c_functions_are_compared_when_a_c_compiler_is_present(monkeypatch):
    """A `.c` function goes to the native C leg (seeded inputs, no test overlay); without
    `cc` it is `not-compared` with that reason. A `.h` is not C here (the extension is
    shared with C++); a C++ source is the `cpp` row, so next to a C function it is
    `not-compared` only because one run compares one language."""
    c = lambda n, f='adler32.c': dict(changed(n), file=f, path=f, language=pr_mode.source_language(f))
    backends = pr_mode._backends()
    monkeypatch.setattr(backends.shutil, 'which', lambda tool: '/usr/bin/' + tool)
    language, notes = pr_mode.behaviour_plan([c('adler32_combine_'), c('inline_max', 'util.h'),
                                              c('Ring::push', 'ring.cpp')])
    assert language == 'c' and set(notes) == {'inline_max', 'Ring::push'}
    assert notes['inline_max'] == pr_mode.behaviour_toolchain('c-header')
    assert 'shared by C and C++' in notes['inline_max']
    assert 'cpp function' in notes['Ring::push'] and 'compared c' in notes['Ring::push']
    assert 'native C' in backends.CROSS_REVISION_INPUTS['c']
    monkeypatch.setattr(backends.shutil, 'which', lambda tool: None)
    language, notes = pr_mode.behaviour_plan([c('adler32_combine_')])
    assert language is None and 'cc not on PATH' in notes['adler32_combine_']


def test_a_c_counter_input_names_the_bare_function_and_both_results():
    row = {'function': 'clamp', 'args': '(int 0)', 'detail': 'cc=int 0 lean=int 1',
           'lean_repr': 'EResult.val (Val.int 1)', 'origin': 'boundary-zero',
           'observation': {'outcome': ['val', ['int', 0]]}}
    out, _ = pr_mode.behaviour_results([dict(changed('clamp'), file='lib.c')],
                                       {'runtime_cases': [{'name': 'clamp', 'comparison': 'diverge'}],
                                        'divergence_detail': [row]}, None, {})
    assert out['clamp']['status'] == 'changed'
    assert out['clamp']['counter_inputs'][0]['call'] == 'clamp(int 0)'
    assert out['clamp']['counter_inputs'][0]['base_model'] == 'returns int 1'
    assert out['clamp']['counter_inputs'][0]['head_runtime'] == 'returns int 0'


def test_a_method_the_jvm_oracle_skips_is_not_compared_with_the_oracles_reason():
    name = 'p.A.offset:int(int)'
    cross = {'runtime_cases': [], 'divergence_detail': [],
             'backend_skipped': {name: 'instance method: needs a receiver'},
             'coverage': {'by_status': {name: 'blocked (unexercised): hole-free, no case built'}}}
    out, _ = pr_mode.behaviour_results([dict(changed(name), file='A.java')], cross, None, {})
    assert out[name]['status'] == 'not-compared'
    assert out[name]['reason'] == 'the oracle did not call it: instance method: needs a receiver'
    assert pr_mode._compared_languages([dict(changed(name), file='A.java')], out) == []


# ------------------------------------------------------- readable reason strings

CLASSPATH = [f'/home/ci/.m2/repository/org/lib{i}/lib{i}-1.{i}.jar' for i in range(400)]


def not_compared(name, conformance):
    """`evidence` for one hole-free, type-checked function the oracle did not compare."""
    return pr_mode.evidence([changed(name)], [fn(name)], conformance, None, None,
                            dict(STAGES, oracle={'status': 'failed',
                                                 'reason': 'exit 2: backend kotlin: {"dependency_classpath": ["'
                                                           + CLASSPATH[0]}),
                            'Probe', EXPORTER)[0]


def test_an_oracle_failure_reason_is_a_summary_never_the_backend_info_dump():
    # The shape `differential.py` writes when the JVM backend builds no case: before,
    # the reason was the stage's log tail, a truncated JSON dump of `backend_info`
    # (dependency classpath included) followed by `backend_status`, the same dict again.
    name = 'm.py:<module>.f'
    info = {'primitive_static_candidates': 0, 'primitive_instance_candidates': 1,
            'dependency_classpath': CLASSPATH, 'processor_path': CLASSPATH[:3]}
    conformance = {'backend': 'jvm', 'backend_info': info,
                   'backend_status': 'UNSUPPORTED: no testable surface — ' + str(info),
                   'backend_skipped': {name: 'instance method: needs a receiver (built for Java only)'},
                   'status': 'INCONCLUSIVE: no runtime comparisons', 'coverage': {'by_status': {}}}
    record = not_compared(name, conformance)
    assert record['level'] == 'translated'
    assert record['reason'] == ('type-checked; not adjudicated by the oracle: UNSUPPORTED: no testable '
                                'surface: instance method: needs a receiver (built for Java only) '
                                '(jvm, 0 cases built)')
    assert '.jar' not in record['reason'] and '{' not in record['reason']


@pytest.mark.parametrize('info, skipped, cause', [
    ({'primitive_static_candidates': 3, 'primitive_instance_candidates': 0, 'files_candidate': 3,
      'files_compiled': 0, 'files_failed': 3, 'dependency_classpath': CLASSPATH,
      'compile_failure_causes': {'unresolved package (missing classpath or source root)': 2,
                                 'other javac error': 1}},
     {'javac failed: Foo.java:3: error: package com.x does not exist'},
     'UNSUPPORTED: javac failed on 3/3 candidate file(s): unresolved package (missing classpath or '
     'source root) x2, other javac error x1'),
    ({'primitive_static_candidates': 2, 'primitive_instance_candidates': 0, 'dependency_classpath': CLASSPATH},
     {'kotlinc failed: ' + ':'.join(CLASSPATH)[-1500:] + 'ountry(\n'
      '/work/src/main/kotlin/com/x/PriceMapper.kt:381:9: error: unresolved reference \'Credit\'.\n'
      '/work/src/main/kotlin/com/x/PriceMapper.kt:382:9: error: unresolved reference \'Other\'.\n'},
     "UNSUPPORTED: kotlinc failed: PriceMapper.kt:381:9: error: unresolved reference 'Credit'."),
])
def test_candidates_that_did_not_compile_are_not_called_no_testable_surface(info, skipped, cause):
    name = 'm.py:<module>.f'
    conformance = {'backend': 'kotlin', 'backend_info': info,
                   'backend_status': 'UNSUPPORTED: no testable surface — ' + str(info),
                   'backend_skipped': {name: next(iter(skipped))}, 'coverage': {'by_status': {}}}
    reason = not_compared(name, conformance)['reason']
    own = pr_mode.skip_reason(next(iter(skipped)))
    tail = '' if own in cause else ': ' + own   # the function's own reason, unless it IS the cause
    assert reason == f'type-checked; not adjudicated by the oracle: {cause}{tail} (kotlin, 0 cases built)'
    assert 'no testable surface' not in reason and '.jar' not in reason
    assert len(reason) <= pr_mode.REASON_CAP


def test_every_reason_is_capped_and_never_carries_a_classpath():
    name = 'p.A.f:int(int)'
    out, _ = pr_mode.behaviour_results([dict(changed(name), file='A.kt')], {
        'runtime_cases': [], 'divergence_detail': [], 'coverage': {'by_status': {}},
        'backend_skipped': {name: 'kotlinc failed: warning: ' + ':'.join(CLASSPATH)}}, None, {})
    assert out[name]['reason'] == 'the oracle did not call it: kotlinc failed'
    long = pr_mode.readable('cannot compile against ' + ':'.join(CLASSPATH) + ' because ' + 'x' * 2000)
    assert len(long) <= pr_mode.REASON_CAP and long.endswith('...')
    assert long.startswith('cannot compile against <classpath> because x')
    # Without a conformance.json the stage's log tail is the reason, minus the dump.
    record = not_compared('m.py:<module>.f', None)
    assert record['reason'] == 'type-checked; not adjudicated by the oracle: exit 2: backend kotlin: {...}'


# ------------------------------------------------------------- the evidence gate

def gated(*statuses, files=None):
    return [dict(changed(f'm.py:<module>.f{i}'), file=(files or {}).get(i, 'm.py'),
                 behaviour={'status': s} if s else None) for i, s in enumerate(statuses)]


def test_the_gate_is_inconclusive_when_no_changed_non_test_function_was_compared():
    assert pr_mode.evidence_gate(gated('not-compared'), []) is None   # no --fail-on: no gate
    for fail_on in (['behaviour-changed'], ['no-evidence']):
        gate = pr_mode.evidence_gate(gated('not-compared', None), fail_on)
        assert gate['status'] == 'inconclusive' and gate['exit_code'] == 3
        assert gate['reason'].startswith('inconclusive: no evidence')
    # A compared TEST function is no evidence about the change under test.
    gate = pr_mode.evidence_gate(gated('not-compared', 'unchanged-on-inputs',
                                       files={1: 'src/test/java/p/ATest.java'}), ['behaviour-changed'])
    assert gate['status'] == 'inconclusive' and gate['subjects'] == 1
    for evidence in ('changed', 'unchanged-on-inputs'):
        assert pr_mode.evidence_gate(gated('not-compared', evidence), ['no-evidence'])['status'] == 'evidence'
    # Nothing but test code changed (or nothing at all): nothing for the gate to compare.
    assert pr_mode.evidence_gate(gated('not-compared', files={0: 'tests/test_a.py'}),
                                 ['behaviour-changed'])['status'] == 'evidence'
    assert pr_mode.evidence_gate([], ['behaviour-changed'])['status'] == 'evidence'


@pytest.mark.parametrize('path, test', [
    ('tests/test_a.py', True), ('pkg/test_a.py', True), ('src/test/java/p/A.java', True),
    ('src/main/kotlin/p/ValidatorTest.kt', True), ('lib/a.spec.ts', True), ('a_test.go', True),
    ('src/main/java/p/Contest.java', False), ('pkg/latest.py', False), ('src/main/java/p/A.java', False),
])
def test_test_code_is_recognised_by_path(path, test):
    assert pr_mode.is_test_function({'file': path}) is test


def test_an_inconclusive_gate_is_the_first_line_of_the_markdown():
    report = report_for(list(levels().values()))
    assert not pr_mode.markdown_comment(report).startswith('**autoform: INCONCLUSIVE')
    report['gate'] = pr_mode.evidence_gate(gated('not-compared'), ['behaviour-changed'])
    first = pr_mode.markdown_comment(report).splitlines()[0]
    assert first.startswith('**autoform: INCONCLUSIVE (exit 3): inconclusive: no evidence')


@needs_git
def test_a_timed_out_oracle_is_reported_as_a_timeout_per_function(tmp_path, monkeypatch):
    """A killed oracle writes no conformance.json, and the per-function reason used to say
    exactly that ('produced no conformance.json'), which reads as a crash. It says how
    long the stage ran instead."""
    repo = tmp_path / 'repo'
    (repo / 'p').mkdir(parents=True)
    (repo / 'p/A.java').write_text('package p; public class A { static int f(int x) { return x; } }\n')
    for args in (['init', '-q'], ['add', '.'],
                 ['-c', 'user.name=t', '-c', 'user.email=t@t', 'commit', '-q', '-m', 'base']):
        subprocess.run(['git', *args], cwd=repo, check=True)
    name = 'p.A.f:int(int)'
    monkeypatch.setattr(pr_mode.shutil, 'which', lambda tool, **kw: '/usr/bin/' + tool)
    monkeypatch.setattr(pr_mode, 'export_ast', lambda source, out, log_dir, timeout: Path(out).write_text(
        json.dumps([dict(fn(name), file='p/A.java')])))
    monkeypatch.setattr(pr_mode.Chain, 'render', lambda self, ast: True)
    monkeypatch.setattr(pr_mode.Chain, 'build', lambda self: True)

    def oracle(self, ast_path, cases, tests):
        self.timeout = 0.2
        self.run('oracle', [sys.executable, '-c', 'import time; time.sleep(30)'], cwd=self.report,
                 log_name='conformance.log', ok=(0, 1))
        return None

    monkeypatch.setattr(pr_mode.Chain, 'oracle', oracle)
    function = dict(changed(name), file='p/A.java', path='p/A.java', language='java')
    results, stages, _ = pr_mode.run_behaviour(repo, 'HEAD', repo, '', [function], 'PullRequestTimeout',
                                               tmp_path / 'report', 2, None, sys.executable, 0.2,
                                               lambda message: None)
    assert stages['behaviour-oracle']['reason'] == 'timed out after 0.2s'
    assert results[name]['status'] == 'not-compared'
    assert 'timed out after 0.2s' in results[name]['reason']
    assert 'conformance.json' not in results[name]['reason']


# ---------------------------------------------------------------- the exporter
# `autoform.sh` passes the frontend the arguments `source_context.context` assembles
# (CPP_DEFINES, the compilation database, kernel-tree defines, the delombok mode, the
# over-cap excludes); `export_ast` used to pass only the delombok mode, so a C repository
# analysed with `autoform pr` lost its defines and its compilation database, and the base
# and head exports could differ from what `autoform source` produces (zlib typedefs
# behind `#ifdef` stayed unresolved). These tests stub `subprocess` and pin the
# joern-parse argv for each tree.

def fake_joern_home(tmp_path):
    """A JOERN_HOME whose two binaries exist; `subprocess` is what each test stubs."""
    joern = tmp_path / 'joern' / 'joern-cli'
    joern.mkdir(parents=True)
    for name in ('joern-parse', 'joern'):
        (joern / name).write_text('#!/bin/sh\nexit 0\n')
    return joern


def clear_frontend_env(monkeypatch):
    """The environment `source_context.context` reads, cleared: a test sets only the knob
    it names, so no ambient setting can leak an argument into the assertions."""
    for name in ('CPP_DEFINES', 'AUTOFORM_LANGUAGE', 'AUTOFORM_FRONTEND', 'AUTOFORM_DELOMBOK_MODE',
                 'AUTOFORM_COMPILE_COMMANDS', 'AUTOFORM_MAX_FILE_BYTES', 'AUTOFORM_DATA_MODEL'):
        monkeypatch.delenv(name, raising=False)


def stubbed_joern(tmp_path, monkeypatch):
    """`export_ast`'s two Joern calls, both succeeding under a stubbed `subprocess.run`
    that records every argv. The `joern` call stands in for export_ast.sc: its output
    file is not read here, only the frontend's argv is under test."""
    joern = fake_joern_home(tmp_path)
    monkeypatch.setenv('JOERN_HOME', str(joern))
    seen = []

    def run(argv, **kwargs):
        seen.append(list(argv))
        stdout = '' if Path(argv[0]).name == 'joern-parse' else 'exported 1 functions + 0 module initializers\n'
        return subprocess.CompletedProcess(argv, 0, stdout, '')

    monkeypatch.setattr(pr_mode.subprocess, 'run', run)
    return str(joern), seen


def parse_of(seen, joern, source):
    """The recorded joern-parse argv with its fixed head ([joern-parse, source, --output,
    cpg]) stripped, leaving only the frontend arguments."""
    parse = seen[0]
    assert parse[:4] == [joern + '/joern-parse', str(source), '--output', parse[3]]
    assert parse[3].endswith('cpg.bin')
    return parse[4:]


def test_the_export_passes_the_c_preprocessor_configuration_to_joern(tmp_path, monkeypatch):
    joern, seen = stubbed_joern(tmp_path, monkeypatch)
    clear_frontend_env(monkeypatch)
    monkeypatch.setenv('CPP_DEFINES', 'TESTGUARD,OF_TYPE=unsigned')
    source = tmp_path / 'source'
    source.mkdir()
    (source / 'inflate.c').write_text('int f(void) { return 0; }\n')
    notes = pr_mode.export_ast(source, tmp_path / 'ast.json', tmp_path, 30)
    args = ['--frontend-args', '--define', 'TESTGUARD', '--define', 'OF_TYPE=unsigned']
    assert parse_of(seen, joern, source) == args
    assert notes == {'frontend_args': args}


def test_the_export_passes_the_compilation_database_to_joern(tmp_path, monkeypatch):
    joern, seen = stubbed_joern(tmp_path, monkeypatch)
    clear_frontend_env(monkeypatch)
    source = tmp_path / 'source'
    (source / 'lib').mkdir(parents=True)
    (source / 'lib/trees.c').write_text('int f(void) { return 0; }\n')
    (source / 'compile_commands.json').write_text('[]\n')
    notes = pr_mode.export_ast(source, tmp_path / 'ast.json', tmp_path, 30)
    args = ['--frontend-args', '--compilation-database',
            str((source / 'compile_commands.json').resolve())]
    assert parse_of(seen, joern, source) == args
    assert notes == {'frontend_args': args}


def test_the_export_passes_the_delombok_mode_to_a_java_tree(tmp_path, monkeypatch):
    joern, seen = stubbed_joern(tmp_path, monkeypatch)
    clear_frontend_env(monkeypatch)
    source = tmp_path / 'source'
    (source / 'src/main/java/p').mkdir(parents=True)
    (source / 'src/main/java/p/A.java').write_text('package p;\nclass A { int f() { return 1; } }\n')
    notes = pr_mode.export_ast(source, tmp_path / 'ast.json', tmp_path, 30)
    assert parse_of(seen, joern, source) == ['--frontend-args', '--delombok-mode', 'types-only']
    assert notes == {'frontend_args': ['--frontend-args', '--delombok-mode', 'types-only']}


def test_the_export_passes_no_frontend_args_for_a_python_tree(tmp_path, monkeypatch):
    joern, seen = stubbed_joern(tmp_path, monkeypatch)
    clear_frontend_env(monkeypatch)
    source = tmp_path / 'source'
    source.mkdir()
    (source / 'mod.py').write_text('def f():\n    return 1\n')
    notes = pr_mode.export_ast(source, tmp_path / 'ast.json', tmp_path, 30)
    assert parse_of(seen, joern, source) == []
    assert notes == {'frontend_args': []}


def test_the_export_passes_the_forced_frontend_language_to_joern(tmp_path, monkeypatch):
    """AUTOFORM_FRONTEND forces a Joern frontend in `autoform source` (autoform.sh's
    LANGUAGE_ARGS, passed before the frontend args); the export passes it too, so a
    forced frontend reaches the head and base trees of a pull request. It is not part
    of `frontend_args`: that list stays the one source_context.py's args file holds."""
    joern, seen = stubbed_joern(tmp_path, monkeypatch)
    clear_frontend_env(monkeypatch)
    monkeypatch.setenv('AUTOFORM_FRONTEND', 'c')
    source = tmp_path / 'source'
    source.mkdir()
    (source / 'inflate.c').write_text('int f(void) { return 0; }\n')
    notes = pr_mode.export_ast(source, tmp_path / 'ast.json', tmp_path, 30)
    assert parse_of(seen, joern, source) == ['--language', 'c']
    assert notes == {'frontend_args': []}


def test_the_no_overlay_reparse_keeps_the_frontend_args(tmp_path, monkeypatch):
    """The dataflow-overlay fallback re-parses the tree; the re-parse must not lose the
    configuration the first parse had."""
    joern = fake_joern_home(tmp_path)
    monkeypatch.setenv('JOERN_HOME', str(joern))
    clear_frontend_env(monkeypatch)
    monkeypatch.setenv('CPP_DEFINES', 'TESTGUARD')
    source = tmp_path / 'source'
    source.mkdir()
    (source / 'a.c').write_text('int f(void) { return 0; }\n')
    crash = ('ERROR ReachingDefPass Pass io.joern.dataflowengineoss.passes.reachingdef.ReachingDefPass '
             'failed\njava.util.NoSuchElementException: key not found: MethodRef')
    seen = []

    def run(argv, **kwargs):
        seen.append(list(argv))
        if Path(argv[0]).name == 'joern-parse':
            if '--nooverlays' in argv:
                return subprocess.CompletedProcess(argv, 0, 'parsed\n', '')
            return subprocess.CompletedProcess(argv, 1, crash, '')
        script = argv[argv.index('--script') + 1]
        if script.endswith('prepare_cpg.sc'):
            return subprocess.CompletedProcess(argv, 0,
                                               'prepared cpg without dataflowOss; overlays: base\n', '')
        return subprocess.CompletedProcess(argv, 0, 'exported 1 functions + 0 module initializers\n', '')

    monkeypatch.setattr(pr_mode.subprocess, 'run', run)
    notes = pr_mode.export_ast(source, tmp_path / 'ast.json', tmp_path, 30)
    args = ['--frontend-args', '--define', 'TESTGUARD']
    reparse = seen[1]
    assert seen[0][4:] == args
    # The re-parse carries --nooverlays before the same frontend arguments.
    assert reparse[:5] == [str(joern) + '/joern-parse', str(source), '--nooverlays', '--output',
                           reparse[4]]
    assert reparse[5:] == args
    assert notes == {'frontend_args': args,
                     'overlays': 'dataflowOss skipped: the default joern-parse failed in the dataflow '
                                 'overlay; the exporter reads no dataflow'}


@needs_git
def test_the_head_and_base_exports_get_the_same_frontend_args_and_pr_json_records_them(
        tmp_path, monkeypatch):
    """Both trees are parsed with the list `autoform source` would pass for them, and the
    report says which: the head's on the exporter record and the export stage, the base's
    on the behaviour-export stage. The base tree is exported here for change identity (no
    cross-revision C oracle is offered), so no compiler or Lean is needed."""
    repo = tmp_path / 'repo'
    (repo / 'lib').mkdir(parents=True)
    pr_fixture.git(repo.parent, 'init', '-q', str(repo))
    commits = {}
    for tag, text in (('base', 'int f(void) { return 1; }\n'),
                      ('head', 'int f(void) { return 2; }\n')):
        (repo / 'lib/a.c').write_text(text)
        pr_fixture.git(repo, 'add', '-A')
        pr_fixture.git(repo, 'commit', '-q', '-m', tag)
        commits[tag] = pr_fixture.git(repo, 'rev-parse', 'HEAD')
    joern = fake_joern_home(tmp_path)
    monkeypatch.setenv('JOERN_HOME', str(joern))
    clear_frontend_env(monkeypatch)
    monkeypatch.setenv('CPP_DEFINES', 'TESTGUARD')
    for name in ('AUTOFORM_ORACLE_PYTHON', 'AUTOFORM_ORACLE_PYTEST_ADDOPTS'):
        monkeypatch.delenv(name, raising=False)
    real_run, parses = subprocess.run, []

    def run(argv, **kwargs):
        name = Path(argv[0]).name
        if name not in ('joern-parse', 'joern'):
            return real_run(argv, **kwargs)   # git, tar and the oracle probe run for real
        if name == 'joern-parse':
            parses.append(list(argv))
            return subprocess.CompletedProcess(argv, 0, '', '')
        out = next(a[len('out='):] for a in argv if a.startswith('out='))
        # behaviour/raw.json is the base export; the head's is ast-<module>.full.json.
        value = 1 if Path(out).name == 'raw.json' else 2
        Path(out).write_text(json.dumps([dict(fn('lib/a.c:f', {'k': 'ret', 'e': {'k': 'int', 'v': value}}),
                                              file='lib/a.c')]))
        return subprocess.CompletedProcess(argv, 0,
                                           f'exported 1 functions + 0 module initializers to {out}\n', '')

    monkeypatch.setattr(pr_mode.subprocess, 'run', run)
    monkeypatch.setattr(pr_mode, 'behaviour_toolchain', lambda language: 'no C oracle in this test')
    monkeypatch.setattr(pr_mode.Chain, 'render', lambda self, ast: False)
    out = tmp_path / 'out'
    assert pr_mode.main([str(repo), '--base', commits['base'], '--head', commits['head'], '--module',
                         'PullRequestFrontend', '--out', str(out)]) == 0
    args = ['--frontend-args', '--define', 'TESTGUARD']
    head, base = parses
    assert head[1] != base[1]                 # two trees: the head checkout, the archived base
    assert head[4:] == base[4:] == args
    report = json.loads((out / 'pr.json').read_text())
    assert report['exporter']['source'] == 'joern'
    assert report['exporter']['frontend_args'] == args
    assert report['stages']['export']['frontend_args'] == args
    assert report['behaviour']['stages']['behaviour-export']['frontend_args'] == args


# --------------------------------------------------------- the script, offline

def bare_env(tmp_path):
    """No `lake` on PATH, no Joern, a HOME without ~/.elan."""
    (tmp_path / 'home').mkdir(exist_ok=True)
    (tmp_path / 'bin').mkdir(exist_ok=True)
    for tool in ('git', 'tar', 'sh', 'bash'):
        found = shutil.which(tool)
        if found and not (tmp_path / 'bin' / tool).exists():
            os.symlink(found, tmp_path / 'bin' / tool)
    return dict(os.environ, PATH=str(tmp_path / 'bin'), HOME=str(tmp_path / 'home'),
                JOERN_HOME=str(tmp_path / 'no-joern'), AUTOFORM_NO_REEXEC='1')


def run_script(args, env):
    return subprocess.run([sys.executable, str(ROOT / 'scripts/pr_mode.py'), *map(str, args)],
                          env=env, text=True, capture_output=True, timeout=600)


@needs_git
def test_without_an_exporter_every_changed_function_is_reported_with_no_evidence(tmp_path):
    history = pr_fixture.make_history(tmp_path / 'repo')
    out = tmp_path / 'out'
    result = run_script([history['repo'], '--base', 'base', '--head', 'head', '--module', 'PullRequestTestNoJoern',
                         '--out', out, '--sarif', out / 'pr.sarif', '--markdown', out / 'pr.md'],
                        bare_env(tmp_path))
    # The report is still written in full, but nothing was analysed: exit 2, never a pass.
    assert result.returncode == 2, result.stdout + result.stderr
    assert 'could not analyse the change' in result.stdout
    report = json.loads((out / 'pr.json').read_text())
    assert report['exporter']['status'] == 'unavailable' and 'Joern' in report['exporter']['reason']
    assert len(report['functions']) == 5
    assert {f['level'] for f in report['functions']} == {'none'}
    assert all('no exporter output' in f['reason'] for f in report['functions'])
    assert {name: s['status'] for name, s in report['stages'].items()} == {
        'export': 'failed', 'render': 'skipped', 'build': 'skipped', 'oracle': 'skipped',
        'ledger': 'skipped', 'specs': 'skipped', 'mutation': 'skipped'}
    sarif = json.loads((out / 'pr.sarif').read_text())
    assert pr_mode.validate_sarif(sarif) == []
    assert [r['ruleId'] for r in sarif['runs'][0]['results']] == ['autoform/none'] * 5
    assert sarif['runs'][0]['versionControlProvenance'][0]['revisionId'] == history['head']
    assert '| none | 5 |' in (out / 'pr.md').read_text()


@needs_git
def test_a_changed_file_in_another_language_is_named_when_its_functions_cannot_be(tmp_path):
    history = pr_fixture.make_history(tmp_path / 'repo')
    (Path(history['repo']) / 'm.c').write_text('int f(int x) { return x; }\n')
    out = tmp_path / 'out'
    result = run_script([history['repo'], '--base', 'head', '--module', 'PullRequestTestOther',
                         '--out', out, '--markdown', out / 'pr.md'], bare_env(tmp_path))
    assert result.returncode == 2, result.stdout + result.stderr
    report = json.loads((out / 'pr.json').read_text())
    assert report['head']['commit'] is None and report['functions'] == []
    (record,) = report['files']
    assert record['path'] == 'm.c' and record['analysed'] == 'changed-file'
    assert record['note'] == 'no exporter output, so its functions cannot be named'
    assert '`m.c` (no exporter output, so its functions cannot be named)' in (out / 'pr.md').read_text()


@needs_git
def test_a_supplied_ast_without_lean_stops_at_holes_and_says_why(tmp_path):
    history = pr_fixture.make_history(tmp_path / 'repo')
    exported = [fn('numbers.py:<module>.quotient'), fn('numbers.py:<module>.clamp'),
                fn('numbers.py:<module>.label'), fn('numbers.py:<module>.first'),
                fn('numbers.py:<module>.raw', {'k': 'ret', 'e': {'k': 'hole', 'label': 'lit:bytes'}}),
                fn('numbers.py:<module>.add'), fn('<module-objects>:<module>'), fn('numbers.py:<module>')]
    for function in exported:
        function['file'] = 'numbers.py' if function['name'].startswith('numbers') else ''
    (tmp_path / 'ast.json').write_text(json.dumps(exported))
    out = tmp_path / 'out'
    result = run_script([history['repo'], '--base', 'base', '--head', 'head', '--module', 'PullRequestTestNoLean',
                         '--ast', tmp_path / 'ast.json', '--out', out, '--sarif', out / 'pr.sarif'],
                        bare_env(tmp_path))
    assert result.returncode == 0, result.stdout + result.stderr
    report = json.loads((out / 'pr.json').read_text())
    assert report['exporter']['source'] == 'supplied' and 'Joern not run' in report['exporter']['reason']
    by_name = {f['name'].rsplit('.', 1)[-1]: f for f in report['functions']}
    assert by_name['raw']['level'] == 'hole' and by_name['raw']['holes'] == ['lit:bytes']
    assert by_name['quotient']['level'] == 'none'
    assert 'lake is not on PATH' in by_name['quotient']['reason']
    assert report['stages']['render']['status'] == 'passed'
    assert report['stages']['build'] == {'status': 'skipped', 'reason': 'lake is not on PATH (install elan; see docs/running.md)'}
    # Only the changed functions and the module entries were rendered: `add` was left out.
    assert 'numbers.py:<module>.add' not in report['selection']['selected']
    assert pr_mode.validate_sarif(json.loads((out / 'pr.sarif').read_text())) == []


@needs_git
def test_the_script_refuses_a_plain_directory_and_an_unknown_ref(tmp_path):
    (tmp_path / 'plain').mkdir()
    result = run_script([tmp_path / 'plain', '--base', 'x'], bare_env(tmp_path))
    assert result.returncode == 2 and 'not a Git checkout' in result.stderr
    history = pr_fixture.make_history(tmp_path / 'repo')
    result = run_script([history['repo'], '--base', 'no-such-ref'], bare_env(tmp_path))
    assert result.returncode == 2 and 'unknown ref' in result.stderr
    assert 'git fetch --unshallow' in result.stderr   # the usual cause in CI is a shallow clone


@needs_git
@pytest.mark.parametrize('edit, reason', [
    (('README.md', '# notes\n'), 'no changed file is source code in a supported language'),
    (('numbers.py', None), 'no changed function in a changed Python file'),
])
def test_a_change_with_nothing_to_analyse_exits_0_with_the_reason_and_no_export(tmp_path, edit, reason):
    history = pr_fixture.make_history(tmp_path / 'repo')
    repo = Path(history['repo'])
    name, text = edit
    if text is None:   # a comment-only edit: the file changed, no def's AST did
        text = (repo / name).read_text() + '\n# trailing comment\n'
    (repo / name).write_text(text)
    pr_fixture.git(repo, 'add', name)
    pr_fixture.git(repo, 'commit', '-q', '-m', 'nothing to analyse')
    out = tmp_path / 'out'
    # `--ast` names a file that does not exist: had the exporter stage run, it would fail.
    # Commit ids, not the `head` tag: on a case-insensitive file system `head` is `HEAD`.
    result = run_script([repo, '--base', history['head'], '--head', pr_fixture.git(repo, 'rev-parse', 'HEAD'),
                         '--module', 'PullRequestNothing',
                         '--ast', tmp_path / 'absent.json', '--out', out,
                         '--sarif', out / 'pr.sarif', '--markdown', out / 'pr.md'], bare_env(tmp_path))
    assert result.returncode == 0, result.stdout + result.stderr
    assert f'nothing to analyse: {reason}' in result.stdout
    report = json.loads((out / 'pr.json').read_text())
    assert report['functions'] == [] and report['exporter'] == {'status': 'not-run', 'reason': reason}
    assert [f['path'] for f in report['files']] == [name]
    assert {stage['status'] for stage in report['stages'].values()} == {'skipped'}
    assert {stage['reason'] for stage in report['stages'].values()} == {reason}
    sarif = json.loads((out / 'pr.sarif').read_text())
    assert pr_mode.validate_sarif(sarif) == [] and sarif['runs'][0]['results'] == []
    assert reason in (out / 'pr.md').read_text()


@needs_git
def test_the_exit_code_is_0_reported_1_refuted_2_could_not_run(tmp_path, monkeypatch, capsys):
    history = pr_fixture.make_history(tmp_path / 'repo')
    monkeypatch.setenv('JOERN_HOME', str(tmp_path / 'no-joern'))
    hole = {'k': 'ret', 'e': {'k': 'hole', 'label': 'lit:bytes'}}   # level `hole`: no oracle runs
    (tmp_path / 'ast.json').write_text(json.dumps([fn('numbers.py:<module>.quotient', hole)]))
    argv = [history['repo'], '--base', 'base', '--head', 'head', '--module', 'PullRequestExit', '--no-behaviour',
            '--ast', str(tmp_path / 'ast.json')]
    assert pr_mode.main(argv + ['--out', str(tmp_path / 'reported')]) == 0
    # A changed supported file with no AST is "could not run", not a pass.
    assert pr_mode.main(argv[:-2] + ['--out', str(tmp_path / 'unexported')]) == 2
    real = pr_mode.evidence

    def one_refuted(*args, **kwargs):
        results = real(*args, **kwargs)
        return [dict(results[0], level='refuted')] + results[1:]

    monkeypatch.setattr(pr_mode, 'evidence', one_refuted)
    assert pr_mode.main(argv + ['--out', str(tmp_path / 'refuted')]) == 1
    assert json.loads((tmp_path / 'refuted/pr.json').read_text())['summary']['refuted'] == 1
    assert pr_mode.main([history['repo'], '--base', 'no-such-ref', '--out', str(tmp_path / 'x')]) == 2
    assert 'unknown ref' in capsys.readouterr().err


@needs_git
def test_fail_on_behaviour_changed_turns_a_behaviour_change_into_exit_1(tmp_path, monkeypatch):
    history = pr_fixture.make_history(tmp_path / 'repo')
    hole = {'k': 'ret', 'e': {'k': 'hole', 'label': 'lit:bytes'}}
    (tmp_path / 'ast.json').write_text(json.dumps([fn('numbers.py:<module>.quotient', hole)]))
    changed = {'status': 'changed', 'cases': 1, 'counter_inputs': [
        {'call': 'quotient(1, 0)', 'base_model': 'raises ZeroDivisionError', 'head_runtime': '0'}]}
    monkeypatch.setattr(pr_mode, 'run_behaviour', lambda repo, base, source, subdir, functions, *rest, **kw: (
        {f['name']: changed for f in functions}, {}, {'suppressed_as_model_noise': 0, 'languages': ['python']}))
    argv = [history['repo'], '--base', 'base', '--head', 'head', '--module', 'PullRequestFailOn',
            '--ast', str(tmp_path / 'ast.json')]
    assert pr_mode.main(argv + ['--out', str(tmp_path / 'default')]) == 0
    assert pr_mode.main(argv + ['--out', str(tmp_path / 'gated'), '--fail-on', 'behaviour-changed']) == 1
    # The gate had evidence (a compared function), so it is not inconclusive either way.
    assert json.loads((tmp_path / 'gated/pr.json').read_text())['gate']['status'] == 'evidence'


@needs_git
def test_a_gate_that_compared_nothing_exits_3_not_0(tmp_path, monkeypatch, capsys):
    # Measured: `--fail-on behaviour-changed` exited 0 on every run of an evaluation,
    # seeded regressions included, in runs where no changed function was compared.
    history = pr_fixture.make_history(tmp_path / 'repo')
    hole = {'k': 'ret', 'e': {'k': 'hole', 'label': 'lit:bytes'}}
    (tmp_path / 'ast.json').write_text(json.dumps([fn('numbers.py:<module>.quotient', hole)]))
    nothing = {'status': 'not-compared', 'reason': 'the oracle stage failed', 'compared': 0,
               'counter_inputs': [], 'suppressed_as_model_noise': 0}
    monkeypatch.setattr(pr_mode, 'run_behaviour', lambda repo, base, source, subdir, functions, *rest, **kw: (
        {f['name']: nothing for f in functions}, {}, {'suppressed_as_model_noise': 0, 'languages': []}))
    monkeypatch.setattr(pr_mode.Chain, 'render', lambda self, ast_path: False)   # no Lean needed here
    argv = [history['repo'], '--base', 'base', '--head', 'head', '--module', 'PullRequestNoEvidence',
            '--ast', str(tmp_path / 'ast.json')]
    # Default behaviour is unchanged: no --fail-on, no gate, exit 0.
    assert pr_mode.main(argv + ['--out', str(tmp_path / 'default')]) == 0
    assert 'gate' not in json.loads((tmp_path / 'default/pr.json').read_text())
    capsys.readouterr()
    for fail_on in ('behaviour-changed', 'no-evidence'):
        out = tmp_path / fail_on
        assert pr_mode.main(argv + ['--out', str(out), '--markdown', str(out / 'pr.md'),
                                    '--fail-on', fail_on]) == 3
        assert 'inconclusive: no evidence' in capsys.readouterr().out
        assert (out / 'pr.md').read_text().startswith('**autoform: INCONCLUSIVE (exit 3)')
        assert json.loads((out / 'pr.json').read_text())['gate']['status'] == 'inconclusive'
    # --no-behaviour compares nothing at all: under the gate that is inconclusive too.
    assert pr_mode.main(argv + ['--out', str(tmp_path / 'off'), '--no-behaviour',
                                '--fail-on', 'behaviour-changed']) == 3


# --------------------------------------------------------------- the Rust leg

# The fixture crate's base revision: a private helper and seven public functions, one per
# verdict the Rust leg can report. `halve` is the one the harness cannot encode at base
# (floats), `untouched` the one the change below must prune, and `next` calls the private
# helper the change edits (no line of `next` changes).
RUST_BASE = '''fn bump(x: u32) -> u32 {
    x + 1
}

pub fn clamp(x: u32, lo: u32, hi: u32) -> u32 {
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}

pub fn gcd(mut a: u32, mut b: u32) -> u32 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

pub fn next(x: u32) -> u32 {
    bump(x)
}

pub fn untouched(x: u32) -> u32 {
    x * 3
}

pub fn halve(x: f64) -> f64 {
    x / 2.0
}

pub fn add_wrapping(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

pub fn is_even(x: u32) -> bool {
    x % 2 == 0
}
'''

RUST_PR_EDITS = [
    # the private helper: `next` changes behaviour with none of its lines touched
    ('    x + 1\n', '    x + 2\n'),
    # a regression in a translated function: clamp no longer clamps from above
    ('        hi\n', '        x\n'),
    # a rename-only refactor of a translated function: the same behaviour
    ('let t = a % b;', 'let r = a % b;'),
    ('b = t;', 'b = r;'),
    # an edit in a function the harness cannot encode at base (floats)
    ('x / 2.0', 'x * 0.5'),
    # a signature change: not comparable
    ('pub fn add_wrapping(a: u32, b: u32) -> u32 {', 'pub fn add_wrapping(a: u64, b: u64) -> u64 {'),
    # a removal, and an addition
    ('pub fn is_even(x: u32) -> bool {\n    x % 2 == 0', 'pub fn is_odd(x: u32) -> bool {\n    x % 2 == 1'),
]


def _rust_pr_head():
    """The fixture's head text: the base with every edit above applied (each string is
    unique in the base, and none moves a line)."""
    text = RUST_BASE
    for old, new in RUST_PR_EDITS:
        assert text.count(old) == 1, old
        text = text.replace(old, new)
    return text


def _rust_crate(tree, tag):
    (tree / 'src').mkdir(parents=True, exist_ok=True)
    (tree / 'Cargo.toml').write_text('[package]\nname = "proto"\nversion = "0.1.0"\n'
                                     'edition = "2021"\n')
    (tree / 'src' / 'lib.rs').write_text(RUST_BASE if tag == 'base' else _rust_pr_head())


def _rust_pr_history(repo):
    """The fixture crate as two commits: `base`, and a `head` with the edits above."""
    return two_commit_history(repo, _rust_crate)


def _rust_spans(text):
    """`function_spans` as rust_regress writes them (rustdoc's span of each public
    function, the file relative to the crate), read off the fixture text."""
    lines, out = text.splitlines(), {}
    for i, line in enumerate(lines, 1):
        if line.startswith('pub fn '):
            end = next(j for j in range(i, len(lines) + 1) if lines[j - 1] == '}')
            name = line[len('pub fn '):].split('(')[0]
            out['proto::' + name] = {'file': 'src/lib.rs', 'begin_line': i, 'end_line': end}
    return out


def _fake_rust_report():
    """A rust_regress report in the shape `rust_regress.run` writes (every key, per-function
    records with the classifier's counters, examples with Rust literals and `ok ...`
    results) for the fixture's head. `untouched` was compared but the change never
    touched it (the leg compares every public function; the prune is pr mode's), `halve`
    is never called (the harness cannot encode it at base), `next` is a hole at base
    (native-only: no model verdict), and `is_odd` exists only at head."""
    def fn(name, status, evidence='model', regression=0, behaviour=0, unchanged=0,
           not_comparable=0, **extra):
        return {'function': 'proto::' + name, 'callee': 'proto::' + name, 'evidence': evidence,
                'cases': regression + behaviour + unchanged + not_comparable,
                'regression': regression, 'behaviour-change': behaviour, 'unchanged': unchanged,
                'inconclusive': 0, 'unstable': 0, 'not-comparable': not_comparable,
                'status': status, **extra}

    functions = [
        fn('add_wrapping', 'not-comparable', not_comparable=2, reason='signature changed at head'),
        fn('clamp', 'regression', regression=1, unchanged=2,
           examples=[{'args': ['7u32', '0u32', '5u32'], 'base_native': 'ok 5', 'base_model': 'ok 5',
                      'head_native': 'ok 7'}]),
        fn('gcd', 'unchanged', unchanged=4),
        fn('is_even', 'not-comparable', not_comparable=2,
           reason='removed at head (no public function proto::is_even)'),
        fn('next', 'behaviour-change', evidence='native-only', behaviour=1, unchanged=2,
           examples=[{'args': ['0u32'], 'base_native': 'ok 1', 'base_model': None,
                      'head_native': 'ok 2'}]),
        fn('untouched', 'unchanged', unchanged=3),
    ]
    not_comparable = {'proto::add_wrapping': 'signature changed at head',
                      'proto::is_even': 'removed at head (no public function proto::is_even)'}
    return {
        'language': 'rust', 'kind': 'rust-regression', 'base': 'base', 'head': 'head',
        'crate': 'proto',
        'oracle': 'native Rust at head vs the base revision\'s Aeneas model (where translated) and '
                  'vs native Rust at base, on the same inputs; debug profile',
        'base_model': {'functions': 7, 'translated': 5, 'holes': 2,
                       'conformance': {'agree': 9, 'total': 9, 'divergences': 0, 'inconclusive': 0}},
        'functions_model_backed': ['proto::add_wrapping', 'proto::clamp', 'proto::gcd',
                                   'proto::is_even', 'proto::untouched'],
        'functions_native_only': ['proto::next'],
        'functions_not_encodable': {'proto::halve': 'f64: float types are not encoded exactly'},
        'functions_added_at_head': ['proto::is_odd'],
        'not_comparable': not_comparable,
        'function_spans': {'base': _rust_spans(RUST_BASE), 'head': _rust_spans(_rust_pr_head())},
        'cases': {'regression': 1, 'behaviour-change': 1, 'unchanged': 11, 'inconclusive': 0,
                  'unstable': 0, 'not-comparable': 4},
        'total_cases': 17,
        'control': {'cases': 17, 'reproduced_base_model_run': 9, 'flagged': 0, 'flagged_detail': []},
        'functions': functions,
        'regressions': [f for f in functions if f['status'] == 'regression'],
        'behaviour_changes': [f for f in functions if f['status'] == 'behaviour-change'],
        'assumptions': ['debug profile at both revisions (overflow checks on, what Aeneas models)'],
        'sandbox': None, 'wall_clock_seconds': 1.0,
    }


def _fake_rust_regress(seen, report=None, error=None):
    """rust_regress.main replaced: the trees it was handed are recorded, and either the
    recorded report is written where the leg reads it with the leg's exit (1 when it
    found a regression or a behaviour change), or, with `error`, the refusal record
    `main` writes for a RustPathError, and exit 2."""
    def main(argv=None):
        seen['argv'] = list(argv or [])
        seen['trees'] = {side: (Path(argv[argv.index(side) + 1]) / 'src' / 'lib.rs').read_text()
                         for side in ('--base', '--head')}
        out = Path(argv[argv.index('--out') + 1])
        out.mkdir(parents=True, exist_ok=True)
        if error:
            (out / 'rust-regress-error.json').write_text(json.dumps(error))
            return 2
        (out / 'rust-regression.json').write_text(json.dumps(report))
        return 1 if report['regressions'] or report['behaviour_changes'] else 0

    return main


RUST_STAGE = {'status': 'passed',
              'note': '17 case(s) run at base, the control and head; the control flagged 0, '
                      '0 unstable case(s) excluded',
              'report': 'rust/rust-regression.json'}


@needs_git
def test_the_rust_leg_maps_each_verdict_to_a_behaviour_record(tmp_path, monkeypatch):
    """A Rust-only change in a Cargo library: the exporter does not run, the Rust leg is
    the whole comparison, and each of its verdicts becomes one behaviour record -- the
    change's public functions (and one a changed private helper made behave differently),
    pruned by their rustdoc span; the removed one is listed as removed."""
    monkeypatch.setattr(rust_aeneas, 'missing', lambda env=None: [])
    seen = {}
    monkeypatch.setattr(rust_regress, 'main', _fake_rust_regress(seen, _fake_rust_report()))
    repo = _rust_pr_history(tmp_path / 'repo')
    out = tmp_path / 'out'
    assert pr_mode.main([str(repo), '--base', 'base', '--head', 'head',
                         '--module', 'PullRequestRust', '--out', str(out),
                         '--sarif', str(out / 'pr.sarif'), '--markdown', str(out / 'pr.md'),
                         '--fail-on', 'behaviour-changed']) == 1
    # the leg was handed the two revisions the change names
    assert seen['trees'] == {'--base': RUST_BASE, '--head': _rust_pr_head()}
    argv = seen['argv']
    assert argv[argv.index('--out') + 1] == str((out / 'rust').resolve())
    report = json.loads((out / 'pr.json').read_text())
    # a Rust-only change: no exporter, and no stage of the chain ran
    assert report['exporter'] == {'status': 'not-run',
                                  'reason': 'every changed source file is Rust; the Rust leg '
                                            'compares it (the exporter has no Rust frontend)'}
    assert {name: stage['status'] for name, stage in report['stages'].items()} == {
        name: 'skipped' for name in ('export', 'render', 'build', 'oracle', 'ledger',
                                     'specs', 'mutation')}
    assert 'rustdoc spans for Rust' in report['detection']
    by_name = {f['name']: f for f in report['functions']}
    assert set(by_name) == {'proto::clamp', 'proto::gcd', 'proto::next', 'proto::halve',
                            'proto::add_wrapping', 'proto::is_odd'}
    assert all(f['level'] == 'none' and f['language'] == 'rust' and f['detection'] == 'rustdoc'
               and f['path'] == 'src/lib.rs' and 'no evidence level for Rust' in f['reason']
               for f in report['functions'])
    assert (by_name['proto::clamp']['line'], by_name['proto::clamp']['end_line']) == (5, 13)
    # regression -> changed, with the counter-input as the leg recorded it
    clamp = by_name['proto::clamp']
    assert clamp['change'] == 'modified' and 'change_detail' not in clamp
    assert clamp['behaviour']['status'] == 'changed'
    assert clamp['behaviour']['counter_inputs'] == [{
        'call': 'proto::clamp(7u32, 0u32, 5u32)', 'receiver': None, 'base_model': 'ok 5',
        'base_runtime': 'ok 5', 'head_runtime': 'ok 7', 'detail': None, 'origin': 'model'}]
    assert (clamp['behaviour']['diverging'], clamp['behaviour']['compared'],
            clamp['behaviour']['agree']) == (1, 3, 2)
    assert '1 regression(s)' in clamp['behaviour']['reason']
    # behaviour-change on a function none of whose lines changed: reported, and said so
    nxt = by_name['proto::next']
    assert nxt['change'] == 'modified' and 'not on the changed lines' in nxt['change_detail']
    assert nxt['behaviour']['status'] == 'changed'
    assert nxt['behaviour']['counter_inputs'] == [{
        'call': 'proto::next(0u32)', 'receiver': None, 'base_model': 'none (no model: native-only)',
        'base_runtime': 'ok 1', 'head_runtime': 'ok 2', 'detail': None, 'origin': 'native-only'}]
    assert '1 behaviour change(s)' in nxt['behaviour']['reason']
    # unchanged -> unchanged-on-inputs
    assert by_name['proto::gcd']['behaviour'] == {
        'status': 'unchanged-on-inputs', 'compared': 4, 'agree': 4, 'inconclusive': 0,
        'suppressed_as_model_noise': 0, 'counter_inputs': [],
        'reason': '4 case(s) compared, all agreed; this is not a proof of equivalence on other inputs'}
    # not comparable / not encodable / added -> not-compared, each with the leg's reason
    halve = by_name['proto::halve']['behaviour']
    assert halve['status'] == 'not-compared' and 'cannot encode it at the base revision' \
        in halve['reason'] and 'f64' in halve['reason']
    wrapping = by_name['proto::add_wrapping']['behaviour']
    assert wrapping['status'] == 'not-compared' and 'signature changed at head' in wrapping['reason']
    odd = by_name['proto::is_odd']
    assert odd['change'] == 'added' and odd['behaviour'] == {
        'status': 'not-compared', 'reason': 'added at head: it has no base model to compare',
        'compared': 0, 'counter_inputs': [], 'suppressed_as_model_noise': 0}
    # removed at head: listed as removed, like a removed Python function, never a subject
    assert report['removed'] == [{'name': 'proto::is_even', 'path': 'src/lib.rs', 'file': 'src/lib.rs',
                                  'change': 'removed', 'detection': 'rustdoc', 'language': 'rust',
                                  'reason': 'removed at head (no public function proto::is_even)'}]
    # the comparison is the leg's, in the behaviour summary, and the change failed the gate
    behaviour = report['behaviour']
    assert behaviour['languages'] == ['rust']
    assert behaviour['stages'] == {'rust': RUST_STAGE}
    assert behaviour['rust']['exit_code'] == 1 and 'flagged' in behaviour['rust']['control']
    assert behaviour['summary'] == {'changed': 2, 'unchanged-on-inputs': 1, 'not-compared': 3}
    assert report['gate']['status'] == 'evidence'
    assert (report['gate']['subjects'], report['gate']['compared']) == (6, 3)
    assert report['gate']['exit_code'] == 1
    (record,) = report['files']
    assert record['analysed'] == 'rust-file' and 'note' not in record
    assert pr_mode.validate_sarif(json.loads((out / 'pr.sarif').read_text())) == []
    sarif = (out / 'pr.sarif').read_text()
    assert 'proto::clamp(7u32, 0u32, 5u32): base model ok 5, base runtime ok 5, head runtime ok 7' in sarif
    markdown = (out / 'pr.md').read_text()
    assert 'Languages compared: rust' in markdown
    assert '`proto::next(0u32)`: base model none (no model: native-only); base runtime ok 1; ' \
           'head runtime ok 2' in markdown
    assert 'Removed at head (nothing to verify): `proto::is_even`' in markdown
    # without --fail-on a behaviour change is reported, not failed (pr's rule for every language)
    assert pr_mode.main([str(repo), '--base', 'base', '--head', 'head',
                         '--module', 'PullRequestRust', '--out', str(out)]) == 0
    assert json.loads((out / 'pr.json').read_text())['behaviour']['summary']['changed'] == 2


@needs_git
def test_a_mixed_python_and_rust_change_merges_both_summaries(tmp_path, monkeypatch):
    """A change touching a Python function and the crate: the behaviour stage compares the
    Python function, the Rust leg the crate's, and the two summaries merge -- both
    languages listed, the leg's stage and detail under `rust`, each record keeping its
    own leg's verdict, and the Rust functions never enter the chain's selection."""
    monkeypatch.setattr(rust_aeneas, 'missing', lambda env=None: [])
    monkeypatch.setattr(rust_regress, 'main', _fake_rust_regress({}, _fake_rust_report()))

    def write(tree, tag):
        _rust_crate(tree, tag)
        (tree / 'numbers.py').write_text('def q(a, b):\n    return a // b\n' if tag == 'base'
                                         else 'def q(a, b):\n    return a // b + 1\n')

    repo = two_commit_history(tmp_path / 'repo', write)
    changed = {'status': 'changed', 'compared': 2, 'agree': 1, 'inconclusive': 0,
               'suppressed_as_model_noise': 0, 'diverging': 1, 'counter_inputs': [
                   {'call': 'q(4, 2)', 'receiver': None, 'base_model': '2', 'head_runtime': '3',
                    'detail': None, 'origin': 'tests'}],
               'reason': '1 input(s) where the base model and the head runtime disagree'}
    handed = {}

    def fake_behaviour(repo, base, source, subdir, functions, *rest, **kw):
        handed['names'] = [f['name'] for f in functions]
        return ({f['name']: changed for f in functions}, {'behaviour': {'status': 'passed'}},
                {'suppressed_as_model_noise': 0, 'languages': ['python']})

    monkeypatch.setattr(pr_mode, 'run_behaviour', fake_behaviour)
    (tmp_path / 'ast.json').write_text(json.dumps([]))   # the exporter named no function here
    out = tmp_path / 'out'
    assert pr_mode.main([str(repo), '--base', 'base', '--head', 'head',
                         '--module', 'PullRequestMixed', '--out', str(out),
                         '--ast', str(tmp_path / 'ast.json'), '--sarif', str(out / 'pr.sarif'),
                         '--markdown', str(out / 'pr.md'), '--fail-on', 'behaviour-changed']) == 1
    assert handed['names'] == ['numbers.py:<module>.q']   # the Python leg never sees Rust
    report = json.loads((out / 'pr.json').read_text())
    by_name = {f['name']: f for f in report['functions']}
    assert set(by_name) == {'numbers.py:<module>.q', 'proto::clamp', 'proto::gcd', 'proto::next',
                            'proto::halve', 'proto::add_wrapping', 'proto::is_odd'}
    assert by_name['numbers.py:<module>.q']['behaviour'] == changed
    assert by_name['proto::clamp']['behaviour']['status'] == 'changed'
    assert by_name['proto::gcd']['behaviour']['status'] == 'unchanged-on-inputs'
    assert by_name['proto::is_odd']['behaviour']['status'] == 'not-compared'
    behaviour = report['behaviour']
    assert behaviour['languages'] == ['python', 'rust']
    assert behaviour['stages'] == {'behaviour': {'status': 'passed'}, 'rust': RUST_STAGE}
    assert set(behaviour['rust']) == {'control', 'model', 'runtime', 'inputs', 'exit_code'}
    assert behaviour['summary'] == {'changed': 3, 'unchanged-on-inputs': 1, 'not-compared': 3}
    assert (report['gate']['subjects'], report['gate']['compared']) == (7, 4)
    assert report['gate']['exit_code'] == 1
    assert report['exporter']['status'] == 'available' and report['exporter']['source'] == 'supplied'
    assert report['stages']['render'] == {'status': 'skipped',
                                          'reason': "no changed function is in the exporter's output"}
    assert report['selection']['missing'] == ['numbers.py:<module>.q']
    assert [f['name'] for f in report['removed']] == ['proto::is_even']
    assert pr_mode.validate_sarif(json.loads((out / 'pr.sarif').read_text())) == []
    assert 'Languages compared: python, rust' in (out / 'pr.md').read_text()


@needs_git
def test_missing_rust_prerequisites_leave_the_change_not_compared_and_exit_2(
        tmp_path, monkeypatch, capsys):
    """The Rust leg's tools missing: the leg is never called, the files are `not compared`
    with every missing prerequisite named, no function is reported, and with nothing else
    analysed the run exits 2 (a CI gate must not pass on a comparison that could not run),
    the way a failed export does."""
    monkeypatch.setattr(rust_aeneas, 'missing', lambda env=None: ['charon', 'aeneas'])
    called = []
    monkeypatch.setattr(rust_regress, 'main', lambda argv=None: called.append(argv) or 0)
    repo = _rust_pr_history(tmp_path / 'repo')
    out = tmp_path / 'out'
    assert pr_mode.main([str(repo), '--base', 'base', '--head', 'head',
                         '--module', 'PullRequestRustNone', '--out', str(out),
                         '--markdown', str(out / 'pr.md')]) == 2
    assert called == []
    report = json.loads((out / 'pr.json').read_text())
    assert report['functions'] == [] and 'gate' not in report
    rust = report['behaviour']['rust']
    assert rust['status'] == 'not-compared'
    assert rust['reason'] == 'Rust prerequisites missing: charon, aeneas (see docs/rust.md)'
    assert report['behaviour']['stages'] == {'rust': {'status': 'skipped', 'reason': rust['reason']}}
    assert report['behaviour']['languages'] == []
    assert report['behaviour']['summary'] == {'changed': 0, 'unchanged-on-inputs': 0,
                                             'not-compared': 0}
    (record,) = report['files']
    assert record['analysed'] == 'rust-file' and record['note'] == 'not compared: ' + rust['reason']
    assert 'Rust prerequisites missing: charon, aeneas' in (out / 'pr.md').read_text()
    assert 'could not analyse the change' in capsys.readouterr().out
    # with --fail-on the run still could not run: 2, not the gate's 3 and never 0
    assert pr_mode.main([str(repo), '--base', 'base', '--head', 'head',
                         '--module', 'PullRequestRustNone', '--out', str(out),
                         '--fail-on', 'behaviour-changed']) == 2


@needs_git
def test_a_refused_rust_leg_is_not_compared_with_its_named_reason(tmp_path, monkeypatch):
    """rust_regress refused (exit 2, its RustPathError record written): pr mode reports
    the refusal's name, message and hint, fabricates no verdict, and exits 2."""
    monkeypatch.setattr(rust_aeneas, 'missing', lambda env=None: [])
    error = {'error': 'base-model-failed',
             'message': 'the Rust path did not complete on the base revision: lean-build-failed: x',
             'hint': 'set AUTOFORM_RUST_LEAN_PROJECT'}
    monkeypatch.setattr(rust_regress, 'main', _fake_rust_regress({}, error=error))
    repo = _rust_pr_history(tmp_path / 'repo')
    out = tmp_path / 'out'
    assert pr_mode.main([str(repo), '--base', 'base', '--head', 'head',
                         '--module', 'PullRequestRustRefused', '--out', str(out)]) == 2
    report = json.loads((out / 'pr.json').read_text())
    assert report['functions'] == [] and report['removed'] == []
    stage = report['behaviour']['stages']['rust']
    assert stage['status'] == 'failed'
    assert stage['reason'] == ('the Rust leg did not run: base-model-failed: the Rust path did not '
                               'complete on the base revision: lean-build-failed: x '
                               '(set AUTOFORM_RUST_LEAN_PROJECT)')
    assert report['files'][0]['note'] == 'not compared: ' + stage['reason']


@needs_git
def test_rust_files_outside_a_cargo_library_stay_not_compared(tmp_path, monkeypatch):
    """A `.rs` change where the base has no Cargo library (no Cargo.toml; or a workspace
    root with no [package]): the leg is never called, the file says why, and nothing to
    analyse exits 0."""
    called = []
    monkeypatch.setattr(rust_regress, 'main', lambda argv=None: called.append(argv) or 0)

    def write(tree, tag):
        (tree / 'src').mkdir(parents=True, exist_ok=True)
        (tree / 'src' / 'lib.rs').write_text('pub fn f() {}\n' if tag == 'base'
                                              else 'pub fn f() -> u8 { 1 }\n')

    def workspace(tree, tag):
        write(tree, tag)
        (tree / 'Cargo.toml').write_text('[workspace]\nmembers = ["a"]\n')

    for name, layout in (('none', write), ('workspace', workspace)):
        repo = two_commit_history(tmp_path / name, layout)
        out = tmp_path / ('out-' + name)
        assert pr_mode.main([str(repo), '--base', 'base', '--head', 'head',
                             '--module', 'PullRequestRustNoCrate', '--out', str(out)]) == 0
        report = json.loads((out / 'pr.json').read_text())
        assert report['functions'] == [] and 'behaviour' not in report
        assert report['exporter'] == {'status': 'not-run',
                                      'reason': 'the changed Rust file(s) are outside a Cargo '
                                                'library at base, and the Rust leg runs only on '
                                                'a crate'}
        (record,) = [r for r in report['files'] if r['path'] == 'src/lib.rs']
        assert record['analysed'] == 'rust-file'
        assert record['note'] == ('not compared: no Cargo library at base (a Cargo.toml with '
                                  '[package], and src/lib.rs or [lib]): the Rust leg runs only '
                                  'on a Cargo library')
    assert called == []


@needs_git
def test_no_behaviour_leaves_the_rust_files_not_compared(tmp_path, monkeypatch):
    """--no-behaviour skips the Rust leg (it is part of the behaviour comparison): the
    files are left `not compared` with that said, and nothing is analysed."""
    called = []
    monkeypatch.setattr(rust_regress, 'main', lambda argv=None: called.append(argv) or 0)
    repo = _rust_pr_history(tmp_path / 'repo')
    out = tmp_path / 'out'
    assert pr_mode.main([str(repo), '--base', 'base', '--head', 'head',
                         '--module', 'PullRequestRustOff', '--out', str(out),
                         '--no-behaviour']) == 0
    assert called == []
    report = json.loads((out / 'pr.json').read_text())
    assert report['functions'] == [] and 'behaviour' not in report
    assert report['exporter'] == {'status': 'not-run',
                                  'reason': '--no-behaviour: the Rust leg, the only '
                                            'comparison these file(s) have, did not run'}
    (record,) = report['files']
    assert record['note'] == ('not compared: --no-behaviour: the Rust leg is part of the '
                              'behaviour comparison')


# ------------------------------------------- change identity (non-Python files)

JF = 'src/p/A.java'
KF = 'kotlin/p/B.kt'


def jvm(name, body=None, file=JF, **extra):
    """A function record shaped like the exporter's JVM output (no position fields)."""
    method = name.split(':', 1)[0].rsplit('.', 1)[-1]
    return dict({'name': name, 'file': file, 'sourceName': method, 'paramTypes': [], 'returnType': 'int',
                 'params': [], 'body': body if body is not None else {'k': 'ret', 'e': {'k': 'int', 'v': 1}}},
                **extra)


def ret(value):
    return {'k': 'ret', 'e': {'k': 'int', 'v': value}}


def fnref(name):
    return {'k': 'ret', 'e': {'k': 'call', 'f': 'map', 'args': [{'k': 'fnref', 'v': name}]}}


def candidates(head, files):
    """What `run` builds for a changed file before the base is consulted: everything."""
    return [{'name': f['name'], 'path': files[f['file']], 'file': f['file'], 'change': 'modified',
             'line': None, 'end_line': None, 'detection': 'changed-file',
             'language': pr_mode.source_language(f['file'])} for f in head if f['file'] in files]


def file_records(files):
    return [{'path': path, 'status': 'M', 'file': rel, 'language': 'other', 'analysed': 'changed-file'}
            for rel, path in files.items()]


def classify(head, base, files=None, extra=()):
    files = files or {JF: JF, KF: 'src/main/' + KF}
    records = file_records(files)
    out = pr_mode.classify_against_base(list(extra) + candidates(head, files), records, head, base)
    return out, {f['name']: f for f in out['changed']}, records


def test_identical_functions_are_dropped_and_only_real_edits_stay():
    base = [jvm('p.A.same:int()', ret(1)), jvm('p.A.edited:int()', ret(1)), jvm('p.A.gone:int()'),
            jvm('p.A.deep:int()', {'k': 'seq', 'a': {'k': 'skip'}, 'b': ret(2)})]
    head = [jvm('p.A.same:int()', ret(1)), jvm('p.A.edited:int()', ret(2)), jvm('p.A.fresh:int()'),
            jvm('p.A.deep:int()', {'k': 'seq', 'a': {'k': 'skip'}, 'b': ret(2)})]
    out, by_name, _ = classify(head, base)
    assert set(by_name) == {'p.A.edited:int()', 'p.A.fresh:int()'}
    assert by_name['p.A.edited:int()']['change'] == 'modified'
    # Absent at base is `added`, not "the exporter did not export it from the base tree".
    assert by_name['p.A.fresh:int()']['change'] == 'added'
    assert out['unchanged'] == ['p.A.deep:int()', 'p.A.same:int()']
    assert [(r['name'], r['change'], r['path']) for r in out['removed']] == [('p.A.gone:int()', 'removed', JF)]
    # The exporter's AST has no positions for exported functions: no line is invented.
    assert all(f['line'] is None for f in out['changed'])
    assert out['counts'] == {'unchanged': 2, 'modified': 1, 'added': 1, 'signature_changed': 0,
                             'removed': 1, 'identical_but_holed': 0, 'renumbered_lambdas': 0}


def test_a_signature_or_arity_change_keeps_its_base_version():
    base = [jvm('p.A.f:int(int)', ret(1)), jvm('p.B.g:<unresolvedSignature>(2)', ret(1), file=KF)]
    head = [jvm('p.A.f:int(int,int)', ret(1)), jvm('p.B.g:<unresolvedSignature>(3)', ret(2), file=KF)]
    out, by_name, _ = classify(head, base)
    java, kotlin = by_name['p.A.f:int(int,int)'], by_name['p.B.g:<unresolvedSignature>(3)']
    assert java['change'] == kotlin['change'] == 'modified'
    assert java['signature_change'] == {'base': 'p.A.f:int(int)'} and java['base_name'] == 'p.A.f:int(int)'
    assert java['change_detail'] == 'signature changed (base: p.A.f:int(int))'
    assert kotlin['signature_change'] == {'base': 'p.B.g:<unresolvedSignature>(2)'}
    assert out['removed'] == [] and out['counts']['signature_changed'] == 2


def test_an_ambiguous_overload_change_is_not_paired_by_guess():
    base = [jvm('p.A.f:int(int)'), jvm('p.A.f:int(long)')]
    head = [jvm('p.A.f:int(int,int)')]
    out, by_name, _ = classify(head, base)
    assert by_name['p.A.f:int(int,int)']['change'] == 'added'
    assert 'signature_change' not in by_name['p.A.f:int(int,int)']
    assert [r['name'] for r in out['removed']] == ['p.A.f:int(int)', 'p.A.f:int(long)']


def test_lambdas_are_matched_by_body_not_by_index():
    owner = 'p.B.get'
    lam = lambda n, body, sig='java.lang.String()': jvm(f'{owner}.<lambda>{n}:{sig}', body, file=KF,
                                                         sourceName=f'<lambda>{n}')
    base = [jvm(owner + ':<unresolvedSignature>(1)', fnref(owner + '.<lambda>3:java.lang.String()'), file=KF),
            lam(3, ret(3)), lam(4, ret(4)), lam(6, ret(6), 'int()')]
    # Head inserts a new lambda first: every index shifts by two, nothing else changes,
    # except `<lambda>6` -> `<lambda>8`, which is also edited.
    head = [jvm(owner + ':<unresolvedSignature>(1)', fnref(owner + '.<lambda>5:java.lang.String()'), file=KF),
            lam(3, ret(99), 'boolean()'), lam(5, ret(3)), lam(6, ret(4)), lam(8, ret(7), 'int()')]
    out, by_name, _ = classify(head, base)
    assert out['renumbered'] == {owner + '.<lambda>5:java.lang.String()': owner + '.<lambda>3:java.lang.String()',
                                 owner + '.<lambda>6:java.lang.String()': owner + '.<lambda>4:java.lang.String()',
                                 owner + '.<lambda>8:int()': owner + '.<lambda>6:int()'}
    # The enclosing method only refers to a renumbered lambda: read under the base's
    # name, its body is the base's, so it is unchanged -- but it encloses the edited
    # Kotlin lambda `<lambda>8`, which no name calls, so it is compared for it.
    assert owner + ':<unresolvedSignature>(1)' not in out['unchanged']
    assert set(by_name) == {owner + '.<lambda>3:boolean()', owner + '.<lambda>8:int()',
                            owner + ':<unresolvedSignature>(1)'}
    assert by_name[owner + ':<unresolvedSignature>(1)']['encloses_changed_lambdas'] == [owner + '.<lambda>8:int()']
    assert by_name[owner + '.<lambda>3:boolean()']['change'] == 'added'
    edited = by_name[owner + '.<lambda>8:int()']
    assert edited['change'] == 'modified' and edited['base_name'] == owner + '.<lambda>6:int()'
    assert 'lambda renumbered and edited' in edited['change_detail']
    assert out['removed'] == []


def test_an_edited_kotlin_lambda_is_compared_through_its_enclosing_function():
    """The JVM oracle cannot call a lambda ("lambda: not callable by name"): the named
    function around an edited Kotlin lambda is selected for it, even though its own
    record is identical at both revisions. A Java lambda, an unchanged lambda, and an
    enclosing function that changed itself are left as they were."""
    owner = 'p.B.find'
    lam = lambda body, file=KF: jvm(owner + '.<lambda>0:boolean()', body, file=file, sourceName='<lambda>0')
    outer = lambda file=KF: jvm(owner + ':int(java.lang.String)', fnref(owner + '.<lambda>0:boolean()'), file=file)
    out, by_name, _ = classify([outer(), lam(ret(2))], [outer(), lam(ret(1))])
    assert set(by_name) == {owner + '.<lambda>0:boolean()', owner + ':int(java.lang.String)'}
    pulled = by_name[owner + ':int(java.lang.String)']
    assert pulled['change'] == 'modified' and pulled['encloses_changed_lambdas'] == [owner + '.<lambda>0:boolean()']
    assert 'not callable by name' in pulled['change_detail']
    assert out['unchanged'] == [] and out['counts']['unchanged'] == 0 and out['counts']['modified'] == 2
    # Unedited lambda: nothing is pulled back.
    out, by_name, _ = classify([outer(), lam(ret(1))], [outer(), lam(ret(1))])
    assert by_name == {} and out['counts']['unchanged'] == 2
    # Java: lambdas are not selected through their owner.
    out, by_name, _ = classify([outer(JF), lam(ret(2), JF)], [outer(JF), lam(ret(1), JF)])
    assert set(by_name) == {owner + '.<lambda>0:boolean()'}


def test_js_lambdas_are_matched_by_body_and_unedited_functions_dropped():
    """The JS/TS exporter names a lambda `<file>::program:<owner>:<lambda>N`; it is
    identified by body as the JVM's `.<lambda>N` is, so a renumbering is no change."""
    tf, owner = 'lib/a.ts', 'lib/a.ts::program:build'
    ts = lambda name, body: jvm(name, body, file=tf, sourceName=name.rsplit(':', 1)[-1])
    base = [ts('lib/a.ts::program', ret(0)), ts(owner, fnref(owner + ':<lambda>0')),
            ts(owner + ':<lambda>0', ret(3)), ts('lib/a.ts::program:same', ret(5)),
            ts('lib/a.ts::program:edited', ret(6))]
    head = [ts('lib/a.ts::program', ret(0)), ts(owner, fnref(owner + ':<lambda>1')),
            ts(owner + ':<lambda>0', ret(99)), ts(owner + ':<lambda>1', ret(3)),
            ts('lib/a.ts::program:same', ret(5)), ts('lib/a.ts::program:edited', ret(7))]
    out, by_name, _ = classify(head, base, {tf: tf})
    assert out['renumbered'] == {owner + ':<lambda>1': owner + ':<lambda>0'}
    assert set(out['unchanged']) == {'lib/a.ts::program', owner, owner + ':<lambda>1', 'lib/a.ts::program:same'}
    assert set(by_name) == {owner + ':<lambda>0', 'lib/a.ts::program:edited'}
    assert by_name[owner + ':<lambda>0']['change'] == 'added'
    assert by_name['lib/a.ts::program:edited']['change'] == 'modified'
    assert by_name['lib/a.ts::program:edited']['language'] == 'ts'


def test_a_function_identical_only_up_to_its_holes_is_not_dropped():
    """Measured on a TypeScript package: `{...A, ...B}` -> `{...B, ...A}` and an edited
    template literal export the same record at both revisions (`op:spread`,
    `op:formatString` holes keep no source). Identical is no evidence there."""
    tf = 'lib/a.ts'
    ts = lambda name, body: jvm(name, body, file=tf, sourceName=name.rsplit(':', 1)[-1])
    hole = {'k': 'ret', 'e': {'k': 'hole', 'label': 'op:formatString'}}
    base = [ts(tf + '::program:stepName', hole), ts(tf + '::program:plain', ret(1))]
    head = [ts(tf + '::program:stepName', hole), ts(tf + '::program:plain', ret(1))]
    out, by_name, records = classify(head, base, {tf: tf})
    assert out['unchanged'] == [tf + '::program:plain']
    kept = by_name[tf + '::program:stepName']
    assert kept['change'] == 'modified' and 'op:formatString' in kept['change_detail']
    assert 'not provably unchanged' in kept['change_detail'] and 'base_name' not in kept
    assert out['counts']['identical_but_holed'] == 1 and out['counts']['unchanged'] == 1
    assert 'note' not in records[0]


def test_identity_leaves_python_candidates_alone_and_notes_a_file_with_no_edit():
    python = changed('m.py:<module>.f')
    head, base = [jvm('p.A.same:int()')], [jvm('p.A.same:int()')]
    out, by_name, records = classify(head, base, {JF: JF}, extra=[python])
    assert out['changed'] == [python]
    assert records[0]['note'].startswith('every exported function is identical to the base export')


def test_a_module_entry_is_never_a_candidate_or_a_removal():
    base = [jvm('p.A.f:int()'), {'name': JF + ':<module>', 'file': JF, 'params': [], 'body': ret(0)}]
    out, _, _ = classify([jvm('p.A.f:int()')], base)
    assert out['changed'] == [] and out['removed'] == []


def test_a_deep_body_is_fingerprinted_without_recursion():
    body = ret(0)
    for _ in range(50_000):
        body = {'k': 'seq', 'a': {'k': 'skip'}, 'b': body}
    record = jvm('p.A.deep:int()', body)
    assert pr_mode._fingerprint(record) == pr_mode._fingerprint(dict(record, name='other'))
    assert pr_mode._fingerprint(jvm('p.A.x:int()', {'k': 'x', 'v': [1, 2]})) != \
        pr_mode._fingerprint(jvm('p.A.x:int()', {'k': 'x', 'v': [12]}))


def java_history(tmp_path):
    repo = tmp_path / 'repo'
    (repo / 'src/p').mkdir(parents=True)
    pr_fixture.git(repo.parent, 'init', '-q', str(repo))
    commits = {}
    for tag, text in (('base', 'class A { int f(int x) { return x; } }\n'),
                      ('head', 'class A { int f(int x, int y) { return x; } int g() { return 1; } }\n')):
        (repo / JF).write_text(text)
        pr_fixture.git(repo, 'add', '-A')
        pr_fixture.git(repo, 'commit', '-q', '-m', tag)
        commits[tag] = pr_fixture.git(repo, 'rev-parse', 'HEAD')
    return repo, commits


@needs_git
def test_change_identity_uses_the_base_export_even_when_no_runtime_can_compare(tmp_path, monkeypatch):
    """A TypeScript change on a machine without Node: nothing can be compared, but the
    base tree is still exported, so an unedited function of the touched file is dropped
    rather than reported (it was: every function of the file, `change_identity` absent)."""
    tf = 'lib/a.ts'
    repo = tmp_path / 'repo'
    (repo / 'lib').mkdir(parents=True)
    pr_fixture.git(repo.parent, 'init', '-q', str(repo))
    commits = {}
    for tag, text in (('base', 'function f() { return 1; }\nfunction g() { return 5; }\n'),
                      ('head', 'function f() { return 2; }\nfunction g() { return 5; }\n')):
        (repo / tf).write_text(text)
        pr_fixture.git(repo, 'add', '-A')
        pr_fixture.git(repo, 'commit', '-q', '-m', tag)
        commits[tag] = pr_fixture.git(repo, 'rev-parse', 'HEAD')
    ts = lambda name, body: jvm(name, body, file=tf, sourceName=name.rsplit(':', 1)[-1])
    head = [ts(tf + '::program:f', ret(2)), ts(tf + '::program:g', ret(5))]
    base = [ts(tf + '::program:f', ret(1)), ts(tf + '::program:g', ret(5))]
    (tmp_path / 'ast.json').write_text(json.dumps(head))
    exported = []
    monkeypatch.setattr(pr_mode, 'export_ast', lambda source, out, log_dir, timeout: (
        exported.append(Path(source)), Path(out).write_text(json.dumps(base)), {})[-1])
    monkeypatch.setattr(pr_mode._backends().shutil, 'which', lambda tool, **kw: None)
    monkeypatch.setattr(pr_mode.Chain, 'render', lambda self, path: False)
    out = tmp_path / 'out'
    assert pr_mode.main([str(repo), '--base', commits['base'], '--head', commits['head'], '--module',
                         'PullRequestTsIdentity', '--ast', str(tmp_path / 'ast.json'), '--out', str(out)]) == 0
    assert len(exported) == 1   # the base tree, for change identity
    report = json.loads((out / 'pr.json').read_text())
    assert report['change_identity']['status'] == 'base-export'
    assert report['change_identity']['unchanged'] == [tf + '::program:g']
    (function,) = report['functions']
    assert function['name'] == tf + '::program:f' and function['language'] == 'ts'
    assert function['behaviour']['status'] == 'not-compared'
    assert 'node not on PATH' in function['behaviour']['reason']
    stages = report['behaviour']['stages']
    assert 'change identity only' in stages['behaviour-export']['note']
    assert stages['behaviour']['status'] == 'skipped'


@needs_git
def test_run_refines_changed_file_detection_with_the_behaviour_base_export(tmp_path, monkeypatch):
    repo, commits = java_history(tmp_path)
    head = [jvm('p.A.f:int(int,int)'), jvm('p.A.g:int()', ret(2)), jvm('p.A.same:int()')]
    base = [jvm('p.A.f:int(int)'), jvm('p.A.same:int()'), jvm('p.A.old:int()')]
    (tmp_path / 'ast.json').write_text(json.dumps(head))
    seen = {}

    def fake_behaviour(repo_, base_, source, subdir, functions, *rest, **kw):
        refine = rest[-1]
        kept = refine(base)
        seen['before'] = sorted(f['name'] for f in functions)
        seen['after'] = sorted(f['name'] for f in kept)
        return {}, {'behaviour': {'status': 'passed'}}, {'suppressed_as_model_noise': 0, 'languages': []}

    monkeypatch.setattr(pr_mode, 'run_behaviour', fake_behaviour)
    rendered = []
    monkeypatch.setattr(pr_mode.Chain, 'render', lambda self, path: rendered.append(
        sorted(f['name'] for f in json.loads(Path(path).read_text()))) or False)
    argv = [str(repo), '--base', commits['base'], '--head', commits['head'], '--module', 'PullRequestIdentity',
            '--ast', str(tmp_path / 'ast.json')]
    out = tmp_path / 'out'
    assert pr_mode.main(argv + ['--out', str(out), '--markdown', str(out / 'pr.md')]) == 0
    assert seen['before'] == ['p.A.f:int(int,int)', 'p.A.g:int()', 'p.A.same:int()']
    assert seen['after'] == ['p.A.f:int(int,int)', 'p.A.g:int()']
    report = json.loads((out / 'pr.json').read_text())
    by_name = {f['name']: f for f in report['functions']}
    assert set(by_name) == {'p.A.f:int(int,int)', 'p.A.g:int()'}
    assert by_name['p.A.g:int()']['change'] == 'added'
    assert by_name['p.A.f:int(int,int)']['signature_change'] == {'base': 'p.A.f:int(int)'}
    assert [r['name'] for r in report['removed']] == ['p.A.old:int()']
    assert report['selection']['changed'] == ['p.A.f:int(int,int)', 'p.A.g:int()']
    # The head chain ran on the refined set: the unchanged function was not rendered.
    assert rendered == [['p.A.f:int(int,int)', 'p.A.g:int()']]
    assert report['change_identity']['status'] == 'base-export'
    assert report['change_identity']['unchanged'] == ['p.A.same:int()']
    text = (out / 'pr.md').read_text()
    assert 'modified (signature changed (base: p.A.f:int(int)))' in text and '`p.A.old:int()`' in text

    # Without the behaviour stage there is no base export: the whole file stands, and says why.
    assert pr_mode.main(argv + ['--out', str(tmp_path / 'plain'), '--no-behaviour']) == 0
    report = json.loads((tmp_path / 'plain/pr.json').read_text())
    assert {f['name']: f['change'] for f in report['functions']} == {
        'p.A.f:int(int,int)': 'modified', 'p.A.g:int()': 'modified', 'p.A.same:int()': 'modified'}
    assert report['change_identity']['status'] == 'unavailable'
    assert '--no-behaviour' in report['change_identity']['reason'] and 'not refined' in report['detection']


# ------------------------------------------------------------------- the CLI

@pytest.fixture
def cli(monkeypatch):
    monkeypatch.syspath_prepend(str(ROOT / 'src'))
    import autoform.cli as module
    calls = []
    monkeypatch.setattr(module, '_run_command', lambda command, **kw: calls.append((command, kw)) or 0)
    module._calls = calls
    return module


@needs_git
def test_cli_pr_hands_the_bundled_script_every_flag(tmp_path, cli):
    history = pr_fixture.make_history(tmp_path / 'repo')
    workspace = tmp_path / 'ws'
    code = cli.main(['--workspace', str(workspace), 'pr', history['repo'], '--base', 'base',
                     '--head', 'head', '--sarif', 'out/pr.sarif', '--markdown', 'out/pr.md',
                     '--mutants', '3', '--timeout', '60'])
    assert code == 0
    (command, kwargs), = cli._calls
    assert command[1] == str(workspace / 'scripts/pr_mode.py')
    assert command[2] == history['repo']
    assert command[command.index('--module') + 1] == 'PullRequest'
    assert command[command.index('--out') + 1] == str(workspace / 'artifacts/pr/PullRequest')
    assert command[command.index('--base') + 1] == 'base'
    assert command[command.index('--head') + 1] == 'head'
    assert command[command.index('--mutants') + 1] == '3'
    assert command[command.index('--sarif') + 1] == str(Path('out/pr.sarif').resolve())
    assert kwargs['timeout'] == 60


@needs_git
def test_cli_pr_passes_every_fail_on_condition_and_the_scripts_exit_code(tmp_path, cli, monkeypatch):
    history = pr_fixture.make_history(tmp_path / 'repo')
    monkeypatch.setattr(cli, '_run_command', lambda command, **kw: cli._calls.append((command, kw)) or 3)
    code = cli.main(['--workspace', str(tmp_path / 'ws'), 'pr', history['repo'], '--base', 'base',
                     '--fail-on', 'behaviour-changed', '--fail-on', 'no-evidence'])
    assert code == 3
    (command, _), = cli._calls
    assert [command[i + 1] for i, c in enumerate(command) if c == '--fail-on'] == ['behaviour-changed',
                                                                                 'no-evidence']


def test_cli_pr_refuses_a_plain_directory(tmp_path, cli, capsys):
    (tmp_path / 'plain').mkdir()
    code = cli.main(['--workspace', str(tmp_path / 'ws'), 'pr', str(tmp_path / 'plain'), '--base', 'x'])
    assert code == 2
    assert 'Git' in capsys.readouterr().err


def test_cli_pr_rejects_impossible_counts(tmp_path, cli):
    with pytest.raises(SystemExit):
        cli.main(['--workspace', str(tmp_path / 'ws'), 'pr', '.', '--base', 'x', '--cases', '0'])


# ------------------------------------------------------------ the real chain

@pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_JOERN') != '1',
                    reason='set AUTOFORM_TEST_JOERN=1 to run the real chain on the fixture history')
def test_the_real_chain_proves_the_changed_functions_it_can(tmp_path):
    history = pr_fixture.make_history(tmp_path / 'repo')
    out = tmp_path / 'out'
    env = dict(os.environ, PATH=str(Path.home() / '.elan/bin') + os.pathsep + os.environ['PATH'])
    result = run_script([history['repo'], '--base', 'base', '--head', 'head', '--module', 'PullRequestTest',
                         '--out', out, '--sarif', out / 'pr.sarif', '--markdown', out / 'pr.md', '--mutants', '2'],
                        env)
    assert result.returncode == 0, result.stdout + result.stderr
    report = json.loads((out / 'pr.json').read_text())
    by_name = {f['name'].rsplit('.', 1)[-1]: f for f in report['functions']}
    assert by_name['quotient']['level'] == 'proved' and by_name['clamp']['level'] == 'proved'
    assert by_name['raw']['level'] == 'hole' and by_name['raw']['holes'] == ['lit:bytes']
    assert by_name['first']['level'] == 'translated'
    # The gate's verdict is whatever mutation.json says; what is pinned is that it is
    # attached to the theorem about this function and that the stage ran to a verdict.
    assert list(by_name['quotient']['mutation']['verdicts']) == ['conform_numbers_py__module__quotient']
    assert 'mutant(s) run' in report['stages']['mutation']['note']
    assert all(s['status'] == 'passed' for s in report['stages'].values()), report['stages']
    assert pr_mode.validate_sarif(json.loads((out / 'pr.sarif').read_text())) == []


@pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_JOERN') != '1',
                    reason='set AUTOFORM_TEST_JOERN=1 to run the real cross-revision chain')
@needs_git
def test_the_real_chain_flags_a_behaviour_change_and_not_an_unchanged_function(tmp_path):
    repo = tmp_path / 'repo'
    (repo / 'tests').mkdir(parents=True)
    git = lambda *a: subprocess.run(['git', '-c', 'user.name=t', '-c', 'user.email=t@t', *a], cwd=repo,
                                    check=True, capture_output=True)
    git('init', '-q')
    lib = ('def clamp(x):\n    if x > {top}:\n        return {top}\n    return x\n\n'
           'def same(x):\n    return {one}\n')
    (repo / 'tests/test_lib.py').write_text(
        'import sys, os\nsys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))\n'
        'import lib\n\ndef test_all():\n    for n in (-1, 0, 5, 9, 10, 11, 20):\n'
        '        lib.clamp(n)\n        lib.same(n)\n\nif __name__ == "__main__":\n    test_all()\n')
    (repo / 'lib.py').write_text(lib.format(top=10, one='x + 1'))
    git('add', '-A'); git('commit', '-qm', 'base'); git('tag', 'base')
    (repo / 'lib.py').write_text(lib.format(top=9, one='1 + x'))
    git('add', '-A'); git('commit', '-qm', 'head'); git('tag', 'head')
    out = tmp_path / 'out'
    env = dict(os.environ, PATH=str(Path.home() / '.elan/bin') + os.pathsep + os.environ['PATH'])
    result = run_script([repo, '--base', 'base', '--head', 'head', '--module', 'PullRequestTestBehaviour',
                         '--out', out, '--sarif', out / 'pr.sarif', '--markdown', out / 'pr.md'], env)
    assert result.returncode == 0, result.stdout + result.stderr   # a behaviour change is not a failure
    report = json.loads((out / 'pr.json').read_text())
    by_name = {f['name'].rsplit('.', 1)[-1]: f['behaviour'] for f in report['functions']}
    assert by_name['clamp']['status'] == 'changed'
    item = by_name['clamp']['counter_inputs'][0]
    assert item['call'].startswith('clamp(') and 'returns' in item['base_model'] and 'returns' in item['head_runtime']
    assert item['base_model'] != item['head_runtime']
    assert by_name['same']['status'] == 'unchanged-on-inputs' and by_name['same']['compared'] >= 1
    sarif = json.loads((out / 'pr.sarif').read_text())
    assert pr_mode.validate_sarif(sarif) == []
    assert [r['properties']['function'].rsplit('.', 1)[-1] for r in sarif['runs'][0]['results']
            if r['ruleId'] == 'autoform/behaviour-changed'] == ['clamp']
    assert '### PR verdict' in (out / 'pr.md').read_text()


JAVA_CALC = '''package com.example.calc;

public class Calc {{
    private int base;

    public static int clamp(int x) {{
        if (x > {top}) {{
            return {top};
        }}
        return x;
    }}

    public static int twice(int x) {{
{twice}
    }}

    public int offset(int x) {{
        return x + base + {off};
    }}
}}
'''


@pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_JOERN') != '1',
                    reason='set AUTOFORM_TEST_JOERN=1 to run the real cross-revision chain')
@pytest.mark.skipif(shutil.which('javac') is None, reason='javac is required for the JVM oracle')
@needs_git
def test_the_real_chain_compares_java_behaviour_across_revisions(tmp_path):
    """A Gradle-style Java tree: `clamp` changes behaviour, `twice` is rewritten to the
    same sum (a different AST, so still a changed function: a formatting-only edit is
    dropped as identical to the base export), `offset` is an instance method: the JVM
    oracle runs it on a receiver from the class's no-arg constructor (Java receivers), so
    its `+ 1` is a behaviour change, observed with that receiver."""
    repo = tmp_path / 'repo'
    src = repo / 'src/main/java/com/example/calc'
    src.mkdir(parents=True)
    (repo / 'settings.gradle').write_text("rootProject.name = 'calc'\n")
    (repo / 'build.gradle').write_text("plugins { id 'java' }\n")
    git = lambda *a: subprocess.run(['git', '-c', 'user.name=t', '-c', 'user.email=t@t', *a], cwd=repo,
                                    check=True, capture_output=True)
    git('init', '-q')
    (src / 'Calc.java').write_text(JAVA_CALC.format(top=40, twice='        return x + x;', off=0))
    git('add', '-A'); git('commit', '-qm', 'base'); git('tag', 'base')
    (src / 'Calc.java').write_text(JAVA_CALC.format(
        top=30, twice='        return 2 * x;', off=1))
    git('add', '-A'); git('commit', '-qm', 'head'); git('tag', 'head')
    out = tmp_path / 'out'
    env = dict(os.environ, PATH=str(Path.home() / '.elan/bin') + os.pathsep + os.environ['PATH'])
    result = subprocess.run([sys.executable, str(ROOT / 'scripts/pr_mode.py'), str(repo), '--base', 'base',
                             '--head', 'head', '--module', 'PullRequestTestJavaBehaviour', '--out', str(out),
                             '--sarif', str(out / 'pr.sarif'), '--markdown', str(out / 'pr.md'),
                             '--mutants', '0', '--behaviour-cases', '16'],
                            env=env, text=True, capture_output=True, timeout=1800)
    assert result.returncode in (0, 1), result.stdout + result.stderr
    report = json.loads((out / 'pr.json').read_text())
    by_name = {f['name'].split(':')[0].rsplit('.', 1)[-1]: f['behaviour'] for f in report['functions']}
    assert by_name['clamp']['status'] == 'changed', by_name
    item = by_name['clamp']['counter_inputs'][0]
    assert item['call'].startswith('Calc.clamp(int ') and item['base_model'] != item['head_runtime']
    assert by_name['twice']['status'] == 'unchanged-on-inputs' and by_name['twice']['compared'] >= 1, by_name
    assert by_name['offset']['status'] == 'changed', by_name['offset']
    item = by_name['offset']['counter_inputs'][0]
    assert item['base_model'] != item['head_runtime'], item
    assert report['behaviour']['languages'] == ['java']
    assert pr_mode.validate_sarif(json.loads((out / 'pr.sarif').read_text())) == []
    assert 'Languages compared: java' in (out / 'pr.md').read_text()


C_LIB = '''#include <stdint.h>

int clamp(int x) {{
    if (x > {top})
        return {top};
    return x;
}}

int twice(int x) {{
{twice}
}}

int first(const int *p) {{
    return p[{index}];
}}
'''


@pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_JOERN') != '1',
                    reason='set AUTOFORM_TEST_JOERN=1 to run the real cross-revision chain')
@pytest.mark.skipif(shutil.which('cc') is None, reason='cc is required for the native C oracle')
@needs_git
def test_the_real_chain_compares_c_behaviour_across_revisions(tmp_path):
    """A C tree: `clamp` changes behaviour (exit 1 under --fail-on behaviour-changed);
    `twice` is rewritten from `x + x` to `2 * x`, which agree wherever both are defined:
    the inputs that overflow `int` are undefined behaviour, a hole in the model, so they
    are inconclusive and never a divergence; `first` takes a pointer, which the scalar
    native C oracle does not call."""
    repo = tmp_path / 'repo'
    repo.mkdir()
    git = lambda *a: subprocess.run(['git', '-c', 'user.name=t', '-c', 'user.email=t@t', *a], cwd=repo,
                                    check=True, capture_output=True)
    git('init', '-q')
    (repo / 'lib.c').write_text(C_LIB.format(top=40, twice='    return x + x;', index=0))
    git('add', '-A'); git('commit', '-qm', 'base'); git('tag', 'base')
    (repo / 'lib.c').write_text(C_LIB.format(top=30, twice='    return 2 * x;', index=1))
    git('add', '-A'); git('commit', '-qm', 'head'); git('tag', 'head')
    out = tmp_path / 'out'
    env = dict(os.environ, PATH=str(Path.home() / '.elan/bin') + os.pathsep + os.environ['PATH'])
    result = subprocess.run([sys.executable, str(ROOT / 'scripts/pr_mode.py'), str(repo), '--base', 'base',
                             '--head', 'head', '--module', 'PullRequestTestCBehaviour', '--out', str(out),
                             '--sarif', str(out / 'pr.sarif'), '--markdown', str(out / 'pr.md'),
                             '--mutants', '0', '--behaviour-cases', '24', '--fail-on', 'behaviour-changed'],
                            env=env, text=True, capture_output=True, timeout=1800)
    assert result.returncode == 1, result.stdout + result.stderr
    report = json.loads((out / 'pr.json').read_text())
    by_name = {f['name']: f['behaviour'] for f in report['functions']}
    assert by_name['clamp']['status'] == 'changed', by_name
    item = by_name['clamp']['counter_inputs'][0]
    assert item['call'].startswith('clamp(int ') and item['base_model'] != item['head_runtime']
    assert by_name['twice']['status'] == 'unchanged-on-inputs' and by_name['twice']['compared'] >= 1, by_name
    assert by_name['first']['status'] == 'not-compared', by_name['first']
    assert report['behaviour']['languages'] == ['c']
    assert report['behaviour']['inputs'] == pr_mode._backends().CROSS_REVISION_INPUTS['c']
    assert report['behaviour']['control'] == 'run'
    assert pr_mode.validate_sarif(json.loads((out / 'pr.sarif').read_text())) == []
    assert 'Languages compared: c' in (out / 'pr.md').read_text()



JS_LIB = '''const dep = require('fixture-dep');

function clamp(x) {{
  if (x > {top}) {{
    return {top};
  }}
  return x;
}}

function sign(x) {{
  if (x > 0) {{
    return "{pos}";
  }}
  return "neg";
}}

function versioned(name) {{
  return name + dep.suffix();
}}

function twice(x) {{
  const {local} = x + x;
  return {local};
}}

class Counter {{
  constructor() {{ this.n = 0; }}
  offset(x) {{
    return this.n + x + {off};
  }}
}}

module.exports = {{ clamp, sign, versioned, twice, Counter }};
'''


def two_commit_history(repo, write):
    """`write(repo, revision)` lays out each revision; tags `base` and `head`."""
    repo.mkdir(parents=True)
    git = lambda *a: subprocess.run(['git', '-c', 'user.name=t', '-c', 'user.email=t@t', *a], cwd=repo,
                                    check=True, capture_output=True)
    git('init', '-q')
    for tag in ('base', 'head'):
        write(repo, tag)
        git('add', '-A'); git('commit', '-qm', tag); git('tag', tag)
    return repo


def run_real_pr(repo, out, module):
    env = dict(os.environ, PATH=str(Path.home() / '.elan/bin') + os.pathsep + os.environ['PATH'])
    result = subprocess.run([sys.executable, str(ROOT / 'scripts/pr_mode.py'), str(repo), '--base', 'base',
                             '--head', 'head', '--module', module, '--out', str(out),
                             '--sarif', str(out / 'pr.sarif'), '--markdown', str(out / 'pr.md'),
                             '--mutants', '0', '--behaviour-cases', '16'],
                            env=env, text=True, capture_output=True, timeout=1800)
    assert result.returncode in (0, 1), result.stdout + result.stderr
    report = json.loads((out / 'pr.json').read_text())
    assert pr_mode.validate_sarif(json.loads((out / 'pr.sarif').read_text())) == []
    return report


@pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_JOERN') != '1',
                    reason='set AUTOFORM_TEST_JOERN=1 to run the real cross-revision chain')
@pytest.mark.skipif(shutil.which('node') is None, reason='node is required for the Node oracle')
@needs_git
def test_the_real_chain_compares_javascript_behaviour_across_revisions(tmp_path):
    """A JS package whose module imports an installed (git-ignored) package: `clamp`
    (number -> number) and `sign` (number -> string) change behaviour, `twice` only
    renames a local, `offset` is an instance method compared on a receiver the Node
    driver builds itself (its class has a zero-argument constructor) and its `+ off`
    edit changes behaviour, `versioned` is not edited. The head and base runtimes are
    `git archive`s, so they load only because the working tree's `node_modules` is
    linked."""
    def write(repo, tag):
        if tag == 'base':
            (repo / '.gitignore').write_text('node_modules/\n')
            (repo / 'package.json').write_text('{"name": "fixture", "version": "1.0.0"}\n')
            dep = repo / 'node_modules/fixture-dep'
            dep.mkdir(parents=True)
            (dep / 'package.json').write_text('{"name": "fixture-dep", "main": "index.js"}\n')
            (dep / 'index.js').write_text("exports.suffix = () => 'v1';\n")
        values = dict(top=40, pos='pos', local='sum', off=0) if tag == 'base' else \
            dict(top=30, pos='plus', local='doubled', off=1)
        (repo / 'lib.js').write_text(JS_LIB.format(**values))

    repo = two_commit_history(tmp_path / 'repo', write)
    out = tmp_path / 'out'
    report = run_real_pr(repo, out, 'PullRequestTestJsBehaviour')
    by_name = {f['name'].rsplit(':', 1)[-1]: f for f in report['functions']}
    # Change identity against the base export: the unedited function is not reported.
    assert report['change_identity']['status'] == 'base-export'
    assert 'lib.js::program:versioned' in report['change_identity']['unchanged']
    assert set(by_name) == {'clamp', 'sign', 'twice', 'offset'}, sorted(by_name)
    assert all(f['language'] == 'js' for f in report['functions'])
    behaviour = {name: f['behaviour'] for name, f in by_name.items()}
    assert behaviour['clamp']['status'] == 'changed', behaviour
    item = behaviour['clamp']['counter_inputs'][0]
    assert item['call'].startswith('clamp(') and item['base_model'] != item['head_runtime']
    assert behaviour['sign']['status'] == 'changed', behaviour['sign']
    assert any('plus' in c['head_runtime'] and 'pos' in c['base_model']
               for c in behaviour['sign']['counter_inputs']), \
        behaviour['sign']
    assert behaviour['twice']['status'] == 'unchanged-on-inputs' and behaviour['twice']['compared'] >= 1
    assert behaviour['offset']['status'] == 'changed', behaviour['offset']
    assert any(c['base_model'] != c['head_runtime']
               for c in behaviour['offset']['counter_inputs']), behaviour['offset']
    assert report['behaviour']['languages'] == ['js']
    assert report['dependencies']['linked'] == ['node_modules']
    assert 'Languages compared: js' in (out / 'pr.md').read_text()


GO_CALC = '''package calc

import "example.com/svc/limits"

func Scale(x int) int {{
	return x*3 + {top}
}}

func Twice(x int) int {{
	{local} := x + x
	return {local}
}}

func Cap(x int) int {{
	switch {{
	case x > limits.Max:
		return limits.Max
	}}
	return x
}}

type Counter struct {{
	n int
}}

func (c Counter) Offset(x int) int {{
	return c.n + x + {off}
}}
'''


@pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_JOERN') != '1',
                    reason='set AUTOFORM_TEST_JOERN=1 to run the real cross-revision chain')
@pytest.mark.skipif(shutil.which('go') is None, reason='go is required for the Go oracle')
@needs_git
def test_the_real_chain_compares_go_behaviour_across_revisions(tmp_path):
    """A repository whose Go module sits below its root (`svc/go.mod`), run on the root:
    `Scale` changes behaviour, `Twice` only renames a local, `Offset` is a method the Go
    oracle cannot call, `Cap` (which imports a package of the module) is not edited.
    `Cap`'s `switch` exports with a `control:SWITCH` hole, so its identical record is
    no evidence of no edit: it stays a candidate, says why, and is not compared."""
    def write(repo, tag):
        if tag == 'base':
            (repo / 'svc/calc').mkdir(parents=True)
            (repo / 'svc/limits').mkdir(parents=True)
            (repo / 'README.md').write_text('fixture\n')
            (repo / 'svc/go.mod').write_text('module example.com/svc\n\ngo 1.20\n')
            (repo / 'svc/limits/limits.go').write_text('package limits\n\nconst Max = 100\n')
        values = dict(top=1, local='sum', off=0) if tag == 'base' else dict(top=2, local='doubled', off=1)
        (repo / 'svc/calc/calc.go').write_text(GO_CALC.format(**values))

    repo = two_commit_history(tmp_path / 'repo', write)
    out = tmp_path / 'out'
    report = run_real_pr(repo, out, 'PullRequestTestGoBehaviour')
    by_name = {f['name']: f for f in report['functions']}
    pick = lambda word: next(f['behaviour'] for n, f in by_name.items() if word in n)
    assert report['change_identity']['status'] == 'base-export'
    cap = by_name['example.com/svc/calc.Cap']
    assert 'not provably unchanged' in cap['change_detail'], cap
    assert cap['behaviour']['status'] == 'not-compared'
    assert report['change_identity']['counts']['identical_but_holed'] == 1
    assert all(f['language'] == 'go' for f in report['functions'])
    scale = pick('Scale')
    assert scale['status'] == 'changed', by_name
    assert scale['counter_inputs'][0]['base_model'] != scale['counter_inputs'][0]['head_runtime']
    assert pick('Twice')['status'] == 'unchanged-on-inputs' and pick('Twice')['compared'] >= 1, by_name
    assert pick('Offset')['status'] == 'not-compared'
    assert 'receiver' in pick('Offset')['reason'], pick('Offset')
    assert report['behaviour']['languages'] == ['go']
