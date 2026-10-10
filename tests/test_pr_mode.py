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
    assert result.returncode == 0, result.stdout + result.stderr
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
    assert result.returncode == 0, result.stdout + result.stderr
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
