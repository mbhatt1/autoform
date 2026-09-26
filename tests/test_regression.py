"""`scripts/regression.py` and `autoform regress`: what could be proven at one commit
and not at another.

The unit tests build report directories by hand, so they pin the comparison rules
without Joern or Lean. The CLI test replaces the bundled `autoform.sh` with a fake that
writes a report shaped by the checked-out commit, so the two-commit orchestration
(clone, checkout, run, copy, compare, exit code) is exercised end to end with only Git.
The last test runs the real pipeline on two commits of the Python fixture and is
gated on `AUTOFORM_TEST_JOERN=1`.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import textwrap

import pytest

from conftest import ROOT, load

ROOT = Path(ROOT)
from test_cli import run_cli

regression = load(str(ROOT / 'scripts' / 'regression.py'), 'af_regression')


def function(name, body=None, file='m.py'):
    return {'name': name, 'file': file, 'params': [],
            'body': body if body is not None else {'k': 'ret', 'e': {'k': 'lit', 'v': 1}}}


def holed(name, label):
    return function(name, {'k': 'ret', 'e': {'k': 'hole', 'label': label}})


def case(name, args, outcome, comparison='agree'):
    return {'name': name, 'self': None, 'args': args, 'outcome': outcome,
            'comparison': comparison, 'origin': 'random'}


def theorem(subject, proved=True, status=None):
    short = subject.replace('.py:<module>.', '_py__module__')
    return {'id': 'conform_' + short, 'family': 'conform', 'subject': subject,
            'status': status or ('proved' if proved else 'refuted'), 'proved': proved, 'domain': 3}


def write_report(folder, functions, cases=(), theorems=(), status='passed', commit=None,
                 module='Mod'):
    folder = Path(folder)
    folder.mkdir(parents=True, exist_ok=True)
    (folder / f'ast-{module}.json').write_text(json.dumps(list(functions)))
    by_status = {f['name']: 'compared' for f in functions}
    (folder / 'conformance.json').write_text(json.dumps({
        'coverage': {'by_status': by_status}, 'runtime_cases': list(cases)}))
    (folder / 'specs.json').write_text(json.dumps({'module': module, 'specs': list(theorems)}))
    (folder / 'pipeline.json').write_text(json.dumps({
        'module': module, 'stage': 'complete' if status == 'passed' else 'build',
        'status': status, 'exit_code': 0 if status == 'passed' else 1}))
    if commit:
        (folder / 'repository.json').write_text(json.dumps({'commit': commit, 'input': 'repo'}))
    return folder


ADD = 'm.py:<module>.add'
SUB = 'm.py:<module>.sub'


def test_profile_records_holes_theorems_and_cases(tmp_path):
    report = write_report(tmp_path, [function(ADD), holed(SUB, 'call:type')],
                          cases=[case(ADD, [['int', 1]], ['val', ['int', 2]])],
                          theorems=[theorem(ADD)], commit='abc')
    profile = regression.profile(report)
    assert profile['commit'] == 'abc'
    assert profile['functions'][ADD]['holes'] == []
    assert profile['functions'][SUB]['holes'] == ['call:type']
    assert profile['functions'][ADD]['cases'] == {'agree': 1, 'diverge': 0, 'other': 0}
    assert profile['theorems']['conform_m_py__module__add']['proved'] is True
    assert profile['summary'] == {'functions': 2, 'hole_free': 1, 'theorems': 1, 'proved': 1,
                                  'cases': 1, 'agree': 1, 'diverge': 0}


def test_profile_refuses_a_run_that_never_translated(tmp_path):
    (tmp_path / 'pipeline.json').write_text(json.dumps({'module': 'Mod', 'stage': 'parsing',
                                                       'status': 'failed'}))
    with pytest.raises(regression.ReportError, match='did not reach translation'):
        regression.profile(tmp_path)
    assert regression.main(['compare', str(tmp_path), str(tmp_path)]) == 2


def test_identical_reports_do_not_regress(tmp_path):
    report = write_report(tmp_path / 'a', [function(ADD)],
                          cases=[case(ADD, [['int', 1]], ['val', ['int', 2]])], theorems=[theorem(ADD)])
    result = regression.compare(regression.profile(report), regression.profile(report))
    assert result['verdict'] == 'no-regression'
    assert not result['regressions'] and not result['behavior_changes'] and not result['improvements']
    assert regression.exit_code(result) == 0


def test_a_new_hole_and_a_lost_theorem_are_regressions(tmp_path):
    base = write_report(tmp_path / 'base', [function(ADD)],
                        cases=[case(ADD, [['int', 1]], ['val', ['int', 2]])], theorems=[theorem(ADD)])
    # At head the function gained an unsupported construct: it holes, so no theorem is
    # emitted for it and its recorded case cannot be compared.
    head = write_report(tmp_path / 'head', [holed(ADD, 'call:type')])
    result = regression.compare(regression.profile(base), regression.profile(head))
    kinds = sorted((f['kind'], f['subject']) for f in result['regressions'])
    assert kinds == [('proof', ADD), ('translation', ADD)]
    assert result['verdict'] == 'regressed'
    assert regression.exit_code(result) == 1
    # The other direction is the same facts, read as improvements.
    back = regression.compare(regression.profile(head), regression.profile(base))
    assert sorted(f['kind'] for f in back['improvements']) == ['proof', 'translation']
    assert not back['regressions'] and regression.exit_code(back) == 0


def test_a_refuted_theorem_and_a_new_divergence_are_regressions(tmp_path):
    base = write_report(tmp_path / 'base', [function(ADD)],
                        cases=[case(ADD, [['int', 1]], ['val', ['int', 2]])], theorems=[theorem(ADD)])
    head = write_report(tmp_path / 'head', [function(ADD)],
                        cases=[case(ADD, [['int', 1]], ['val', ['int', 2]], comparison='diverge')],
                        theorems=[theorem(ADD, proved=False)])
    result = regression.compare(regression.profile(base), regression.profile(head))
    assert sorted(f['kind'] for f in result['regressions']) == ['conformance', 'proof']
    assert 'refuted' in next(f['detail'] for f in result['regressions'] if f['kind'] == 'proof')


def test_same_inputs_different_outcome_is_a_proven_behavior_change(tmp_path):
    inputs = [['int', 11], ['int', 7]]
    base = write_report(tmp_path / 'base', [function(ADD)],
                        cases=[case(ADD, inputs, ['val', ['int', 18]])], theorems=[theorem(ADD)])
    head = write_report(tmp_path / 'head', [function(ADD)],
                        cases=[case(ADD, inputs, ['val', ['int', 4]])], theorems=[theorem(ADD)])
    result = regression.compare(regression.profile(base), regression.profile(head))
    assert not result['regressions']
    assert result['behavior_changes'] == [dict(
        subject=ADD, inputs=[None, inputs], base=['val', ['int', 18]], head=['val', ['int', 4]],
        proven_both=True, origin='random')]
    assert result['verdict'] == 'behavior-changed'
    # A proven difference between the commits is a nonzero exit, reported under its
    # own heading: the tool cannot tell an intended change from a bug.
    assert regression.exit_code(result) == 1
    text = regression.render_markdown(result)
    assert 'Behavior changes on identical inputs (1)' in text
    assert 'proved in the kernel at both commits' in text


def test_added_and_removed_functions_are_not_regressions(tmp_path):
    base = write_report(tmp_path / 'base', [function(ADD)], theorems=[theorem(ADD)])
    head = write_report(tmp_path / 'head', [holed(SUB, 'call:type')])
    result = regression.compare(regression.profile(base), regression.profile(head))
    assert not result['regressions'] and result['verdict'] == 'no-regression'
    assert result['removed'] == [dict(subject=ADD, file='m.py',
                                      proved_theorems_lost=['conform_m_py__module__add'])]
    assert result['added'] == [dict(subject=SUB, file='m.py', holes=['call:type'])]


def test_a_pipeline_that_stops_passing_is_a_regression(tmp_path):
    base = write_report(tmp_path / 'base', [function(ADD)])
    head = write_report(tmp_path / 'head', [function(ADD)], status='failed')
    result = regression.compare(regression.profile(base), regression.profile(head))
    assert [f['kind'] for f in result['regressions']] == ['pipeline']


def test_compare_command_writes_json_and_markdown(tmp_path):
    base = write_report(tmp_path / 'base', [function(ADD)], theorems=[theorem(ADD)], commit='1111')
    head = write_report(tmp_path / 'head', [holed(ADD, 'x')], commit='2222')
    out, md = tmp_path / 'r' / 'regression.json', tmp_path / 'r' / 'regression.md'
    assert regression.main(['compare', str(base), str(head), '--out', str(out),
                            '--markdown', str(md), '--quiet']) == 1
    report = json.loads(out.read_text())
    assert report['base']['commit'] == '1111' and report['head']['commit'] == '2222'
    assert report['verdict'] == 'regressed'
    assert md.read_text().startswith('# Regression report')
    assert '`1111`' in md.read_text() and '`2222`' in md.read_text()


# --------------------------------------------------------------------- the CLI flow
#
# The workspace refuses a modified bundled `autoform.sh`, so the pipeline is stubbed at
# the one seam `_regress` uses to run it: `_run_command`. Everything else -- the Git
# clone of each ref, the report copies, the comparison through the bundled
# `scripts/regression.py`, the exit code -- is the real code path.

def fake_pipeline(marker_of):
    """A stand-in for running autoform.sh: the report depends on the checkout only."""
    def run(command, *, env, timeout=None, **_):
        _, script, checkout, module = command
        report = Path(script).parent / 'artifacts/pipeline' / module
        marker = marker_of(Path(checkout))
        add = {'name': ADD, 'file': 'm.py', 'params': ['a'],
               'body': {'k': 'ret', 'e': {'k': 'name', 'v': 'a'}}}
        if marker == 'broken':
            add = holed(ADD, 'call:type')
        outcome = ['val', ['int', 4]] if marker == 'changed' else ['val', ['int', 18]]
        write_report(report, [add], module=module,
                     cases=[] if marker == 'broken' else [case(ADD, [['int', 11], ['int', 7]], outcome)],
                     theorems=[] if marker == 'broken' else [theorem(ADD)])
        return 0
    return run


def git(*args, cwd):
    return subprocess.run(['git', *args], cwd=cwd, check=True, text=True, capture_output=True,
                          env=dict(os.environ, GIT_AUTHOR_NAME='t', GIT_AUTHOR_EMAIL='t@t',
                                   GIT_COMMITTER_NAME='t', GIT_COMMITTER_EMAIL='t@t')).stdout.strip()


def make_history(tmp_path, markers):
    """One commit per marker, tagged with the marker's name; returns the repository."""
    repo = tmp_path / 'repo'
    repo.mkdir()
    git('init', '-q', '-b', 'main', cwd=repo)
    for marker in markers:
        (repo / 'marker.txt').write_text(marker + '\n')
        (repo / 'm.py').write_text('def add(a):\n    return a\n')
        git('add', '.', cwd=repo)
        git('commit', '-q', '-m', marker, cwd=repo)
        git('tag', marker, cwd=repo)
    return repo


@pytest.fixture
def cli(monkeypatch):
    monkeypatch.syspath_prepend(str(ROOT / 'src'))
    import autoform.cli as module
    monkeypatch.setattr(module, '_run_command',
                        fake_pipeline(lambda checkout: (checkout / 'marker.txt').read_text().strip()))
    return module


needs_git = pytest.mark.skipif(shutil.which('git') is None, reason='git is required')


@needs_git
def test_regress_runs_both_commits_and_reports_the_lost_proof(tmp_path, cli, capsys):
    repo = make_history(tmp_path, ['good', 'broken'])
    workspace = tmp_path / 'ws'
    code = cli.main(['--workspace', str(workspace), 'regress', str(repo), 'Probe',
                     '--base', 'good', '--head', 'broken'])
    assert code == 1, capsys.readouterr()
    out = workspace / 'artifacts/regression/Probe'
    report = json.loads((out / 'regression.json').read_text())
    assert report['verdict'] == 'regressed'
    assert sorted(f['kind'] for f in report['regressions']) == ['proof', 'translation']
    runs = json.loads((out / 'runs.json').read_text())
    assert runs['base']['commit'] == git('rev-parse', 'good', cwd=repo)
    assert runs['head']['commit'] == git('rev-parse', 'broken', cwd=repo)
    assert report['base']['commit'] == runs['base']['commit']
    assert (out / 'base' / 'ast-Probe.json').is_file() and (out / 'head' / 'ast-Probe.json').is_file()
    assert (out / 'regression.md').read_text().startswith('# Regression report')
    assert 'regression report:' in capsys.readouterr().out
    # Neither checkout is left behind.
    sources = workspace / 'sources'
    assert not sources.exists() or not any(sources.iterdir())


@needs_git
def test_regress_defaults_head_to_the_repository_head_and_sees_behavior_changes(tmp_path, cli):
    repo = make_history(tmp_path, ['good', 'changed'])
    workspace = tmp_path / 'ws'
    code = cli.main(['--workspace', str(workspace), 'regress', repo.resolve().as_uri(), 'Probe',
                     '--base', 'good'])
    assert code == 1
    report = json.loads((workspace / 'artifacts/regression/Probe/regression.json').read_text())
    assert report['verdict'] == 'behavior-changed'
    assert report['head']['commit'] == git('rev-parse', 'HEAD', cwd=repo)
    assert report['behavior_changes'][0]['base'] == ['val', ['int', 18]]
    assert report['behavior_changes'][0]['head'] == ['val', ['int', 4]]
    assert report['behavior_changes'][0]['proven_both'] is True


@needs_git
def test_regress_exits_zero_when_nothing_is_lost(tmp_path, cli):
    repo = make_history(tmp_path, ['good', 'good-again'])
    workspace = tmp_path / 'ws'
    code = cli.main(['--workspace', str(workspace), 'regress', str(repo), 'Probe',
                     '--base', 'good', '--head', 'good-again'])
    assert code == 0
    report = json.loads((workspace / 'artifacts/regression/Probe/regression.json').read_text())
    assert report['verdict'] == 'no-regression'


@needs_git
def test_regress_reports_a_base_run_that_never_translated(tmp_path, cli, monkeypatch, capsys):
    repo = make_history(tmp_path, ['good', 'good-again'])
    monkeypatch.setattr(cli, '_run_command', lambda command, **_: 1)  # parsing failed, no AST
    code = cli.main(['--workspace', str(tmp_path / 'ws'), 'regress', str(repo), 'Probe',
                     '--base', 'good', '--head', 'good-again'])
    assert code == 1
    # (`scripts/regression.py` itself explains on its own stderr that base has no AST.)
    assert 'the base run (good) exited 1' in capsys.readouterr().err


def test_regress_refuses_a_plain_directory(tmp_path, cli, capsys):
    (tmp_path / 'plain').mkdir()
    code = cli.main(['--workspace', str(tmp_path / 'ws'), 'regress', str(tmp_path / 'plain'), 'Probe',
                     '--base', 'x'])
    assert code == 2
    assert 'Git' in capsys.readouterr().err


# ------------------------------------------------------------ the real pipeline

@pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_JOERN') != '1',
                    reason='set AUTOFORM_TEST_JOERN=1 to run the real pipeline at two commits')
def test_regress_detects_a_behavior_change_and_a_new_hole_on_the_python_fixture(tmp_path):
    """Two commits of the Python numeric fixture: the second changes what `add`
    computes and makes `quotient` call something the translator cannot model. The
    proofs at each commit are compared, not the source text."""
    repo = tmp_path / 'repo'
    shutil.copytree(ROOT / 'examples/source/python', repo,
                    ignore=shutil.ignore_patterns('__pycache__'))
    git('init', '-q', '-b', 'main', cwd=repo)
    git('add', '.', cwd=repo)
    git('commit', '-q', '-m', 'base', cwd=repo)
    git('tag', 'base', cwd=repo)
    source = (repo / 'numbers.py').read_text()
    assert 'def add(a, b):\n    return a + b\n' in source
    changed = source.replace('def add(a, b):\n    return a + b\n',
                             'def add(a, b):\n    return a - b\n', 1)
    changed = changed.replace('def quotient(a, b):\n', 'def quotient(a, b):\n    a = type(a)(a)\n', 1)
    assert changed != source
    (repo / 'numbers.py').write_text(changed)
    git('commit', '-q', '-am', 'head', cwd=repo)
    workspace = tmp_path / 'ws'
    env = {'AUTOFORM_ALLOW_DIRTY': '1', 'LEAN_NUM_THREADS': '1',
           'JOERN_HOME': os.environ.get('JOERN_HOME', str(Path.home() / 'joern'))}
    result = run_cli('--workspace', str(workspace), 'regress', str(repo), 'RegressProbe',
                     '--base', 'base', env=env, timeout=3600)
    assert result.returncode == 1, result.stdout + result.stderr
    report = json.loads((workspace / 'artifacts/regression/RegressProbe/regression.json').read_text())
    changed_subjects = {c['subject'] for c in report['behavior_changes']}
    assert 'numbers.py:<module>.add' in changed_subjects, report
    assert all(c['proven_both'] for c in report['behavior_changes']
               if c['subject'] == 'numbers.py:<module>.add')
    # `quotient` now calls `type(a)(a)`: whether that lands as a translation hole or as
    # a theorem the pipeline can no longer emit depends on the exporter's coverage of
    # `type`; either way the proof that held at base is reported lost.
    regressed = {(f['kind'], f['subject']) for f in report['regressions']}
    assert regressed & {('translation', 'numbers.py:<module>.quotient'),
                        ('proof', 'numbers.py:<module>.quotient')}, report
