"""The Python oracle's interpreter, and what it says when the project's suite does not run.

Measured on a 103-file package with 399 unit tests: the oracle ran the suite under the
tool's own interpreter, which lacked the project's dependencies, so every module that
imported them failed and the suite never ran. pytest exited 4 (project `addopts` naming a
plugin that interpreter did not have) and the report blamed the test directory's name;
modules that raised on import were reported as "not imported by the suite". All five seeded
regressions read "not compared". Each of those silences is pinned here.
"""
from __future__ import annotations

import json
import os
import shutil
import stat
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

from conftest import ROOT, SCRIPTS, load

pr_mode = load(str(Path(SCRIPTS) / 'pr_mode.py'), 'af_pr_mode_interp')
pr_fixture = load(str(Path(SCRIPTS) / 'pr_fixture.py'), 'af_pr_fixture_interp')
DIFFERENTIAL = str(Path(SCRIPTS) / 'differential.py')

needs_git = pytest.mark.skipif(shutil.which('git') is None, reason='git is required')


def _fake_interpreter(path, body):
    path.write_text('#!/bin/sh\n' + body)
    path.chmod(path.stat().st_mode | stat.S_IXUSR)
    return path


# ------------------------------------------------------------ pytest exit codes

@pytest.mark.parametrize('rc, words', [
    (2, 'interrupted, or errors during collection'),
    (3, 'pytest internal error'),
    (4, 'pytest usage error'),
    (5, 'no tests were collected'),
])
def test_each_pytest_exit_code_gets_its_own_diagnosis_with_the_last_output(differential, rc, words):
    run = {'dir': '/x/tests', 'rc': rc, 'runner': {'runner': 'pytest'},
           'output_tail': ['ERROR: usage: pytest [options]', 'pytest: error: unrecognized arguments: --cov']}
    got = differential.diagnose_test_run(run)
    assert got.startswith('TEST SUITE DID NOT RUN: /x/tests (exit %d: ' % rc)
    assert words in got
    assert 'unrecognized arguments: --cov' in got
    # The old message, printed for every code but 0/1, sent the reader to rename directories.
    assert 'imported as a package' not in got


def test_a_usage_error_names_the_explicit_way_out(differential):
    got = differential.diagnose_test_run({'dir': 't', 'rc': 4, 'output_tail': []})
    assert 'AUTOFORM_ORACLE_PYTEST_ADDOPTS=ignore' in got and 'recorded' in got


def test_the_package_naming_hint_appears_only_for_an_import_path_mismatch(differential):
    got = differential.diagnose_test_run({'dir': 't', 'rc': 2, 'output_tail': [
        'E   _pytest.pathlib.ImportPathMismatchError: (...)', 'import file mismatch:']})
    assert 'imported as a package' in got


def test_a_run_that_ran_is_silent_unless_modules_failed_to_collect(differential):
    assert differential.diagnose_test_run({'dir': 't', 'rc': 0}) is None
    assert differential.diagnose_test_run({'dir': 't', 'rc': 1}) is None
    got = differential.diagnose_test_run({'dir': 't', 'rc': 1, 'collection_errors': {
        't/test_a.py': "ModuleNotFoundError: No module named 'licensed_solver'"}})
    assert got.startswith('TEST MODULES NOT COLLECTED') and 'licensed_solver' in got


def test_an_exception_from_the_runner_is_reported_as_such(differential):
    got = differential.diagnose_test_run({'dir': 't', 'error': "RuntimeError('boom')"})
    assert 'raised' in got and 'boom' in got
    # Measured: `--cov-config setup.cfg` in addopts raised out of pytest.main, because the
    # path is relative to the cwd and the oracle runs from its report directory.
    got = differential.diagnose_test_run({'dir': 't', 'runner': {'project_addopts': 'applied'},
                                          'error': "ConfigError(\"Couldn't read 'setup.cfg'\")"})
    assert 'AUTOFORM_ORACLE_PYTEST_ADDOPTS=ignore' in got


def test_collection_errors_are_read_from_the_runner_output(differential):
    output = textwrap.dedent('''\
        \x1b[31m___________ ERROR collecting tests/test_a.py ___________\x1b[0m
        ImportError while importing test module '/r/tests/test_a.py'.
        Traceback:
        E   ModuleNotFoundError: No module named 'licensed_solver'
        ___________ ERROR collecting tests/sub/test_b.py ___________
        E   ValueError: bad fixture
        =========================== short test summary info ============================
        ERROR tests/test_a.py
        ''')
    assert differential.collection_errors(output) == {
        'tests/test_a.py': "ModuleNotFoundError: No module named 'licensed_solver'",
        'tests/sub/test_b.py': 'ValueError: bad fixture'}


def test_the_pytest_command_line_keeps_project_addopts_unless_told_and_says_so(differential):
    args, record = differential.pytest_args('/t', environ={})
    assert '--continue-on-collection-errors' in args and '-o' not in args
    assert record['project_addopts'] == 'applied'
    args, record = differential.pytest_args('/t', environ={'AUTOFORM_ORACLE_PYTEST_ADDOPTS': 'ignore'})
    assert args[-2:] == ['-o', 'addopts=']
    assert record['project_addopts'].startswith('ignored')
    with pytest.raises(ValueError):
        differential.pytest_args('/t', environ={'AUTOFORM_ORACLE_PYTEST_ADDOPTS': 'drop'})


def _project(tmp_path, addopts):
    root = tmp_path / 'proj'
    (root / 'tests').mkdir(parents=True)
    (root / 'tests' / 'test_ok.py').write_text('def test_ok():\n    assert True\n')
    (root / 'tests' / 'test_broken.py').write_text('import licensed_solver_not_installed\n')
    (root / 'setup.cfg').write_text('[tool:pytest]\naddopts = %s\n' % addopts)
    return root


def _run_dir(root, env=None):
    code = ('import json, sys; sys.path.insert(0, %r); import differential as d; '
            'print("@@" + json.dumps(d.run_test_dir(%r)))' % (SCRIPTS, str(root / 'tests')))
    out = subprocess.run([sys.executable, '-c', code], cwd=str(root), capture_output=True, text=True,
                         env=dict(os.environ, AUTOFORM_NO_REEXEC='1', **(env or {})), timeout=300)
    line = [l for l in out.stdout.splitlines() if l.startswith('@@')]
    assert line, out.stdout + out.stderr
    return json.loads(line[-1][2:])


def test_a_project_option_pytest_rejects_is_a_usage_error_and_ignoring_it_is_recorded(tmp_path, differential):
    root = _project(tmp_path, '--an-option-of-a-missing-plugin')
    run = _run_dir(root)
    assert run['rc'] == 4
    assert 'usage error' in differential.diagnose_test_run(run)
    assert any('an-option-of-a-missing-plugin' in line for line in run['output_tail'])
    run = _run_dir(root, {'AUTOFORM_ORACLE_PYTEST_ADDOPTS': 'ignore'})
    # The module that imports a missing dependency is named; the other still ran.
    assert run['rc'] == 1 and run['runner']['project_addopts'].startswith('ignored')
    assert "licensed_solver_not_installed" in run['collection_errors']['tests/test_broken.py']
    assert any('1 passed' in line for line in run['output_tail'])


# ------------------------------------------------------------ module import errors

def test_a_module_that_fails_to_import_is_reported_with_its_exception(tmp_path, monkeypatch, differential):
    pkg = tmp_path / 'src' / 'w3pkg'
    pkg.mkdir(parents=True)
    (pkg / '__init__.py').write_text('')
    (pkg / 'heavy.py').write_text('import a_dependency_not_installed\n\ndef f(x):\n    return x\n')
    (pkg / 'light.py').write_text('def g(x):\n    return x\n')
    monkeypatch.syspath_prepend(str(tmp_path / 'src'))
    monkeypatch.setattr(differential, 'IMPORT_ERRORS', {})
    # A src/ layout: the AST path is not the import name; the dotted suffix is.
    assert differential.find_module('src/w3pkg/light.py').__name__ == 'w3pkg.light'
    assert differential.find_module('src/w3pkg/heavy.py') is None
    assert differential.IMPORT_ERRORS['src/w3pkg/heavy.py'] == (
        "w3pkg.heavy: ModuleNotFoundError: No module named 'a_dependency_not_installed'")
    for name in [n for n in sys.modules if n.startswith('w3pkg')]:
        monkeypatch.delitem(sys.modules, name)


def test_the_behaviour_reason_names_the_import_failure_when_no_case_was_kept():
    name = 'src/pkg/heavy.py:<module>.f'
    cross = {'runtime_cases': [], 'divergence_detail': [], 'coverage': {'by_status': {}},
             'import_errors': {'src/pkg/heavy.py': "pkg.heavy: ModuleNotFoundError: No module named 'dep'"}}
    out, _ = pr_mode.behaviour_results([{'name': name, 'file': 'src/pkg/heavy.py', 'change': 'modified'}],
                                       cross, None, {})
    assert out[name]['status'] == 'not-compared'
    assert "module failed to import: pkg.heavy: ModuleNotFoundError: No module named 'dep'" in out[name]['reason']


# ------------------------------------------------------------ the interpreter setting

def test_the_oracle_reexecutes_under_the_requested_interpreter(tmp_path):
    record = tmp_path / 'argv.txt'
    fake = _fake_interpreter(tmp_path / 'python', 'printf "%%s\\n" "$@" > %s\n'
                             'echo "seed=$PYTHONHASHSEED exec=$AUTOFORM_ORACLE_PYTHON_EXEC" >> %s\n'
                             % (record, record))
    out = subprocess.run([sys.executable, DIFFERENTIAL, 'ast.json', 'src', 'Mod'], cwd=str(tmp_path),
                         env=dict(os.environ, AUTOFORM_ORACLE_PYTHON=str(fake)),
                         capture_output=True, text=True, timeout=120)
    assert out.returncode == 0, out.stdout + out.stderr
    lines = record.read_text().splitlines()
    assert lines[:4] == [os.path.abspath(DIFFERENTIAL), 'ast.json', 'src', 'Mod']
    assert lines[4] == 'seed=0 exec=%s' % fake


def test_an_unusable_interpreter_is_refused_with_a_report(tmp_path):
    out = subprocess.run([sys.executable, DIFFERENTIAL, 'ast.json', 'src', 'Mod'], cwd=str(tmp_path),
                         env=dict(os.environ, AUTOFORM_ORACLE_PYTHON=str(tmp_path / 'missing')),
                         capture_output=True, text=True, timeout=120)
    assert out.returncode == 2 and 'REFUSING' in out.stdout
    report = json.loads((tmp_path / 'conformance.json').read_text())
    assert report['status'] == 'REFUSED: oracle interpreter unavailable' and report['total'] == 0


def test_the_target_is_not_resolved_through_symlinks(differential, tmp_path):
    link = tmp_path / 'venv-python'
    link.symlink_to(sys.executable)
    assert differential.oracle_interpreter_target({}, sys.executable) is None
    assert differential.oracle_interpreter_target({'AUTOFORM_ORACLE_PYTHON': str(link)},
                                                  sys.executable) == str(link)
    assert differential.oracle_interpreter_target({'AUTOFORM_ORACLE_PYTHON': str(link)}, str(link)) is None
    assert differential.oracle_interpreter_target(
        {'AUTOFORM_ORACLE_PYTHON': str(link), 'AUTOFORM_ORACLE_PYTHON_EXEC': str(link)}, sys.executable) is None


def test_the_record_names_the_interpreter_and_the_setting(differential, monkeypatch):
    monkeypatch.delenv('AUTOFORM_ORACLE_PYTHON', raising=False)
    got = differential.oracle_interpreter_record()
    assert got['path'] == sys.executable and got['version'] == sys.version.split()[0]
    assert got['requested'] is None and got['setting'].startswith('default')
    monkeypatch.setenv('AUTOFORM_ORACLE_PYTHON', sys.executable)
    assert differential.oracle_interpreter_record()['setting'] == 'AUTOFORM_ORACLE_PYTHON'


def test_pr_mode_validates_the_interpreter_before_any_stage(tmp_path):
    good = _fake_interpreter(tmp_path / 'py-good', 'echo 3.12.4; echo 1\n')
    env, record = pr_mode.oracle_settings(str(good), None, environ={})
    assert env == {'AUTOFORM_ORACLE_PYTHON': str(good)}
    assert record == {'path': str(good), 'version': '3.12.4', 'setting': '--python',
                      'pytest_addopts': 'project'}
    env, record = pr_mode.oracle_settings(None, 'ignore', environ={'AUTOFORM_ORACLE_PYTHON': str(good)})
    assert env['AUTOFORM_ORACLE_PYTEST_ADDOPTS'] == 'ignore' and record['setting'] == 'AUTOFORM_ORACLE_PYTHON'
    env, record = pr_mode.oracle_settings(None, None, environ={})
    assert env == {} and record['path'] == sys.executable
    old = _fake_interpreter(tmp_path / 'py-old', 'echo 3.8.10; echo 0\n')
    broken = _fake_interpreter(tmp_path / 'py-broken', 'exit 3\n')
    for bad, words in ((tmp_path / 'nope', 'not an executable'), (old, 'needs 3.10+'),
                       (broken, 'did not start')):
        with pytest.raises(pr_mode.PrError, match=words):
            pr_mode.oracle_settings(str(bad), None, environ={})
    with pytest.raises(pr_mode.PrError, match='project'):
        pr_mode.oracle_settings(None, 'drop', environ={})


def test_the_chain_hands_the_oracle_settings_to_every_stage(tmp_path):
    chain = pr_mode.Chain(ROOT, tmp_path, 'M', tmp_path, sys.executable, 10, print,
                          {'AUTOFORM_ORACLE_PYTHON': '/venv/bin/python'})
    assert chain.env['AUTOFORM_ORACLE_PYTHON'] == '/venv/bin/python'


@pytest.fixture
def cli(monkeypatch):
    monkeypatch.syspath_prepend(str(Path(ROOT) / 'src'))
    import autoform.cli as module
    calls = []
    monkeypatch.setattr(module, '_run_command', lambda command, **kw: calls.append((command, kw)) or 0)
    module._calls = calls
    return module


def test_cli_pr_passes_the_interpreter_and_addopts_setting_through_the_environment(tmp_path, cli):
    repo = tmp_path / 'repo'
    (repo / '.git').mkdir(parents=True)
    link = tmp_path / 'venv' / 'bin' / 'python'
    link.parent.mkdir(parents=True)
    link.symlink_to(sys.executable)
    code = cli.main(['--workspace', str(tmp_path / 'ws'), 'pr', str(repo), '--base', 'x',
                     '--python', str(link), '--pytest-addopts', 'ignore'])
    assert code == 0
    (command, kwargs), = cli._calls
    assert kwargs['env']['AUTOFORM_ORACLE_PYTHON'] == str(link)       # the link, not its target
    assert kwargs['env']['AUTOFORM_ORACLE_PYTEST_ADDOPTS'] == 'ignore'


# ------------------------------------------------ pr's own project virtualenv

def _venv(repo, rel='.venv/bin/python', body='echo 3.12.4; echo 1\n'):
    """A fake project virtualenv at `repo`'s root: a script that prints a version."""
    path = Path(repo) / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    return _fake_interpreter(path, body)


@pytest.mark.parametrize('rel, setting', [('.venv/bin/python', 'auto: .venv'),
                                          ('venv/bin/python', 'auto: venv')])
def test_a_lone_project_venv_is_used_and_recorded(tmp_path, rel, setting):
    venv = _venv(tmp_path, rel)
    env, record = pr_mode.oracle_settings(None, None, environ={}, repo=tmp_path, python_change=True)
    assert env == {pr_mode.ORACLE_PYTHON_ENV: str(venv)}
    assert record == {'path': str(venv), 'version': '3.12.4', 'setting': setting,
                      'pytest_addopts': 'project'}


def test_without_a_project_venv_the_default_interpreter_stands(tmp_path):
    # A Windows layout is never a candidate, so this repo has none.
    _venv(tmp_path, 'venv/Scripts/python.exe')
    env, record = pr_mode.oracle_settings(None, None, environ={}, repo=tmp_path, python_change=True)
    assert env == {} and record['path'] == sys.executable
    assert record['setting'].startswith('default') and 'note' not in record


def test_two_project_venvs_are_never_chosen_between_and_the_note_names_them(tmp_path):
    for rel in pr_mode.PROJECT_VENVS:
        _venv(tmp_path, rel)
    env, record = pr_mode.oracle_settings(None, None, environ={}, repo=tmp_path, python_change=True)
    assert env == {} and record['path'] == sys.executable
    # Both candidates are named, with the way out: nothing is guessed.
    assert ', '.join(pr_mode.PROJECT_VENVS) in record['note'] and '--python' in record['note']


def test_a_change_in_no_python_file_never_takes_the_project_venv(tmp_path):
    _venv(tmp_path)
    env, record = pr_mode.oracle_settings(None, None, environ={}, repo=tmp_path, python_change=False)
    assert env == {} and record['path'] == sys.executable and 'note' not in record


def test_an_interpreter_given_by_hand_outranks_the_project_venv(tmp_path):
    _venv(tmp_path)
    chosen = _fake_interpreter(tmp_path / 'chosen', 'echo 3.12.4; echo 1\n')
    env, record = pr_mode.oracle_settings(str(chosen), None, environ={}, repo=tmp_path,
                                          python_change=True)
    assert record['path'] == str(chosen) and record['setting'] == '--python'
    env, record = pr_mode.oracle_settings(None, None, environ={pr_mode.ORACLE_PYTHON_ENV: str(chosen)},
                                          repo=tmp_path, python_change=True)
    assert record['path'] == str(chosen) and record['setting'] == pr_mode.ORACLE_PYTHON_ENV


@pytest.mark.parametrize('body, words', [('echo 3.8.10; echo 0\n', 'needs 3.10+'),
                                         ('exit 3\n', 'did not start')])
def test_an_auto_detected_venv_is_validated_like_a_given_one_and_says_where_it_came_from(
        tmp_path, body, words):
    _venv(tmp_path, body=body)
    with pytest.raises(pr_mode.PrError, match=words) as caught:
        pr_mode.oracle_settings(None, None, environ={}, repo=tmp_path, python_change=True)
    assert 'auto-detected .venv/bin/python' in str(caught.value)


def test_a_venv_whose_base_interpreter_is_gone_is_refused_not_skipped(tmp_path):
    (tmp_path / '.venv/bin').mkdir(parents=True)
    (tmp_path / '.venv/bin/python').symlink_to(tmp_path / 'removed-base-python')
    with pytest.raises(pr_mode.PrError, match='not an executable file') as caught:
        pr_mode.oracle_settings(None, None, environ={}, repo=tmp_path, python_change=True)
    assert 'auto-detected .venv/bin/python' in str(caught.value)


# The whole script, offline as test_pr_mode.py runs it: no Joern, so the export stage
# fails and the report is still written in full.

def _pr_env(tmp_path):
    """No Joern and no inherited oracle settings, so pr's own resolution is what runs."""
    env = dict(os.environ, JOERN_HOME=str(tmp_path / 'no-joern'), AUTOFORM_NO_REEXEC='1')
    for name in (pr_mode.ORACLE_PYTHON_ENV, pr_mode.PYTEST_ADDOPTS_ENV):
        env.pop(name, None)
    return env


def _run_pr(repo, args, env):
    return subprocess.run([sys.executable, str(Path(SCRIPTS) / 'pr_mode.py'), str(repo), *map(str, args)],
                          env=env, text=True, capture_output=True, timeout=600)


@needs_git
def test_pr_runs_the_project_under_the_venv_it_found_and_records_it(tmp_path):
    history = pr_fixture.make_history(tmp_path / 'repo')
    venv = _venv(history['repo'])
    out = tmp_path / 'out'
    result = _run_pr(history['repo'], ['--base', 'base', '--head', 'head', '--module', 'PrVenvFound',
                                       '--out', out, '--no-behaviour'], _pr_env(tmp_path))
    assert result.returncode == 2, result.stdout + result.stderr
    # The head tree is a `git archive` and the venv is untracked, so this also pins that
    # the detection looked at the repository, not at the scratch tree it analyses.
    assert json.loads((out / 'pr.json').read_text())['oracle_interpreter'] == {
        'path': str(venv), 'version': '3.12.4', 'setting': 'auto: .venv',
        'pytest_addopts': 'project'}
    assert 'auto: .venv' in result.stdout


@needs_git
def test_pr_records_a_note_when_it_refuses_to_choose_between_two_venvs(tmp_path):
    history = pr_fixture.make_history(tmp_path / 'repo')
    for rel in pr_mode.PROJECT_VENVS:
        _venv(history['repo'], rel)
    out = tmp_path / 'out'
    result = _run_pr(history['repo'], ['--base', 'base', '--head', 'head', '--module', 'PrVenvTwo',
                                       '--out', out, '--no-behaviour'], _pr_env(tmp_path))
    assert result.returncode == 2, result.stdout + result.stderr
    record = json.loads((out / 'pr.json').read_text())['oracle_interpreter']
    assert record['path'] == sys.executable
    assert ', '.join(pr_mode.PROJECT_VENVS) in record['note']


@needs_git
def test_pr_never_auto_detects_a_venv_for_a_change_in_no_python_file(tmp_path):
    history = pr_fixture.make_history(tmp_path / 'repo')
    _venv(history['repo'])
    (Path(history['repo']) / 'm.c').write_text('int f(int x) { return x; }\n')
    out = tmp_path / 'out'
    result = _run_pr(history['repo'], ['--base', 'head', '--module', 'PrVenvNotPython',
                                       '--out', out], _pr_env(tmp_path))
    assert result.returncode == 2, result.stdout + result.stderr
    record = json.loads((out / 'pr.json').read_text())['oracle_interpreter']
    assert record['path'] == sys.executable and record['setting'].startswith('default')
    assert 'note' not in record
