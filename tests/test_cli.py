"""The `autoform` command surface, from a checkout, with no Joern, Lean or network.

`test_package.py` exercises an actually built wheel and skips without one. These run
against `src/` directly, so they gate every change to `src/autoform/cli.py` in an
ordinary `pytest` run. What they pin is the part of the CLI a fresh installer meets
first: `--help`, `--version`, and `doctor` on a machine with nothing installed.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
SUBCOMMANDS = ('init', 'doctor', 'source', 'assure', 'machine')


def run_cli(*args, env=None, cwd=None, timeout=180):
    environment = dict(os.environ)
    environment['PYTHONPATH'] = str(ROOT / 'src') + (
        os.pathsep + environment['PYTHONPATH'] if environment.get('PYTHONPATH') else '')
    environment.update(env or {})
    return subprocess.run([sys.executable, '-m', 'autoform', *args], cwd=cwd or ROOT,
                          env=environment, text=True, capture_output=True, timeout=timeout)


def bare_environment(tmp_path):
    """No tools on PATH, an empty HOME (so `~/.elan/bin` resolves to nothing), no Joern."""
    (tmp_path / 'empty-bin').mkdir()
    (tmp_path / 'home').mkdir()
    return {'PATH': str(tmp_path / 'empty-bin'), 'HOME': str(tmp_path / 'home'),
            'JOERN_HOME': str(tmp_path / 'no-joern')}


def test_help_names_every_subcommand_and_the_exit_codes():
    result = run_cli('--help')
    assert result.returncode == 0, result.stderr
    for name in SUBCOMMANDS:
        assert name in result.stdout, name
    # The epilog is the one place a first-time user is told what 1 and 2 mean.
    assert 'exit codes' in result.stdout
    assert 'autoform doctor' in result.stdout


def test_version_carries_both_external_pins():
    """`autoform 0.1.0` alone is not a reproducible bug report: the AST is a function of
    the Joern build and every proof of the Lean toolchain."""
    result = run_cli('--version')
    assert result.returncode == 0, result.stderr
    lean = (ROOT / 'lean-toolchain').read_text().strip()
    joern = (ROOT / 'joern-version').read_text().strip()
    assert result.stdout.startswith('autoform ')
    assert lean in result.stdout
    assert joern in result.stdout


def test_doctor_json_on_a_bare_machine(tmp_path):
    result = run_cli('doctor', '--json', env=bare_environment(tmp_path))
    # Required tools are absent, so this is a failure -- and a well-formed one.
    assert result.returncode == 1, result.stderr
    report = json.loads(result.stdout)
    assert report['schema_version'] == 1
    assert report['exit_code'] == 1
    for key in ('autoform', 'platform', 'pins', 'tools', 'problems', 'warnings'):
        assert key in report, key
    assert report['pins']['joern'] == (ROOT / 'joern-version').read_text().strip()
    assert report['pins']['lean_toolchain'] == (ROOT / 'lean-toolchain').read_text().strip()
    tools = report['tools']
    for name in ('python', 'git', 'lake', 'lean', 'leanchecker', 'joern'):
        assert tools[name]['required'] is True, name
    # The interpreter running the test is what `doctor` reports for python, so it is
    # present whatever PATH says.
    assert tools['python']['status'] == 'ok'
    assert tools['joern']['status'] == 'missing'
    assert 'hint' in tools['joern'] and 'joern-cli.zip' in tools['joern']['hint']
    assert any(problem.startswith('joern:') for problem in report['problems'])


def test_doctor_treats_a_missing_language_runtime_as_a_warning_that_names_the_language(tmp_path):
    result = run_cli('doctor', '--json', env=bare_environment(tmp_path))
    report = json.loads(result.stdout)
    node = report['tools']['node']
    assert node['required'] is False
    assert node['status'] == 'missing'
    # Optional means: the translation and proofs still run; ONE oracle is unavailable,
    # and the report says which one rather than leaving "optional" to be guessed at.
    assert 'JavaScript' in ' '.join(node['disables'])
    assert not any(problem.startswith('node:') for problem in report['problems'])
    assert any(warning.startswith('node:') for warning in report['warnings'])
    # A missing [machine] extra is likewise a warning with an install line.
    assert report['tools']['pypcode']['required'] is False
    assert 'autoform-lean[machine]' in report['tools']['pypcode']['hint']


def test_doctor_human_summary_gives_an_install_line_per_problem(tmp_path):
    result = run_cli('doctor', env=bare_environment(tmp_path))
    assert result.returncode == 1
    assert result.stdout.startswith('autoform doctor:')
    assert 'MISSING ' in result.stdout          # a required tool, loud
    assert 'install:' in result.stdout
    assert 'exit codes:' in result.stdout
    # Problems are repeated on stderr for scripts that only capture that stream.
    assert 'required check(s) failed' in result.stderr


def test_doctor_json_stdout_is_only_json(tmp_path):
    """Scripts parse stdout; the human chatter must all be on stderr."""
    result = run_cli('doctor', '--json', env=bare_environment(tmp_path))
    json.loads(result.stdout)  # would raise on any stray line


def test_module_name_is_validated_before_any_tool_is_needed(tmp_path):
    """A lowercase module is refused with exit 2 and a reason, before Joern or Lean
    are ever consulted -- so a bad name never costs a JVM start."""
    result = run_cli('--workspace', str(tmp_path / 'ws'), 'source', str(tmp_path), 'lowercase',
                     env=bare_environment(tmp_path))
    assert result.returncode == 2, result.stdout + result.stderr
    assert 'uppercase' in result.stderr
