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
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
from autoform import cli  # noqa: E402
SUBCOMMANDS = ('init', 'doctor', 'source', 'assure', 'regress', 'pr', 'machine')


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
    # The release has per-platform zips only; a hint naming `.../joern-cli.zip` was a 404.
    assert re.search(r'/download/v[^/ ]+/joern-cli-(linux|macos)-(x86_64|arm64)\.zip ',
                     tools['joern']['hint']), tools['joern']['hint']
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
    # A missing [machine] extra is likewise a warning with an install line. The extra is
    # a Python package, not a PATH entry, so an empty PATH does not remove it: on a machine
    # that has it the entry is healthy and carries no hint at all.
    pypcode = report['tools']['pypcode']
    assert pypcode['required'] is False
    if pypcode['status'] == 'ok':
        assert 'hint' not in pypcode
    else:
        assert 'autoform-lean[machine]' in pypcode['hint']


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


# The schema_version 1 contract fleet automation parses. Additions are compatible and
# keep the version; removing or renaming anything here, or a new `status` value, is a
# breaking change that needs schema_version 2 (docs/packaging.md).
DOCTOR_V1_KEYS = {'schema_version': int, 'autoform': str, 'platform': str, 'pins': dict,
                  'host': dict, 'tools': dict, 'problems': list, 'warnings': list, 'exit_code': int}
TOOL_V1_KEYS = {'path', 'required', 'status', 'found_version', 'expected_version', 'note',
                'hint', 'disables'}
HOST_V1_KEYS = {'os': str, 'distro': dict, 'package_manager': (str, type(None)),
                'user_namespaces': dict, 'bwrap': (str, type(None)),
                'sandbox': (dict, type(None)), 'proxy': dict}


def test_doctor_json_schema_v1_is_stable(tmp_path):
    result = run_cli('doctor', '--json', env=bare_environment(tmp_path))
    report = json.loads(result.stdout)
    assert report['schema_version'] == 1
    for key, kind in DOCTOR_V1_KEYS.items():
        assert isinstance(report[key], kind), key
    assert report['exit_code'] == result.returncode
    for key, kind in HOST_V1_KEYS.items():
        assert isinstance(report['host'][key], kind), key
    assert set(report['host']['distro']) == {'id', 'id_like', 'version_id', 'pretty_name', 'family'}
    assert report['host']['distro']['family'] in ('rhel', 'debian', 'alpine', 'macos', None)
    for name, entry in report['tools'].items():
        assert set(entry) <= TOOL_V1_KEYS, (name, set(entry) - TOOL_V1_KEYS)
        assert entry['status'] in ('ok', 'missing', 'version-mismatch', 'unknown-version'), name
        assert isinstance(entry['required'], bool), name
        # Every non-ok entry is actionable, and every problem/warning names its tool.
        if entry['status'] != 'ok':
            assert entry['hint'], name
            bucket = report['problems'] if entry['required'] else report['warnings']
            assert any(line.startswith(name + ':') for line in bucket), name
    # The sandbox is reported and optional: without one, every oracle refuses to run the
    # code under test, but translation and kernel proofs do not need it.
    assert report['tools']['sandbox']['required'] is False


def test_doctor_reports_proxies_without_their_credentials(tmp_path):
    env = dict(bare_environment(tmp_path), HTTPS_PROXY='http://alice:s3cret@proxy.internal:3128',
               NO_PROXY='localhost,.internal')
    report = json.loads(run_cli('doctor', '--json', env=env).stdout)
    assert report['host']['proxy']['HTTPS_PROXY'] == 'http://***@proxy.internal:3128'
    assert report['host']['proxy']['NO_PROXY'] == 'localhost,.internal'
    human = run_cli('doctor', env=env)
    assert 's3cret' not in human.stdout + human.stderr
    assert 'proxy.internal' in human.stdout


ROCKY_9 = 'NAME="Rocky Linux"\nID="rocky"\nID_LIKE="rhel centos fedora"\nVERSION_ID="9.4"\n'
CENTOS_7 = 'NAME="CentOS Linux"\nID="centos"\nID_LIKE="rhel fedora"\nVERSION_ID="7"\n'
UBUNTU = 'NAME="Ubuntu"\nID=ubuntu\nID_LIKE=debian\nVERSION_ID="24.04"\n'
ALPINE = 'NAME="Alpine Linux"\nID=alpine\nVERSION_ID=3.20.1\n'


def _release(tmp_path, text):
    path = tmp_path / 'os-release'
    path.write_text(text)
    return cli.os_release(path)


def test_distro_family_and_package_manager_come_from_os_release(tmp_path):
    rocky = _release(tmp_path, ROCKY_9)
    assert rocky['id'] == 'rocky' and rocky['version_id'] == '9.4'
    assert cli.distro_family(rocky) == 'rhel'
    assert cli.package_manager('rhel', rocky) == 'sudo dnf install -y'
    centos7 = _release(tmp_path, CENTOS_7)
    assert cli.package_manager(cli.distro_family(centos7), centos7) == 'sudo yum install -y'
    assert cli.distro_family(_release(tmp_path, UBUNTU)) == 'debian'
    assert cli.package_manager(cli.distro_family(_release(tmp_path, ALPINE))) == 'sudo apk add'
    assert cli.distro_family(_release(tmp_path, 'ID=plan9\n')) is None
    assert cli.os_release(tmp_path / 'absent') == {}


def test_linux_install_hints_use_the_hosts_package_manager(tmp_path, monkeypatch):
    monkeypatch.setattr(cli, '_os_flavor', lambda: 'linux')
    # Debian-family hosts keep the apt lines they always had.
    cases = [(_release(tmp_path, text), cc, go) for text, cc, go in (
        (ROCKY_9, 'sudo dnf install -y gcc gcc-c++ make', 'sudo dnf install -y golang'),
        (ALPINE, 'sudo apk add build-base', 'sudo apk add go'),
        (UBUNTU, 'sudo apt-get install -y build-essential', 'sudo apt-get install -y golang-go'))]
    for release, cc, go in cases:
        monkeypatch.setattr(cli, 'os_release', lambda path=None, release=release: release)
        assert cli.install_hint('cc') == cc
        assert cli.install_hint('go') == go
        assert cli.install_hint('ld.lld').endswith(' lld')     # the package, not the binary


def test_sandbox_hint_names_the_package_and_the_sysctl_that_block_it(monkeypatch):
    monkeypatch.setattr(cli, '_os_flavor', lambda: 'linux')
    rocky = {'id': 'rocky', 'id_like': 'rhel centos fedora', 'version_id': '9.4'}
    hint = cli.sandbox_hint(release=rocky, userns={'max_user_namespaces': 0}, bwrap='')
    assert 'sudo dnf install -y bubblewrap' in hint
    assert 'sudo sysctl -w user.max_user_namespaces=15000' in hint
    assert 'AUTOFORM_SANDBOX=off' in hint
    ubuntu = {'id': 'ubuntu', 'id_like': 'debian'}
    hint = cli.sandbox_hint(release=ubuntu, bwrap='/usr/bin/bwrap',
                            userns={'max_user_namespaces': 63000, 'unprivileged_userns_clone': 1,
                                    'apparmor_restrict_unprivileged_userns': 1})
    assert 'bubblewrap' not in hint.split('#')[0]
    assert 'kernel.apparmor_restrict_unprivileged_userns=0' in hint


def test_user_namespaces_reads_absent_sysctls_as_none(tmp_path):
    (tmp_path / 'user').mkdir()
    (tmp_path / 'user' / 'max_user_namespaces').write_text('0\n')
    assert cli.user_namespaces(tmp_path) == {'max_user_namespaces': 0, 'unprivileged_userns_clone': None,
                                             'apparmor_restrict_unprivileged_userns': None}


def test_module_name_is_validated_before_any_tool_is_needed(tmp_path):
    """A lowercase module is refused with exit 2 and a reason, before Joern or Lean
    are ever consulted -- so a bad name never costs a JVM start."""
    result = run_cli('--workspace', str(tmp_path / 'ws'), 'source', str(tmp_path), 'lowercase',
                     env=bare_environment(tmp_path))
    assert result.returncode == 2, result.stdout + result.stderr
    assert 'uppercase' in result.stderr


def test_doctor_names_a_joern_launcher_that_cannot_start(tmp_path):
    """A complete Joern whose launcher needs `greadlink` is not usable without it."""
    lib = tmp_path / 'joern' / 'joern-cli' / 'lib'
    lib.mkdir(parents=True)
    (lib / 'io.joern.joern-cli-4.0.606.jar').write_bytes(b'')
    (lib.parent / 'joern-parse').write_text('#!/usr/bin/env sh\nSCRIPT_ABS_PATH=$(greadlink -f "$0")\n')
    (tmp_path / 'bin').mkdir()
    env = {'JOERN_HOME': str(tmp_path / 'joern'), 'PATH': str(tmp_path / 'bin')}
    path, found, note = cli.joern_report(env)
    assert found is None and 'greadlink' in note and 'coreutils' in note
    (tmp_path / 'bin' / 'greadlink').write_text('#!/bin/sh\n')
    (tmp_path / 'bin' / 'greadlink').chmod(0o755)
    assert cli.joern_report(env)[1:] == ('4.0.606', None)
