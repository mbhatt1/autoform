"""The code under test cannot reach the network and cannot write outside its work directory.

`scripts/sandbox.py` is the one confinement layer behind the differential oracle, the
native C worker and the nl runners. The exit criterion for roadmap 5.2 is a test in which
the subject tries to exfiltrate and fails. Each subject here is a real process: a Python
fixture that opens a TCP connection to a port this test is listening on and writes a
file beside its work directory, and the same two attempts from compiled C through the
native worker. The unsandboxed control run proves the fixtures would have succeeded, so a
pass is never vacuous; a host without a mechanism skips with the install message.
"""
import json
import os
import shutil
import socket
import subprocess
import sys
from pathlib import Path

import pytest

from conftest import SCRIPTS, load

PROBE = '''
import json, os, socket, sys, tempfile
port, outside, inside = int(sys.argv[1]), sys.argv[2], sys.argv[3]
out = {}
try:
    s = socket.create_connection(("127.0.0.1", port), timeout=3); s.sendall(b"secret"); s.close()
    out["network"] = "connected"
except OSError as e:
    out["network"] = "blocked: " + type(e).__name__
try:
    with open(outside, "w") as f: f.write("leak")
    out["outside"] = "written"
except OSError as e:
    out["outside"] = "blocked: " + type(e).__name__
try:
    with open(inside, "w") as f: f.write("ok")
    out["inside"] = "written"
except OSError as e:
    out["inside"] = "blocked: " + type(e).__name__
out["tmpdir"] = tempfile.gettempdir()
try:
    out["tmpfile"] = tempfile.NamedTemporaryFile(delete=False).name
except OSError as e:
    out["tmpfile"] = "blocked: " + type(e).__name__
print(json.dumps(out))
'''


@pytest.fixture
def sandbox(monkeypatch):
    """The shipped layer, with the policy at its default and no inherited sandbox."""
    monkeypatch.delenv('AUTOFORM_SANDBOX', raising=False)
    monkeypatch.delenv('AUTOFORM_SANDBOX_ACTIVE', raising=False)
    return load(os.path.join(SCRIPTS, 'sandbox.py'), 'af_sandbox')


def _require_mechanism(sandbox):
    mechanism, detail = sandbox.detect()
    if mechanism is None:
        pytest.skip('no sandbox mechanism on this host: ' + detail)
    return mechanism


@pytest.fixture
def listener():
    with socket.socket() as s:
        s.bind(('127.0.0.1', 0))
        s.listen(1)
        s.settimeout(0.2)
        yield s


def _accepted(listener):
    try:
        conn, _ = listener.accept()
    except socket.timeout:
        return False
    conn.close()
    return True


def _run_probe(sandbox, listener, tmp_path, confined):
    work = tmp_path / 'work'
    outside = tmp_path / 'outside'
    outside.mkdir()
    probe = tmp_path / 'probe.py'
    probe.write_text(PROBE)
    port = listener.getsockname()[1]
    cmd = [sys.executable, '-I', str(probe), str(port), str(outside / 'leak.txt'), str(work / 'ok.txt')]
    if confined:
        launch = sandbox.sandboxed(cmd, cwd=str(work), work=work)
        assert launch.record['enforced'] is True and launch.record['network'] == 'denied'
        argv, env, cwd = launch.argv, launch.env, launch.cwd
    else:
        work.mkdir(exist_ok=True)
        argv, env, cwd = cmd, dict(os.environ), str(work)
    r = subprocess.run(argv, cwd=cwd, env=env, capture_output=True, text=True, timeout=120,
                       start_new_session=True)
    assert r.returncode == 0, r.stderr[-2000:]
    return json.loads(r.stdout.strip().splitlines()[-1]), _accepted(listener), outside, work


def test_subject_cannot_reach_the_network_or_write_outside_work(sandbox, listener, tmp_path):
    mechanism = _require_mechanism(sandbox)
    out, accepted, outside, work = _run_probe(sandbox, listener, tmp_path, confined=True)
    assert out['network'].startswith('blocked'), (mechanism, out)
    assert not accepted, 'the listener received a connection from the sandboxed subject'
    assert out['outside'].startswith('blocked'), (mechanism, out)
    assert not (outside / 'leak.txt').exists()
    assert out['inside'] == 'written' and (work / 'ok.txt').read_text() == 'ok'
    # The ordinary temp directory is not a hole: TMPDIR lives inside the work directory.
    assert Path(out['tmpdir']).resolve() == (work / 'tmp').resolve(), out
    assert Path(out['tmpfile']).resolve().is_relative_to(work.resolve()), out


def test_the_fixture_would_have_exfiltrated_without_the_sandbox(sandbox, listener, tmp_path):
    """Guards the test above against passing for the wrong reason (a broken fixture)."""
    out, accepted, outside, _ = _run_probe(sandbox, listener, tmp_path, confined=False)
    assert out['network'] == 'connected' and accepted, out
    assert out['outside'] == 'written' and (outside / 'leak.txt').read_text() == 'leak'


def test_native_code_is_confined_through_the_worker(sandbox, listener, tmp_path, differential):
    if not shutil.which('cc'):
        pytest.skip('C compiler unavailable')
    _require_mechanism(sandbox)
    import native_c
    source = tmp_path / 'source'
    source.mkdir()
    outside = tmp_path / 'outside'
    outside.mkdir()
    (source / 'native.c').write_text('''
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>
int exfiltrate(int port) {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return -errno;
    struct sockaddr_in a; memset(&a, 0, sizeof a);
    a.sin_family = AF_INET; a.sin_port = htons((unsigned short) port);
    a.sin_addr.s_addr = htonl(0x7f000001);
    if (connect(fd, (struct sockaddr *) &a, sizeof a)) { int e = errno; close(fd); return -e; }
    write(fd, "secret", 6); close(fd); return 1;
}
int leak(int unused) {
    int fd = open(LEAK_PATH, O_CREAT | O_WRONLY, 0600);
    if (fd < 0) return -errno;
    write(fd, "leak", 4); close(fd); return 1;
}
'''.replace('LEAK_PATH', json.dumps(str(outside / 'leak.txt'))))
    fs = [dict(name=n, sourceName=n, file='native.c', params=['a'], paramIntegerTypes=['i32'],
               returnIntegerType='i32') for n in ('exfiltrate', 'leak')]
    library = native_c.compile_sources(source, fs, tmp_path / 'work')
    assert library.info['execution']['sandbox']['enforced'] is True
    assert library.info['execution']['sandboxed'] is True
    port = listener.getsockname()[1]
    assert library(fs[0])(port) < 0, 'native code connected to the listener'
    assert not _accepted(listener)
    assert library(fs[1])(0) < 0, 'native code wrote outside its work directory'
    assert not (outside / 'leak.txt').exists()


def test_opt_out_is_explicit_and_recorded(sandbox, monkeypatch, tmp_path):
    monkeypatch.setenv('AUTOFORM_SANDBOX', 'off')
    launch = sandbox.sandboxed(['true'], work=tmp_path / 'w')
    assert launch.argv == ['true']
    assert launch.record == dict(mechanism='off', enforced=False, network='unrestricted',
                                 filesystem='unrestricted', reason='AUTOFORM_SANDBOX=off')
    assert sandbox.report()['enforced'] is False
    assert 'AUTOFORM_SANDBOX_ACTIVE' not in launch.env


def test_no_mechanism_fails_by_default_and_names_what_to_install(sandbox, monkeypatch, tmp_path):
    monkeypatch.setattr(sandbox, '_probe', lambda mechanism: (None, 'probe disabled by the test'))
    with pytest.raises(sandbox.SandboxUnavailable) as err:
        sandbox.sandboxed(['true'], work=tmp_path / 'w')
    message = str(err.value)
    assert 'AUTOFORM_SANDBOX=off' in message
    assert ('bubblewrap' in message) if sys.platform == 'linux' else ('sandbox-exec' in message)
    record = sandbox.report()
    assert record['mechanism'] == 'none' and record['enforced'] is False and 'AUTOFORM_SANDBOX=off' in record['reason']


def test_unknown_policy_value_is_refused(sandbox, monkeypatch, tmp_path):
    monkeypatch.setenv('AUTOFORM_SANDBOX', 'maybe')
    with pytest.raises(ValueError):
        sandbox.sandboxed(['true'], work=tmp_path / 'w')


def test_a_launch_inside_the_sandbox_is_passed_through_and_reported_as_inherited(sandbox, monkeypatch, tmp_path):
    inner = dict(mechanism='seatbelt', enforced=True, network='denied', filesystem={'writable': ['/x']})
    monkeypatch.setenv('AUTOFORM_SANDBOX_ACTIVE', json.dumps(inner))
    launch = sandbox.sandboxed(['true'], work=tmp_path / 'w')
    assert launch.argv == ['true'] and launch.record == dict(inner, inherited=True)
    assert sandbox.report() == dict(inner, inherited=True)


def test_the_oracle_records_that_an_in_process_run_is_not_confined(tmp_path, differential, monkeypatch):
    """`differential.main()` entered in process (as this suite does) cannot re-execute
    itself; its report must say the oracle process was not confined rather than inherit a
    claim from the mechanism its drivers use."""
    monkeypatch.delenv('AUTOFORM_SANDBOX', raising=False)
    monkeypatch.delenv('AUTOFORM_SANDBOX_ACTIVE', raising=False)
    ast = tmp_path / 'ast.json'
    ast.write_text(json.dumps([dict(name='pkg.F', file='f.generated', params=[], body=dict(k='skip'))]))
    monkeypatch.setattr(differential, 'go_backend', lambda *a: ([], {}, {}))
    monkeypatch.setattr(differential, 'missing_tools', lambda *a: [])
    monkeypatch.setattr(differential.sys, 'argv',
                        ['differential.py', str(ast), str(tmp_path), 'Test', '3', '--language', 'go'])
    monkeypatch.chdir(tmp_path)
    assert differential.main() == 2
    report = json.loads((tmp_path / 'conformance.json').read_text())
    assert report['sandbox']['mechanism'] == 'none' and report['sandbox']['enforced'] is False
    assert 'command-line entry' in report['sandbox']['reason']


def test_the_oracle_refuses_without_a_mechanism_from_the_command_line(tmp_path, monkeypatch):
    """From its command-line entry the oracle re-executes itself under the sandbox; with
    no mechanism and no opt-out it refuses, loudly, and leaves a report that says so."""
    ast = tmp_path / 'ast.json'
    ast.write_text(json.dumps([dict(name='pkg.F', file='f.go', params=[], body=dict(k='skip'))]))
    env = dict(os.environ, AUTOFORM_SANDBOX='bwrap' if sys.platform == 'darwin' else 'seatbelt',
               PYTHONHASHSEED='0')
    env.pop('AUTOFORM_SANDBOX_ACTIVE', None)
    r = subprocess.run([sys.executable, os.path.join(SCRIPTS, 'differential.py'), str(ast), str(tmp_path),
                        'Test', '3', '--language', 'go'], cwd=tmp_path, env=env,
                       capture_output=True, text=True, timeout=300)
    assert r.returncode == 2 and 'REFUSING to run' in r.stdout, (r.stdout[-1500:], r.stderr[-1500:])
    report = json.loads((tmp_path / 'conformance.json').read_text())
    assert report['status'] == 'REFUSED: no sandbox'
    assert report['sandbox']['enforced'] is False and 'AUTOFORM_SANDBOX=off' in report['sandbox']['reason']
