"""`scripts/audit_all.py` runs the kernel replay through `lake env`, which starts
`leanchecker` as its own child. A timeout has to kill that grandchild too: with plain
`subprocess.run` it did not, and a 4-6 GB replay kept running, unreported, after the audit
had already printed "leanchecker timed out"."""
import importlib.util
import os
import subprocess
import sys
import time

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _load():
    spec = importlib.util.spec_from_file_location(
        "audit_all_under_test", os.path.join(ROOT, "scripts", "audit_all.py"))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def _alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    # a zombie (killed, not yet reaped by init) is not running
    try:
        with open(f"/proc/{pid}/stat") as fh:
            return fh.read().rsplit(")", 1)[1].split()[0] != "Z"
    except (FileNotFoundError, ProcessLookupError):
        return False


def _grandchild_cmd(pidfile):
    # the shell stands for `lake env`; the backgrounded sleep for `leanchecker`
    return ["sh", "-c", f"sleep 300 & echo $! > {pidfile}; wait"]


def _wait_dead(pid, seconds=5.0):
    end = time.time() + seconds
    while time.time() < end:
        if not _alive(pid):
            return True
        time.sleep(0.05)
    return not _alive(pid)


@pytest.mark.skipif(not sys.platform.startswith("linux"), reason="reads /proc")
def test_timeout_kills_the_grandchild_too(tmp_path):
    audit = _load()
    pidfile = tmp_path / "pid"
    with pytest.raises(subprocess.TimeoutExpired):
        audit.run_in_group(_grandchild_cmd(pidfile), timeout=1)
    pid = int(pidfile.read_text())
    assert _wait_dead(pid), "the grandchild outlived the timeout: a leaked leanchecker"


@pytest.mark.skipif(not sys.platform.startswith("linux"), reason="reads /proc")
def test_plain_subprocess_run_does_leak_the_grandchild(tmp_path):
    """The behaviour being fixed, reconstructed: this is what the audit did."""
    pidfile = tmp_path / "pid"
    with pytest.raises(subprocess.TimeoutExpired):
        subprocess.run(_grandchild_cmd(pidfile), capture_output=True, text=True, timeout=1)
    pid = int(pidfile.read_text())
    try:
        assert _alive(pid), "expected the old code path to leak the grandchild"
    finally:
        try:
            os.kill(pid, 9)
        except ProcessLookupError:
            pass


def test_run_in_group_returns_a_completed_process():
    audit = _load()
    r = audit.run_in_group(["sh", "-c", "echo out; echo err >&2; exit 3"], timeout=10)
    assert (r.returncode, r.stdout.strip(), r.stderr.strip()) == (3, "out", "err")


def test_timeout_is_configurable_and_the_message_says_how():
    src = open(os.path.join(ROOT, "scripts", "audit_all.py")).read()
    assert "AUTOFORM_LEANCHECKER_TIMEOUT" in src and "timed out after" in src
