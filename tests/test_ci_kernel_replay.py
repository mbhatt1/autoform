"""The independent kernel replay (`leanchecker --fresh Autoform`) takes hours, so CI runs it
as its own job and the build job's audit says it did NOT run it. That split is only honest
if neither half can be dropped silently: delete the `kernel-replay` job and the build job
would still print PASS. These tests pin both halves, and the audit's behaviour in each mode."""
import importlib.util
import json
import os
import re
import sys

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CI = os.path.join(ROOT, ".github", "workflows", "ci.yml")


def _jobs():
    """{job name: its text} for the top-level jobs of ci.yml (no YAML dependency)."""
    text = open(CI).read()
    body = text.split("\njobs:\n", 1)[1]
    parts = re.split(r"(?m)^  ([a-z][a-z0-9-]*):\s*$", body)
    return {parts[i]: parts[i + 1] for i in range(1, len(parts) - 1, 2)}


def _run_lines(job):
    return [l.strip() for l in job.splitlines() if l.strip().startswith("run:")]


def test_the_build_job_delegates_the_kernel_replay_explicitly():
    build = _jobs()["build-and-audit"]
    audits = [l for l in _run_lines(build) if "audit_all.py" in l]
    assert audits == ["run: python3 scripts/audit_all.py --strict --skip-kernel"], audits


def test_a_kernel_replay_job_exists_runs_strictly_and_waits_for_the_build():
    jobs = _jobs()
    assert "kernel-replay" in jobs, (
        "the build job skips the kernel replay on the promise that this job runs it")
    job = jobs["kernel-replay"]
    assert "needs: build-and-audit" in job
    assert [l for l in _run_lines(job) if "audit_all.py" in l] == [
        "run: python3 scripts/audit_all.py --kernel-only --strict"]
    m = re.search(r"timeout-minutes:\s*(\d+)", job)
    assert m and 120 <= int(m.group(1)) <= 360, "hours-long job needs a real budget (<= 360)"
    assert "fail-on-cache-miss: true" in job, (
        "without the build job's .lake this job would silently become a second build")


def _audit():
    spec = importlib.util.spec_from_file_location(
        "audit_all_modes", os.path.join(ROOT, "scripts", "audit_all.py"))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


CLEAN_AXIOMS = {"status": "OK", "leaks": [], "declarations": 7, "declared_axioms": [],
                "nonstandard_axioms": [], "axiom_histogram": {}}


def test_skip_kernel_is_reported_as_delegated_not_as_a_pass(tmp_path, monkeypatch, capsys):
    a = _audit()
    monkeypatch.setattr(a, "axiom_sweep", lambda: dict(CLEAN_AXIOMS))
    monkeypatch.setattr(a, "lean4checker", lambda **k: pytest.fail("replay must not run"))
    out = tmp_path / "audit.json"
    monkeypatch.setattr(sys, "argv", ["audit_all.py", "--strict", "--skip-kernel", "-o", str(out)])
    rc = a.main()
    text = capsys.readouterr().out
    report = json.loads(out.read_text())
    assert rc == 0
    assert report["lean4checker"]["status"] == "DELEGATED"
    assert "kernel replay was NOT run here" in text
    assert "VERDICT: PASS (no trusted-code leak)\n" not in text


def test_kernel_only_runs_the_replay_and_skips_the_axiom_sweep(tmp_path, monkeypatch, capsys):
    a = _audit()
    monkeypatch.setattr(a, "axiom_sweep", lambda: pytest.fail("axiom sweep must not run"))
    monkeypatch.setattr(a, "lean4checker", lambda **k: {
        "status": "VERIFIED", "available": True, "command": "leanchecker", "returncode": 0,
        "detail": "replayed"})
    out = tmp_path / "audit.json"
    monkeypatch.setattr(sys, "argv", ["audit_all.py", "--strict", "--kernel-only", "-o", str(out)])
    assert a.main() == 0
    report = json.loads(out.read_text())
    assert report["lean4checker"]["status"] == "VERIFIED"
    assert report["axiom_sweep"]["status"] == "SKIPPED"


def test_a_failed_replay_still_fails_the_audit(tmp_path, monkeypatch):
    a = _audit()
    monkeypatch.setattr(a, "lean4checker", lambda **k: {
        "status": "FAILED", "available": True, "command": "leanchecker", "returncode": 1,
        "stdout": "", "stderr": "rejected", "detail": "REJECTED"})
    monkeypatch.setattr(sys, "argv", ["audit_all.py", "--strict", "--kernel-only",
                                      "-o", str(tmp_path / "a.json")])
    assert a.main() != 0


def test_the_two_modes_are_opposites(monkeypatch):
    a = _audit()
    monkeypatch.setattr(sys, "argv", ["audit_all.py", "--skip-kernel", "--kernel-only"])
    with pytest.raises(SystemExit) as e:
        a.main()
    assert e.value.code == 2
