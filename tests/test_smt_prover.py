"""`scripts/prover/smt.py` must tell "no solver" apart from "a solver that gave up".

The driver once caught every exception from the solver subprocess and returned None, so a
cvc5 that hit its 30 s budget was printed as `unavailable: no working cvc5/z3`. Lean records
that line verbatim on the open obligation, so the report said nothing had been tried when
something had been tried and found hard. `try_binary` also ignored the resolved path it was
handed and re-ran the bare name, so the name/path pair could disagree silently.
"""
import os
import stat
import subprocess
import sys
from pathlib import Path

import pytest

from conftest import SCRIPTS, load

SMT = Path(SCRIPTS) / "prover" / "smt.py"
PROBLEM = "(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n"


@pytest.fixture
def smt():
    return load(str(SMT), "af_smt_prover")


def fake_solver(directory: Path, name: str, body: str) -> Path:
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / name
    path.write_text("#!/bin/sh\n" + body + "\n")
    path.chmod(path.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
    return path


def no_z3_module(directory: Path) -> Path:
    """A `z3` package that refuses to import, so the module fallback is deterministic
    whether or not the real z3 is installed in this interpreter."""
    pkg = directory / "shim" / "z3"
    pkg.mkdir(parents=True)
    (pkg / "__init__.py").write_text("raise ImportError('z3 shimmed out for the test')\n")
    return pkg.parent


def test_sleeping_solver_is_timed_out_not_unavailable(tmp_path, smt):
    path = fake_solver(tmp_path / "bin", "cvc5", "exec sleep 30")
    verdict = smt.try_binary("cvc5", str(path), PROBLEM, timeout=0.5)
    assert verdict.startswith("timed out"), verdict
    assert "unavailable" not in verdict


def test_try_binary_runs_the_given_path_not_the_name(tmp_path, smt, monkeypatch):
    # Nothing called `cvc5` is on PATH; only the explicit path can answer.
    empty = tmp_path / "empty"
    empty.mkdir()
    monkeypatch.setenv("PATH", str(empty) + os.pathsep + "/bin" + os.pathsep + "/usr/bin")
    path = fake_solver(tmp_path / "elsewhere", "not-the-name", "echo unsat")
    assert smt.try_binary("cvc5", str(path), PROBLEM, timeout=5) == "unsat"


def test_crashing_solver_keeps_its_message(tmp_path, smt):
    path = fake_solver(tmp_path / "bin", "z3", "echo 'parse error at line 1' >&2; exit 1")
    verdict = smt.try_binary("z3", str(path), PROBLEM, timeout=5)
    assert verdict.startswith("error"), verdict
    assert "parse error at line 1" in verdict


def test_clean_exit_without_a_verdict_line_is_not_a_solver(tmp_path, smt):
    path = fake_solver(tmp_path / "bin", "cvc5", "echo 'usage: cvc5 [options]'")
    assert smt.try_binary("cvc5", str(path), PROBLEM, timeout=5) is None


def test_unexecutable_solver_reports_the_os_error(tmp_path, smt):
    path = tmp_path / "bin" / "cvc5"
    path.parent.mkdir()
    path.write_text("not a program")          # no execute bit
    verdict = smt.try_binary("cvc5", str(path), PROBLEM, timeout=5)
    assert verdict.startswith("error: could not run cvc5"), verdict


def test_driver_prints_timed_out_when_every_binary_times_out(tmp_path):
    bin_dir = tmp_path / "bin"
    fake_solver(bin_dir, "cvc5", "exec sleep 30")
    fake_solver(bin_dir, "z3", "exec sleep 30")
    env = dict(os.environ,
               PATH=str(bin_dir) + os.pathsep + os.environ.get("PATH", ""),
               PYTHONPATH=str(no_z3_module(tmp_path)),
               AUTOFORM_SMT_TIMEOUT="0.5")
    run = subprocess.run([sys.executable, str(SMT)], input=PROBLEM, env=env,
                         capture_output=True, text=True, timeout=60)
    # Exit 0: Portfolio.lean's runDriver discards stdout on a non-zero exit, and the
    # whole point is that the timeout text reaches the obligation record.
    assert run.returncode == 0, run.stderr
    line = run.stdout.strip()
    assert line.startswith("timed out"), line
    assert "cvc5" in line and "z3" in line and "unavailable" not in line


def test_driver_reports_unavailable_only_when_nothing_could_be_tried(tmp_path):
    empty = tmp_path / "empty"
    empty.mkdir()
    env = dict(os.environ,
               PATH=str(empty) + os.pathsep + "/bin" + os.pathsep + "/usr/bin",
               PYTHONPATH=str(no_z3_module(tmp_path)))
    run = subprocess.run([sys.executable, str(SMT)], input=PROBLEM, env=env,
                         capture_output=True, text=True, timeout=60)
    assert run.returncode == 0, run.stderr
    assert run.stdout.strip().startswith("unavailable:"), run.stdout


def test_driver_prefers_a_verdict_from_the_first_working_binary(tmp_path):
    bin_dir = tmp_path / "bin"
    fake_solver(bin_dir, "cvc5", "exec sleep 30")
    fake_solver(bin_dir, "z3", "echo sat")
    env = dict(os.environ,
               PATH=str(bin_dir) + os.pathsep + os.environ.get("PATH", ""),
               PYTHONPATH=str(no_z3_module(tmp_path)),
               AUTOFORM_SMT_TIMEOUT="0.5")
    run = subprocess.run([sys.executable, str(SMT)], input=PROBLEM, env=env,
                         capture_output=True, text=True, timeout=60)
    assert run.stdout.strip() == "sat (z3)", run.stdout
