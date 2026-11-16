#!/usr/bin/env python3
"""Solver driver for the Autoform proof portfolio (STRATEGY.md §5, tier 2).

Reads an SMT-LIB2 problem on stdin (or from the file named by argv[1]), runs whichever
solver is available, and prints one line. The first word is the outcome:

    unsat / sat / unknown   a verdict, followed by the solver that gave it
    timed out               a solver exists but gave no answer within the budget
    no verdict              a solver exists but crashed, or printed no verdict line
    unavailable             no cvc5/z3 binary and no z3 Python module

The distinction matters: `unavailable` says nothing was tried, `timed out` says the
problem was tried and is hard (or the budget is wrong). A driver that reported both as
"no working solver" once hid a 30 s timeout behind a missing-binary message.

IMPORTANT — this script produces *evidence*, never a proof. `Portfolio.lean` never
assigns a goal from this output; an `unsat` verdict is recorded on an `Obligation`
as a solver's opinion. Reconstruction of a Lean proof from a solver certificate is
not implemented, so the obligation stays open by construction. Trusting this
process would be precisely the trusted-code leak `scripts/audit_all.py` exists to
catch.

Resolution order: `cvc5` binary, `z3` binary, then the `z3` Python module (the
binary on some machines is a snap shim that cannot solve). The per-solver budget is
`AUTOFORM_SMT_TIMEOUT` seconds (default 30); it also bounds the Python module.
"""
import os
import shutil
import subprocess
import sys
import tempfile

VERDICTS = ("unsat", "sat", "unknown")
DEFAULT_TIMEOUT_S = 30.0


def solver_timeout():
    raw = os.environ.get("AUTOFORM_SMT_TIMEOUT")
    try:
        return float(raw) if raw else DEFAULT_TIMEOUT_S
    except ValueError:
        return DEFAULT_TIMEOUT_S


def try_binary(name, path, problem, timeout=DEFAULT_TIMEOUT_S):
    """Run the solver executable at `path` (reported as `name`) on `problem`.

    Returns a verdict from VERDICTS; `"timed out after Ns"` when the process was still
    running at the deadline; `"error: ..."` when it could not be executed or exited
    non-zero without a verdict (the message is kept, not swallowed); or None when it
    exited cleanly but printed no verdict line, i.e. it is not a working solver for
    this input. Anything else propagates -- an unexpected failure in the driver is a
    bug to see, not an "unavailable" to shrug at.
    """
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as f:
        f.write(problem)
        fn = f.name
    try:
        try:
            out = subprocess.run([path, fn], capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return "timed out after %gs" % timeout
        except OSError as e:
            return "error: could not run %s: %s" % (name, e)
        for line in (out.stdout + out.stderr).strip().splitlines():
            line = line.strip()
            if line in VERDICTS:
                return line
        if out.returncode != 0:
            tail = (out.stderr or out.stdout).strip().splitlines()
            return "error: %s exited %d%s" % (name, out.returncode,
                                              (": " + tail[-1]) if tail else "")
        return None
    finally:
        os.unlink(fn)


def try_z3_module(problem, timeout=DEFAULT_TIMEOUT_S):
    """The z3 Python module, if importable. Same return convention as `try_binary`;
    the module's own timeout turns an over-budget check into `unknown`."""
    try:
        import z3  # noqa: F401
    except ImportError:
        return None
    try:
        s = z3.Solver()
        s.set("timeout", int(timeout * 1000))
        s.from_string(problem)
        return str(s.check())
    except Exception as e:                                     # noqa: BLE001
        return "error: z3 python module: %s" % e


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    problem = open(argv[0]).read() if argv else sys.stdin.read()
    timeout = solver_timeout()
    problems = []   # solvers that were tried and gave no verdict, with why

    for exe in ("cvc5", "z3"):
        path = shutil.which(exe)
        if not path:
            continue
        r = try_binary(exe, path, problem, timeout)
        if r in VERDICTS:
            print("%s (%s)" % (r, exe))
            return 0
        if r is not None:
            problems.append("%s: %s" % (exe, r))

    r = try_z3_module(problem, timeout)
    if r in VERDICTS:
        note = ("; " + "; ".join(problems)) if problems else ""
        print("%s (z3 python module)%s" % (r, note))
        return 0
    if r is not None:
        problems.append(r)

    if problems:
        if all("timed out" in p for p in problems):
            print("timed out (%s)" % "; ".join(problems))
        else:
            print("no verdict (%s)" % "; ".join(problems))
        return 0
    print("unavailable: no working cvc5/z3 on this machine")
    return 0


if __name__ == "__main__":
    sys.exit(main())
