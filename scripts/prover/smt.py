#!/usr/bin/env python3
"""Solver driver for the Autoform proof portfolio (STRATEGY.md §5, tier 2).

Reads an SMT-LIB2 problem on stdin, runs whichever solver is available, and prints
one line: `unsat`, `sat`, `unknown`, or `unavailable: <reason>`.

IMPORTANT — this script produces *evidence*, never a proof. `Portfolio.lean` never
assigns a goal from this output; an `unsat` verdict is recorded on an `Obligation`
as a solver's opinion. Reconstruction of a Lean proof from a solver certificate is
not implemented, so the obligation stays open by construction. Trusting this
process would be precisely the trusted-code leak `scripts/audit_all.py` exists to
catch.

Resolution order: `cvc5` binary, `z3` binary, then the `z3` Python module (the
binary on some machines is a snap shim that cannot solve).
"""
import subprocess
import sys
import shutil
import tempfile
import os


def try_binary(name, path):
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as f:
        f.write(problem)
        fn = f.name
    try:
        out = subprocess.run([name, fn], capture_output=True, text=True, timeout=30)
        txt = (out.stdout + out.stderr).strip().splitlines()
        for line in txt:
            line = line.strip()
            if line in ("unsat", "sat", "unknown"):
                return line
        return None
    except Exception:
        return None
    finally:
        os.unlink(fn)


def try_z3_module():
    try:
        import z3  # noqa
    except Exception as e:
        return None
    try:
        s = z3.Solver()
        s.from_string(problem)
        return str(s.check())
    except Exception:
        return None


problem = open(sys.argv[1]).read() if len(sys.argv) > 1 else sys.stdin.read()

for exe in ("cvc5", "z3"):
    if shutil.which(exe):
        r = try_binary(exe, shutil.which(exe))
        if r:
            print("%s (%s)" % (r, exe))
            sys.exit(0)

r = try_z3_module()
if r:
    print("%s (z3 python module)" % r)
    sys.exit(0)

print("unavailable: no working cvc5/z3 on this machine")
