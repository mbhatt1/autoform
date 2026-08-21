#!/usr/bin/env python3
"""check_specs.py — do the synthesised specification modules still elaborate?

They did not, and nothing noticed for weeks.

`Autoform/SpecsGen/*.lean` holds every theorem this repository claims about a translated
corpus — the 79 `Cachetools` theorems that were the headline number, plus the V8Base and
LinuxLib theorems added later. None of these modules was in the build. `lake build` was
green because the `Autoform` library's root is `Autoform.lean`, and `Autoform.lean` did
not import them; `audit_all.py` printed PASS because `leanchecker` replays the import
closure of `Autoform`, which did not include them either; and CI's proof-inventory step
counted theorems with `grep -c '^ *theorem '`, which counts *text*.

So the inventory floor was met by a file that had not type-checked since
`Autoform/SpecsGen/Basis.lean` changed shape underneath it. Three separate green signals,
none of them looking at the thing they were supposed to be about. That is the exact shape
this repository keeps re-learning: silence read as success.

`Autoform/SpecsGen/Basis.lean` is now imported from `Autoform.lean`, so it is kernel-
checked on every build. The corpus modules are too large to put in the gating build (a
single `lake env lean` on `SpecsGen/V8Base.lean` runs for well over ten minutes), so this
script is the check for them: it elaborates each one and reports, per module, whether it
proved, how many theorems it states, and what failed.

Failure is per-module and attributed. A module that cannot be found, or a module whose
`Autoform/Generated/<M>.lean` dependency is not built, is a FAILURE with that reason --
never a skip, and never an empty run that exits 0.

Usage:  scripts/check_specs.py [Module ...]      (default: every Autoform/SpecsGen/*.lean)
        scripts/check_specs.py --quick            (skip modules over --max-lines)
Exit:   0 every module elaborated; 1 a module failed; 2 there was nothing to check.
"""
from __future__ import annotations
import argparse, os, re, subprocess, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SPECS = os.path.join(ROOT, "Autoform", "SpecsGen")


def modules(names):
    if names:
        return list(names)
    if not os.path.isdir(SPECS):
        return []
    return sorted(f[:-5] for f in os.listdir(SPECS) if f.endswith(".lean"))


def theorem_count(path):
    """Text count. Deliberately NOT the check -- it is the number this script exists to
    stop anyone from trusting on its own. Reported only alongside an elaboration verdict."""
    return len(re.findall(r'^\s*theorem ', open(path).read(), re.M))


def elaborate(mod, timeout):
    path = os.path.join(SPECS, mod + ".lean")
    if not os.path.exists(path):
        return "MISSING", 0, "no such module: %s" % path, 0.0
    n = theorem_count(path)
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    t0 = time.time()
    try:
        r = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True,
                           cwd=ROOT, env=env, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "TIMEOUT", n, ("did not finish in %ds -- this is not a pass; raise "
                              "--timeout or split the module" % timeout), time.time() - t0
    dt = time.time() - t0
    if r.returncode == 0:
        return "OK", n, "", dt
    errs = [l for l in (r.stdout + r.stderr).splitlines() if ": error: " in l]
    # A failed proof becomes `sorryAx`, and the module's own `#print axioms` lines then
    # report it as a trusted-code leak. Those are consequences, not causes; separate them
    # so the reason shown is the first real elaboration error.
    leaks = [l for l in errs if "TRUSTED-CODE LEAK" in l]
    real = [l for l in errs if "TRUSTED-CODE LEAK" not in l]
    why = "%d elaboration error(s)%s\n      first: %s" % (
        len(real), " and %d downstream sorryAx leak(s)" % len(leaks) if leaks else "",
        (real or leaks or ["(no error line parsed -- see the raw output)"])[0][:200])
    if not real and not leaks:
        why = "lean exited %d with no parseable error line: %s" % (
            r.returncode, (r.stdout + r.stderr)[-300:].replace("\n", " "))
    return "FAIL", n, why, dt


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("modules", nargs="*")
    ap.add_argument("--timeout", type=int, default=5400)
    ap.add_argument("--quick", action="store_true",
                    help="skip modules over --max-lines; the skip is REPORTED and the "
                         "exit code says the run was partial")
    ap.add_argument("--max-lines", type=int, default=1000)
    a = ap.parse_args()

    mods = modules(a.modules)
    if not mods:
        print("check_specs: nothing to check -- %s holds no .lean module. If the "
              "specification modules were removed, that is a regression, not a pass."
              % SPECS)
        return 2

    rows, bad, skipped = [], 0, []
    for m in mods:
        p = os.path.join(SPECS, m + ".lean")
        if a.quick and os.path.exists(p) and sum(1 for _ in open(p)) > a.max_lines:
            skipped.append(m); continue
        st, n, why, dt = elaborate(m, a.timeout)
        rows.append((m, st, n, why, dt))
        if st != "OK": bad += 1
        print("%-8s %-16s %4d theorems  %5.0fs%s"
              % (st, m, n, dt, ("\n      " + why) if why else ""))

    total = sum(n for _, st, n, _, _ in rows if st == "OK")
    print("\ncheck_specs: %d/%d module(s) elaborated; %d theorem(s) are in modules that "
          "actually proved." % (len(rows) - bad, len(rows), total))
    if skipped:
        print("PARTIAL: %d module(s) skipped by --quick (%s). A skipped module is "
              "UNCHECKED, not passing." % (len(skipped), ", ".join(skipped)))
    if bad:
        print("A module that does not elaborate states no theorems, whatever `grep -c "
              "theorem` says about it.")
    return 1 if (bad or skipped) else 0


if __name__ == "__main__":
    sys.exit(main())
