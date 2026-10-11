#!/usr/bin/env python3
"""rust_aeneas.py -- differential oracle for Rust via Charon + Aeneas (EXPERIMENTAL).

No Rust parser is written here. Charon extracts the crate to LLBC, Aeneas emits Lean,
and this script runs the REAL Rust function natively (a generated cargo harness binary)
and `#eval`s the Aeneas-emitted Lean function on the same integer inputs. Any
disagreement is a divergence. See docs/rust.md for what is and is not modelled.

The Aeneas Lean library needs its own toolchain (Lean + mathlib), so the Lean side runs in
a SCRATCH Lake project (--lean-project), never in Autoform's project; Autoform's
lean-toolchain and lakefile are untouched. Only integer inputs and outputs are supported.

Mapping assumptions (each is reported in conformance.json under "assumptions"):
  * Rust panic (overflow in a debug build, division by zero, ...)  <->  Aeneas `fail`.
  * Aeneas `div` (non-termination marker) is INCONCLUSIVE, never agreement.
  * The Rust harness is built with the chosen profile (default debug = overflow checks ON,
    which is what Aeneas models). --profile release wraps on `+` and is EXPECTED to diverge
    from Aeneas on overflowing inputs; that is how the assumption is tested.

Usage: rust_aeneas.py --crate DIR --lean-project DIR [--out DIR] [--profile debug|release]
Env:   AENEAS_HOME = dir holding `aeneas`, `charon`, `charon-driver` (else PATH).
Exit:  0 no divergence and everything conclusive; 1 divergence; 2 tool missing/inconclusive.
"""
from __future__ import annotations
import argparse, json, os, random, shutil, subprocess, sys, tempfile

INT = {}
for _b in (8, 16, 32, 64):
    INT["u%d" % _b] = (0, 2 ** _b - 1)
    INT["i%d" % _b] = (-2 ** (_b - 1), 2 ** (_b - 1) - 1)
INT["usize"] = INT["u64"]; INT["isize"] = INT["i64"]   # arm64/x86_64 only


def tool(name):
    home = os.environ.get("AENEAS_HOME")
    if home and os.access(os.path.join(home, name), os.X_OK):
        return os.path.join(home, name)
    return shutil.which(name)


def missing():
    """Names of absent prerequisites (used by the test for a NAMED skip reason)."""
    out = [n for n in ("cargo", "charon", "aeneas", "lake") if not tool(n) and not shutil.which(n)]
    return out


def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def cases_for(types, rng, cap=60, nrand=60):
    def bound(t):
        lo, hi = INT[t]
        s = {lo, hi, 0, 1, 2, 7, hi - 1, lo + 1, -1, hi // 2, lo // 2, 255, 256, 65535, 65536}
        return sorted(v for v in s if lo <= v <= hi)
    import itertools
    full = list(itertools.product(*[bound(t) for t in types]))
    if len(full) > cap:
        full = rng.sample(full, cap)
    rand = [tuple(rng.randint(*INT[t]) for t in types) for _ in range(nrand)]
    seen, out = set(), []
    for c in full + rand:
        if c not in seen:
            seen.add(c); out.append(c)
    return out


def harness_source(spec):
    arms = []
    for f in spec["functions"]:
        args = []
        for i, t in enumerate(f["args"]):
            args.append("p[%d].parse::<%s>().unwrap()" % (i + 1, t))
        arms.append('        "%s" => std::panic::catch_unwind(|| %s::%s(%s).to_string()),'
                    % (f["name"], spec["crate"], f["name"], ", ".join(args)))
    return """use std::io::BufRead;
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    for line in std::io::stdin().lock().lines() {
        let line = line.unwrap();
        let p: Vec<&str> = line.split(' ').collect();
        let r = match p[0] {
%s
            _ => panic!("unknown function"),
        };
        match r { Ok(v) => println!("ok {}", v), Err(_) => println!("panic") }
    }
}
""" % "\n".join(arms)


def lean_eval_source(spec, cases):
    lines = ["import %s" % spec["module"], "open Aeneas Aeneas.Std %s" % spec["namespace"],
             "def rs {α} (f : α → String) (r : Aeneas.Std.Result α) : String :=",
             "  match Aeneas.Std.Result.match r with",
             '  | .ok v => "ok " ++ f v',
             '  | .div => "div"',
             '  | .vis _ _ => "fail"'
]
    ty = lambda t: "Std.%s%s" % ("U" if t[0] == "u" else "I", t[1:].upper() if t[1:] != "size" else "size")
    lit = lambda v, t: ("(%d)#%s" % (v, t))
    for f, args in cases:
        fn = next(x for x in spec["functions"] if x["name"] == f)
        a = " ".join(lit(v, t) for v, t in zip(args, fn["args"]))
        lines.append('#eval IO.println (rs (fun (v : %s) => toString v.val) (%s %s))'
                     % (ty(fn["ret"]), f, a))
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--crate", required=True)
    ap.add_argument("--lean-project", required=True)
    ap.add_argument("--out", default=".")
    ap.add_argument("--profile", choices=["debug", "release"], default="debug")
    ap.add_argument("--seed", type=int, default=20261010)
    a = ap.parse_args()
    out = os.path.abspath(a.out); os.makedirs(out, exist_ok=True)
    lp = os.path.abspath(a.lean_project)
    gone = missing()
    if gone:
        print("rust_aeneas: INCONCLUSIVE, missing prerequisites: %s" % ", ".join(gone)); return 2
    spec = json.load(open(os.path.join(a.crate, "aeneas_oracle.json")))
    work = tempfile.mkdtemp(prefix="rust_aeneas_")
    crate = os.path.join(work, "crate"); shutil.copytree(a.crate, crate)
    charon, aeneas = tool("charon"), tool("aeneas")
    env = dict(os.environ)
    if os.environ.get("AENEAS_HOME"):
        env["PATH"] = os.environ["AENEAS_HOME"] + os.pathsep + env["PATH"]
    llbc = os.path.join(work, spec["crate"] + ".llbc")   # aeneas names the module after this file
    r = run([charon, "cargo", "--preset=aeneas", "--dest-file", llbc], cwd=crate, env=env)
    if r.returncode or not os.path.exists(llbc):
        print("rust_aeneas: charon failed\n" + r.stderr[-2000:]); return 2
    leandir = os.path.join(work, "lean"); os.makedirs(leandir)
    r = run([aeneas, "-backend", "lean", llbc, "-dest", leandir], env=env)
    gen = os.path.join(leandir, spec["module"] + ".lean")
    if r.returncode or not os.path.exists(gen):
        print("rust_aeneas: aeneas failed\n" + r.stdout[-2000:] + r.stderr[-2000:]); return 2
    shutil.copy(gen, os.path.join(lp, spec["module"] + ".lean"))
    lake_file = os.path.join(lp, "lakefile.lean")
    if "lean_lib «%s»" % spec["module"] not in open(lake_file).read():
        open(lake_file, "a").write("\nlean_lib «%s» {}\n" % spec["module"])
    r = run(["lake", "build", spec["module"]], cwd=lp, env=env)
    if r.returncode:
        print("rust_aeneas: lake build of the Aeneas output failed (is Aeneas built in %s?)\n%s"
              % (lp, (r.stdout + r.stderr)[-2000:])); return 2

    rng = random.Random(a.seed)
    cases = []
    for f in spec["functions"]:
        cases += [(f["name"], c) for c in cases_for(f["args"], rng)]
    # real Rust side
    hdir = os.path.join(work, "harness"); os.makedirs(os.path.join(hdir, "src"))
    open(os.path.join(hdir, "Cargo.toml"), "w").write(
        '[package]\nname="harness"\nversion="0.0.0"\nedition="2021"\n'
        '[dependencies]\n%s={path="%s"}\n' % (spec["crate"], crate))
    open(os.path.join(hdir, "src", "main.rs"), "w").write(harness_source(spec))
    # the harness must be built by the default (not charon's) toolchain
    benv = {k: v for k, v in env.items() if not k.startswith("RUSTUP_TOOLCHAIN")}
    flags = ["--release"] if a.profile == "release" else []
    r = run(["cargo", "build", "-q"] + flags, cwd=hdir, env=benv)
    if r.returncode:
        print("rust_aeneas: cargo harness build failed\n" + r.stderr[-2000:]); return 2
    exe = os.path.join(hdir, "target", a.profile if a.profile == "release" else "debug", "harness")
    inp = "".join("%s %s\n" % (f, " ".join(map(str, c))) for f, c in cases)
    rust = run([exe], input=inp).stdout.splitlines()
    # Lean side
    open(os.path.join(lp, "OracleEval.lean"), "w").write(lean_eval_source(spec, cases))
    r = run(["lake", "env", "lean", "OracleEval.lean"], cwd=lp, env=env)
    lean = r.stdout.splitlines()
    if len(rust) != len(cases) or len(lean) != len(cases):
        print("rust_aeneas: INCONCLUSIVE: %d cases, %d rust lines, %d lean lines\n%s"
              % (len(cases), len(rust), len(lean), r.stdout[-1500:] + r.stderr[-500:])); return 2

    agree = div = inconclusive = 0; detail = []
    for (f, c), rv, lv in zip(cases, rust, lean):
        rn = "fail" if rv == "panic" else rv        # assumption: Rust panic <-> Aeneas fail
        if lv == "div":
            inconclusive += 1; continue
        if rn == lv:
            agree += 1
        else:
            div += 1
            detail.append({"function": f, "args": list(c), "rust": rv, "lean": lv,
                           "detail": "rust=%s aeneas=%s" % (rv, lv)})
    def ver(cmd, **kw):
        x = run(cmd, **kw); return (x.stdout or x.stderr).strip()
    adir = os.environ.get("AENEAS_HOME")
    result = {
        "language": "rust", "experimental": True, "oracle": "rust-native vs aeneas-lean #eval",
        "crate": spec["crate"], "profile": a.profile, "seed": a.seed,
        "agree": agree, "total": agree + div, "divergences": div,
        "inconclusive": inconclusive, "cases_generated": len(cases),
        "functions": [f["name"] for f in spec["functions"]],
        "divergence_detail": detail,
        "assumptions": [
            "Rust panic <-> Aeneas `fail` (any error kind); not distinguished",
            "Aeneas `div` is counted inconclusive, never agreement",
            "debug profile: overflow checks on (what Aeneas models); release wraps and is "
            "expected to diverge on overflowing `+`",
            "integer arguments/results only; inputs = boundary values + seeded random"],
        "provenance": {
            "charon": ver([charon, "version"], env=env),
            "aeneas": ver([aeneas, "-version"], env=env),
            "rustc_harness": ver(["rustc", "-vV"], env=benv).splitlines()[0:2],
            "rust_toolchain_charon": (open(os.path.join(adir, "rust-toolchain")).read().split("channel")[1].split('"')[1]
                                      if adir and os.path.exists(os.path.join(adir, "rust-toolchain")) else "unknown"),
            "lean_toolchain": open(os.path.join(lp, "lean-toolchain")).read().strip(),
            "lean_version": ver(["lake", "env", "lean", "--version"], cwd=lp, env=env),
        },
    }
    json.dump(result, open(os.path.join(out, "conformance.json"), "w"), indent=1)
    for d in detail[:10]:
        print("DIVERGENCE %s%s: %s" % (d["function"], tuple(d["args"]), d["detail"]))
    print("rust_aeneas [%s]: %d/%d cases agree, %d divergences, %d inconclusive"
          % (a.profile, agree, agree + div, div, inconclusive))
    shutil.rmtree(work, ignore_errors=True)
    return 1 if div else (2 if inconclusive else 0)


if __name__ == "__main__":
    sys.exit(main())
