#!/usr/bin/env python3
"""rust_regress.py -- Rust behaviour regressions between two revisions of one crate.

The Rust path (rust_aeneas.py, docs/rust.md) checks the native code against the Aeneas model
of the SAME revision. This leg carries that model across a commit:

  1. base model   rust_aeneas.py on the BASE tree: the ledger, the oracle (native vs Aeneas
                  `#eval`) and every oracle case with both results (`--cases-out`).
  2. inputs       those cases (model-backed functions), plus seeded boundary/random inputs
                  for every public function that is NOT translated (a hole) but whose
                  signature the harness encodes exactly (native-only: no model).
  3. signatures   rustdoc at both revisions; a function is replayed at HEAD only when the same
                  callee exists there with the same encoded signature. Anything else is listed
                  (removed, signature changed, unencodable at head, added) and never compared.
  4. native runs  one harness per revision, the same inputs in the same order:
                    base     the base tree, rebuilt here
                    control  the base tree AGAIN, from a separate copy and target directory
                    head     the head tree
  5. verdicts     per case, with the classifier applied to the control exactly as to head:
                    regression        base native agreed with the base model, head does not
                    behaviour-change  head native differs from base native where no model
                                      verdict exists (native-only function, model `div`, or a
                                      case where base already diverged from its model)
                    unchanged / inconclusive (with the reason)
                  A case the control flags, or whose base rebuild differs from the result the
                  base model run recorded, is UNSTABLE: excluded from every verdict and listed.

Same discipline as the Rust oracle: debug profile, any panic == any panic (kinds are not
compared), Aeneas `div` gives no model verdict, nothing is compared unless both revisions are
called on the same inputs with the same types.

Usage:
  rust_regress.py --base DIR --head DIR --out DIR [--lean-project LP] [--module M]
                  [--seed N] [--cases N] [--random N] [--base-label S] [--head-label S]
Exit: 0 no regression and no behaviour change; 1 at least one; 2 refused (a tool, the base
model run, a build, or the control failed).
"""
from __future__ import annotations

import argparse
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rust_aeneas as ra  # noqa: E402
from rust_aeneas import RustPathError  # noqa: E402

EXAMPLES = 5


def canon(ty):
    """Encoded types as JSON (tuples -> lists), so recorded and fresh signatures compare."""
    return json.loads(json.dumps(ty))


def signatures(doc):
    """rustdoc -> {callee: ((arg types, ret type) | None, reason, display name)}"""
    funcs, _ = ra.public_functions(doc)
    out = {}
    for f in funcs:
        name = ra.display_name(f, doc)
        try:
            callee = ra.rust_callee(f, doc)
        except (ValueError, KeyError) as exc:
            out["?" + name] = (None, "no callable path: %s" % exc, name)
            continue
        try:
            args, ret = ra.oracle_signature(f)
            out[callee] = ([canon(args), canon(ret)], None, name)
        except (ra.Unencodable, ValueError) as exc:
            out[callee] = (None, str(exc), name)
    return out


def cargo_library_at(repo, ref, subdir=None):
    """Whether the tree of commit `ref` (or its `subdir`) in a local checkout is a Cargo
    library package: a Cargo.toml with `[package]`, and `src/lib.rs` or a `[lib]` table.
    The same test `autoform regress --lang auto` makes (`_cargo_library_at` in the CLI),
    read with git; pr mode asks it of the base revision before it runs the leg here."""
    prefix = (subdir.strip("/") + "/") if subdir and subdir.strip("/") not in ("", ".") else ""
    try:
        shown = subprocess.run(["git", "-C", str(repo), "show", "%s:%sCargo.toml" % (ref, prefix)],
                               capture_output=True, text=True, timeout=60)
        if shown.returncode or not re.search(r"^\s*\[package\]", shown.stdout, re.M):
            return False
        lib = subprocess.run(["git", "-C", str(repo), "cat-file", "-e", "%s:%ssrc/lib.rs" % (ref, prefix)],
                             capture_output=True, timeout=60)
    except (OSError, subprocess.SubprocessError):
        return False
    return lib.returncode == 0 or bool(re.search(r"^\s*\[lib\]", shown.stdout, re.M))


def spans(doc, crate):
    """rustdoc -> {display name: {file, begin_line, end_line}}: where every public
    function lives, `file` relative to the crate root (`crate`, the tree rustdoc ran on),
    so pr mode can tell which of them a change touched."""
    funcs, _ = ra.public_functions(doc)
    out = {}
    for f in funcs:
        span = f.get("span") or {}
        name = span.get("filename")
        if name and os.path.isabs(name):
            rel = os.path.relpath(os.path.realpath(name), os.path.realpath(crate))
            name = None if rel.startswith("..") else rel
        out[ra.display_name(f, doc)] = {
            "file": name.replace(os.sep, "/") if name else None,
            "begin_line": (span.get("begin") or [0, 0])[0],
            "end_line": (span.get("end") or [0, 0])[0],
        }
    return out


def classify(case, base, other):
    """One case: base = base native result, other = the replay being judged (control or
    head). -> (verdict, reason)"""
    if other is None:
        return "inconclusive", "no native result"
    if base is None:
        return "inconclusive", "no base native result"
    model = case.get("aeneas")
    if case["evidence"] == "model" and model is not None and model != "div":
        bv, _ = ra.compare(base, model)
        hv, why = ra.compare(other, model)
        if bv == "agree":
            if hv == "agree":
                return "unchanged", None
            if hv == "diverge":
                return "regression", None
            return "inconclusive", why
    if other == base:
        return "unchanged", None
    return "behaviour-change", None


def prepare(label, src, work, env, toolchain, need_doc=True):
    """Copy a tree, fetch its dependencies (network, no crate code runs), read its metadata
    and (optionally) its rustdoc. -> dict(crate, meta, doc, offline, writable)"""
    root = os.path.join(work, label)
    crate = os.path.join(root, "crate")
    shutil.copytree(src, crate, ignore=shutil.ignore_patterns("target", ".git"))
    cenv = dict(env, RUSTUP_TOOLCHAIN=toolchain, CARGO_TARGET_DIR=os.path.join(root, "target"))
    r = ra.run(["cargo", "fetch", "--manifest-path", os.path.join(crate, "Cargo.toml")], env=cenv, timeout=900)
    if r.returncode:
        raise RustPathError("cargo-fetch-failed", "%s: cargo fetch failed: %s" % (label, ra.first_line(r.stderr)))
    meta = ra.cargo_metadata(crate, env, toolchain)
    offline = dict(cenv, CARGO_NET_OFFLINE="true")
    cargo_home = os.path.realpath(env.get("CARGO_HOME") or os.path.join(os.path.expanduser("~"), ".cargo"))
    writable = [cargo_home, work]
    doc = ra.rustdoc_json(crate, work, offline, writable, meta)[0] if need_doc else None
    return dict(root=root, crate=crate, meta=meta, doc=doc, offline=offline, writable=writable)


def native(tree, cases, work, env):
    if not cases:
        return {}, {}, None
    return ra.native_results([(c["callee"], [ra.rust_lit(t, x) for t, x in zip(c["arg_types"], c["args"])])
                              for c in cases], tree["crate"], tree["meta"], os.path.join(tree["root"], "harness"),
                             work, env, tree["offline"], tree["writable"])


def main(argv=None):
    ap = argparse.ArgumentParser(description="Rust regressions across two revisions of a crate")
    ap.add_argument("--base", required=True, help="the crate directory at the base revision")
    ap.add_argument("--head", required=True, help="the crate directory at the head revision")
    ap.add_argument("--out", required=True)
    ap.add_argument("--lean-project", default=os.environ.get("AUTOFORM_RUST_LEAN_PROJECT"))
    ap.add_argument("--module", default=None)
    ap.add_argument("--seed", type=int, default=20261010)
    ap.add_argument("--cases", type=int, default=60)
    ap.add_argument("--random", type=int, default=40)
    ap.add_argument("--base-label", default="base")
    ap.add_argument("--head-label", default="head")
    ap.add_argument("--keep-work", action="store_true")
    a = ap.parse_args(argv)
    out = os.path.abspath(a.out)
    os.makedirs(out, exist_ok=True)
    for name in ("rust-regression.json", "rust-regression.md", "rust-regress-error.json"):
        if os.path.exists(os.path.join(out, name)):
            os.remove(os.path.join(out, name))
    try:
        return run(a, out)
    except RustPathError as exc:
        with open(os.path.join(out, "rust-regress-error.json"), "w") as fh:
            json.dump(exc.record(), fh, indent=1)
        print("rust_regress: %s: %s" % (exc.name, exc.message), file=sys.stderr)
        if exc.hint:
            print("  hint: " + exc.hint, file=sys.stderr)
        return 2


def run(a, out):
    t0 = time.time()
    env = dict(os.environ)
    if env.get("AENEAS_HOME"):
        env["PATH"] = env["AENEAS_HOME"] + os.pathsep + env.get("PATH", "")
    for side in (a.base, a.head):
        if not os.path.isfile(os.path.join(side, "Cargo.toml")):
            raise RustPathError("not-a-crate", "%s has no Cargo.toml" % side)

    # 1. the base model and its oracle cases
    base_out = os.path.join(out, "base-model")
    cases_path = os.path.join(base_out, "rust-cases.json")
    cmd = [sys.executable, os.path.join(HERE, "rust_aeneas.py"), "--crate", os.path.abspath(a.base),
           "--out", base_out, "--cases-out", cases_path, "--seed", str(a.seed),
           "--cases", str(a.cases), "--random", str(a.random)]
    if a.lean_project:
        cmd += ["--lean-project", a.lean_project]
    if a.module:
        cmd += ["--module", a.module]
    print("rust_regress: base model (%s)" % a.base_label, flush=True)
    r = subprocess.run(cmd, env=env)
    if r.returncode not in (0, 1) or not os.path.exists(cases_path):
        err = os.path.join(base_out, "rust-error.json")
        detail = json.load(open(err)) if os.path.exists(err) else {"error": "exit %d" % r.returncode}
        raise RustPathError("base-model-failed", "the Rust path did not complete on the base revision: %s: %s"
                            % (detail.get("error"), detail.get("message", "")), detail.get("hint"))
    recorded = json.load(open(cases_path))
    toolchain = ra.pinned_rust_toolchain(env)

    work = os.path.realpath(tempfile.mkdtemp(prefix="rust_regress_"))
    try:
        trees = {"base": prepare("base", a.base, work, env, toolchain),
                 "control": prepare("control", a.base, work, env, toolchain, need_doc=False),
                 "head": prepare("head", a.head, work, env, toolchain)}
        base_sigs, head_sigs = signatures(trees["base"]["doc"]), signatures(trees["head"]["doc"])

        # 2. inputs: the base model's cases, then native-only inputs for encodable holes
        cases = [dict(c, evidence="model") for c in recorded["cases"]]
        modelled = {c["callee"] for c in cases}
        rng = random.Random(a.seed)
        native_only = []
        for callee, (sig, _, name) in base_sigs.items():
            if callee in modelled or sig is None:
                continue
            native_only.append(name)
            for v in ra.cases_for(sig[0], rng, cap=a.cases, nrand=a.random):
                cases.append({"function": name, "callee": callee, "arg_types": sig[0], "ret_type": sig[1],
                              "args": canon(list(v)), "rust": None, "aeneas": None, "verdict": None,
                              "evidence": "native-only"})

        # 3. which functions can be called at head with the same signature
        not_comparable = {}
        for c in cases:
            if c["callee"] in not_comparable:
                continue
            got = head_sigs.get(c["callee"])
            if got is None:
                not_comparable[c["callee"]] = "removed at head (no public function %s)" % c["callee"]
            elif got[0] is None:
                not_comparable[c["callee"]] = "not encodable at head: %s" % got[1]
            elif got[0] != [canon(c["arg_types"]), canon(c["ret_type"])]:
                not_comparable[c["callee"]] = "signature changed at head"
        added = sorted(name for callee, (_, _, name) in head_sigs.items() if callee not in base_sigs)
        replay = [i for i, c in enumerate(cases) if c["callee"] not in not_comparable]

        # 4. native runs on the same inputs
        print("rust_regress: %d cases (%d replayed at head); native runs: base, control, head"
              % (len(cases), len(replay)), flush=True)
        base_res, base_notes, sandbox_rec = native(trees["base"], cases, work, env)
        ctrl_res, ctrl_notes, _ = native(trees["control"], cases, work, env)
        head_raw, head_notes_raw, _ = native(trees["head"], [cases[i] for i in replay], work, env)
        head_res = {i: head_raw.get(k) for k, i in enumerate(replay)}
        head_notes = {i: head_notes_raw[k] for k, i in enumerate(replay) if k in head_notes_raw}
    finally:
        if not a.keep_work:
            shutil.rmtree(work, ignore_errors=True)

    # 5. verdicts, the control first
    counts = {k: 0 for k in ("regression", "behaviour-change", "unchanged", "inconclusive",
                             "unstable", "not-comparable")}
    control = {"cases": len(cases), "reproduced_base_model_run": 0, "flagged": 0, "flagged_detail": []}
    per_fn, findings = {}, []
    for i, c in enumerate(cases):
        fn = per_fn.setdefault(c["callee"], {"function": c["function"], "callee": c["callee"],
                                             "evidence": c["evidence"], "cases": 0, **{k: 0 for k in counts}})
        fn["cases"] += 1
        b = base_res.get(i)
        unstable = None
        if c["evidence"] == "model" and b != c["rust"]:
            unstable = "base rebuild %r differs from the base model run's %r" % (b, c["rust"])
        else:
            control["reproduced_base_model_run"] += c["evidence"] == "model"
        cv, cwhy = classify(c, b, ctrl_res.get(i))
        if cv in ("regression", "behaviour-change", "inconclusive"):
            control["flagged"] += 1
            unstable = unstable or "control: %s (%s)" % (cv, cwhy or ctrl_notes.get(i) or "%r vs %r" % (b, ctrl_res.get(i)))
            if len(control["flagged_detail"]) < 20:
                control["flagged_detail"].append({"function": c["function"], "verdict": cv, "base": b,
                                                  "control": ctrl_res.get(i), "note": base_notes.get(i) or ctrl_notes.get(i)})
        if c["callee"] in not_comparable:
            v, why = "not-comparable", not_comparable[c["callee"]]
        elif unstable:
            v, why = "unstable", unstable
        else:
            v, why = classify(c, b, head_res.get(i))
            if v == "inconclusive":
                why = head_notes.get(i) or why
        counts[v] += 1
        fn[v] += 1
        if v in ("regression", "behaviour-change"):
            fn.setdefault("examples", [])
            if len(fn["examples"]) < EXAMPLES:
                fn["examples"].append({"args": [ra.rust_lit(t, x) for t, x in zip(c["arg_types"], c["args"])],
                                       "base_native": b, "base_model": c.get("aeneas"), "head_native": head_res.get(i)})
        elif v in ("inconclusive", "unstable"):
            fn.setdefault("reasons", {})
            fn["reasons"][why] = fn["reasons"].get(why, 0) + 1
    for callee, fn in per_fn.items():
        fn["status"] = ("not-comparable" if callee in not_comparable else
                        "regression" if fn["regression"] else
                        "behaviour-change" if fn["behaviour-change"] else
                        "unchanged" if fn["unchanged"] else "inconclusive")
        if callee in not_comparable:
            fn["reason"] = not_comparable[callee]
        if fn["status"] in ("regression", "behaviour-change"):
            findings.append(fn)

    base_led = next((json.load(open(os.path.join(base_out, n))) for n in sorted(os.listdir(base_out))
                     if n.startswith("ledger-") and n.endswith(".json")), {})
    report = {
        "language": "rust", "kind": "rust-regression",
        "base": a.base_label, "head": a.head_label, "crate": recorded["crate"],
        "oracle": "native Rust at head vs the base revision's Aeneas model (where translated) and "
                  "vs native Rust at base, on the same inputs; debug profile",
        "base_model": {"functions": base_led.get("functions"), "translated": base_led.get("holeFree"),
                       "holes": base_led.get("holes"),
                       "conformance": {k: json.load(open(os.path.join(base_out, "conformance.json"))).get(k)
                                       for k in ("agree", "total", "divergences", "inconclusive")}},
        "functions_model_backed": sorted(modelled),
        "functions_native_only": sorted(native_only),
        "functions_not_encodable": {n: why for _, (s, why, n) in sorted(base_sigs.items()) if s is None},
        "functions_added_at_head": added,
        "not_comparable": not_comparable,
        "function_spans": {side: spans(trees[side]["doc"], trees[side]["crate"]) for side in ("base", "head")},
        "cases": counts, "total_cases": len(cases),
        "control": control,
        "functions": sorted(per_fn.values(), key=lambda f: f["function"]),
        "regressions": [f for f in findings if f["status"] == "regression"],
        "behaviour_changes": [f for f in findings if f["status"] == "behaviour-change"],
        "assumptions": [
            "debug profile at both revisions (overflow checks on, what Aeneas models)",
            "Rust panic == Rust panic and panic <-> Aeneas `fail` of any kind; kinds are not compared",
            "a function is replayed at head only under the same callee path and the same encoded signature",
            "native-only functions (holes at base) have no model: a change is reported, never called a regression",
            "a case the control run flags, or whose base rebuild differs from the base model run, is unstable and excluded"],
        "sandbox": sandbox_rec,
        "wall_clock_seconds": round(time.time() - t0, 1),
    }
    with open(os.path.join(out, "rust-regression.json"), "w") as fh:
        json.dump(report, fh, indent=1)
    with open(os.path.join(out, "rust-regression.md"), "w") as fh:
        fh.write(markdown(report))
    print("rust_regress [%s -> %s]: %d cases: %d regression, %d behaviour-change, %d unchanged, "
          "%d inconclusive, %d unstable, %d not comparable; control flagged %d; "
          "%d regressed functions, %d changed functions"
          % (a.base_label, a.head_label, len(cases), counts["regression"], counts["behaviour-change"],
             counts["unchanged"], counts["inconclusive"], counts["unstable"], counts["not-comparable"],
             control["flagged"], len(report["regressions"]), len(report["behaviour_changes"])))
    for f in findings:
        ex = f["examples"][0]
        print("  %s %s(%s): base %s, base model %s, head %s"
              % (f["status"].upper(), f["function"], ", ".join(ex["args"]), ex["base_native"],
                 ex["base_model"], ex["head_native"]))
    return 1 if findings else 0


def markdown(r):
    lines = ["# Rust regression: %s -> %s (%s)" % (r["base"], r["head"], r["crate"]), "",
             r["oracle"] + ".", "",
             "| verdict | cases |", "|---|---|"]
    lines += ["| %s | %d |" % (k, v) for k, v in r["cases"].items()]
    c = r["control"]
    lines += ["", "Control (the base tree rebuilt and run again): %d of %d cases flagged; "
              "%d model-backed cases reproduced the base model run." % (c["flagged"], c["cases"],
                                                                        c["reproduced_base_model_run"]), ""]
    for title, key in (("Regressions (head departs from the base model where base matched it)", "regressions"),
                       ("Behaviour changes (no model verdict; head differs from base)", "behaviour_changes")):
        lines += ["## " + title, ""]
        if not r[key]:
            lines += ["None.", ""]
        for f in r[key]:
            lines.append("* `%s` (%s): %d of %d cases" % (f["function"], f["evidence"], f[f["status"]], f["cases"]))
            for ex in f["examples"]:
                lines.append("  * `(%s)`: base `%s`, base model `%s`, head `%s`"
                             % (", ".join(ex["args"]), ex["base_native"], ex["base_model"], ex["head_native"]))
        lines.append("")
    lines += ["## Not compared", ""]
    lines += ["* `%s`: %s" % (k, v) for k, v in sorted(r["not_comparable"].items())]
    lines += ["* `%s`: added at head (no base to compare with)" % n for n in r["functions_added_at_head"]]
    lines += ["* `%s`: not encodable by the harness: %s" % kv for kv in sorted(r["functions_not_encodable"].items())]
    if not (r["not_comparable"] or r["functions_added_at_head"] or r["functions_not_encodable"]):
        lines.append("Nothing.")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    sys.exit(main())
