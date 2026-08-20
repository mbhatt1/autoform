#!/usr/bin/env python3
"""Source-level mutation gate for Lean definitions (STRATEGY.md §8/§13, Tier 3).

The dependency-vacuity check (`#audit_depends`) is *necessary* but not *sufficient*:
a theorem can mention a definition and still say nothing about it. The sufficient test
is mutation, as in IronSpec (specification validation) and MutantChick (Coq): inject a
bug into the *implementation*, rebuild, and see whether the theorem still proves.

  * mutant makes the proof fail  -> the mutant is KILLED: the theorem has teeth.
  * mutant compiles unchanged    -> the mutant SURVIVED: the theorem is vacuous with
                                    respect to that bug, and must be scored a FAILURE.

Usage:
    mutate.py <lean-file> <module-name> [--theorems a,b,c] [--max-mutants N]
              [--timeout S] [--json PATH] [--seed N]

Only definitions (`def`/`abbrev`/`instance`) are mutated; theorems are left alone --
mutating the proof would prove nothing about the specification.
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

# ---------------------------------------------------------------------------
# declaration map: which source lines belong to which declaration
# ---------------------------------------------------------------------------

DECL_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|partial\s+|noncomputable\s+|unsafe\s+)*'
    r'(theorem|lemma|example|def|abbrev|instance|inductive|structure|class)\b\s*([A-Za-z_][A-Za-z0-9_\'!?.₀-₉]*)?'
)

THEOREM_KINDS = {"theorem", "lemma"}
DEF_KINDS = {"def", "abbrev", "instance"}
# inductives are *specifications*, not implementations: mutating them mutates the
# thing the theorem is stated against, which proves nothing. They are parsed only so
# their lines are not misattributed to the preceding definition.
SPEC_KINDS = {"inductive", "structure", "class"}


class Decl:
    def __init__(self, kind, name, start):
        self.kind, self.name, self.start, self.end = kind, name, start, start

    def __repr__(self):
        return f"<{self.kind} {self.name} {self.start}-{self.end}>"


def parse_decls(lines):
    """Return declarations with 1-based inclusive line ranges."""
    decls = []
    for i, line in enumerate(lines, start=1):
        m = DECL_RE.match(line)
        if m:
            decls.append(Decl(m.group(1), m.group(2) or f"<anon@{i}>", i))
    for j, d in enumerate(decls):
        d.end = (decls[j + 1].start - 1) if j + 1 < len(decls) else len(lines)
    return decls


def decl_at(decls, line):
    for d in decls:
        if d.start <= line <= d.end:
            return d
    return None


# ---------------------------------------------------------------------------
# mutation operators
# ---------------------------------------------------------------------------

class Mutant:
    def __init__(self, op, line, old, new, decl):
        self.op, self.line, self.old, self.new, self.decl = op, line, old, new, decl

    @property
    def diff(self):
        return f"{self.decl} L{self.line} [{self.op}]\n  - {self.old.rstrip()}\n  + {self.new.rstrip()}"

    def to_json(self):
        return {"op": self.op, "line": self.line, "decl": self.decl,
                "before": self.old.rstrip(), "after": self.new.rstrip()}


def _pair_swaps(pairs):
    """Build a list of (compiled-regex, replacement-fn) for token-level swaps."""
    out = []
    for a, b in pairs:
        out.append((a, b))
        out.append((b, a))
    return out


# tokens are matched with surrounding-space discipline so we do not rewrite
# identifiers or comment prose.
ARITH = _pair_swaps([("+", "-"), ("*", "/")])
CMP = _pair_swaps([("<", ">"), ("≤", "≥"), ("<=", ">="), ("==", "!="), ("≤", "<"), ("≥", ">")])
BOOL_OPS = _pair_swaps([("&&", "||")])
LIT_BOOL = _pair_swaps([("true", "false")])


def _token_mutations(op_name, text, swaps, word=False):
    """Yield (new_text, description) for each single-occurrence token swap."""
    results = []
    for src, dst in swaps:
        if word:
            pat = re.compile(r'(?<![A-Za-z0-9_])' + re.escape(src) + r'(?![A-Za-z0-9_])')
        else:
            pat = re.compile(r'(?<=\s)' + re.escape(src) + r'(?=\s)')
        for m in pat.finditer(text):
            results.append((text[:m.start()] + dst + text[m.end():], f"{op_name}:{src}->{dst}"))
    return results


INT_LIT = re.compile(r'(?<![A-Za-z0-9_.])(\d+)(?![A-Za-z0-9_.])')
ITE = re.compile(r'\bif\s+(.+?)\s+then\s+(.+?)\s+else\s+(.+)$')
ARM = re.compile(r'^(\s*\|\s*.+?=>)(\s*)(\S.*)$')


def gen_mutants(lines, decls):
    """Generate one-at-a-time mutants of every definition body in the file."""
    mutants = []
    defs = [d for d in decls if d.kind in DEF_KINDS]

    # per-definition "default" RHS used by the match-arm-deletion operator
    default_rhs = {}
    for d in defs:
        for ln in range(d.start, d.end + 1):
            m = ARM.match(lines[ln - 1])
            if m and "=>" not in m.group(3):
                default_rhs.setdefault(d.name, m.group(3).strip())
                break

    for d in defs:
        for ln in range(d.start, d.end + 1):
            raw = lines[ln - 1]
            code = raw.split("--")[0]
            if not code.strip() or code.lstrip().startswith(("/-", "-/", "*")):
                continue

            cand = []
            cand += _token_mutations("arith", raw, ARITH)
            cand += _token_mutations("cmp", raw, CMP)
            cand += _token_mutations("bool", raw, BOOL_OPS)
            cand += _token_mutations("lit", raw, LIT_BOOL, word=True)

            # off-by-one on integer literals
            for m in INT_LIT.finditer(code):
                for delta in (1, -1):
                    v = int(m.group(1)) + delta
                    if v < 0:
                        continue
                    cand.append((raw[:m.start()] + str(v) + raw[m.end():],
                                 f"offbyone:{m.group(1)}->{v}"))

            # swap the branches of an if-then-else
            m = ITE.search(code)
            if m:
                swapped = code[:m.start()] + f"if {m.group(1)} then {m.group(3).rstrip()} else {m.group(2)}"
                cand.append((swapped + "\n", "ite-swap"))

            # delete a match arm's body: replace it with the definition's default RHS
            m = ARM.match(raw)
            if m and d.name in default_rhs and m.group(3).strip() != default_rhs[d.name] \
                    and "=>" not in m.group(3):
                cand.append((m.group(1) + m.group(2) + default_rhs[d.name] + "\n", "arm-delete"))

            for new, op in cand:
                if new != raw:
                    mutants.append(Mutant(op, ln, raw, new, d.name))
    return mutants


# ---------------------------------------------------------------------------
# build harness
# ---------------------------------------------------------------------------

ERR_RE = re.compile(r'^(?:.*?):(\d+):(\d+):\s*(error|warning)', re.M)


def lake_env():
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    return env


def run_build(root, module, timeout):
    try:
        r = subprocess.run(["lake", "build", module], cwd=root, env=lake_env(),
                           capture_output=True, text=True, timeout=timeout)
        return r.returncode, (r.stdout or "") + (r.stderr or ""), False
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"") if isinstance(e.stdout, bytes) else (e.stdout or "")
        if isinstance(out, bytes):
            out = out.decode("utf-8", "replace")
        return 1, out, True


def error_lines(output, target_basename):
    """Line numbers carrying an error, restricted to the file under mutation."""
    out = []
    for m in re.finditer(r'^(.*?):(\d+):(\d+):\s*error', output, re.M):
        path = m.group(1).strip()
        if target_basename in path or path in ("", "."):
            out.append(int(m.group(2)))
    return out


# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------

def find_root(path):
    d = os.path.dirname(os.path.abspath(path))
    while d != "/":
        if os.path.exists(os.path.join(d, "lakefile.toml")) or \
           os.path.exists(os.path.join(d, "lakefile.lean")):
            return d
        d = os.path.dirname(d)
    return os.getcwd()


def main():
    ap = argparse.ArgumentParser(description="Lean source-level mutation gate")
    ap.add_argument("lean_file")
    ap.add_argument("module")
    ap.add_argument("--theorems", default=None, help="comma-separated theorem names")
    ap.add_argument("--max-mutants", type=int, default=20)
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--json", dest="json_path", default="mutation.json")
    ap.add_argument("--seed", type=int, default=20260819)
    args = ap.parse_args()

    random.seed(args.seed)
    path = os.path.abspath(args.lean_file)
    root = find_root(path)
    base = os.path.basename(path)

    with open(path, "r", encoding="utf-8") as f:
        original = f.read()
    lines = original.splitlines(keepends=True)
    decls = parse_decls(lines)

    if args.theorems:
        targets = [t.strip() for t in args.theorems.split(",") if t.strip()]
    else:
        targets = [d.name for d in decls if d.kind in THEOREM_KINDS]
    if not targets:
        print("no theorems found; nothing to gate."); return 2

    tmap = {d.name: d for d in decls if d.kind in THEOREM_KINDS and d.name in targets}
    missing = [t for t in targets if t not in tmap]
    for t in missing:
        print(f"warning: theorem {t!r} not found in {base}")
    targets = [t for t in targets if t in tmap]
    if not targets:
        return 2

    all_mutants = gen_mutants(lines, decls)
    random.shuffle(all_mutants)
    mutants = all_mutants[:args.max_mutants]

    print(f"file      : {path}")
    print(f"module    : {args.module}")
    print(f"theorems  : {', '.join(targets)}")
    print(f"mutants   : {len(mutants)} of {len(all_mutants)} generated\n")

    print("baseline build ...", flush=True)
    rc, out, to = run_build(root, args.module, args.timeout)
    if rc != 0:
        print("BASELINE FAILS TO BUILD -- fix the file first.")
        print(out[-2000:])
        return 3
    print("baseline ok\n")

    stats = {t: {"killed": 0, "survived": 0, "survivors": []} for t in targets}
    invalid, records = 0, []

    try:
        for i, mut in enumerate(mutants, 1):
            new_lines = list(lines)
            new_lines[mut.line - 1] = mut.new
            with open(path, "w", encoding="utf-8") as f:
                f.write("".join(new_lines))

            rc, out, timed_out = run_build(root, args.module, args.timeout)
            errs = error_lines(out, base)
            hit_defs = {decl_at(decls, l).name for l in errs
                        if decl_at(decls, l) and decl_at(decls, l).kind in DEF_KINDS}
            hit_thms = {decl_at(decls, l).name for l in errs
                        if decl_at(decls, l) and decl_at(decls, l).kind in THEOREM_KINDS}

            rec = mut.to_json()
            if rc != 0 and hit_defs and not hit_thms:
                # the mutation broke the definition itself: not a behavioural bug
                rec["verdict"] = "invalid"
                invalid += 1
                print(f"[{i}/{len(mutants)}] INVALID  {mut.op:22s} L{mut.line} ({mut.decl}) "
                      f"— mutant does not typecheck")
            else:
                rec["verdict"] = {}
                rec["timeout"] = timed_out
                for t in targets:
                    dead = (t in hit_thms) or timed_out or (rc != 0 and not errs)
                    if dead:
                        stats[t]["killed"] += 1
                    else:
                        stats[t]["survived"] += 1
                        stats[t]["survivors"].append(mut.to_json())
                    rec["verdict"][t] = "killed" if dead else "survived"
                tag = ",".join(f"{t}={v}" for t, v in rec["verdict"].items())
                mark = "KILLED " if all(v == "killed" for v in rec["verdict"].values()) else "SURVIVED"
                print(f"[{i}/{len(mutants)}] {mark} {mut.op:22s} L{mut.line} ({mut.decl}) {tag}")
            records.append(rec)
    finally:
        with open(path, "w", encoding="utf-8") as f:
            f.write(original)
        # make sure the restored file is what the build cache sees next time
        run_build(root, args.module, args.timeout)

    print("\n=== mutation score ===")
    report = {"file": path, "module": args.module, "seed": args.seed,
              "mutants_generated": len(all_mutants), "mutants_run": len(mutants),
              "invalid": invalid, "theorems": {}, "mutants": records}
    exit_code = 0
    for t in targets:
        k, s = stats[t]["killed"], stats[t]["survived"]
        score = (k / (k + s)) if (k + s) else 0.0
        verdict = "HAS TEETH" if score == 1.0 else ("WEAK" if score > 0 else "VACUOUS")
        print(f"{t}: killed {k}, survived {s}  score {score:.2%}  [{verdict}]")
        for sv in stats[t]["survivors"]:
            print(f"    survivor: {sv['decl']} L{sv['line']} [{sv['op']}]")
            print(f"      - {sv['before']}")
            print(f"      + {sv['after']}")
        report["theorems"][t] = {"killed": k, "survived": s, "score": score,
                                 "verdict": verdict, "survivors": stats[t]["survivors"]}
        if s:
            exit_code = 1
    if invalid:
        print(f"({invalid} mutants discarded: they broke the definition's own typechecking)")

    with open(args.json_path, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)
    print(f"\nwrote {os.path.abspath(args.json_path)}")
    return exit_code


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\ninterrupted", file=sys.stderr)
        sys.exit(130)
