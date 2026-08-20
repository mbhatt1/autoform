#!/usr/bin/env python3
"""check_render.py — is the committed Lean module actually a render of the committed AST?

Everything downstream (ledger, conformance, specs, proofs) is a statement about
`Autoform/Generated/<M>.lean`. Nothing checked that this file was the one the AST
produces, and the gap was not hypothetical:

* A **mutation-gate mutant reached git** and survived four commits. `_DefaultSize.__getitem__`
  returned 0 where the source docstring says "a constant size 1 for any key" and the AST
  says `int 1`. For those commits the repository's translated program was silently wrong.
  Every proof about it still passed, because a mutant is a perfectly well-typed program.
* The module and the AST drifted apart entirely — 238 functions against 208 — when a
  concurrent pipeline re-rendered from a different AST.

Neither is detectable from the module alone, and neither is detectable by any check that
compares the module to something derived from the module. It needs an independent
recomputation, which is exactly what the exporter provides: `render_lean.py` is
deterministic (verified byte-identical across runs), so `render(AST)` is a total
specification of what the module must contain.

This is the same argument as STRATEGY.md §17/§30/§31: a metric computed from the artifact
it describes will flatter itself. Rendering again is the independent artifact.

Usage:  scripts/check_render.py [Module ...]      (default: every tracked module with an AST)
Exit:   0 all modules match; 1 a module differs; 2 nothing could be checked.
"""
from __future__ import annotations
import difflib, os, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RENDER = os.path.join(ROOT, "cartographer", "render_lean.py")


def modules():
    out = []
    for fn in sorted(os.listdir(ROOT)):
        if fn.startswith("ast-") and fn.endswith(".json"):
            m = fn[4:-5]
            if os.path.exists(os.path.join(ROOT, "Autoform", "Generated", m + ".lean")):
                out.append(m)
    return out


def check(m: str) -> str | None:
    ast = os.path.join(ROOT, f"ast-{m}.json")
    have = os.path.join(ROOT, "Autoform", "Generated", f"{m}.lean")
    with tempfile.TemporaryDirectory(prefix="autoform_render_") as d:
        want = os.path.join(d, f"{m}.lean")
        r = subprocess.run([sys.executable, RENDER, ast, want, m],
                           capture_output=True, text=True, timeout=1800)
        if r.returncode != 0:
            return f"{m}: render failed ({r.returncode}): {(r.stderr or r.stdout)[-500:]}"
        a = open(want).read().splitlines()
        b = open(have).read().splitlines()
        if a == b:
            return None
        diff = [l for l in difflib.unified_diff(a, b, "render(AST)", "committed", n=0, lineterm="")]
        body = [l for l in diff if l.startswith(("+", "-")) and not l.startswith(("+++", "---"))]
        head = "\n".join("    " + l for l in body[:12])
        more = f"\n    ... {len(body) - 12} more differing lines" if len(body) > 12 else ""
        return (f"{m}: the committed module is NOT a render of ast-{m}.json "
                f"({len(body)} differing lines).\n{head}{more}\n"
                f"    Regenerate with: cartographer/render_lean.py ast-{m}.json "
                f"Autoform/Generated/{m}.lean {m}")


def main():
    ms = sys.argv[1:] or modules()
    if not ms:
        print("check_render: no module has both an AST and a generated file", file=sys.stderr)
        return 2
    bad = [e for e in (check(m) for m in ms) if e]
    for e in bad:
        print("MISMATCH " + e, file=sys.stderr)
    if bad:
        print(f"\ncheck_render: {len(bad)}/{len(ms)} modules do not match their AST. "
              f"Anything measured from them describes a program nobody wrote.",
              file=sys.stderr)
        return 1
    print(f"check_render: {len(ms)} module(s) match a fresh render of their AST")
    return 0


if __name__ == "__main__":
    sys.exit(main())
