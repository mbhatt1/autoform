#!/usr/bin/env python3
"""Per-language coverage measurement over exported neutral ASTs.

`docs/languages.md` is the write-up; this is the measurement that produced it. It reads
the `ast-<Module>.json` files that `autoform.sh` step 3 leaves behind (or any exported
AST) and reports, per corpus: function count, AST node count, hole count, hole-free
percentage, the inferred dialect, and holes broken down by cause.

Why this exists separately from `Autoform/Ledger.lean`:

* The ledger runs *after* `render_lean.py`, so it can only report on corpora that
  rendered. Real JavaScript (lodash, 693 functions) does not: `json.load` in
  `render_lean.py` hits `RecursionError` on the nesting depth jssrc2cpg produces. This
  script raises the recursion limit and walks the AST iteratively, so a corpus that
  cannot be rendered can still be measured. A pipeline stage that fails is a result, and
  the result should be quantified rather than left blank.
* Holes-by-cause is the interesting per-language signal: it names exactly which CPG node
  kinds the exporter does not map, and those differ sharply by frontend.

Usage:
    python3 scripts/lang_matrix.py ast-LangJava.json ast-LangGo.json ...
    python3 scripts/lang_matrix.py            # every ast-*.json in the repo root
"""
import json, sys, os, glob, collections

sys.setrecursionlimit(100000)

# Same extension -> dialect table as `cartographer/render_lean.py`. Duplicated
# deliberately: this script measures the pipeline, so it must not import from it and
# inherit a change silently.
DIALECT = {".py": "python", ".c": "cLike", ".h": "cLike", ".cpp": "cLike",
           ".java": "cLike", ".js": "cLike", ".ts": "cLike", ".kt": "cLike",
           ".go": "cLike"}

def walk(node):
    """Yield every dict node in an AST, iteratively (the JS ASTs are deep)."""
    stack = [node]
    while stack:
        n = stack.pop()
        if isinstance(n, dict):
            yield n
            stack.extend(n.values())
        elif isinstance(n, list):
            stack.extend(n)

def func_stats(f):
    nodes = holes = 0
    causes = collections.Counter()
    for n in walk(f.get("body", {})):
        if "k" not in n:
            continue
        nodes += 1
        if n["k"] in ("hole", "holeS"):
            holes += 1
            causes[n.get("label", "?")] += 1
    return nodes, holes, causes

def analyse(path):
    with open(path) as fh:
        funcs = json.load(fh)
    exts = collections.Counter(os.path.splitext(f.get("file", ""))[1] for f in funcs)
    votes = collections.Counter(DIALECT[e] for e in exts.elements() if e in DIALECT)
    dialect = votes.most_common(1)[0][0] if votes else "python (defaulted)"
    total_nodes = total_holes = hole_free = 0
    causes = collections.Counter()
    for f in funcs:
        n, h, c = func_stats(f)
        total_nodes += n
        total_holes += h
        causes += c
        if h == 0:
            hole_free += 1
    return {
        "path": path, "funcs": len(funcs), "nodes": total_nodes, "holes": total_holes,
        "hole_free": hole_free,
        "hole_free_pct": (100.0 * hole_free / len(funcs)) if funcs else 0.0,
        "hole_pct": (100.0 * total_holes / total_nodes) if total_nodes else 0.0,
        "exts": exts, "dialect": dialect, "causes": causes,
    }

def main():
    paths = sys.argv[1:] or sorted(glob.glob("ast-*.json"))
    if not paths:
        raise SystemExit("no AST files given and no ast-*.json in the current directory")
    rows = [analyse(p) for p in paths]
    w = max(len(os.path.basename(r["path"])) for r in rows)
    print(f"{'corpus'.ljust(w)}  {'ext':>6} {'dialect':>8} {'funcs':>6} {'nodes':>7} "
          f"{'holes':>6} {'hole%':>6} {'holefree':>9}")
    for r in rows:
        ext = r["exts"].most_common(1)[0][0] if r["exts"] else "?"
        print(f"{os.path.basename(r['path']).ljust(w)}  {ext:>6} {r['dialect']:>8} "
              f"{r['funcs']:>6} {r['nodes']:>7} {r['holes']:>6} {r['hole_pct']:>5.1f}% "
              f"{r['hole_free']:>4} ({r['hole_free_pct']:.0f}%)")
    for r in rows:
        print(f"\n-- {os.path.basename(r['path'])}: holes by cause")
        for label, n in r["causes"].most_common(15):
            print(f"   {n:>5}  {label}")
        if len(r["causes"]) > 15:
            print(f"   ... {len(r['causes']) - 15} more labels")

if __name__ == "__main__":
    main()
