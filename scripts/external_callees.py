#!/usr/bin/env python3
"""external_callees.py — which calls leave the translated program, ranked.

    python3 scripts/external_callees.py ast-Cachetools.json ast-LangJava.json ... [--json OUT] [--top N]

Call closure (Autoform/Ledger.lean, `Ctx.resolvable`) is the reason the verifiable core
is smaller than the hole-free set: a function whose body is fully translated still cannot
be verified unconditionally when one of its callees is not in the program. This script
lists those callees, per corpus and aggregated, so the choice of which standard-library
call to model or contract next (docs/GOAL-arbitrary-codebases.md, milestone 3) is made
from a frequency table rather than from a guess.

It mirrors the ledger's resolvability rule rather than re-deciding it:

* a free call `f` resolves when `f` is a table key verbatim, or is the dotted tail of
  exactly ONE key (`Ctx.resolve`'s unique-suffix rule), or -- under `.python` -- is a
  modelled builtin (`Stdlib.freeNames`, read from `Stdlib.lean` so the two cannot drift);
* a method call `m` resolves when SOME key ends in `.m` (`Ctx.resolveMethod` takes the
  first match; the ledger has no receiver to do better).

Everything else is an external callee. A method call is keyed `Recv.m` when the receiver
is a plain name (`Math.max`, `strings.ToUpper`) and `.m` otherwise, because a contract is
written against a receiver, not against a bare method name.

Two counts per callee: `sites` (how many call sites) and `blocks` (how many HOLE-FREE
functions have this callee as their only external one -- contracting it alone would move
them into the core). The second is the number that says what a contract is worth.
"""
from __future__ import annotations
import argparse, collections, json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STDLIB = os.path.join(ROOT, "Autoform", "Lang", "Core", "Stdlib.lean")


def _lean_string_list(src: str, name: str) -> list[str]:
    """The string literals of `def <name> : List String := [...]` in a Lean file. Reads the
    block up to the first blank line, which is how these lists are laid out."""
    m = re.search(r"^def %s : List String :=\n(.*?)\n\n" % re.escape(name), src, re.S | re.M)
    if not m:
        raise SystemExit("external_callees: could not find `def %s` in %s" % (name, STDLIB))
    return re.findall(r'"([^"]*)"', m.group(1))


def python_free_names() -> set[str]:
    src = open(STDLIB, encoding="utf-8").read()
    return set(_lean_string_list(src, "excNames")) | set(_lean_string_list(src, "freeNames"))


def dialect_of(ast: list[dict]) -> str:
    """The dialect the render would give this AST: `render_lean.infer_dialect`, imported
    rather than re-implemented, so the two cannot vote differently on the same files."""
    sys.path.insert(0, os.path.join(ROOT, "cartographer"))
    from render_lean import infer_dialect  # noqa: E402
    return infer_dialect(ast).lstrip(".")


def dotted_tails(key: str) -> list[str]:
    parts = key.split(".")
    return [".".join(parts[i:]) for i in range(1, len(parts))]


class Resolver:
    """`Ctx.resolvable`, mirrored (see the module docstring)."""

    def __init__(self, names: list[str], dialect: str):
        self.exact = set(names)
        self.suffix = collections.Counter()
        for k in names:
            for t in dotted_tails(k):
                self.suffix[t] += 1
        self.builtins = python_free_names() if dialect == "python" else set()

    def free(self, f: str) -> bool:
        return f in self.exact or self.suffix.get(f, 0) == 1 or f in self.builtins

    def method(self, m: str) -> bool:
        return self.suffix.get(m, 0) >= 1


def walk(node, out: list, holes: list):
    """Collect (kind, key) for every call site and every hole label under `node`."""
    if isinstance(node, dict):
        k = node.get("k")
        if k == "call":
            out.append(("call", node.get("f", "")))
        elif k == "mcall":
            recv = node.get("recv") or {}
            r = recv.get("v") if recv.get("k") == "name" else None
            out.append(("mcall", (r, node.get("m", ""))))
        elif k in ("hole", "holeS"):
            holes.append(node.get("label", "?"))
        for v in node.values():
            walk(v, out, holes)
    elif isinstance(node, list):
        for v in node:
            walk(v, out, holes)


def analyse(path: str) -> dict:
    ast = json.load(open(path, encoding="utf-8"))
    dialect = dialect_of(ast)
    names = [f["name"] for f in ast]
    res = Resolver(names, dialect)
    sites = collections.Counter()
    blocks = collections.Counter()
    per_function = {}
    hole_free_blocked = 0
    for f in ast:
        calls, holes = [], []
        walk(f.get("body"), calls, holes)
        ext = []
        for kind, key in calls:
            if kind == "call":
                if not res.free(key):
                    ext.append(key)
            else:
                recv, m = key
                if not res.method(m):
                    ext.append("%s.%s" % (recv, m) if recv else ".%s" % m)
        for e in ext:
            sites[e] += 1
        distinct = sorted(set(ext))
        if distinct:
            per_function[f["name"]] = distinct
        if not holes and distinct:
            hole_free_blocked += 1
            if len(distinct) == 1:
                blocks[distinct[0]] += 1
    return {
        "artifact": os.path.relpath(path, ROOT) if path.startswith(ROOT) else path,
        "dialect": dialect,
        "functions": len(ast),
        "hole_free_but_open": hole_free_blocked,
        "external_callees": {
            k: {"sites": sites[k], "blocks": blocks.get(k, 0)}
            for k in sorted(sites, key=lambda k: (-sites[k], k))
        },
        "per_function": per_function,
    }


def aggregate(reports: list[dict]) -> list[dict]:
    rows = {}
    for r in reports:
        for k, v in r["external_callees"].items():
            row = rows.setdefault(k, {"callee": k, "sites": 0, "blocks": 0, "corpora": []})
            row["sites"] += v["sites"]
            row["blocks"] += v["blocks"]
            row["corpora"].append("%s(%s)" % (r["artifact"].replace("ast-", "").replace(".json", ""), r["dialect"]))
    return sorted(rows.values(), key=lambda r: (-r["blocks"], -r["sites"], r["callee"]))


def render(reports: list[dict], top: int) -> str:
    out = []
    for r in reports:
        out.append("%s  (%s): %d functions, %d hole-free but call-open, %d distinct external callees"
                   % (r["artifact"], r["dialect"], r["functions"], r["hole_free_but_open"],
                      len(r["external_callees"])))
    out.append("")
    out.append("| # | external callee | sites | blocks (hole-free functions it alone keeps out of the core) | corpora |")
    out.append("|--:|---|--:|--:|---|")
    for i, row in enumerate(aggregate(reports)[:top], 1):
        out.append("| %d | `%s` | %d | %d | %s |" % (i, row["callee"], row["sites"], row["blocks"],
                                                  ", ".join(row["corpora"])))
    return "\n".join(out)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("asts", nargs="+")
    ap.add_argument("--json", dest="json_path")
    ap.add_argument("--top", type=int, default=100)
    a = ap.parse_args(argv)
    reports = [analyse(p) for p in a.asts]
    print(render(reports, a.top))
    if a.json_path:
        with open(a.json_path, "w", encoding="utf-8") as fh:
            json.dump({"corpora": reports, "ranking": aggregate(reports)}, fh, indent=1)
            fh.write("\n")
        print("\nwrote %s" % a.json_path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
