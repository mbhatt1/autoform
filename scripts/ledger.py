#!/usr/bin/env python3
"""ledger.py — the trust ledger computed from the neutral AST, without elaborating Lean.

`scripts/ledger.lean.tmpl` computes `ledger-<M>.json` by `#eval`-ing `Program.ledgerJson`
(`Autoform/Ledger.lean`) on the *built* generated module. That is the reference, and it
stays the reference: it is kernel-adjacent code over the same `Program` the proofs see.
It also needs the whole module elaborated first, which on Django's 10k functions is
244 s and 3.3 GB per part with sharding (docs/scale.md) — and the ledger then reads the
whole thing back. The milestone-5 exit in docs/GOAL-arbitrary-codebases.md asks for the
Django ledger in under 60 s; that is not reachable through elaboration.

This script computes the same ledger from `ast-<M>.json` directly, in Python, in seconds.
It is NOT a second definition of the ledger. It mirrors, arm for arm:

* the renderer's node mapping (`cartographer/render_lean.py`: `_EXPR_FIELDS`,
  `_STMT_FIELDS`, `_HEADS`, the literal and `boxFields*` special forms), and its lowering
  passes, which are *imported* and run, not reimplemented, so this script sees the same
  functions the generated module defines;
* `Expr.holes`/`Stmt.holes`, `Expr.size`/`Stmt.size` (`Autoform/Lang/Core/Syntax.lean`);
* `Analysis.eCalls`/`sCalls`, `eCallees`/`sCallees`, `eRisk`/`sRisk`, `ResolveIndex`,
  `contractedCallees` and `Program.coverage` (`Autoform/Ledger.lean`);
* `Stdlib.knowsFree`, `Iteration.knowsFree` and `Stdlib.methodNames`, whose name lists are
  copied below and held equal to the Lean source by `tests/test_ledger_py.py`.

A mirror can drift silently, and a ledger that drifted in the flattering direction is the
exact failure this project keeps catching (Ledger.lean, "Static hole-freedom is an upper
bound"). So the cross-check is a test, not a note: `tests/test_ledger_py.py` runs this
script on cachetools and on one Django part and compares every field with the ledger Lean
wrote for the same AST. A disagreement fails the test; nothing here is trusted on its own.

Usage:
    scripts/ledger.py ast-<M>.json <M> [--out ledger-<M>.json]
                      [--part K --shard-functions N] [--quiet]

`--part K --shard-functions N` computes the ledger of the program that part K of a
`render_lean.py --shard-functions N` render defines on its own (`PartK.partFuncs` as
`funcs`, no auxiliary functions, the full class-declaration table). That is the program
the cross-check elaborates, because one part is what fits in memory; the whole-module
ledger is the default.

What the output is: `functions`, `nodes`, `holes`, `holeFree`, `verifiableCore`
(= `closedByTranslation`), `closedByContract`, `contractsUsed`, `dynamicHoleRisk`,
`holesByLabel`, with the same meanings as `Program.ledgerJson`, plus `producer`,
`astSha256` and `wallClockSeconds` so a reader can tell this product from the Lean one.
`holesByLabel` is sorted by count then label; Lean's order among equal counts is
hash-map order, so compare the two as a map, not as a list.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
import sys
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "cartographer"))
import deep_json                      # noqa: E402
import render_lean as R               # noqa: E402  (the renderer's own node tables)

# ---------------------------------------------------------------------------
# Name lists copied from the Lean sources. tests/test_ledger_py.py parses the Lean files
# and fails if any of these differ, so an edit on one side cannot go unnoticed.
# ---------------------------------------------------------------------------

# `Stdlib.excNames` (Autoform/Lang/Core/Stdlib.lean)
STDLIB_EXC_NAMES = [
    "Exception", "BaseException", "ArithmeticError", "AssertionError", "AttributeError",
    "EOFError", "FloatingPointError", "ImportError", "IndentationError", "IndexError",
    "KeyError", "KeyboardInterrupt", "LookupError", "MemoryError", "NameError",
    "NotImplementedError", "OverflowError", "RecursionError", "ReferenceError",
    "RuntimeError", "StopIteration", "StopAsyncIteration", "SyntaxError", "SystemError",
    "SystemExit", "TypeError", "UnboundLocalError", "ValueError", "ZeroDivisionError"]
# `Stdlib.freeNames` = excNames ++ these
STDLIB_FREE_NAMES = STDLIB_EXC_NAMES + [
    "len", "abs", "sum", "min", "max", "sorted", "bool", "str", "repr", "format", "int",
    "ord", "chr", "callable", "isinstance", "getattr", "hasattr",
    "list", "tuple", "dict"]
# `Iteration.freeNames` (Autoform/Lang/Core/Iteration.lean)
ITERATION_FREE_NAMES = [
    "iter", "next", "<python-iter>", "<python-next>", "<iterator-next>", "<sequence-iter>",
    "<iterator-identical>", "<iterator-tuple>", "<iterator-sum-add>", "<iterator-length-hint>",
    "any", "all", "<python-bool>"]
# `Stdlib.methodNames`
STDLIB_METHOD_NAMES = [
    "get", "keys", "values", "items", "copy", "count", "index",
    "append", "insert", "extend", "clear", "remove", "pop", "popitem",
    "setdefault", "update", "add", "discard"]
# `contractedCallees` (Autoform/Ledger.lean), per dialect
CONTRACTED_CALLEES = {
    ".python": ["." + m for m in STDLIB_METHOD_NAMES] + ["functools.update_wrapper"],
    ".cLike": ["strlen", "Objects.requireNonNull", "requireNonNull",
               "Math.max", "Math.min", "Math.abs",
               "fmt.Sprintf", "Sprintf",
               "strings.ToUpper", "strings.ToLower", "strings.TrimSpace"],
    ".java": ["Objects.requireNonNull", "requireNonNull", "Math.max", "Math.min", "Math.abs"],
    ".go": ["fmt.Sprintf", "Sprintf", "strings.ToUpper", "strings.ToLower", "strings.TrimSpace"],
    ".javascript": ["Math.floor", "Math.ceil", "Math.max", "Math.min", "Math.abs",
                    "Number.isInteger", "JSON.stringify"],
}
# `Dialect.name`
DIALECT_NAME = {".python": "python", ".cLike": "c-like", ".javascript": "javascript",
                ".java": "java", ".go": "go"}


def knows_free(dialect: str, name: str) -> bool:
    """`Stdlib.knowsFree d n || Iteration.knowsFree d n`: both are `.python`-only."""
    return dialect == ".python" and (name in STDLIB_FREE_SET or name in ITERATION_FREE_SET)


STDLIB_FREE_SET = frozenset(STDLIB_FREE_NAMES)
ITERATION_FREE_SET = frozenset(ITERATION_FREE_NAMES)

# ---------------------------------------------------------------------------
# The analyses, over the JSON node shapes the renderer maps to Core constructors.
#
# Each walker is one function per node, with the Lean arm it mirrors named in a comment
# where the arm is not "recurse into every child". Children are enumerated from the
# renderer's own field tables, so a node kind the renderer does not know raises here just
# as it raises there -- the ledger never silently counts a construct as hole-free.
# ---------------------------------------------------------------------------

# Expression constructors whose `eRisk` arm adds 1 (Ledger.lean, `eRisk`).
_EXPR_RISK_1 = {"field", "index", "mcall", "binop", "call", "callV", "alloc", "inOp",
                "irefIndex", "irefField", "derefIref", "strByte", "strFrom", "slice"}
# Statement constructors whose `sRisk` arm adds 1 (and recurses) ...
_STMT_RISK_1 = {"setField", "delIndex", "setSlice", "delSlice", "setDerefIref", "forIn"}
# ... and the one arm that is a constant: `| .setIndex _ _ _ => 1`, no recursion.
_STMT_RISK_CONST = {"setIndex": 1}
_LITERALS = {"int", "str", "bool", "unit", "float"}


def _children(node, kind):
    """`(tag, value)` children in constructor order, from the renderer's tables. Literal
    expressions and the two `boxFields` forms are the renderer's special cases."""
    if not isinstance(node, dict):
        raise ValueError(f"{kind} node is not an object: {node!r}")
    k = node.get("k")
    if kind == "e":
        if k in _LITERALS:
            return "lit", []
        if k == "boxFields":
            return "boxFields", [("ps", [[{"k": "str", "v": key}, val]
                                         for key, val in R._field(node, "fields", "expr")])]
        if k == "boxFieldsRange":
            n = R._field(node, "n", "expr")
            if not isinstance(n, int) or n < 0:
                raise ValueError(f"boxFieldsRange node has invalid n: {n!r}")
            # `(List.range n).map (fun i => (lit (str i), lit unit))`: n literal pairs.
            return "boxFields", [("ps", [[{"k": "str", "v": str(i)}, {"k": "unit"}]
                                         for i in range(n)])]
        table = R._EXPR_FIELDS
    else:
        table = R._STMT_FIELDS
    if k not in table:
        raise ValueError(f"unknown {'expression' if kind == 'e' else 'statement'} node kind "
                         f"{k!r} (node: {json.dumps(node)[:200]})")
    out = []
    for spec in table[k].split():
        tag, key = spec.split(":")
        if tag in ("e", "s", "es", "ps"):
            out.append((tag, R._field(node, key, kind)))
    return k, out


def _each(children):
    """Flatten list children to `(kind, node)` pairs, in order."""
    for tag, value in children:
        if tag in ("e", "s"):
            yield tag, value
        elif tag == "es":
            for item in R._seq(value):
                yield "e", item
        else:  # ps
            for pair in R._seq(value):
                if not (isinstance(pair, list) and len(pair) == 2):
                    raise ValueError(f"dictE pair must be a 2-element array, got {pair!r}")
                yield "e", pair[0]
                yield "e", pair[1]


class Analysis:
    """One pass over a body collecting holes, size, calls, callees and risk together."""

    __slots__ = ("holes", "size", "calls", "callees", "risk")

    def __init__(self):
        self.holes, self.size, self.calls, self.callees, self.risk = [], 0, [], [], 0

    def stmt(self, node):
        k, children = _children(node, "s")
        if k == "holeS":                       # `.hole l => [l]`; size 1; no calls; risk 0
            self.holes.append(R._field(node, "label", "stmt"))
            self.size += 1
            return
        # `Stmt.size`: `seq a b => a.size + b.size`, every other constructor 1 + children.
        if k != "seq":
            self.size += 1
        if k in _STMT_RISK_CONST:              # `.setIndex _ _ _ => 1`
            self.risk += _STMT_RISK_CONST[k]
            # holes/size/calls still descend (Stmt.holes, Stmt.size and sCalls do).
            saved = self.risk
            for tag, child in _each(children):
                self.expr(child) if tag == "e" else self.stmt(child)
            self.risk = saved
            return
        if k in _STMT_RISK_1:
            self.risk += 1
        for tag, child in _each(children):
            self.expr(child) if tag == "e" else self.stmt(child)

    def expr(self, node):
        k, children = _children(node, "e")
        self.size += 1                         # `Expr.size`: every constructor is 1 + ...
        if k == "hole":                        # `.hole l => [l]`
            self.holes.append(R._field(node, "label", "expr"))
            return
        if k == "call":                        # `(false, f) :: eCallsL as`
            f = R._field(node, "f", "expr")
            self.calls.append((False, f))
            self.callees.append((False, f, f))
        elif k == "mcall":                     # `(true, m) :: eCalls r ++ eCallsL as`
            m = R._field(node, "m", "expr")
            recv = R._field(node, "recv", "expr")
            key = (recv["v"] + "." + m) if isinstance(recv, dict) and recv.get("k") == "name" \
                else "." + m
            self.calls.append((True, m))
            self.callees.append((True, m, key))
        if k in _EXPR_RISK_1:
            self.risk += 1
        for tag, child in _each(children):
            self.expr(child) if tag == "e" else self.stmt(child)


def analyze(f):
    """`Func.analyzedBody := f.analysisBody.getD f.body`, walked once."""
    a = Analysis()
    a.stmt(f["analysisBody"] if "analysisBody" in f else f["body"])
    return a


# ---------------------------------------------------------------------------
# `ResolveIndex` (Ledger.lean)
# ---------------------------------------------------------------------------

def dotted_tails(k: str):
    """`dottedTails`: every string `k` ends with immediately after a `.`, longest first."""
    parts = k.split(".")
    return [".".join(parts[i:]) for i in range(1, len(parts))]


def dotted_owner(k: str):
    """`dottedOwner`: `k` without its last dotted segment, or None without a dot."""
    parts = k.split(".")
    return ".".join(parts[:-1]) if len(parts) >= 2 else None


class ResolveIndex:
    def __init__(self, table_keys, declared_classes, dialect):
        self.dialect = dialect
        self.exact = set(table_keys)
        self.suffix_count = collections.Counter()
        self.suffix_key = {}
        self.method_keys = set()
        declared = set(declared_classes)
        for k in table_keys:
            for t in dotted_tails(k):
                self.suffix_count[t] += 1
                self.suffix_key[t] = k
            owner = dotted_owner(k)
            if owner is not None and owner in declared:
                self.method_keys.add(k)

    def resolvable(self, is_method: bool, n: str) -> bool:
        """`ResolveIndex.resolvable`, arm for arm."""
        if is_method:
            return self.suffix_count.get(n, 0) >= 1
        if n in self.exact:
            return True
        if self.suffix_count.get(n, 0) == 1 and not (
                self.dialect == ".python" and "." not in n
                and self.suffix_key.get(n, "") in self.method_keys):
            return True
        return knows_free(self.dialect, n)


# ---------------------------------------------------------------------------
# `Program.coverage` / `Program.ledgerJson`
# ---------------------------------------------------------------------------

def load_program(ast_path):
    """The lowered functions exactly as `render_lean._run_main` sees them."""
    funcs = R.lower_generators(deep_json.load(ast_path))
    dialect = R.infer_dialect(funcs)
    if dialect == ".python":
        funcs = R.lower_truth_values(R.lower_truth_conditions(funcs))
    auxiliary = [helper for function in funcs
                 for kind in ("generatorHelpers", "truthHelpers", "decoratedEntries")
                 for helper in function.get(kind, [])]
    return funcs, auxiliary, dialect


def declared_classes(funcs):
    """The names in `Program.classDecls`, as `render_lean.program_classes` emits them."""
    return [row["name"] for f in funcs for row in f.get("classDeclarations", []) or []]


def ledger(funcs, auxiliary, dialect, classes, module):
    """`Program.ledgerJson` for `{ dialect, funcs, auxiliaryFuncs := auxiliary, classDecls }`."""
    analyses = [analyze(f) for f in funcs]
    table_keys = [f["name"] for f in funcs] + [a["name"] for a in auxiliary]
    idx = ResolveIndex(table_keys, classes, dialect)
    contracts = set(CONTRACTED_CALLEES[dialect])

    holes = [l for a in analyses for l in a.holes]
    nodes = sum(a.size for a in analyses)
    core = [(f, a) for f, a in zip(funcs, analyses) if not a.holes]      # verifiableCore
    closed = [f for f, a in core
              if all(idx.resolvable(m, n) for m, n in a.calls)]          # callClosed
    closed_with = [f for f, a in core
                   if all(idx.resolvable(m, n) or key in contracts
                          for m, n, key in a.callees)]                   # callClosedWith
    by_translation = {f["name"] for f in closed}
    by_contract = [f for f in closed_with if f["name"] not in by_translation]
    used = collections.Counter(key for a in analyses for _, _, key in a.callees
                               if key in contracts)
    risk = sum(a.risk for a in analyses)
    by_label = collections.Counter(holes)

    def tally(counter):
        return sorted(counter.items(), key=lambda kv: (-kv[1], kv[0]))

    return {
        "module": module,
        "dialect": DIALECT_NAME[dialect],
        "functions": len(funcs),
        "nodes": nodes,
        "holes": len(holes),
        "holeFree": len(core),
        "verifiableCore": len(closed),
        "closedByTranslation": len(closed),
        "closedByContract": len(by_contract),
        "contractsUsed": [{"callee": k, "sites": n} for k, n in tally(used)],
        "dynamicHoleRisk": risk,
        "holesByLabel": [{"label": l, "count": n} for l, n in tally(by_label)],
    }, [f["name"] for f in closed]


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def compute(ast_path, module, part=None, shard=0):
    t0 = time.monotonic()
    funcs, auxiliary, dialect = load_program(ast_path)
    classes = declared_classes(funcs)
    if part is not None:
        # Part K of a sharded render defines `PartK.partFuncs` = its slice of `funcs`
        # (render_lean: parts chunk `funcs + auxiliary` in order, and a part's list keeps
        # only entries that are in `funcs`). No auxiliary function is in a part's program.
        if shard <= 0:
            raise SystemExit("ledger: --part needs --shard-functions N with N > 0")
        lo = (part - 1) * shard
        if lo >= len(funcs):
            raise SystemExit(f"ledger: part {part} is beyond the {len(funcs)} functions")
        funcs, auxiliary = funcs[lo:lo + shard], []
        # `classes` stays the module's whole table, as in `lean_part_check`.
    out, core_names = ledger(funcs, auxiliary, dialect, classes, module)
    out["producer"] = "scripts/ledger.py"
    out["astSha256"] = sha256_file(ast_path)
    if part is not None:
        out["part"] = part
        out["shardFunctions"] = shard
    out["wallClockSeconds"] = round(time.monotonic() - t0, 3)
    return out, core_names


def lean_part_check(ast_path, module, part, shard, out_json):
    """Lean source that computes, with `Program.ledgerJson`, the ledger of the program part
    `part` of a `--shard-functions shard` render defines on its own, and writes it to
    `out_json`. Run it with `lake env lean` after `lake build
    Autoform.Generated.<M>.PartNNNN` -- one part, which is what fits in memory.

    The program is `{ dialect, classDecls := <the module's whole class table>, funcs :=
    PartNNNN.partFuncs }`; `compute(..., part, shard)` is the Python side of the same
    program, so the two are comparable field for field. The class table is the module's,
    exactly the literal the root module carries, because `ResolveIndex`'s method-key arm
    needs the classes and their methods together and the exporter emits every class
    declaration on the module initializers, which sit at the end of the function list
    (Django: 1,970 declarations, a 1.3 MB literal that elaborates in about a minute).
    """
    funcs, _, dialect = load_program(ast_path)
    if shard <= 0:
        raise SystemExit("ledger: --part needs --shard-functions N with N > 0")
    lo = (part - 1) * shard
    if lo >= len(funcs):
        raise SystemExit(f"ledger: part {part} is beyond the {len(funcs)} functions")
    classes = R.program_classes(funcs)
    name = f"Part{part:04d}"
    agree_msg = (f"call-closure index agrees with Ctx.resolvable on {module} {name} "
                 f"({{partProgram.callClosed.length}} functions)")
    return "\n".join([
        f"import Autoform.Generated.{module}.{name}",
        "import Autoform.Ledger",
        f"open Autoform.Core Autoform.Generated.{module}",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "",
        f"/-- The program `{name}` defines on its own: its slice of `funcs`, no auxiliary",
        "functions, the module's class table. `scripts/ledger.py --part` computes the same",
        "program's ledger from the AST; tests/test_ledger_py.py compares the two. -/",
        "def partProgram : Program :=",
        f"  {{ dialect := {dialect}, classDecls := [{classes}], funcs := {name}.partFuncs }}",
        "",
        "#eval do",
        "  if partProgram.callClosureAgrees then",
        f'    IO.println s!"{agree_msg}"',
        "  else",
        "    throw (IO.userError",
        f'      "{module} {name}: ResolveIndex disagrees with Ctx.resolvable -- the ledger is NOT trustworthy")',
        "",
        "#eval do",
        f'  IO.FS.writeFile "{out_json}" (partProgram.ledgerJson "{module}").pretty',
        f'  IO.println "wrote {out_json}"',
        "",
    ])


def render_text(out, core_names):
    def pct(a, b):
        return "n/a" if b == 0 else f"{(a * 100) // b}%"
    lines = [
        f"╭─ autoform trust ledger ─ {out['module']} (scripts/ledger.py, from the AST)",
        f"│ functions translated : {out['functions']}",
        f"│ AST nodes            : {out['nodes']}",
        f"│ holes                : {out['holes']}  ({pct(out['holes'], out['nodes'])} of nodes)",
        f"│ hole-free (upper bd) : {out['holeFree']} / {out['functions']} functions  "
        f"({pct(out['holeFree'], out['functions'])})",
        f"│ VERIFIABLE CORE      : {out['verifiableCore']} / {out['functions']} functions  "
        f"({pct(out['verifiableCore'], out['functions'])}) — hole-free AND call-closed",
        f"│ closed by contract   : +{out['closedByContract']} functions — hole-free, open only on "
        f"contracted callees ({len(out['contractsUsed'])} names used); NOT in the core above",
        f"│ dynamic-hole risk    : {out['dynamicHoleRisk']} constructs may hole at runtime "
        f"(input-dependent)",
        "│ NOT PROVED           : transpiler faithfulness — see conformance.json",
        "│ NOT the Lean ledger  : cross-checked against Program.ledgerJson by "
        "tests/test_ledger_py.py",
        "├─ holes by cause ─────────────────────────────────────────────",
    ]
    rows = out["holesByLabel"]
    lines += [f"│ {r['count']}  {r['label']}" for r in rows[:12]]
    if len(rows) > 12:
        lines.append(f"│         … {len(rows) - 12} more labels")
    lines.append("╰───────────────────────────────────────────────────────────────")
    lines.append(f"\nverifiable core ({len(core_names)}) — first 15:")
    lines += [f"  {n}" for n in core_names[:15]]
    lines.append(f"\nwall clock: {out['wallClockSeconds']} s")
    return "\n".join(lines)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("ast")
    ap.add_argument("module")
    ap.add_argument("--out", default=None, help="default: ledger-<module>.json")
    ap.add_argument("--part", type=int, default=None)
    ap.add_argument("--shard-functions", type=int, default=0)
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--emit-lean-check", metavar="FILE", default=None,
                    help="with --part: also write the Lean file that computes the same "
                         "part's ledger with Program.ledgerJson (run it with `lake env lean`)")
    a = ap.parse_args(argv)
    if a.emit_lean_check:
        if a.part is None:
            raise SystemExit("ledger: --emit-lean-check needs --part K --shard-functions N")
        lean_out = a.out or f"ledger-{a.module}-Part{a.part:04d}.lean.json"
        with open(a.emit_lean_check, "w") as fh:
            fh.write(lean_part_check(a.ast, a.module, a.part, a.shard_functions, lean_out))
        print(f"wrote {a.emit_lean_check} (lake env lean it to produce {lean_out})")
        return 0
    out, core_names = compute(a.ast, a.module, a.part, a.shard_functions)
    dst = a.out or f"ledger-{a.module}.json"
    with open(dst, "w") as fh:
        json.dump(out, fh, indent=1)
        fh.write("\n")
    if not a.quiet:
        print(render_text(out, core_names))
    print(f"wrote {dst}")
    return 0


def _on_big_stack(fn):
    """Same reason as `render_lean.main`: depth follows the source's nesting, and a module
    initializer of a few hundred statements is a `seq` chain that deep."""
    sys.setrecursionlimit(300_000)
    try:
        threading.stack_size(512 * 1024 * 1024)
    except (ValueError, RuntimeError):
        try:
            threading.stack_size(64 * 1024 * 1024)
        except (ValueError, RuntimeError):
            pass
    box = {}

    def go():
        try:
            box["r"] = fn()
        except BaseException as e:        # noqa: BLE001 - re-raised on the main thread
            box["e"] = e

    t = threading.Thread(target=go)
    t.start()
    t.join()
    if "e" in box:
        raise box["e"]
    return box["r"]


if __name__ == "__main__":
    sys.exit(_on_big_stack(main))
