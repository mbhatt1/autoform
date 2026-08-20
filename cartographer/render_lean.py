#!/usr/bin/env python3
"""Render the language-neutral JSON AST as a Lean 4 `Autoform.Core.Program`.

Deterministic printer. The only judgement it makes is name sanitisation; everything
else is a direct structural mapping, so the output is diffable and reviewable.

Two invariants this file exists to protect:

* **Every expression and statement is fully parenthesised.** A previous version emitted
  `.ret .name "a"`, which Lean parses as `Stmt.ret` applied to three arguments. Anything
  that is not a nullary constructor gets wrapped, always.
* **The printer is a function of the JSON alone.** No dict/set iteration order, no
  timestamps, no paths beyond what the AST records — the same input must give a
  byte-identical file.

Usage: render_lean.py ast.json Out.lean [ModuleName]
"""
import json, sys, re, os

# Break a term across lines once its flat form would push past this column. Purely
# cosmetic: the layout below is whitespace-insensitive because every term is
# parenthesised or bracketed, so wrapping can never change what Lean parses.
WIDTH = 100
INDENT = 2

# ---------------------------------------------------------------------------
# Lean literals
# ---------------------------------------------------------------------------

# Lean 4 string escapes are a short list: \\ \" \' \n \t \r \x?? \u????. Anything
# outside it is either passed through as UTF-8 (Lean source is UTF-8) or hex-escaped.
_SIMPLE_ESCAPES = {
    '\\': '\\\\',
    '"':  '\\"',
    '\n': '\\n',
    '\t': '\\t',
    '\r': '\\r',
}

def lean_str(s) -> str:
    """Escape a Python string as a Lean 4 string literal.

    Control characters (including DEL and the C1 block) become `\\x..`/`\\u....`; printable
    non-ASCII is emitted verbatim, since Lean reads UTF-8 source. Lone surrogates cannot
    appear in a Lean string at all, so they are hex-escaped too — which keeps the file
    writable even when the source contained mojibake.
    """
    if not isinstance(s, str):
        s = str(s)
    out = []
    for ch in s:
        if ch in _SIMPLE_ESCAPES:
            out.append(_SIMPLE_ESCAPES[ch])
            continue
        o = ord(ch)
        if o < 0x20 or o == 0x7F:
            out.append('\\x%02x' % o)
        elif 0x80 <= o <= 0x9F or 0xD800 <= o <= 0xDFFF or o in (0xFEFF, 0x2028, 0x2029):
            # C1 controls, surrogates, BOM and line/paragraph separators: invisible or
            # illegal in source, so never emit them raw.
            out.append('\\u%04x' % o)
        else:
            out.append(ch)
    return '"' + ''.join(out) + '"'

def lean_int(i) -> str:
    i = int(i)
    return f"({i})" if i < 0 else str(i)

def lean_bool(b) -> str:
    return "true" if b else "false"

# ---------------------------------------------------------------------------
# Structure: each node becomes a head token plus a list of children.
#
# A child is one of:
#   ("atom", text)          already-rendered leaf (string/int/bool literal)
#   ("e", node)             sub-expression
#   ("s", node)             sub-statement
#   ("es", [node, ...])     list of sub-expressions  -> [a, b, c]
#   ("ps", [[k, v], ...])   list of expression pairs -> [(k, v), ...]
# ---------------------------------------------------------------------------

def _field(n, key, kind):
    if key not in n:
        raise ValueError(f"{kind} node {n.get('k')!r} is missing required field {key!r}")
    return n[key]

def expr_shape(n):
    if not isinstance(n, dict):
        raise ValueError(f"expression node is not an object: {n!r}")
    k = n.get("k")
    f = lambda key: _field(n, key, "expr")
    if k == "int":    return ".lit", [("atom", f"(.int {lean_int(f('v'))})")]
    if k == "str":    return ".lit", [("atom", f"(.str {lean_str(f('v'))})")]
    if k == "bool":   return ".lit", [("atom", f"(.bool {lean_bool(f('v'))})")]
    if k == "unit":   return ".lit", [("atom", ".unit")]
    if k == "name":   return ".name", [("atom", lean_str(f('v')))]
    if k == "binop":  return ".binop", [("atom", lean_str(f('op'))), ("e", f('a')), ("e", f('b'))]
    if k == "unop":   return ".unop", [("atom", lean_str(f('op'))), ("e", f('a'))]
    if k == "index":  return ".index", [("e", f('a')), ("e", f('b'))]
    if k == "call":   return ".call", [("atom", lean_str(f('f'))), ("es", f('args'))]
    if k == "hole":   return ".hole", [("atom", lean_str(f('label')))]
    # --- objects, containers, control ---
    if k == "field":  return ".field", [("e", f('a')), ("atom", lean_str(f('f')))]
    if k == "mcall":  return ".mcall", [("e", f('recv')), ("atom", lean_str(f('m'))), ("es", f('args'))]
    if k == "alloc":  return ".alloc", [("atom", lean_str(f('cls'))), ("es", f('args'))]
    if k == "fnref":  return ".fnref", [("atom", lean_str(f('v')))]
    # A function value that reads variables of an enclosing function. `fnref` is the
    # cheaper form and is used wherever the exporter proved there is nothing to capture.
    if k == "closure": return ".closure", [("atom", lean_str(f('f')))]
    if k == "listE":  return ".listE", [("es", f('items'))]
    if k == "tupleE": return ".tupleE", [("es", f('items'))]
    if k == "dictE":  return ".dictE", [("ps", f('pairs'))]
    if k == "cond":   return ".cond", [("e", f('c')), ("e", f('t')), ("e", f('e'))]
    if k == "isOp":   return ".isOp", [("atom", lean_bool(f('neg'))), ("e", f('a')), ("e", f('b'))]
    if k == "inOp":   return ".inOp", [("atom", lean_bool(f('neg'))), ("e", f('a')), ("e", f('b'))]
    raise ValueError(f"unknown expr node kind {k!r} (node: {json.dumps(n)[:200]})")

def stmt_shape(n):
    if not isinstance(n, dict):
        raise ValueError(f"statement node is not an object: {n!r}")
    k = n.get("k")
    f = lambda key: _field(n, key, "stmt")
    if k == "skip":     return ".skip", []
    if k == "brk":      return ".brk", []
    if k == "cont":     return ".cont", []
    if k == "holeS":    return ".hole", [("atom", lean_str(f('label')))]
    if k == "exprS":    return ".expr", [("e", f('e'))]
    if k == "assign":   return ".assign", [("atom", lean_str(f('x'))), ("e", f('e'))]
    if k == "ret":      return ".ret", [("e", f('e'))]
    if k == "seq":      return ".seq", [("s", f('a')), ("s", f('b'))]
    if k == "ifte":     return ".ifte", [("e", f('c')), ("s", f('t')), ("s", f('e'))]
    if k == "loop":     return ".loop", [("e", f('c')), ("s", f('body'))]
    # --- objects, iteration, exceptions ---
    if k == "setField": return ".setField", [("e", f('r')), ("atom", lean_str(f('f'))), ("e", f('v'))]
    if k == "setIndex": return ".setIndex", [("e", f('r')), ("e", f('i')), ("e", f('v'))]
    if k == "forIn":    return ".forIn", [("atom", lean_str(f('x'))), ("e", f('e')), ("s", f('body'))]
    if k == "tryCatch": return ".tryCatch", [("s", f('body')), ("atom", lean_str(f('x'))), ("s", f('handler'))]
    if k == "raise":    return ".raise", [("e", f('e'))]
    if k == "del":      return ".del", [("atom", lean_str(f('x')))]
    # --- module-level scope ---
    if k == "setGlobal":  return ".setGlobal", [("atom", lean_str(f('x'))), ("e", f('e'))]
    if k == "declGlobal": return ".declGlobal", [("atom", lean_str(f('x')))]
    raise ValueError(f"unknown stmt node kind {k!r} (node: {json.dumps(n)[:200]})")

SHAPE = {"e": expr_shape, "s": stmt_shape}

# ---------------------------------------------------------------------------
# Printing
# ---------------------------------------------------------------------------

def flat(node, kind) -> str:
    """Single-line rendering. Always fully parenthesised (except nullary constructors)."""
    head, children = SHAPE[kind](node)
    if not children:
        return head
    return "(" + head + " " + " ".join(flat_child(c) for c in children) + ")"

def flat_child(c) -> str:
    tag, val = c
    if tag == "atom":
        return val
    if tag in ("e", "s"):
        return flat(val, tag)
    if tag == "es":
        return "[" + ", ".join(flat(x, "e") for x in _seq(val)) + "]"
    if tag == "ps":
        return "[" + ", ".join(_flat_pair(p) for p in _seq(val)) + "]"
    raise AssertionError(tag)

def _seq(val):
    if val is None:
        return []
    if not isinstance(val, list):
        raise ValueError(f"expected a JSON array, got {val!r}")
    return val

def _flat_pair(p):
    if not (isinstance(p, list) and len(p) == 2):
        raise ValueError(f"dictE pair must be a 2-element array, got {p!r}")
    return "(" + flat(p[0], "e") + ", " + flat(p[1], "e") + ")"

def render(node, kind, col) -> str:
    """Render `node` starting at column `col`, wrapping if the flat form is too wide.

    The returned string's first line is *not* indented (the caller has already placed the
    cursor at `col`); continuation lines carry their own indentation.
    """
    one = flat(node, kind)
    if col + len(one) <= WIDTH or "\n" in one:
        return one
    head, children = SHAPE[kind](node)
    if not children:
        return one
    inner = col + INDENT
    pad = " " * inner
    parts = [render_child(c, inner) for c in children]
    return "(" + head + "\n" + "\n".join(pad + p for p in parts) + ")"

def render_child(c, col) -> str:
    tag, val = c
    if tag == "atom":
        return val
    if tag in ("e", "s"):
        return render(val, tag, col)
    if tag in ("es", "ps"):
        items = _seq(val)
        if not items:
            return "[]"
        one = flat_child(c)
        if col + len(one) <= WIDTH:
            return one
        # Leading-comma layout: every element starts at the same column, so the block
        # stays readable and each line is independently diffable.
        pad = " " * col
        rendered = ([render(x, "e", col + INDENT) for x in items] if tag == "es"
                    else [render_pair(p, col + INDENT) for p in items])
        body = ("\n" + pad + ", ").join(rendered)
        return "[ " + body + " ]"
    raise AssertionError(tag)

def render_pair(p, col) -> str:
    one = _flat_pair(p)
    if col + len(one) <= WIDTH:
        return one
    inner = col + INDENT
    return ("(" + render(p[0], "e", inner) + ",\n" + " " * inner
            + render(p[1], "e", inner) + ")")

# Kept as the public entry points other tooling may import.
def expr(n) -> str:
    return flat(n, "e")

def stmt(n) -> str:
    return flat(n, "s")

# ---------------------------------------------------------------------------

def ident(name: str) -> str:
    s = re.sub(r'[^A-Za-z0-9_]', '_', name)
    return ("f_" + s)[:120]

# Integer division/modulo convention by source language. Getting this wrong is silent
# mistranslation, so it is recorded per program rather than assumed.
DIALECT = {".py": ".python", ".c": ".cLike", ".h": ".cLike", ".cpp": ".cLike",
           ".java": ".cLike", ".js": ".cLike", ".ts": ".cLike", ".kt": ".cLike",
           ".go": ".cLike"}

def infer_dialect(funcs) -> str:
    exts = [os.path.splitext(f.get("file", ""))[1] for f in funcs]
    votes = [DIALECT[e] for e in exts if e in DIALECT]
    if not votes:
        return ".python"
    return max(set(votes), key=votes.count)

def render_func(f, nm) -> list:
    params = ", ".join(lean_str(p) for p in f.get("params", []))
    body = render(f["body"], "s", 10)  # "  , body := " is 12 wide; 10 keeps a margin
    return [
        f"/-- `{f['name']}`  (from `{f.get('file','?')}`) -/",
        f"def {nm} : Func :=",
        f"  {{ name := {lean_str(f['name'])}",
        f"  , params := [{params}]",
        f"  , body := {body} }}",
        "",
    ]

def main():
    src, dst = sys.argv[1], sys.argv[2]
    module = sys.argv[3] if len(sys.argv) > 3 else "Translated"
    with open(src) as fh:
        funcs = json.load(fh)
    dialect = infer_dialect(funcs)

    out = [
        "import Autoform.Lang.Core.Semantics",
        "",
        "/-!",
        f"# {module} — machine-generated",
        "",
        "Emitted by `cartographer/render_lean.py` from a Joern code property graph.",
        "Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the",
        "transpiler did not translate, tagged with the CPG node label responsible.",
        "-/",
        "",
        "namespace Autoform.Generated",
        "open Autoform.Core",
        "",
    ]
    names = []
    seen = set()
    for f in funcs:
        nm = ident(f["name"])
        while nm in seen:
            nm += "'"
        seen.add(nm)
        names.append(nm)
        try:
            out.extend(render_func(f, nm))
        except ValueError as e:
            raise SystemExit(f"render_lean: in function {f.get('name')!r} "
                             f"(from {f.get('file','?')}): {e}")

    # Module-level bindings are exported as zero-argument *initializer* functions, one
    # per source file, whose bodies are runs of `Stmt.setGlobal`. Running them is what
    # makes module-level constants, classes and `def`s resolvable, so the entry points
    # that need them have to know which functions they are.
    inits = [n for f, n in zip(funcs, names)
             if f["name"].endswith(":<module>") or f["name"].endswith(":<global>")]
    out.append("/-- Module-level initializers: run these to populate the globals frame")
    out.append("before calling any entry point. -/")
    out.append("def moduleInits : List Func := [" + ", ".join(inits) + "]")
    out.append("")
    out.append(f"/-- Source dialect: `{dialect}` (integer division/modulo convention). -/")
    out.append("def program : Program := { dialect := " + dialect + ", funcs := [")
    out.append(",\n".join("  " + n for n in names))
    out.append("] }")
    out.append("")
    out.append("end Autoform.Generated")
    with open(dst, "w") as fh:
        fh.write("\n".join(out))
    print(f"rendered {len(funcs)} functions -> {dst}")

if __name__ == "__main__":
    main()
