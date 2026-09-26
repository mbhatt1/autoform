#!/usr/bin/env python3
"""Render the language-neutral JSON AST as a Lean 4 `Autoform.Core.Program`.

Deterministic translation. Ordinary nodes map structurally to Core; suspended
generator bodies are compiled to explicit heap frames by generator_lowering.py.

Two invariants this file exists to protect:

* **Every expression and statement is fully parenthesised.** A previous version emitted
  `.ret .name "a"`, which Lean parses as `Stmt.ret` applied to three arguments. Anything
  that is not a nullary constructor gets wrapped, always.
* **The printer is a function of the JSON alone.** No dict/set iteration order, no
  timestamps, no paths beyond what the AST records — the same input must give a
  byte-identical file.

Usage: render_lean.py ast.json Out.lean [ModuleName]
"""
import json
import threading, sys, re, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'scripts'))
import deep_json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from generator_lowering import lower_generators
from python_truth_lowering import lower_truth_conditions
from python_truth_values import lower_truth_values

# Break a term across lines once its flat form would push past this column. Purely
# cosmetic: the layout below is whitespace-insensitive because every term is
# parenthesised or bracketed, so wrapping can never change what Lean parses.
WIDTH = 100
INDENT = 2
# Indentation stops growing past this column. Without a cap, a right-nested `seq` chain
# of n statements indents 2n spaces at its deepest line, so the OUTPUT is O(n^2)
# characters -- 2000 statements produced a 20 MB module, and the cost is in the file, not
# the algorithm. Real code nests: V8 has functions with thousands of statements in a
# single body. Past ~20 levels the staircase has stopped conveying structure anyway, and
# this is generated code that says "do not edit" at the top. Capping makes the output
# linear; it changes only where the continuation lines sit, never the term.
MAX_INDENT = 40

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

def lean_float_bits(v) -> int:
    """The IEEE-754 binary64 bit pattern of a decimal float literal.

    `Autoform/Lang/Core/Float.lean` models floats by bit pattern and its docstring names
    exactly this conversion: `struct.unpack('<Q', struct.pack('<d', x))[0]`. Emitting BITS
    rather than decimal text is the point -- `Format.ofDecimal` can round a decimal
    correctly on the way in, but going back out to decimal is not modelled, so bits are the
    only spelling that round-trips through the differential harness.

    Python's float() is correctly rounded, so this is the same value a C or Python compiler
    would produce for the same source text. A literal that does not parse is an error here
    rather than a silent 0.0: 854 lines of verified IEEE-754 are not improved by feeding
    them a guess.
    """
    import struct
    x = float(str(v).rstrip("fFlL"))
    return struct.unpack("<Q", struct.pack("<d", x))[0]


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

def lean_default(n):
    """A `DefaultValue` from the on-disk shapes a parameter default may take.

    Two forms, both time-invariant: a literal, and a reference to an in-program
    function. Anything else is not a default Core can bind at call time, and the
    exporter is supposed to have holed the definition rather than reach here.
    """
    if isinstance(n, dict) and n.get("k") == "fnref":
        return f"(.fnref {lean_str(_field(n, 'v', 'default function reference'))})"
    return f"(.lit {lean_lit(n)})"


def lean_lit(n):
    """A `Lit` from the same on-disk literal shapes `expr_shape` accepts.

    Used only for literal parameter defaults. Deliberately narrow: anything that is not
    one of the five literal forms is not a literal default, and the exporter is supposed
    to have holed the definition rather than reach here. Raising keeps a silent
    mistranslation from being the failure mode if it ever does.
    """
    if not isinstance(n, dict):
        raise ValueError(f"default is not an object: {n!r}")
    k = n.get("k")
    f = lambda key: _field(n, key, "literal default")
    if k == "int":   return f"(.int {lean_int(f('v'))})"
    if k == "str":   return f"(.str {lean_str(f('v'))})"
    if k == "bool":  return f"(.bool {lean_bool(f('v'))})"
    if k == "unit":  return ".unit"
    if k == "float": return f"(.float (Fl.ofBits {lean_float_bits(f('v'))}))"
    raise ValueError(f"parameter default is not a literal: {k!r}")


# Each field is a child kind and wire key, in constructor argument order. String
# and boolean atoms are encoded here; all other tags are walked by the printer.
_EXPR_FIELDS = {
    "name": "str:v", "binop": "str:op e:a e:b", "unop": "str:op e:a",
    "index": "e:a e:b", "slice": "e:a e:lo e:hi e:st",
    "call": "str:f es:args", "callV": "e:f es:args", "hole": "str:label",
    "boxNew": "e:e", "boxArray": "e:n", "irefIndex": "e:a e:i",
    "irefField": "e:a str:f", "derefIref": "e:p",
    "strByte": "e:a e:b", "strFrom": "e:a e:b", "field": "e:a str:f",
    "mcall": "e:recv str:m es:args", "alloc": "str:cls es:args",
    "fnref": "str:v", "closure": "str:f", "classClosure": "str:c",
    "listE": "es:items", "tupleE": "es:items", "dictE": "ps:pairs",
    "cond": "e:c e:t e:e", "isOp": "bool:neg e:a e:b",
    "inOp": "bool:neg e:a e:b", "starred": "e:a",
    "kwargE": "str:n e:a", "dstarred": "e:a",
}
_STMT_FIELDS = {
    "skip": "", "brk": "", "cont": "", "holeS": "str:label",
    "exprS": "e:e", "assign": "str:x e:e", "ret": "e:e", "seq": "s:a s:b",
    "ifte": "e:c s:t s:e", "loop": "e:c s:body", "breakBlock": "s:body",
    "setField": "e:r str:f e:v", "setIndex": "e:r e:i e:v",
    "delIndex": "e:a e:i", "setSlice": "e:r e:lo e:hi e:st e:v",
    "delSlice": "e:r e:lo e:hi e:st", "setDerefIref": "e:p e:v",
    "forIn": "str:x e:e s:body", "tryCatch": "s:body str:x s:handler",
    "tryFinally": "s:body s:fin", "raise": "e:e", "del": "str:x",
    "setGlobal": "str:x e:e", "declGlobal": "str:x",
}
_HEADS = {"callV": "callValue", "exprS": "expr", "holeS": "hole"}
_ATOMS = {"str": lean_str, "bool": lean_bool}


def _shape(n, kind, fields):
    if not isinstance(n, dict):
        noun = "expression" if kind == "expr" else "statement"
        raise ValueError(f"{noun} node is not an object: {n!r}")
    k = n.get("k")
    f = lambda key: _field(n, key, kind)
    if kind == "expr":
        if k in ("int", "str", "bool", "unit", "float"):
            return ".lit", [("atom", lean_lit(n))]
        if k == "boxFields":
            # Core uses expression pairs for both field dictionaries and dictE.
            return ".boxFields", [("ps", [
                [{"k": "str", "v": key}, val] for key, val in f("fields")])]
        if k == "boxFieldsRange":
            size = f("n")
            if not isinstance(size, int) or size < 0:
                raise ValueError(f"boxFieldsRange node has invalid n: {size!r}")
            atom = (f"((List.range {size}).map (fun i => "
                    '(Expr.lit (Lit.str s!"{i}"), Expr.lit Lit.unit)))')
            return ".boxFields", [("atom", atom)]
    if k not in fields:
        raise ValueError(f"unknown {kind} node kind {k!r} (node: {json.dumps(n)[:200]})")
    children = []
    for spec in fields[k].split():
        tag, key = spec.split(":")
        value = f(key)
        children.append(("atom", _ATOMS[tag](value)) if tag in _ATOMS else (tag, value))
    return "." + _HEADS.get(k, k), children


def expr_shape(n):
    return _shape(n, "expr", _EXPR_FIELDS)


def stmt_shape(n):
    return _shape(n, "stmt", _STMT_FIELDS)


SHAPE = {"e": expr_shape, "s": stmt_shape}


def _seq(val):
    if val is None:
        return []
    if not isinstance(val, list):
        raise ValueError(f"expected a JSON array, got {val!r}")
    return val


class _Term:
    """A measured document: no subtree strings are built or repeatedly flattened."""
    __slots__ = ("tag", "head", "children", "size")

    def __init__(self, tag, head, children):
        self.tag, self.head, self.children = tag, head, children
        if tag == "atom":
            self.size = len(head)
        else:
            overhead = len(head) + len(children) + 2 if tag == "node" else 2 * len(children)
            self.size = overhead + sum(child.size for child in children)


def _print(value, kind, col=None, cap=None):
    """Measure once, then emit once, using explicit stacks for every tree shape.

    `col=None` selects flat output. Layout uses the same measured documents, with
    leading commas for lists and capped continuation indentation. The output buffer
    contains only final fragments, so deep chains take linear time and space.
    """
    pending, measured = [(kind, value)], []
    while pending:
        tag, value = pending.pop()
        if tag == "finish":
            layout, head, count = value
            children = measured[-count:]
            del measured[-count:]
            measured.append(_Term(layout, head, children))
            continue
        if tag == "atom":
            measured.append(_Term(tag, value, []))
            continue
        if tag in SHAPE:
            head, children = SHAPE[tag](value)
            layout = "node"
            if not children:
                measured.append(_Term("atom", head, []))
                continue
        elif tag in ("es", "ps"):
            children = [("e" if tag == "es" else "pair", item) for item in _seq(value)]
            head, layout = "", "list"
            if not children:
                measured.append(_Term("atom", "[]", []))
                continue
        elif tag == "pair":
            if not (isinstance(value, list) and len(value) == 2):
                raise ValueError(f"dictE pair must be a 2-element array, got {value!r}")
            head, layout = "", "pair"
            children = [("e", item) for item in value]
        else:
            raise AssertionError(tag)
        pending.append(("finish", (layout, head, len(children))))
        pending.extend(reversed(children))
    root, = measured
    if cap is not None and root.size > cap:
        return None
    output, pending = [], [(root, col)]
    while pending:
        term, col = pending.pop()
        if isinstance(term, str):
            output.append(term)
            continue
        if term.tag == "atom":
            output.append(term.head)
            continue
        fits = col is None or col + term.size <= WIDTH
        inner = None if fits else min(col + INDENT, MAX_INDENT)
        if term.tag == "node":
            prefix, suffix = "(" + term.head, ")"
            separator = " " if fits else "\n" + " " * inner
            prefix += separator
        elif term.tag == "list":
            prefix, suffix = ("[", "]") if fits else ("[ ", " ]")
            separator = ", " if fits else "\n" + " " * col + ", "
        else:
            prefix, suffix = "(", ")"
            separator = ", " if fits else ",\n" + " " * inner
        output.append(prefix)
        pending.append((suffix, None))
        for index in range(len(term.children) - 1, -1, -1):
            pending.append((term.children[index], inner))
            if index:
                pending.append((separator, None))
    return "".join(output)


def flat(node, kind) -> str:
    return _print(node, kind)


def flat_capped(node, kind, cap):
    return _print(node, kind, cap=cap)


def render(node, kind, col) -> str:
    """Wrap at WIDTH; the caller supplies indentation for the first line."""
    return _print(node, kind, col)


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
# `.cc`/`.cxx`/`.hh`/`.hpp` are C++ exactly as `.cpp` is. Their absence was not
# hypothetical: V8's `src/base` is 104 `.cc` files against 53 `.h`, so its dialect was
# being decided by the *headers* alone, and a corpus of `.cc` files with no header
# aborted the render outright. Found by tests/test_render_lean.py, which recorded it as
# a strict xfail before it had a fix.
#
# `.js`/`.ts`/`.tsx`/`.jsx`/`.mjs`/`.cjs` map to `.javascript`, not `.cLike`. Mapping them
# to `.cLike` was itself a measured, confirmed wrong answer (docs/languages.md): `&&`/`||`
# returned a coerced boolean instead of an operand, and arithmetic wrapped at 32 bits
# instead of matching Node's IEEE-double `Number` (`2147483647 + 1` gave `-2147483648`
# instead of Node's `2147483648`). `Autoform.Core.Dialect.javascript`
# (`Autoform/Lang/Core/Syntax.lean`) is the real fix; this table just has to point at it.
DIALECT = {".py": ".python", ".c": ".cLike", ".h": ".cLike", ".cpp": ".cLike",
           ".cc": ".cLike", ".cxx": ".cLike", ".hh": ".cLike", ".hpp": ".cLike",
           # `.java`/`.go` are real constructors (`Autoform.Core.Dialect.java`/`.go`,
           # `Syntax.lean`): 64-bit Go `int`, value strings, boxed arrays/slices, Java's
           # reference `==` as a named hole. Kotlin/JVM shares Java's integer model and
           # boolean operators, so it rides `.java`; its structural string `==` lands on
           # the same conservative hole.
           ".java": ".java", ".kt": ".java", ".go": ".go",
           ".js": ".javascript", ".ts": ".javascript", ".tsx": ".javascript",
           ".jsx": ".javascript", ".mjs": ".javascript", ".cjs": ".javascript"}

def infer_dialect(funcs) -> str:
    """Pick the arithmetic/string dialect from file extensions.

    Refuses rather than defaulting. Defaulting to `.python` when no extension
    voted meant a `.tsx` file was translated with Python's floored division and
    modulo: measured, `-7 % 3` gave 2 where TypeScript gives -1, and `-7/2` gave
    -4 where TypeScript gives -3.5. That is the original modulo bug re-entering
    through the extension table, which is exactly the class of silent
    mistranslation the dialect parameter exists to prevent — so an unrecognized
    extension is an error, not an assumption.
    """
    exts = [os.path.splitext(f.get("file", ""))[1] for f in funcs]
    unknown = sorted({e for e in exts if e and e not in DIALECT})
    if unknown:
        raise SystemExit("render_lean: cannot infer dialect — unrecognized extensions: %s. "
                         "Use a supported source frontend or formalize the compiled binary "
                         "with autoform.sh --machine." % unknown)
    votes = [DIALECT[e] for e in exts if e in DIALECT]
    if not votes:
        seen = sorted({e for e in exts if e})
        raise SystemExit(
            "render_lean: cannot infer dialect — no known extension among %s.\n"
            "  Known: %s\n"
            "  Add the extension to DIALECT (with its real integer-division and\n"
            "  string semantics) rather than letting it default." % (seen or "[]",
                                                                    sorted(DIALECT)))
    dialects = sorted(set(votes))
    if len(dialects) != 1:
        raise SystemExit("render_lean: mixed source dialects %s cannot share one Core program. "
                         "Translate each dialect separately, or formalize the linked binary "
                         "with autoform.sh --machine; majority voting changes program semantics."
                         % dialects)
    return dialects[0]

def program_exc_classes(funcs) -> str:
    """The `Program.excClasses` literal: the corpus's own exception classes, as the module
    initializers carry them (`exceptionClasses`), deduplicated and sorted. `Stmt.raise`
    accepts these names exactly as it accepts the builtin ones (Python reference §8.4.1:
    a handler matches by class or base class, so the name is what matters)."""
    names = set()
    for f in funcs:
        for n in (f.get("exceptionClasses") or []):
            if not isinstance(n, str):
                raise ValueError(f"render_lean: malformed exceptionClasses entry {n!r}")
            names.add(n)
    return ", ".join(lean_str(n) for n in sorted(names))


def program_properties(funcs) -> str:
    """The `Program.properties` literal: every `(class, name)` a `@property` getter was
    recorded under, aggregated across the module initializers, deduplicated and sorted.

    Keyed by class as well as name, so two classes with a same-named property are not a
    conflict -- `evalExpr` dispatches on `(o.cls, f)` and picks the right one. Contrast
    `builtinBases`, which is keyed by class name alone and therefore has to drop a class
    recorded with two different bases.
    """
    pairs = set()
    for f in funcs:
        for pair in (f.get("classProperties") or []):
            if (not isinstance(pair, list) or len(pair) != 2
                    or not all(isinstance(x, str) for x in pair)):
                raise ValueError(f"render_lean: malformed classProperties entry {pair!r}")
            pairs.add((pair[0], pair[1]))
    return ", ".join("({}, {})".format(lean_str(c), lean_str(n)) for c, n in sorted(pairs))


def program_classes(funcs) -> str:
    """Render qualified class namespaces without collapsing duplicate identities."""
    declarations = []
    allowed = {'name', 'shortName', 'bases', 'attributes',
               'definitionBarrier', 'inheritanceBarrier', 'slots'}
    for function in funcs:
        rows = function.get('classDeclarations', [])
        if not isinstance(rows, list):
            raise ValueError('classDeclarations must be a list')
        for row in rows:
            if (not isinstance(row, dict) or set(row) - allowed
                    or not {'name', 'shortName', 'bases', 'attributes'} <= set(row)
                    or any(not isinstance(row[key], str) or not row[key]
                           for key in ('name', 'shortName'))
                    or not isinstance(row['bases'], list)
                    or any(not isinstance(base, str) or not base for base in row['bases'])
                    or not isinstance(row['attributes'], list)):
                raise ValueError('malformed class declaration')
            fields = ['name := ' + lean_str(row['name']),
                      'shortName := ' + lean_str(row['shortName']),
                      'bases := [' + ', '.join(map(lean_str, row['bases'])) + ']']
            attributes = []
            for attribute in row['attributes']:
                if (not isinstance(attribute, dict) or set(attribute) != {'name', 'kind', 'value'}
                        or attribute['kind'] not in ('method', 'property', 'stored', 'slot', 'opaque')
                        or any(not isinstance(attribute[key], str) or not attribute[key]
                               for key in ('name', 'value'))):
                    raise ValueError('malformed class attribute')
                attributes.append('(' + lean_str(attribute['name']) + ', .'
                                  + attribute['kind'] + ' ' + lean_str(attribute['value']) + ')')
            fields.append('attributes := [' + ', '.join(attributes) + ']')
            if 'slots' in row:
                slots = row['slots']
                if (not isinstance(slots, list)
                        or any(not isinstance(name, str) or not name for name in slots)
                        or len(set(slots)) != len(slots)):
                    raise ValueError('malformed class slot layout')
                fields.append('slots := some [' + ', '.join(map(lean_str, slots)) + ']')
            for key in ('definitionBarrier', 'inheritanceBarrier'):
                if key in row:
                    if not isinstance(row[key], str) or not row[key]:
                        raise ValueError('malformed class lookup barrier')
                    fields.append(key + ' := some ' + lean_str(row[key]))
            declarations.append((row['name'], '{ ' + ', '.join(fields) + ' }'))
    return ', '.join(rendered for _, rendered in sorted(declarations))


def render_func(f, nm) -> list:
    params = ", ".join(lean_str(p) for p in f.get("params", []))
    body = render(f["body"], "s", 10)  # "  , body := " is 12 wide; 10 keeps a margin
    # `vararg`/`kwarg` are emitted only when the AST records them, so a corpus with no
    # variadic parameters renders byte-identically to the way it did before the calling
    # convention existed. Both fields default to `none` in `Core.Func`.
    variadic = []
    if 'analysisBody' in f:
        variadic.append("  , analysisBody := some " + render(f['analysisBody'], 's', 10))
    if f.get("vararg") is not None:
        variadic.append(f"  , vararg := some {lean_str(f['vararg'])}")
    if f.get("kwarg") is not None:
        variadic.append(f"  , kwarg := some {lean_str(f['kwarg'])}")
    if 'pythonSignature' in f:
        signature = f['pythonSignature']
        keys = ('positionalOnly', 'keywordOnly', 'required')
        if (not isinstance(signature, dict) or not set(keys) <= set(signature)
                or set(signature) - set(keys) - {'isMethod', 'defaults', 'receiverKind', 'classAttrDefaults', 'receiverName'}):
            raise ValueError('invalid Python signature fields')
        if 'isMethod' in signature and type(signature['isMethod']) is not bool:
            raise ValueError('invalid Python method classification')
        # The only receiver kind Core distinguishes is the class of a `@classmethod`.
        # Anything else is not a value this renderer knows how to bind, and inventing
        # one is exactly the silent mistranslation a raise here prevents.
        if 'receiverKind' in signature and signature['receiverKind'] != 'class':
            raise ValueError('unknown Python receiver kind: %r' % (signature['receiverKind'],))
        ordinary = set(f.get('params', [])) - {f.get('vararg'), f.get('kwarg')}
        for key in keys:
            values = signature[key]
            if (not isinstance(values, list) or not all(isinstance(x, str) for x in values)
                    or len(set(values)) != len(values) or not set(values) <= ordinary):
                raise ValueError('invalid Python signature parameters: ' + key)
        if set(signature['positionalOnly']) & set(signature['keywordOnly']):
            raise ValueError('overlapping Python parameter kinds')
        fields = ', '.join(key + ' := [' + ', '.join(map(lean_str, signature[key])) + ']'
                           for key in keys)
        if 'isMethod' in signature:
            fields += ', isMethod := some ' + str(signature['isMethod']).lower()
        if 'receiverKind' in signature:
            fields += ', receiverKind := some ' + lean_str(signature['receiverKind'])
        # The stripped instance receiver's name, kept so `kwargsRejected` can refuse a
        # keyword of that name (`o.f(self=1)` on `def f(self, **kw)`). It was stripped, so
        # it must NOT also be an ordinary parameter, and it is a receiver, so the function
        # must be a method.
        if 'receiverName' in signature:
            name = signature['receiverName']
            if (not isinstance(name, str) or not name or name in f.get('params', [])
                    or signature.get('isMethod') is not True):
                raise ValueError('invalid Python receiver name: %r' % (name,))
            fields += ', receiverName := some ' + lean_str(name)
        defaults = signature.get('defaults') or []
        if defaults:
            # A default names an ordinary parameter, names it once, and never names a
            # required one -- "required" is defined as "has no default", so an overlap
            # would mean the two fields disagree about the same parameter.
            if not isinstance(defaults, list):
                raise ValueError('invalid Python defaults')
            names = [d[0] for d in defaults]
            if (not all(isinstance(d, list) and len(d) == 2 and isinstance(d[0], str)
                        for d in defaults)
                    or len(set(names)) != len(names)
                    or not set(names) <= ordinary
                    or set(names) & set(signature['required'])):
                raise ValueError('invalid Python defaults')
            rendered = ', '.join(f'({lean_str(nm)}, {lean_default(v)})' for nm, v in defaults)
            fields += ', defaults := [' + rendered + ']'
        class_attrs = signature.get('classAttrDefaults') or []
        if class_attrs:
            # `(parameter, class, mangled attribute)`. A parameter has ONE default, so it
            # may not also appear in `defaults`; and a defaulted parameter is not
            # `required`, for the same reason as above.
            lit_names = {d[0] for d in (signature.get('defaults') or [])}
            names = [d[0] for d in class_attrs]
            if (not isinstance(class_attrs, list)
                    or not all(isinstance(d, list) and len(d) == 3
                               and all(isinstance(x, str) for x in d) for d in class_attrs)
                    or len(set(names)) != len(names)
                    or not set(names) <= ordinary
                    or set(names) & set(signature['required'])
                    or set(names) & lit_names):
                raise ValueError('invalid Python class-attribute defaults')
            rendered = ', '.join(f'({lean_str(p)}, {lean_str(c)}, {lean_str(a)})'
                                 for p, c, a in class_attrs)
            fields += ', classAttrDefaults := [' + rendered + ']'
        variadic.append('  , pythonSignature := some { ' + fields + ' }')
    return [
        f"/-- `{f['name']}`  (from `{f.get('file','?')}`) -/",
        f"def {nm} : Func :=",
        f"  {{ name := {lean_str(f['name'])}",
        f"  , params := [{params}]",
        *variadic,
        f"  , body := {body} }}",
        "",
    ]

def _run_main():
    src, dst = sys.argv[1], sys.argv[2]
    module = sys.argv[3] if len(sys.argv) > 3 else "Translated"
    funcs = lower_generators(deep_json.load(src))
    dialect = infer_dialect(funcs)
    if dialect == '.python':
        funcs = lower_truth_values(lower_truth_conditions(funcs))
    auxiliary = [helper for function in funcs
                 for kind in ('generatorHelpers', 'truthHelpers', 'decoratedEntries')
                 for helper in function.get(kind, [])]

    out = [
        "import Autoform.Lang.Core.Semantics",
        "",
        "-- Lean's default `maxRecDepth` (512) is a guard against runaway elaboration, not",
        "-- a statement about reasonable programs. A deep-embedded function body is one",
        "-- term, so the elaborator's recursion depth tracks the *source's* nesting depth:",
        "-- Linux `lib/` hit the limit at two declarations and the whole module failed to",
        "-- type-check. Raising it costs nothing for shallow modules and is the difference",
        "-- between compiling a real codebase and not.",
        "--",
        "-- 8000 was not enough either. The binding constraint is not the nesting depth of",
        "-- any one body (Ansible's deepest is 297) but the `funcs := [...]` list literal,",
        "-- which elaborates as nested cons cells -- one frame or more per function, and",
        "-- Ansible has 5,546. So the limit has to scale with the module's function count,",
        "-- not with how deep its code happens to be.",
        f"set_option maxRecDepth {max(8000, 8 * len(funcs) + 8000)}",
        "",
        "-- Lean's default `maxHeartbeats` (200000) budgets ONE declaration's own",
        "-- elaboration cost, separately from `maxRecDepth` above (which bounds nesting",
        "-- depth, not total work). A single source file whose top-level declarations",
        "-- carry a large static table -- SQLite's `test_vdbecov.c`, whose `<global>`",
        "-- initializer alone is ~5.3M characters of generated Lean -- blows through the",
        "-- default budget on that ONE declaration and fails with a `(deterministic)",
        "-- timeout at isDefEq` error, unrelated to whether the translation is correct.",
        "-- Unlike `maxRecDepth`, this does not scale with function COUNT (Ansible-style",
        "-- corpora with thousands of small functions never hit it); it is one",
        "-- pathologically large declaration, which no per-function-count formula would",
        "-- predict, so this disables the budget outright rather than guessing a bigger",
        "-- number that the next large static table would just exceed again. Scoped to",
        "-- THIS generated file only (`set_option` here does not touch hand-written proof",
        "-- files elsewhere in the project, which keep the default as a real safety net",
        "-- against a genuine runaway elaboration bug while someone is editing them).",
        "set_option maxHeartbeats 0",
        "",
        "/-!",
        f"# {module} — machine-generated",
        "",
        "Emitted by `cartographer/render_lean.py` from a Joern code property graph.",
        "Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the",
        "transpiler did not translate, tagged with the CPG node label responsible.",
        "-/",
        "",
        # Each corpus gets its OWN namespace, `Autoform.Generated.<Module>`, so that
        # `program` becomes `Autoform.Generated.<Module>.program` and two rendered
        # corpora can live in one import graph. When every module declared
        # `namespace Autoform.Generated`, importing a second one failed outright with
        # "environment already contains 'Autoform.Generated.program'", which is why the
        # proof modules for cachetools and for V8 could never share a build -- and hence
        # why they sat outside the root import graph, unchecked by `leanchecker --fresh`.
        f"namespace Autoform.Generated.{module}",
        "open Autoform.Core",
        "",
    ]
    names = []
    seen = set()
    for f in funcs + auxiliary:
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
    # Classes whose single base is a builtin type (`class X(tuple)`), as recorded by
    # `cartographer/export_ast.sc` on the module initializer of the file that declares
    # them. Collected across all entries, deduplicated, and *dropped* on conflict: two
    # same-named classes with different bases cannot be told apart by `Expr.alloc`, which
    # carries only the short name, so the honest answer is to record neither and leave
    # both as opaque references -- exactly the pre-existing behaviour.
    bases = {}
    conflicts = set()
    for f in funcs:
        for cls, base in sorted((f.get("classBases") or {}).items()):
            if cls in bases and bases[cls] != base:
                conflicts.add(cls)
            bases[cls] = base
    for c in conflicts:
        bases.pop(c, None)
    base_ctor = {"tuple": ".tuple", "list": ".list", "dict": ".dict", "str": ".str"}
    unknown = sorted(set(b for b in bases.values() if b not in base_ctor))
    if unknown:
        raise SystemExit("render_lean: unmodelled builtin base(s) {}; "
                         "Core.BuiltinBase has no constructor for them".format(unknown))
    bb = ", ".join("({}, {})".format(lean_str(c), base_ctor[bases[c]])
                   for c in sorted(bases))
    props = program_properties(funcs)
    excs = program_exc_classes(funcs)
    classes = program_classes(funcs)

    extra = ""
    if auxiliary:
        extra += ", auxiliaryFuncs := [" + ", ".join(names[len(funcs):]) + "]"
    notes = []
    if classes:
        extra += ", classDecls := [" + classes + "]"
        notes.append("`classDecls` records qualified class namespaces and ordered bases;")
        notes.append("unresolved ancestry remains an explicit lookup boundary.")
    if bb:
        extra += ", builtinBases := [" + bb + "]"
        notes.append("`builtinBases` lists the classes whose base is a builtin type, so that")
        notes.append("`Expr.alloc` builds a `Val.bobj` and not an opaque `Val.ref`.")
    if props:
        extra += ", properties := [" + props + "]"
        notes.append("`properties` lists every `@property` as `(class, name)`, so that an")
        notes.append("attribute read of one runs the getter instead of missing the field.")
    if excs:
        extra += ", excClasses := [" + excs + "]"
        notes.append("`excClasses` lists the program's own exception classes, so that")
        notes.append("`raise` of one is a represented exception and handlers can match it.")
    if notes:
        out.append(f"/-- Source dialect: `{dialect}` (integer division/modulo convention).")
        out.append("")
        out.extend(notes[:-1])
        out.append(notes[-1] + " -/")
    else:
        out.append(f"/-- Source dialect: `{dialect}` (integer division/modulo convention). -/")
    out.append("def program : Program := { dialect := " + dialect + extra + ", funcs := [")
    out.append(",\n".join("  " + n for n in names[:len(funcs)]))
    out.append("] }")
    out.append("")
    out.append(f"end Autoform.Generated.{module}")
    with open(dst, "w") as fh:
        fh.write("\n".join(out))
    print(f"rendered {len(funcs)} functions -> {dst}")

def main():
    """Render on a thread with a large stack.

    The emitters are mutually recursive over the AST, so depth is the source's nesting
    depth, not a constant. Python's default limit is 1000 frames and this file never
    raised it -- `scripts/lang_matrix.py` set it to 100000 before calling in, but
    `autoform.sh` invokes this script directly, so the default applied to every real run.
    It failed at 247 consecutive top-level statements.

    Raising `setrecursionlimit` alone is not enough and is actively dangerous: the limit
    is a guard against overrunning the *C* stack, and lifting it without a bigger stack
    turns a clean RecursionError into a segfault. A thread with an explicit stack size is
    the portable way to get both.
    """
    sys.setrecursionlimit(300_000)
    try:
        threading.stack_size(512 * 1024 * 1024)
    except (ValueError, RuntimeError):
        try:
            threading.stack_size(64 * 1024 * 1024)   # some platforms cap this
        except (ValueError, RuntimeError):
            pass
    box = {}

    def go():
        try:
            _run_main()
        except BaseException as e:        # noqa: BLE001 - re-raised on the main thread
            box["e"] = e

    t = threading.Thread(target=go)
    t.start()
    t.join()
    if "e" in box:
        raise box["e"]


if __name__ == "__main__":
    main()
