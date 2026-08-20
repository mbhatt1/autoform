#!/usr/bin/env python3
"""Differential harness: Lean semantics vs. the real runtime.

This is the conformance oracle from STRATEGY.md §2/§5. It is not optional
infrastructure: a proof about a semantics that does not match the real runtime is
theater. Here we test the *transpiler + semantics* jointly, which is exactly the
composite the ledger claims.

Two sources of test cases, in value order:

1. **The repository's own test suite** (STRATEGY.md §3: "every repo ships its own
   conformance suite"). We run the project's pytest/unittest suite under a
   `sys.settrace` hook that records `(function, receiver, args, outcome)` for every call
   that lands in a function we translated, then replay exactly those tuples against the
   Lean `Autoform.Core` interpreter. This gives *realistic* arguments — including
   strings, lists, dicts and live objects — and reaches code random ints never can.
2. **Random integers** for module-level functions, as a fallback / supplement.

Class methods are testable because the recorded receiver is snapshotted into a Lean
`Heap` literal and passed as `self`; the generated scratch file calls `applyFunc`
directly rather than `runFunc`, which always starts from an empty heap.

Outcomes are three-valued, never two: agreement, divergence, and INCONCLUSIVE
(`hole`, `outOfFuel`, or a value the harness cannot faithfully encode). A case that was
not actually compared is never reported as passing — that is the cardinal sin here.

Usage: differential.py <ast.json> <source-dir> <lean-module> [n-cases] [--tests DIR]
"""
import json, sys, subprocess, random, importlib.util, os, re, glob, io
import contextlib, inspect, functools

random.seed(20260819)   # deterministic: workflows/proofs must be reproducible

FUEL = 5000
MAX_TOTAL_CASES = 600      # keep the generated Lean file compile-bounded
MAX_DEPTH = 8              # value-encoding depth limit
MAX_ELEMS = 512            # value-encoding breadth limit (a resource
                           # bound, not a fidelity one: containers are
                           # encoded whole or refused, never truncated)


# --------------------------------------------------------------------------- AST

def has_hole(n):
    """Tolerant of unknown node kinds: we only look for the hole markers."""
    if isinstance(n, dict):
        if n.get("k") in ("hole", "holeS"): return True
        return any(has_hole(v) for v in n.values())
    if isinstance(n, list): return any(has_hole(v) for v in n)
    return False


PY_NAME = re.compile(r'(?P<file>.+?):<module>\.(?P<qual>.+)')


def classify(f):
    """(relfile, qualname, is_method) for a Python AST entry, or None."""
    m = PY_NAME.fullmatch(f["name"])
    if not m: return None
    qual = m.group("qual")
    if "<" in qual: return None          # <lambda>N, <redefined>N: no stable call site
    return m.group("file"), qual, ("." in qual)


# ------------------------------------------------------------------ value encoding
#
# Python value -> Lean `Val`, allocating plain objects into a `Heap` (a list of `Obj`).
# Returns None when the value has no faithful Core representation; the caller then
# skips the case rather than comparing something it made up.

class Unencodable(Exception):
    pass


class Encoder:
    """Python value -> Core `Val`, with one encoding per value in *every* position.

    Invariants, all of them load-bearing for the oracle's honesty:

    * A given Python object encodes to the same `Val.ref` whether it appears as the
      receiver, inside a receiver's field, as an argument, or in the result — the memo
      is keyed on `id` and shared across the whole case.
    * `tuple`/`list`/`dict` *subclasses* (e.g. cachetools' `_HashedTuple`) encode
      structurally, by value, in every position — never sometimes-value/sometimes-ref.
    * Nothing is dropped. If any value, however deeply nested inside a receiver, has
      no faithful Core representation, the encoder raises and the *whole case* is
      abandoned. A partially-encoded receiver reads back as `unit` in Core and would
      surface as a confident divergence the harness itself manufactured.
    """

    def __init__(self):
        self.heap = []          # list of (cls, [(field, Val)])
        self.byid = {}          # id(obj) -> ref index
        self.objs = {}          # ref index -> the live object (keeps ids alive)
        self.pin = set()        # ids present before the result was encoded

    def enc(self, v, depth=0, in_key=False):
        if depth > MAX_DEPTH: raise Unencodable("depth")
        if v is None: return ("unit",)
        if isinstance(v, bool): return ("bool", v)
        if isinstance(v, int): return ("int", v)
        if isinstance(v, str): return ("str", v)
        if isinstance(v, (list, tuple)):
            # A *subclass* of a builtin container is not a Core container: the
            # transpiler emits `Expr.alloc "_HashedTuple" [...]`, i.e. a heap object
            # whose fields do not carry the elements at all. A Python value and a Core
            # object are then two different things and comparing them would be the
            # apparatus inventing a disagreement, so refuse.
            if type(v) is not list and type(v) is not tuple:
                raise Unencodable("container-subclass:" + type(v).__name__)
            if len(v) > MAX_ELEMS: raise Unencodable("wide")
            k = "tuple" if isinstance(v, tuple) else "list"
            return (k, [self.enc(x, depth + 1, in_key) for x in v])
        if isinstance(v, dict):
            if type(v) is not dict:
                raise Unencodable("container-subclass:" + type(v).__name__)
            if len(v) > MAX_ELEMS: raise Unencodable("wide")
            # Keys are the subtle case: CPython looks them up by `__hash__`/`__eq__`,
            # which user classes override (cachetools' own tests define a
            # `RecursiveEquals` whose *distinct* instances compare equal), while Core
            # compares `Val`s structurally with `.ref` identity. Any object inside a
            # key therefore makes the lookup unfaithful in either direction, so the
            # case is refused rather than compared.
            return ("dict", [(self.enc(k, depth + 1, True),
                              self.enc(x, depth + 1, in_key)) for k, x in v.items()])
        if isinstance(v, type) or inspect.isroutine(v) or isinstance(v, (
                staticmethod, classmethod, property, functools.partial)):
            # `METHOD_REF`/`TYPE_REF` values: Core models them by name only.
            n = getattr(v, "__qualname__", None) or getattr(v, "__name__", None)
            if n: return ("fn", n)
            raise Unencodable("callable")
        # a callable *instance* is still an object with fields — encode it as one
        if isinstance(v, (float, complex, bytes, frozenset, set)):
            raise Unencodable(type(v).__name__)
        if in_key:
            raise Unencodable("object-as-dict-key")
        return ("ref", self.alloc(v, depth))

    def alloc(self, obj, depth):
        """Snapshot a plain Python object into the heap. Cycles resolve to the same
        ref, which is exactly the identity semantics `Val.ref` has."""
        if id(obj) in self.byid: return self.byid[id(obj)]
        if isinstance(obj, type) or inspect.isroutine(obj):
            raise Unencodable("callable")
        fields = {}
        if hasattr(obj, "__dict__"):
            fields.update(vars(obj))
        for cls in type(obj).__mro__:
            for s in getattr(cls, "__slots__", ()) or ():
                if hasattr(obj, s): fields[s] = getattr(obj, s)
        slotted = any(getattr(c, "__slots__", None) is not None
                      for c in type(obj).__mro__)
        if not fields and not hasattr(obj, "__dict__") and not slotted:
            raise Unencodable("opaque")     # C-level object with no inspectable state
        if len(fields) > MAX_ELEMS: raise Unencodable("wide-object")
        idx = len(self.heap)
        self.heap.append(None)                  # reserve the slot before recursing
        self.byid[id(obj)] = idx
        self.objs[idx] = obj
        out = [(str(k), self.enc(val, depth + 1)) for k, val in fields.items()]
        self.heap[idx] = (type(obj).__name__, out)
        return idx

    def freeze(self):
        """Mark the objects that existed before the call returned."""
        self.pin = set(self.byid)

    def enc_result(self, v):
        """Encode a returned value in the *same* namespace as the arguments.

        An object the callee freshly allocated has no counterpart in the heap Core was
        given, so its `Val.ref` would be a number with no shared meaning — refuse it
        instead of comparing addresses across two different allocators."""
        r = self.enc(v)
        if any(i not in self.pin for i in self.byid):
            raise Unencodable("result-allocates-fresh-object")
        return r


def lean_val(v):
    t = v[0]
    if t == "unit": return "Val.unit"
    if t == "bool": return "Val.bool " + ("true" if v[1] else "false")
    if t == "int":  return "Val.int (%d)" % v[1]
    if t == "str":  return "Val.str " + json.dumps(v[1])
    if t == "ref":  return "Val.ref (base + %d)" % v[1]
    if t == "fn":   return "Val.fn " + json.dumps(v[1])
    if t in ("list", "tuple"):
        return "Val.%s [%s]" % (t, ", ".join(lean_val(x) for x in v[1]))
    if t == "dict":
        return "Val.dict [%s]" % ", ".join("(%s, %s)" % (lean_val(a), lean_val(b))
                                           for a, b in v[1])
    raise Unencodable(t)


def lean_heap(heap):
    # named fields, not `⟨…⟩`: `Obj` has grown a field before (`captured`) and
    # anonymous-constructor literals fail the whole run when it happens again
    return "[%s]" % ", ".join(
        "{ cls := %s, fields := [%s] }"
        % (json.dumps(cls), ", ".join("(%s, %s)" % (json.dumps(k), lean_val(val))
                                      for k, val in fields))
        for cls, fields in heap)


# ------------------------------------------------------------------- repr parsing
#
# We cannot edit the Lean sources, so we parse Lean's derived `Repr` output. It is
# emitted on one line (`Format.pretty` at a huge width) and fully parenthesised.

TOKEN = re.compile(r'\s*("(?:[^"\\]|\\.)*"|[A-Za-z_][A-Za-z0-9_.!?]*|-?\d+|[()\[\],])')


def tokenize(s):
    out, i = [], 0
    while i < len(s):
        m = TOKEN.match(s, i)
        if not m: break
        out.append(m.group(1)); i = m.end()
    return out


class P:
    def __init__(self, toks): self.t, self.i = toks, 0
    def peek(self): return self.t[self.i] if self.i < len(self.t) else None
    def next(self):
        v = self.peek(); self.i += 1; return v
    def expect(self, c):
        if self.next() != c: raise ValueError("expected " + c)

    def atom(self):
        tok = self.peek()
        if tok is None: raise ValueError("eof")
        if tok == "(":
            self.next()
            items = [self.atom()]
            while self.peek() == ",":
                self.next(); items.append(self.atom())
            self.expect(")")
            return items[0] if len(items) == 1 else ("pair", items)
        if tok == "[":
            self.next(); items = []
            if self.peek() != "]":
                items.append(self.atom())
                while self.peek() == ",":
                    self.next(); items.append(self.atom())
            self.expect("]")
            return ("seq", items)
        if re.fullmatch(r'-?\d+', tok):
            self.next(); return ("int", int(tok))
        if tok.startswith('"'):
            self.next(); return ("str", json.loads(tok))
        self.next()
        name = tok.split(".")[-1]
        qual = ".".join(tok.split(".")[-2:])
        if qual in ("Val.unit",):            return ("unit",)
        if qual in ("EResult.outOfFuel",):   return ("outOfFuel",)
        if name in ("true", "false"):        return ("bool", name == "true")
        arg = self.atom()
        if qual == "Val.int":   return ("int", arg[1])
        if qual == "Val.str":   return ("str", arg[1])
        if qual == "Val.bool":  return ("bool", arg[1])
        if qual == "Val.ref":   return ("ref", arg[1])
        if qual == "Val.fn":    return ("fn", arg[1])
        if qual == "Val.list":  return ("list", arg[1])
        if qual == "Val.tuple": return ("tuple", arg[1])
        if qual == "Val.dict":
            return ("dict", [(p[1][0], p[1][1]) for p in arg[1]])
        if qual in ("EResult.val", "EResult.exn", "EResult.hole"):
            return (name, arg)
        raise ValueError("unknown ctor " + tok)


def parse_result(line):
    """-> ('val', Val) | ('exn', Val) | ('hole', str) | ('outOfFuel',)"""
    p = P(tokenize(line))
    r = p.atom()
    if r[0] == "hole":
        return ("hole", r[1][1] if r[1][0] == "str" else "?")
    if r[0] in ("val", "exn"): return (r[0], r[1])
    if r[0] == "outOfFuel": return ("outOfFuel",)
    raise ValueError("not an EResult: " + line[:80])


# ---------------------------------------------------------------------- comparison

def same(py, ln, base):
    """Compare an encoded Python value against a parsed Lean value.

    Dicts compare order-insensitively: Core's `Val.dict` is an association list whose
    order is observable, but Python's insertion order is not part of the contract we
    are checking here, and pretending otherwise would manufacture divergences."""
    if py[0] != ln[0]:
        # Core has no separate tuple/list distinction at some call sites; still, do not
        # paper over it — report as a mismatch.
        return False
    t = py[0]
    if t in ("unit",): return True
    if t in ("int", "bool", "str"): return py[1] == ln[1]
    if t == "fn":
        # `Val.fn` names are spelled differently on the two sides: CPython reports a
        # `__qualname__` (`TTLCache._Link`), Joern a fully-qualified one
        # (`pkg/mod.py:<module>.TTLCache._Link`). Core's own `Ctx.resolve` matches
        # callables by dotted suffix, so accept exactly that and nothing looser.
        a, b = py[1].split(":")[-1], ln[1].split(":")[-1]
        return a == b or a.endswith("." + b) or b.endswith("." + a)
    if t == "ref": return py[1] + base == ln[1]
    if t in ("list", "tuple"):
        return len(py[1]) == len(ln[1]) and all(same(a, b, base)
                                                for a, b in zip(py[1], ln[1]))
    if t == "dict":
        if len(py[1]) != len(ln[1]): return False
        rest = list(ln[1])
        for k, v in py[1]:
            for j, (k2, v2) in enumerate(rest):
                if same(k, k2, base) and same(v, v2, base):
                    rest.pop(j); break
            else:
                return False
        return True
    return False


def show(v):
    t = v[0]
    if t == "unit": return "unit"
    if t in ("int", "bool", "str", "fn", "ref"): return "%s %r" % (t, v[1])
    if t in ("list", "tuple"): return "%s[%s]" % (t, ", ".join(show(x) for x in v[1]))
    if t == "dict": return "{%s}" % ", ".join("%s: %s" % (show(a), show(b))
                                              for a, b in v[1])
    return str(v)


# ------------------------------------------------------------------- test tracing

def find_tests(src_root):
    """Locate the repository's own test suite."""
    roots, cur = [], os.path.abspath(src_root)
    for _ in range(3):
        roots.append(cur); cur = os.path.dirname(cur)
    seen = []
    for r in roots:
        for name in ("tests", "test"):
            d = os.path.join(r, name)
            if os.path.isdir(d) and glob.glob(os.path.join(d, "**", "test_*.py"),
                                              recursive=True):
                seen.append(d)
        if glob.glob(os.path.join(r, "test_*.py")): seen.append(r)
    out = []
    for d in seen:
        if d not in out: out.append(d)
    return out


def resolve_src_root(src_root, rel_files):
    """Find the directory the AST's relative paths are actually rooted at.

    Joern's paths are relative to whatever directory was parsed, which for the modern
    `src/` layout is `<repo>/src` while the tests live at `<repo>/tests`. Pointing the
    harness at the repo root is the natural thing to do and used to silently yield zero
    test-derived cases, so correct it here instead."""
    rels = [r for r in rel_files if r]
    if not rels: return src_root

    def hits(root):
        return sum(1 for r in rels if os.path.exists(os.path.join(root, r)))
    best, n = os.path.abspath(src_root), hits(src_root)
    if n == len(rels): return best
    cands = [os.path.join(src_root, d) for d in ("src", "lib", "python")]
    try:
        cands += [os.path.join(src_root, d.name) for d in os.scandir(src_root)
                  if d.is_dir() and not d.name.startswith(".")]
    except OSError:
        pass
    for c in cands:
        if not os.path.isdir(c): continue
        m = hits(c)
        if m > n: best, n = os.path.abspath(c), m
    if os.path.abspath(best) != os.path.abspath(src_root):
        print("source root corrected: %s -> %s (%d/%d AST paths resolve there)"
              % (src_root, best, n, len(rels)))
    return best


def build_lineno_index(src_root, wanted_files):
    """(abs source file, first line of def) -> qualified AST name.

    Python 3.9 has no `co_qualname`, so we recover the qualified name from the source
    with the `ast` module and key on the code object's `co_firstlineno`."""
    import ast as pyast

    def mangle(name, cls):
        """CPython private name mangling: inside `class C`, `__x` becomes `_C__x`.

        The transpiler applies this rule, so the qualnames recovered here must too —
        otherwise a traced call to `LFUCache.__touch` never matches the translated
        `LFUCache._LFUCache__touch` and the function is silently dropped from the oracle's
        reach. Two or more leading underscores, at most one trailing."""
        if cls is None: return name
        if not name.startswith("__"): return name
        if name.endswith("__"): return name
        return "_" + cls.lstrip("_") + name

    idx = {}
    for rel in wanted_files:
        path = os.path.join(src_root, rel)
        if not os.path.exists(path): continue
        try:
            tree = pyast.parse(open(path, encoding="utf-8").read(), path)
        except SyntaxError:
            continue
        stack = []

        def walk(node, prefix, cls):
            for ch in pyast.iter_child_nodes(node):
                if isinstance(ch, (pyast.FunctionDef, pyast.AsyncFunctionDef)):
                    qual = prefix + mangle(ch.name, cls)
                    # decorators shift co_firstlineno to the first decorator line
                    lines = [ch.lineno] + [d.lineno for d in ch.decorator_list]
                    for ln in lines:
                        idx.setdefault((os.path.abspath(path), ln), (rel, qual))
                    # a nested def does not change the mangling class
                    walk(ch, qual + ".", cls)
                elif isinstance(ch, pyast.ClassDef):
                    walk(ch, prefix + ch.name + ".", ch.name)
                else:
                    walk(ch, prefix, cls)
        walk(tree, "", None)
    return idx


VARARGS, VARKW = 0x04, 0x08


def frame_param_order(code):
    """Parameter names in *source* order, plus how each one binds.

    `co_varnames` lists positional names, then keyword-only names, then `*args`, then
    `**kwargs` — which is not the order they were written in, and not the order the
    transpiler recorded. Rebuild the source order so it can be checked against the AST.
    """
    n, k = code.co_argcount, code.co_kwonlyargcount
    pos = list(code.co_varnames[:n])
    kwonly = list(code.co_varnames[n:n + k])
    i = n + k
    star = None
    if code.co_flags & VARARGS:
        star = code.co_varnames[i]; i += 1
    dstar = code.co_varnames[i] if code.co_flags & VARKW else None
    order = [(p, "pos") for p in pos]
    if star is not None: order.append((star, "star"))
    order += [(p, "kwonly") for p in kwonly]
    if dstar is not None: order.append((dstar, "dstar"))
    return order


def bind_args(order, loc, enc, ast_params, self_name):
    """Encode one call's arguments in the order Core will bind them.

    Core binds by position: `applyFunc` zips `Func.params` with the argument list. That
    is faithful to CPython only if the transpiler's parameter list is name-for-name the
    source parameter list, so require exactly that and refuse otherwise — a silent
    off-by-one in parameter binding would be indistinguishable from a semantics bug.

    `*args` binds to a tuple and `**kwargs` to a dict, which is what the *callee* sees
    and what the translated body reads (`cachetools.keys.hashkey` does `args + _kwmark`
    on it). Refusing these cost ~13k calls for no fidelity reason.
    """
    names = [n for n, _ in order]
    if self_name is not None: names = names[1:]
    if ast_params is not None and names != list(ast_params):
        raise ParamMismatch("%s vs %s" % (names, list(ast_params)))
    slf, args = None, []
    for i, (n, kind) in enumerate(order):
        if i == 0 and n == self_name:
            slf = enc.enc(loc[n])
            continue
        v = loc[n]
        args.append(enc.enc(v))
    return slf, args


class ParamMismatch(Exception):
    pass


def trace_tests(src_root, test_dirs, index, wanted, limit_per_fn, stats,
                params_by_name=None, live=None, pool=None):
    """Run the project's test suite under `sys.settrace`, recording calls into `wanted`.

    Each record is a fully-encoded snapshot taken *at call time*, so later mutation of
    the arguments cannot corrupt it."""
    records = []
    counts = {}
    live_files = set(p for (p, _) in index)

    params_by_name = params_by_name if params_by_name is not None else {}
    live = live if live is not None else {}        # class name -> live instances
    pool = pool if pool is not None else {}        # parameter name -> live values

    def snapshot(frame, qual, key):
        code = frame.f_code
        order = frame_param_order(code)
        loc = frame.f_locals
        self_name = order[0][0] if order and order[0][0] == "self" else None
        enc = Encoder()
        try:
            slf, args = bind_args(order, loc, enc, params_by_name.get(key), self_name)
        except ParamMismatch as e:
            stats["skip_param_mismatch"] = stats.get("skip_param_mismatch", 0) + 1
            r = stats.setdefault("param_mismatch_detail", {})
            r[qual] = e.args[0]
            return None
        except (Unencodable, KeyError) as e:
            stats["skip_unencodable_args"] += 1
            r = stats.setdefault("unencodable_reasons", {})
            k = "%s: %s" % (qual, e.args[0] if e.args else type(e).__name__)
            r[k] = r.get(k, 0) + 1
            return None
        if self_name is not None:
            if slf is None or slf[0] != "ref":
                # e.g. a `tuple` subclass: the receiver is a value, not an object with
                # fields, and Core has no such receiver.
                stats["skip_self_not_object"] = \
                    stats.get("skip_self_not_object", 0) + 1
                return None
            # keep the live receiver: it is the only way to exercise sibling methods
            # the suite never calls (see `constructed_cases`)
            inst = loc[self_name]
            bucket = live.setdefault(type(inst).__name__, [])
            if len(bucket) < 4 and not any(o is inst for o in bucket):
                bucket.append(inst)
        for (n, kind) in order:
            if n == self_name: continue
            b = pool.setdefault(n, [])
            if len(b) < 6:
                try:
                    if not any(o is loc[n] for o in b): b.append(loc[n])
                except KeyError:
                    pass
        return enc, slf, args

    # frames have no user-writable slot, so carry per-call state keyed by frame id
    state_by_frame = {}

    def local2(frame, event, arg):
        st = state_by_frame.get(id(frame))
        if st is None: return None
        if event == "exception":
            st["exn"] = arg[0].__name__
        elif event == "return":
            rec = st["rec"]
            if arg is None and st.get("exn"):
                rec["outcome"] = ("exn", st["exn"])
            else:
                try:
                    rec["outcome"] = ("val", st["enc"].enc_result(arg))
                except Unencodable as e:
                    stats["skip_unencodable_ret"] += 1
                    r = stats.setdefault("unencodable_reasons", {})
                    k = "%s: result %s" % (rec["name"].split(".")[-1],
                                           e.args[0] if e.args else "?")
                    r[k] = r.get(k, 0) + 1
                    rec = None
            state_by_frame.pop(id(frame), None)
            if rec is not None: records.append(rec)
        return local2

    def tracer2(frame, event, arg):
        if event != "call": return None
        code = frame.f_code
        hit = index.get((os.path.abspath(code.co_filename), code.co_firstlineno))
        if hit is None: return None
        rel, qual = hit
        key = "%s:<module>.%s" % (rel, qual)
        if key not in wanted or counts.get(key, 0) >= limit_per_fn: return None
        snap = snapshot(frame, qual, key)
        if snap is None: return None
        enc, slf, args = snap
        counts[key] = counts.get(key, 0) + 1
        enc.freeze()
        state_by_frame[id(frame)] = {
            "rec": {"name": key, "heap": enc.heap, "self": slf, "args": args,
                    "outcome": None},
            "enc": enc, "exn": None}
        return local2

    old_path = list(sys.path)
    sys.path.insert(0, os.path.abspath(src_root))
    for d in test_dirs:
        sys.path.insert(0, os.path.dirname(os.path.abspath(d)))
    ran = []
    buf = io.StringIO()
    try:
        sys.settrace(tracer2)
        for d in test_dirs:
            try:
                with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
                    rc = run_suite(d)
                ran.append({"dir": d, "rc": rc})
            except Exception as e:                       # noqa: BLE001
                ran.append({"dir": d, "error": repr(e)[:200]})
    finally:
        sys.settrace(None)
        sys.path[:] = old_path
    stats["test_runs"] = ran
    return records


def _raw_attr(cls, name):
    """The *descriptor* for `name`, not the value binding it would produce."""
    for c in cls.__mro__:
        if name in c.__dict__: return c.__dict__[name]
    return None


def find_class(rel, clsname):
    """Locate a class the test suite already imported, by module path and name."""
    mod = rel[:-3].replace("/", ".").replace("\\", ".")
    if mod.endswith(".__init__"): mod = mod[:-9]
    m = sys.modules.get(mod)
    if m is None: return None
    obj = m
    for part in clsname.split("."):
        obj = getattr(obj, part, None)
        if obj is None: return None
    return obj if isinstance(obj, type) else None


class Timeout(Exception):
    pass


@contextlib.contextmanager
def time_limit(seconds):
    """Guard against a synthesized call that blocks (locks, sleeps, IO)."""
    import signal
    try:
        def handler(sig, frm): raise Timeout()
        old = signal.signal(signal.SIGALRM, handler)
        signal.setitimer(signal.ITIMER_REAL, seconds)
    except (ValueError, AttributeError):
        yield; return            # not the main thread, or no SIGALRM: run unguarded
    try:
        yield
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old)


def constructed_cases(methods, reached, live, pool, stats, ncases):
    """Exercise hole-free methods the test suite never called.

    The suite is the source of *realistic* state, so rather than fabricating an object
    we reuse a real instance it built for a sibling method (falling back to calling the
    class's own constructor), and draw arguments from values observed at parameters of
    the same name. Everything else — encoding, refusal, comparison — is the same path
    as a traced call, so a constructed case is no more lenient than a recorded one; it
    is only differently sourced, and is tagged `constructed` in the report.
    """
    out = []
    why = stats.setdefault("no_instance_detail", {})
    for f, rel, qual in methods:
        if f["name"] in reached: continue
        if "." not in qual:
            why[qual] = "not a method"; continue
        clsname, attr = qual.rsplit(".", 1)
        insts = list(live.get(clsname.split(".")[-1], ()))
        cls = find_class(rel, clsname)
        if not insts and cls is not None:
            for mk in ((), (1,), (2, 1)):
                try:
                    with time_limit(2.0):
                        insts = [cls(*mk)]
                    break
                except Exception:                       # noqa: BLE001
                    continue
        if not insts:
            why[qual] = "no live instance and constructor rejected ()/(1)/(2,1)"
            continue
        raw = _raw_attr(type(insts[0]), attr) if not cls else \
            (_raw_attr(cls, attr) or _raw_attr(type(insts[0]), attr))
        if isinstance(raw, property): raw = raw.fget
        if isinstance(raw, (staticmethod, classmethod)): raw = raw.__func__
        if not inspect.isroutine(raw):
            why[qual] = "no callable attribute %r on the class" % attr; continue
        try:
            order = frame_param_order(raw.__code__)
        except AttributeError:
            why[qual] = "builtin, no bytecode"; continue
        names = [n for n, _ in order]
        self_name = names[0] if names and names[0] == "self" else None
        if self_name is None:
            why[qual] = "no self parameter"; continue
        if any(k in ("star", "dstar", "kwonly") for _, k in order):
            why[qual] = "varargs/keyword-only: cannot synthesize a faithful call"
            continue
        if [n for n, _ in order][1:] != list(f["params"]):
            why[qual] = "parameter list disagrees with the AST"; continue
        made = 0
        for attempt in range(ncases * 4):
            if made >= ncases: break
            inst = insts[attempt % len(insts)]
            argv = []
            for n, _ in order[1:]:
                cand = pool.get(n) or []
                argv.append(cand[attempt % len(cand)] if cand
                            else random.randint(-8, 8))
            enc = Encoder()
            try:
                slf = enc.enc(inst)
                if slf[0] != "ref": raise Unencodable("self-not-object")
                eargs = [enc.enc(a) for a in argv]
            except Unencodable as e:
                why[qual] = "unencodable receiver/arguments: %s" % (e.args[0],)
                break
            enc.freeze()
            try:
                with time_limit(2.0):
                    got = raw(inst, *argv)
                outcome = ("val", enc.enc_result(got))
            except Timeout:
                why[qual] = "call did not terminate within 2s"; break
            except Unencodable as e:
                why[qual] = "unencodable result: %s" % (e.args[0],); break
            except Exception as e:                       # noqa: BLE001
                outcome = ("exn", type(e).__name__)
            out.append({"name": f["name"], "heap": enc.heap, "self": slf,
                        "args": eargs, "outcome": outcome, "origin": "constructed"})
            made += 1
        if made: why.pop(qual, None)
    return out


def run_suite(test_dir):
    """Run one test directory with whatever runner the project uses."""
    try:
        import pytest
    except ImportError:
        pytest = None
    if pytest is not None:
        return int(pytest.main([test_dir, "-q", "-p", "no:cacheprovider",
                                "--no-header"]))
    import unittest
    loader = unittest.TestLoader()
    suite = loader.discover(test_dir, top_level_dir=os.path.dirname(test_dir))
    return 0 if unittest.TextTestRunner(verbosity=0).run(suite).wasSuccessful() else 1


# ----------------------------------------------------------------------- C runtime

def c_runtime(src_root):
    """Compile the C sources to a shared library and expose them via ctypes.

    Same oracle, different runtime: the point of the Core language is that one semantics
    is checked against whichever real implementation produced the code."""
    import ctypes
    srcs = glob.glob(os.path.join(src_root, "**", "*.c"), recursive=True)
    if not srcs: return None
    lib = "/tmp/autoform_diff_c.dylib" if sys.platform == "darwin" else "/tmp/autoform_diff_c.so"
    r = subprocess.run(["cc", "-shared", "-fPIC", "-O0", "-o", lib] + srcs,
                       capture_output=True, text=True)
    if r.returncode != 0:
        print("cc failed:", r.stderr[:300]); return None
    dll = ctypes.CDLL(lib)

    def get(name, nargs):
        try: fn = getattr(dll, name)
        except AttributeError: return None
        fn.restype = ctypes.c_int
        fn.argtypes = [ctypes.c_int] * nargs
        return fn
    return get


def load_module(path, root):
    name = re.sub(r'[^A-Za-z0-9_]', '_', os.path.relpath(path, root))
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    sys.path.insert(0, root)
    try:
        spec.loader.exec_module(m)
        return m
    except Exception:
        return None


# ---------------------------------------------------------------------------- main

def main():
    argv = [a for a in sys.argv[1:]]
    tests_override = None
    if "--tests" in argv:
        i = argv.index("--tests"); tests_override = argv[i + 1]; del argv[i:i + 2]
    ast_path, src_root, lean_mod = argv[0], argv[1], argv[2]
    ncases = int(argv[3]) if len(argv) > 3 else 5
    funcs = json.load(open(ast_path))
    is_c = any(f.get("file", "").endswith((".c", ".h")) for f in funcs)
    runtime = "cc" if is_c else "cpython"
    module_tag = lean_mod

    holefree = [f for f in funcs if not has_hole(f["body"])]
    stats = {"skip_varargs": 0, "skip_unencodable_args": 0, "skip_unencodable_ret": 0,
             "skip_no_instance": 0, "test_runs": []}

    # cases: dict(name, heap, self, args, outcome, origin)
    cases = []

    if is_c:
        cget = c_runtime(src_root)
        cands = [f for f in holefree
                 if f["params"] and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', f["name"])]
        for f in cands:
            fn = cget(f["name"], len(f["params"])) if cget else None
            if fn is None: continue
            for _ in range(ncases):
                args = [random.randint(-20, 20) for _ in f["params"]]
                try:
                    got = fn(*args)
                except Exception:
                    continue
                cases.append({"name": f["name"], "heap": [], "self": None,
                              "args": [("int", a) for a in args],
                              "outcome": ("val", ("int", got)), "origin": "random",
                              "objs": {}})
    else:
        wanted, methods, modlevel = set(), [], []
        for f in holefree:
            c = classify(f)
            if not c: continue
            rel, qual, is_meth = c
            wanted.add(f["name"])
            (methods if is_meth else modlevel).append((f, rel, qual))

        # (1) the repository's own test suite — the highest-value source of arguments
        rel_files = sorted(set(f.get("file", "") for f in funcs))
        src_root = resolve_src_root(src_root, rel_files)
        test_dirs = [tests_override] if tests_override else find_tests(src_root)
        index = build_lineno_index(src_root, rel_files)
        traced = []
        params_by_name = {f["name"]: f["params"] for f in holefree}
        live, pool = {}, {}
        if test_dirs and index:
            print("test suite: %s" % ", ".join(test_dirs))
            traced = trace_tests(src_root, test_dirs, index, wanted, ncases, stats,
                                 params_by_name, live, pool)
        elif not test_dirs:
            print("test suite: none discovered under %s (pass --tests DIR)" % src_root)
        else:
            print("test suite: %s found, but none of the AST's source files resolve "
                  "under %s — nothing to instrument" % (", ".join(test_dirs), src_root))
        for r in traced:
            r["origin"] = "test-suite"
            cases.append(r)
        print("cases recorded from the test suite: %d" % len(traced))
        if test_dirs and not traced:
            print("  (the suite produced no usable calls — if it failed to even "
                  "collect, try re-running this harness under the interpreter the "
                  "project supports, e.g. `python3.11 scripts/differential.py ...`)")

        # (2) random integers for module-level functions (supplement, not substitute)
        for f, rel, qual in modlevel:
            mod = load_module(os.path.join(src_root, rel), src_root)
            if mod is None or not hasattr(mod, qual): continue
            fn = getattr(mod, qual)
            for _ in range(ncases):
                args = [random.randint(-20, 20) for _ in f["params"]]
                enc = Encoder()
                enc.freeze()
                try:
                    got = fn(*args)
                    out = ("val", enc.enc_result(got))
                except Unencodable:
                    stats["skip_unencodable_ret"] += 1; continue
                except Exception as e:                      # noqa: BLE001
                    out = ("exn", type(e).__name__)
                cases.append({"name": f["name"], "heap": enc.heap, "self": None,
                              "args": [("int", a) for a in args], "outcome": out,
                              "origin": "random"})

        # (3) methods the suite never called: reuse an instance it built for a
        # sibling method, or build one, and synthesize arguments from observed values
        reached = set(c["name"] for c in cases)
        built = constructed_cases(methods, reached, live, pool, stats, ncases)
        cases += built
        print("cases constructed for methods the suite never called: %d (%d functions)"
              % (len(built), len(set(c["name"] for c in built))))
        reached = set(c["name"] for c in cases)
        stats["skip_no_instance"] = sum(1 for f, _, _ in methods
                                        if f["name"] not in reached)

    if len(cases) > MAX_TOTAL_CASES:
        random.shuffle(cases)
        cases = cases[:MAX_TOTAL_CASES]

    result = {"module": module_tag, "source_root": os.path.abspath(src_root),
              "ast": os.path.abspath(ast_path), "runtime": runtime,
              "runtime_version": sys.version.split()[0],
              "functions_total": len(funcs), "functions_hole_free": len(holefree),
              "functions_covered": len(set(c["name"] for c in cases)),
              "cases": len(cases), "agree": 0, "total": 0, "divergences": 0,
              "inconclusive": 0, "rate": "n/a", "by_origin": {},
              "skipped": {k: v for k, v in stats.items() if k.startswith("skip")},
              "test_runs": stats["test_runs"], "divergence_detail": [],
              "unencodable_reasons": stats.get("unencodable_reasons", {})}

    if not cases:
        print("no comparable cases in this corpus")
        json.dump(result, open("conformance.json", "w"), indent=1)
        return 0

    # ---- ask Lean for its answer on exactly those cases
    #
    # Evaluated in chunks with bisection on failure: a single case can bring the whole
    # Lean interpreter down (a stale generated module, an unimplemented constructor),
    # and losing an entire run to one bad case would be a false negative. Cases we
    # cannot get an answer for are INCONCLUSIVE, never agreement.
    env = dict(os.environ,
               PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])
    repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    # A stale `.olean` silently answers with the *previous* semantics — which shows up
    # as fictitious divergences. Rebuild the module before trusting anything it says.
    b = subprocess.run(["lake", "build", "Autoform.Generated.%s" % lean_mod],
                       capture_output=True, text=True, env=env, cwd=repo)
    if b.returncode != 0:
        print("WARNING: `lake build Autoform.Generated.%s` failed; results below are "
              "against a possibly stale build:\n%s" % (lean_mod, b.stderr[:300]))
    gen = os.path.join(repo, "Autoform", "Generated", lean_mod + ".lean")
    has_inits = (os.path.exists(gen)
                 and "def moduleInits" in open(gen, encoding="utf-8").read())
    inits = "moduleInits" if has_inits else "([] : List Func)"

    # Module-level bindings (`Stmt.setGlobal` / `Expr.closure`) only exist after the
    # module initializers have run, so we start from `initGlobals` rather than the empty
    # heap. The globals frame occupies ref 0, so every receiver object the harness
    # materialises must be allocated at `base = h0.length` and upward; all `Val.ref`
    # literals below are emitted relative to `base`. `drun` re-checks that arithmetic
    # against the class name Python recorded — an off-by-one that aliased the globals
    # frame would otherwise be silently wrong rather than loudly wrong.
    header = ["import Autoform.Generated.%s" % lean_mod,
              "open Autoform.Core Autoform.Generated", "",
              "private def gp : Heap × Ref := initGlobals program %d %s" % (FUEL, inits),
              "private def h0 : Heap := gp.1",
              "private def gref : Ref := gp.2",
              "private def base : Nat := h0.length",
              "private def dctx : Ctx := "
              "{ dialect := program.dialect, table := program.table, globals := gref }",
              "",
              "private structure DCase where",
              "  idx  : Nat",
              "  objs : List Obj",
              "  fn   : String",
              "  slf  : Option Val",
              "  args : List Val",
              "  chk  : List (Nat × String)", "",
              "private def drun (c : DCase) : EResult :=",
              "  let h := h0 ++ c.objs",
              "  -- the globals frame must survive, and each receiver must land where",
              "  -- the harness said it would",
              "  if (h.get gref).map (·.cls) != some \"<globals>\" then",
              "    .hole \"harness:globals-frame-clobbered\"",
              "  else if c.chk.any (fun p => (h.get (base + p.1)).map (·.cls) "
              "!= some p.2) then",
              "    .hole \"harness:receiver-alias\"",
              "  else",
              "    match dctx.resolve c.fn with",
              '    | none    => .hole s!"entry:{c.fn}"',
              "    | some fn => (applyFunc dctx %d h fn c.slf c.args).2" % FUEL, ""]
    footer = ["]", "",
              '#eval IO.println ("@@meta@@" ++ toString base ++ " " ++ toString gref)',
              '#eval cases.forM (fun c => IO.println ("@@" ++ toString c.idx ++ "@@" '
              '++ (repr (drun c)).pretty (width := 1000000)))']

    def case_lit(i, c):
        slf = "none" if c["self"] is None else "(some (%s))" % lean_val(c["self"])
        chk = ", ".join('(%d, %s)' % (k, json.dumps(cls))
                        for k, (cls, _) in enumerate(c["heap"]))
        return ("  { idx := %d, objs := %s, fn := %s, slf := %s, args := [%s], "
                "chk := [%s] }"
                % (i, lean_heap(c["heap"]), json.dumps(c["name"]), slf,
                   ", ".join(lean_val(a) for a in c["args"]), chk))

    meta = {"base": 0, "gref": 0}

    def lean_eval(idxs, depth=0):
        """idxs -> {idx: repr line}. Missing keys are cases Lean could not answer."""
        if not idxs: return {}
        src = header + ["private def cases : List DCase := ["] \
            + [",\n".join(case_lit(i, cases[i]) for i in idxs)] + footer
        open("/tmp/autoform_diff.lean", "w").write("\n".join(src) + "\n")
        out = subprocess.run(["lake", "env", "lean", "/tmp/autoform_diff.lean"],
                             capture_output=True, text=True, env=env, cwd=repo)
        got = {}
        for l in out.stdout.splitlines():
            m = re.match(r'@@meta@@(\d+) (\d+)', l)
            if m:
                meta["base"], meta["gref"] = int(m.group(1)), int(m.group(2))
                continue
            m = re.match(r'@@(\d+)@@(.*)', l)
            if m and int(m.group(1)) in idxs: got[int(m.group(1))] = m.group(2)
        if len(got) < len(idxs) and len(idxs) > 1:
            mid = len(idxs) // 2
            got.update(lean_eval(idxs[:mid], depth + 1))
            got.update(lean_eval(idxs[mid:], depth + 1))
        elif len(got) < len(idxs) and depth == 0:
            print("lean could not evaluate any case:",
                  (out.stdout[:200] + out.stderr[:400]).replace("\n", " ")[:400])
        return got

    got = {}
    CHUNK = 20
    order = list(range(len(cases)))
    for i in range(0, len(order), CHUNK):
        got.update(lean_eval(order[i:i + CHUNK]))
    if len(got) < len(cases):
        print("lean answered %d/%d cases; the rest are INCONCLUSIVE"
              % (len(got), len(cases)))

    agree = diverge = incon = 0
    incon_detail: dict = {}
    per_origin = {}
    for i, c in enumerate(cases):
        origin = c.get("origin", "?")
        bucket = per_origin.setdefault(origin, {"agree": 0, "diverge": 0, "incon": 0})
        line = got.get(i)
        if line is None:
            incon += 1; bucket["incon"] += 1
            k = "%s: lean-no-answer (interpreter failed on this case)" % c["name"]
            incon_detail[k] = incon_detail.get(k, 0) + 1
            continue
        try:
            lr = parse_result(line)
        except Exception:                                  # noqa: BLE001
            incon += 1; bucket["incon"] += 1
            print("  unparsable %s: %s" % (c["name"], line[:80]))
            continue
        py = c["outcome"]
        argstr = "(%s)" % ", ".join(show(a) for a in c["args"])
        if lr[0] in ("hole", "outOfFuel"):
            # ignorance is never agreement
            incon += 1; bucket["incon"] += 1
            label = lr[1] if lr[0] == "hole" else "outOfFuel"
            k = "%s: %s" % (c["name"], label)
            incon_detail[k] = incon_detail.get(k, 0) + 1
            continue
        ok = False
        if py[0] == "val" and lr[0] == "val":
            ok = same(py[1], lr[1], meta["base"])
            desc = "%s=%s lean=%s" % (runtime, show(py[1]), show(lr[1]))
        elif py[0] == "exn" and lr[0] == "exn":
            lname = lr[1][1] if lr[1][0] == "str" else show(lr[1])
            ok = (lname == py[1])
            desc = "%s raised %s, lean raised %s" % (runtime, py[1], lname)
        elif py[0] == "exn":
            desc = "%s raised %s, lean returned %s" % (runtime, py[1], show(lr[1]))
        else:
            lname = lr[1][1] if lr[1][0] == "str" else show(lr[1])
            desc = "%s=%s, lean raised %s" % (runtime, show(py[1]), lname)
        if ok:
            agree += 1; bucket["agree"] += 1
        else:
            diverge += 1; bucket["diverge"] += 1
            msg = "  DIVERGENCE %s%s: %s [%s]" % (c["name"], argstr, desc, origin)
            print(msg[:300])
            result["divergence_detail"].append(
                {"function": c["name"], "args": argstr[:200], "detail": desc[:200],
                 "origin": origin})

    total = agree + diverge
    rate = "%d%%" % (100 * agree // total) if total else "n/a"
    result["inconclusive_detail"] = incon_detail
    result.update(agree=agree, total=total, divergences=diverge, inconclusive=incon,
                  rate=rate, by_origin=per_origin)
    print("\nmodule %s (%s, %s)" % (module_tag, os.path.abspath(src_root), runtime))
    print("functions: %d total, %d hole-free, %d actually exercised"
          % (len(funcs), len(holefree), result["functions_covered"]))
    print("conformance: %d/%d agree (%s) vs %s, %d divergences, %d INCONCLUSIVE "
          "(hole / outOfFuel / unrepresentable)" % (agree, total, rate, runtime,
                                                    diverge, incon))
    for k, v in sorted(incon_detail.items(), key=lambda kv: -kv[1])[:10]:
        print("  INCONCLUSIVE x%-3d %s" % (v, k))
    for o, b in sorted(per_origin.items()):
        print("  by origin %-11s agree %d, diverge %d, inconclusive %d"
              % (o, b["agree"], b["diverge"], b["incon"]))
    if stats["skip_no_instance"]:
        print("  skipped %d hole-free methods: no instance reached by the test suite"
              % stats["skip_no_instance"])
    for k, v in result["skipped"].items():
        if v: print("  skipped %s: %d" % (k, v))
    json.dump(result, open("conformance.json", "w"), indent=1)
    return 1 if diverge else 0


if __name__ == "__main__":
    sys.exit(main())
