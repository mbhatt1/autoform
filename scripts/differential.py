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
import os, sys
import json, subprocess, random, importlib.util, re, glob, io
import contextlib, inspect, functools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wasm_backend
import generated_module
import runtime_backends
import external_bases
import deep_json
import struct
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                               "cartographer"))
from generator_lowering import analysis_functions

random.seed(20260819)   # deterministic: workflows/proofs must be reproducible


def _corpus_commit(src_root):
    """Identify the actual corpus tree; a surrounding checkout is not its revision."""
    from pathlib import Path
    try:
        # The corpus may itself import a module named provenance. Load our helper
        # by its exact file without replacing that module in the native program.
        spec = importlib.util.spec_from_file_location(
            '_autoform_source_provenance', Path(__file__).with_name('provenance.py'))
        if spec is None or spec.loader is None:
            raise ImportError('source provenance helper is unavailable')
        provenance = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(provenance)
        revision = provenance.source_revision(Path(src_root))
        return revision[4:] if revision.startswith("git:") else revision
    except Exception as e:                                          # noqa: BLE001
        return "unavailable: %s" % type(e).__name__

# Every scratch artefact lives under one private directory. A fixed `/tmp` path is a
# phantom-result generator: several agents run this harness at once, and a shared
# `/tmp/autoform_diff.lean` means one run can report conformance computed from another
# run's program. Nothing here may be a constant path.
import atexit as _atexit
import tempfile as _tempfile
WORK = _tempfile.mkdtemp(prefix="autoform_diff_%d_" % os.getpid())
_atexit.register(lambda: __import__("shutil").rmtree(WORK, ignore_errors=True))

# Test-suite-derived cases must be reproducible too. Set-iteration and dict-key hashing
# feed which calls the suite makes and in which order, so an unseeded interpreter gives
# a different sample of cases (and a different set of divergences) on every run.
if os.environ.get("PYTHONHASHSEED") != "0" and not os.environ.get("AUTOFORM_NO_REEXEC"):
    os.execve(sys.executable, [sys.executable] + sys.argv,
              dict(os.environ, PYTHONHASHSEED="0"))

FUEL = 5000
MAX_TOTAL_CASES = 600      # keep the generated Lean file compile-bounded
MAX_DEPTH = 8              # value-encoding depth limit
MAX_ELEMS = 512            # value-encoding breadth limit (a resource
                           # bound, not a fidelity one: containers are
                           # encoded whole or refused, never truncated)


# --------------------------------------------------------------------------- AST

def has_hole(n, *, except_labels=()):
    """Tolerant of unknown node kinds: we only look for the hole markers.

    Iterative on purpose. The recursive version blew Python's 1000-frame default on
    Linux `lib/` and raised RecursionError *before any backend ran*, so the largest C
    corpus could not be measured at all — and the failure looked like "the harness broke"
    rather than "this function is deeply nested". Raising the recursion limit is not the
    fix: the limit guards the C stack, and lifting it without a bigger stack turns a clean
    exception into a segfault. An explicit stack has no such ceiling.

    This is the same defect `cartographer/render_lean.py` had (it never set a limit at all
    and died at 247 consecutive statements). Any AST walker here should be assumed to meet
    a 20,000-deep term eventually, because real code nests.
    """
    stack = [n]
    while stack:
        x = stack.pop()
        if isinstance(x, dict):
            if x.get("k") in ("hole", "holeS") and x.get("label") not in except_labels:
                return True
            stack.extend(x.values())
        elif isinstance(x, list):
            stack.extend(x)
    return False


def python_sampling_candidates(funcs):
    """Attempt represented exception paths without claiming static hole-freedom.

    Typed handlers explicitly refuse exception objects outside Core's named-class
    representation. That fallback must remain in the AST and ledger, but it must
    not prevent native comparisons of ordinary builtin exceptions. A case reaching
    the fallback is still INCONCLUSIVE and cannot produce a conformance theorem.
    Other untranslated constructs retain the existing sampling restriction.
    """
    return [f for f in funcs if not has_hole(f['body'], except_labels={
        'control:TRY-exception-representation'})]


def compared_hole_coverage(holefree, compared):
    """Keep the hole-free denominator restricted to its own population."""
    names = {f['name'] for f in holefree}
    return dict(compared_hole_free=len(compared & names),
                compared_with_holes=len(compared - names),
                compared_fraction_of_hole_free=(len(compared & names) / len(names)
                                                if names else 0.0))


PY_NAME = re.compile(r'(?P<file>.+?):<module>\.(?P<qual>.+)')


def undecorated_bodies(funcs):
    """Source name -> exported RAW body, for definitions whose in-program decorators
    are applied at definition time (Language Reference §8.7).

    A traced CPython frame of a decorated `def` executes the function object the
    decorators RECEIVED -- its code is the raw body -- whatever the source name is bound
    to afterwards. The exporter keeps that body under `<name><undecorated>` (with
    `undecoratedOf` naming the source spelling), and the source name is an auxiliary
    entry that calls the decorated binding. Comparing a raw frame against the entry
    would compare two different functions, so frames are routed to the raw body."""
    return {f["undecoratedOf"]: f["name"] for f in funcs if f.get("undecoratedOf")}


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

    def __init__(self, class_identities=None):
        self.heap = []          # list of (cls, [(field, Val)])
        self.byid = {}          # id(obj) -> ref index
        self.objs = {}          # ref index -> the live object (keeps ids alive)
        self.pin = set()        # ids present before the result was encoded
        self.class_identities = class_identities

    def class_identity(self, cls):
        if self.class_identities is None:
            return cls.__name__
        name = type.__getattribute__(cls, '__qualname__')
        if '<locals>' in name:
            raise Unencodable('local-class-captures')
        try:
            source = inspect.getsourcefile(cls)
        except (TypeError, OSError):
            source = None
        key = (os.path.realpath(source), name) if source else None
        identity = self.class_identities.get(key)
        if identity is None:
            # Not a corpus class. A contracted external base (`scripts/external_bases.py`)
            # is encodable under its marker once the LIVE class is checked against the
            # pinned contract; anything else -- a test-defined subclass, an uncontracted
            # stdlib class, a version whose ABC differs -- is refused by name.
            reason = external_bases.verify(cls)
            if reason is not None:
                raise Unencodable('class-identity-unresolved:' + name + ':' + reason)
            identity = external_bases.PREFIX + external_bases.external_name(cls)
        return identity

    def enc(self, v, depth=0, in_key=False):
        if depth > MAX_DEPTH: raise Unencodable("depth")
        if v is None: return ("unit",)
        if (self.class_identities is not None and isinstance(v, (int, float, str))
                and type(v) not in (bool, int, float, str)):
            raise Unencodable('primitive-subclass-state')
        if isinstance(v, bool): return ("bool", v)
        if isinstance(v, int): return ("int", v)
        if isinstance(v, float): return ("float", struct.unpack(">Q", struct.pack(">d", v))[0])
        if isinstance(v, str): return ("str", v)
        if isinstance(v, (list, tuple)):
            if self.class_identities is not None and type(v) not in (list, tuple):
                raise Unencodable('container-subclass-state')
            # Subclasses (`_HashedTuple`, `OrderedDict`) encode structurally: that is
            # faithful for every operation Core can perform on data it was *handed*
            # (index, len, membership, iteration order). Where Core instead *allocates*
            # such a value itself it produces a `Val.ref`, and that shape disagreement
            # is ruled INCONCLUSIVE at comparison time rather than refused here — see
            # `compare_outcome`.
            if len(v) > MAX_ELEMS: raise Unencodable("wide")
            k = "tuple" if isinstance(v, tuple) else "list"
            return (k, [self.enc(x, depth + 1, in_key) for x in v])
        if isinstance(v, dict):
            if self.class_identities is not None and type(v) is not dict:
                raise Unencodable('container-subclass-state')
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
            if self.class_identities is not None:
                if isinstance(v, type):
                    return ('fn', self.class_identity(v) + '<meta>')
                if getattr(v, '__self__', None) is not None:
                    raise Unencodable('bound-callable-state')
                if getattr(v, '__closure__', None):
                    raise Unencodable('callable-captures')
            # `METHOD_REF`/`TYPE_REF` values: Core models them by name only.
            n = getattr(v, "__qualname__", None) or getattr(v, "__name__", None)
            if n and n.endswith('<meta>'):
                # Only the class-identity branch above may create this marker.
                # A user-reassigned function __qualname__ is not a class value.
                raise Unencodable('callable-class-identity-collision')
            if n: return ("fn", n)
            raise Unencodable("callable")
        # a callable *instance* is still an object with fields — encode it as one
        if isinstance(v, (complex, bytes, frozenset, set)):
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
        identity, fields = self.object_fields(obj)
        idx = len(self.heap)
        self.heap.append(None)
        self.byid[id(obj)] = idx
        self.objs[idx] = obj
        self.heap[idx] = (identity, [(str(k), self.enc(v, depth + 1))
                                     for k, v in fields.items()])
        return idx

    def object_fields(self, obj):
        identity = self.class_identity(type(obj))
        fields = {}
        has_dict, slotted = False, False
        if self.class_identities is not None:
            # Read builtin storage descriptors directly, without invoking user
            # attribute hooks or a derived member that shadows an inherited slot.
            import types
            namespaces = [(cls, type.__getattribute__(cls, '__dict__'))
                          for cls in type.__getattribute__(type(obj), '__mro__')]
            for cls, namespace in namespaces:
                if cls is not object:
                    self.class_identity(cls)  # external base storage is not guessed
                slotted = slotted or '__slots__' in namespace
            for cls, namespace in namespaces:
                descriptor = namespace.get('__dict__')
                if isinstance(descriptor, types.GetSetDescriptorType):
                    state = descriptor.__get__(obj, type(obj))
                    if (not isinstance(state, dict)
                            or any(not isinstance(key, str) or key.startswith('<slot>')
                                   for key in state)):
                        raise Unencodable('non-ordinary-instance-dictionary')
                    fields.update(state)
                    has_dict = True
                    break
            for cls, namespace in namespaces:
                for name, descriptor in namespace.items():
                    if not isinstance(descriptor, types.MemberDescriptorType):
                        continue
                    owner = self.class_identity(cls)
                    try:
                        value = descriptor.__get__(obj, type(obj))
                    except AttributeError:
                        continue  # an uninitialized slot has no storage entry
                    fields['<slot>' + owner + '.' + name] = value
        elif hasattr(obj, "__dict__"):
            has_dict = True
            # `vars` can hand back something that is not a dict -- click's objects with a
            # `__dict__` descriptor returning None did -- and that is an object we cannot
            # snapshot faithfully, not a dict with no entries.
            d = vars(obj)
            if not isinstance(d, dict):
                raise Unencodable("non-dict-__dict__")
            fields.update(d)
        if self.class_identities is None:
            for cls in type(obj).__mro__:
                for s in getattr(cls, "__slots__", ()) or ():
                    if hasattr(obj, s): fields[s] = getattr(obj, s)
            slotted = any(getattr(c, "__slots__", None) is not None
                          for c in type(obj).__mro__)
        if not fields and not has_dict and not slotted:
            raise Unencodable("opaque")     # C-level object with no inspectable state
        if len(fields) > MAX_ELEMS: raise Unencodable("wide-object")
        return identity, fields

    def freeze(self):
        """Mark the objects that existed before the call returned."""
        self.pin = set(self.byid)
        self.input_heap = self.heap

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
    if t == "float": return "Val.float (Fl.ofBits %d)" % v[1]
    if t == "str":  return "Val.str " + json.dumps(v[1])
    if t == "ref":  return "Val.ref (base + %d)" % v[1]
    if t == "fn":   return "Val.fn " + json.dumps(v[1])
    if t in ("list", "tuple"):
        return "Val.%s [%s]" % (t, ", ".join(lean_val(x) for x in v[1]))
    if t == "dict":
        return "Val.dict [%s]" % ", ".join("(%s, %s)" % (lean_val(a), lean_val(b))
                                           for a, b in v[1])
    raise Unencodable(t)


from native_heap import graph_encoder
GraphEncoder = graph_encoder(Encoder, Unencodable, MAX_DEPTH, MAX_ELEMS)


def heap_cell(cell):
    """Legacy cells have two fields; graph observations add a container payload."""
    return cell[0], cell[1], cell[2] if len(cell) == 3 else None


def lean_heap(heap, value=lean_val, string=json.dumps):
    cells = []
    for cell in heap:
        cls, fields, payload = heap_cell(cell)
        text = "{ cls := %s, fields := [%s]" % (
            string(cls), ", ".join("(%s, %s)" % (string(k), value(v)) for k, v in fields))
        if payload is not None:
            tag, items = payload
            vals = (", ".join("(%s, %s)" % (value(k), value(v)) for k, v in items)
                    if tag == 'dict' else ", ".join(value(v) for v in items))
            text += ", payload := .%s [%s]" % (tag, vals)
        cells.append(text + " }")
    return "[" + ", ".join(cells) + "]"


def graph_lit(case, value=lean_val, string=json.dumps):
    post = case.get('post_heap')
    if post is None:
        return 'none'
    # Each atom/edge costs at most two checker steps. JSON size deliberately
    # overestimates that count, keeping exhaustion an explicit comparison gap.
    budget = 16 + 2 * len(json.dumps([post, case['outcome']]))
    roots = ', '.join('(base + %d)' % i for i in range(len(case['heap'])))
    return '(some { heap := h0 ++ %s, roots := [%s], budget := %d })' % (
        lean_heap(post, value, string), roots, budget)


def outcome_lit(outcome, value=lean_val, string=json.dumps):
    kind, result = outcome
    return ('EResult.val (%s)' % value(result) if kind == 'val' else
            'EResult.exn (Val.str %s)' % string(result))


def finish_record(enc, record):
    """Complete a record atomically; failure must never fall back to result-only."""
    record['heap'] = enc.input_heap
    # A final-graph observation needs exact identities on both sides. A legacy AST
    # (no `classDeclarations`) has short class names and short function qualnames on
    # the native side against Core's qualified function names, so its comparison is
    # result-only, exactly as before graph observations existed.
    if isinstance(enc, GraphEncoder) and enc.class_identities is not None:
        record['post_heap'] = enc.post_state()
    return record


# ------------------------------------------------------------------- repr parsing
#
# We cannot edit the Lean sources, so we parse Lean's derived `Repr` output. It is
# emitted on one line (`Format.pretty` at a huge width) and fully parenthesised.

TOKEN = re.compile(r'\s*("(?:[^"\\]|\\.)*"|[A-Za-z_][A-Za-z0-9_.!?]*|-?\d+|:=|[{}()\[\],])')


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
        # `Val.bobj cls payload` takes TWO arguments -- the only Val constructor that
        # does. Parsed as a one-argument constructor it consumed the class name and left
        # the payload dangling, so every `_HashedTuple` result came back "unparsable" and
        # was counted INCONCLUSIVE. Core produced the right value; the oracle could not
        # read it.
        if qual == "Val.bobj":
            cls = self.atom()
            payload = self.atom()
            return ("bobj", cls[1] if cls[0] == "str" else "?", payload)
        # `Val.clos name captured` also takes two arguments. Unboxing a function object
        # (Core section 47) exposes these, because a decorator's `wrapper` is a CLOSURE --
        # so the six `_cached.py` functions went from a shape clash straight to
        # "unparsable" and stayed INCONCLUSIVE. A closure IS a function value for the
        # purpose of comparing return values; the captured environment is not something
        # CPython hands the oracle, so it is parsed and dropped rather than compared.
        if qual == "Val.clos":
            nm = self.atom()
            _cap = self.atom()
            return ("fn", nm[1] if nm[0] == "str" else "?")
        if qual == "Val.float":
            self.expect("{")
            self.expect("fmt"); self.expect(":="); self.expect("{")
            fmt = {}
            while self.peek() != "}":
                key = self.next(); self.expect(":=")
                fmt[key] = self.atom()[1]
                if self.peek() == ",": self.next()
            self.expect("}"); self.expect(","); self.expect("bits"); self.expect(":=")
            bits = self.atom()[1]; self.expect("}")
            if fmt == {"prec": 24, "emax": 127, "expBits": 8}:
                bits = struct.unpack(">Q", struct.pack(">d", struct.unpack(">f", struct.pack(">I", bits))[0]))[0]
            elif fmt != {"prec": 53, "emax": 1023, "expBits": 11}:
                raise ValueError("unknown floating-point format")
            return ("float", bits)
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

def unwrap_bobj(v):
    """A `Val.bobj cls payload` compares as its payload.

    `class _HashedTuple(tuple)` translates to `Val.bobj "_HashedTuple" (tuple …)`, and
    Core's `Val.beq` compares such a value BY CONTENTS, ignoring the class — which is
    CPython's answer for a builtin subclass that does not override `__eq__`
    (`hashkey(0) == (0,)` is `True`). CPython hands the oracle a plain tuple, so comparing
    the payload is the same relation the semantics implements, not a convenience.

    Before this the harness had no `bobj` case at all: `hashkey` and `methodkey` came back
    `representation:value-vs-object` and were counted INCONCLUSIVE — the oracle refusing to
    look at a value Core had been fixed to produce correctly."""
    while isinstance(v, tuple) and len(v) == 3 and v[0] == "bobj":
        v = v[2]
    return v


def same(py, ln, base):
    """Compare an encoded Python value against a parsed Lean value.

    Dicts compare order-insensitively: Core's `Val.dict` is an association list whose
    order is observable, but Python's insertion order is not part of the contract we
    are checking here, and pretending otherwise would manufacture divergences."""
    ln = unwrap_bobj(ln)
    if py[0] == ln[0] == "float":
        p, l = py[1], ln[1]
        # NaN payloads are not part of the runtime value contract; signed zero is.
        nan = lambda b: b & 0x7ff0000000000000 == 0x7ff0000000000000 and b & 0xfffffffffffff != 0
        return p == l or (nan(p) and nan(l))
    if py[0] != ln[0]:
        # Core has no separate tuple/list distinction at some call sites; still, do not
        # paper over it — report as a mismatch.
        return False
    t = py[0]
    if t in ("unit",): return True
    if t in ("int", "bool", "str"): return py[1] == ln[1]
    if t == "fn":
        if py[1].endswith('<meta>') or ln[1].endswith('<meta>'):
            # Recovered class values already share an exact source identity.
            # Dropping module qualification would conflate unrelated classes.
            return py[1] == ln[1]
        # `Val.fn` names are spelled differently on the two sides: CPython reports a
        # `__qualname__` (`TTLCache._Link`), Joern a fully-qualified one
        # (`pkg/mod.py:<module>.TTLCache._Link`). Core's own `Ctx.resolve` matches
        # callables by dotted suffix, so accept exactly that and nothing looser.
        # The two sides spell nesting differently: CPython's `__qualname__` inserts
        # `<locals>` for a function defined inside a function (`_locked_info.<locals>.
        # wrapper`), Joern's fully-qualified name inserts `<module>` for file scope
        # (`cachetools/_cached.py:<module>._locked_info.wrapper`). Neither segment names
        # anything a program can refer to, so drop both before matching by dotted suffix.
        def _qual(x):
            x = x.split(":")[-1]
            return ".".join(p for p in x.split(".") if p not in ("<locals>", "<module>"))
        a, b = _qual(py[1]), _qual(ln[1])
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


def shape_clash(py, ln):
    """True when the two sides disagree about value-vs-object representation."""
    ln = unwrap_bobj(ln)
    containers = ("list", "tuple", "dict")
    if py[0] == "ref" and ln[0] in containers: return True
    if ln[0] == "ref" and py[0] in containers: return True
    if py[0] in containers and ln[0] in containers and py[0] != ln[0]: return False
    if py[0] in ("list", "tuple") and ln[0] in ("list", "tuple"):
        return any(shape_clash(a, b) for a, b in zip(py[1], ln[1]))
    return False


def show(v):
    t = v[0]
    if t == "unit": return "unit"
    if t in ("int", "bool", "str", "fn", "ref", "float"): return "%s %r" % (t, v[1])
    if t in ("list", "tuple"): return "%s[%s]" % (t, ", ".join(show(x) for x in v[1]))
    if t == "dict": return "{%s}" % ", ".join("%s: %s" % (show(a), show(b))
                                              for a, b in v[1])
    return str(v)


# ------------------------------------------------------------------- test tracing

def find_tests(src_root):
    """Discover tests within the selected source scope, never in its ancestors.

    A source subdirectory is not permission to execute its host project's tests.
    Call this before correcting a repository root to its src/ import directory;
    repository-local sibling tests then remain discoverable without widening scope.
    An outside suite must be supplied explicitly through --tests.
    """
    root = os.path.abspath(src_root)
    real_root = os.path.realpath(root)
    found = []
    for name in ('tests', 'test'):
        directory = os.path.join(root, name)
        if (os.path.isdir(directory)
                and os.path.commonpath([real_root, os.path.realpath(directory)]) == real_root
                and glob.glob(os.path.join(directory, '**', 'test_*.py'), recursive=True)):
            found.append(directory)
    if glob.glob(os.path.join(root, 'test_*.py')):
        found.append(root)
    return found


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


def class_identity_index(funcs, src_root):
    """Use exact source file and class path; duplicate identities stay unresolved.

    None selects the historical encoding for ASTs without recovered class metadata.
    An empty mapping selects strict refusal when metadata exists but cannot resolve.
    """
    rows = [row for function in funcs for row in function.get('classDeclarations', [])]
    if not rows:
        return None
    identities = {}
    for row in rows:
        name = row['name']
        source, separator, qualified = name.partition(':<module>.')
        if not separator or not source or not qualified:
            continue
        key = (os.path.realpath(os.path.join(src_root, source)), qualified)
        identities[key] = None if key in identities else name
    return identities


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
        # `isfile`, not `exists`: an AST entry with an empty `file` (a module-level
        # initialiser) joins to the source ROOT, which exists and is a directory. Opening
        # it raised IsADirectoryError and killed the run before any case was compared.
        if not os.path.isfile(path): continue
        try:
            tree = pyast.parse(open(path, encoding="utf-8").read(), path)
        except (SyntaxError, OSError, UnicodeDecodeError):
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
        if kind == "star":
            # SPREAD, do not pass the packed tuple.
            #
            # A frame's `*args` local is already the packed tuple. Passing it as one
            # positional argument was right while Core had no calling convention -- it
            # simply bound to the first parameter. Now `bindParams` packs the surplus
            # positionals itself, so passing the packed value packs it AGAIN:
            # `hashkey(0)` came out as `((0,), {})` against CPython's `(0,)`, and was
            # reported as a divergence in the semantics. The bug was here.
            for elem in v:
                args.append(enc.enc(elem))
            continue
        if kind == "dstar":
            # The harness has no keyword channel (it calls `applyFunc … args []`), so a
            # non-empty `**kwargs` cannot be represented and must be refused rather than
            # flattened into positionals, which would bind to the wrong parameters.
            if v:
                raise ParamMismatch("non-empty **%s cannot be passed positionally" % n)
            continue
        args.append(enc.enc(v))
    return slf, args


class ParamMismatch(Exception):
    pass


def trace_return_is_normal(frame):
    """A trace return's None argument does not distinguish return from unwind.

    CPython's actual return instruction does. Other interpreters or unknown
    instructions are refused instead of turning a handled exception into an outcome.
    Suspended generator/coroutine frames are excluded by the call-event handler.
    """
    import dis
    if sys.implementation.name != 'cpython' or frame.f_lasti < 0:
        return None
    try:
        name = dis.opname[frame.f_code.co_code[frame.f_lasti]]
    except (IndexError, TypeError):
        return None
    if name.startswith('<') or name.startswith('YIELD'):
        return None
    if name in ('RETURN_VALUE', 'RETURN_CONST'):
        return True
    return None if 'RETURN' in name else False


def trace_tests(src_root, test_dirs, index, wanted, limit_per_fn, stats,
                params_by_name=None, live=None, pool=None, encoder_factory=Encoder,
                raw_bodies=None):
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
        # A decorated method's raw body keeps `self` as an ordinary first parameter: the
        # decorators' wrapper passes it positionally, and Core injects no receiver.
        if self_name is not None and (params_by_name.get(key) or [None])[:1] == [self_name]:
            self_name = None
        enc = encoder_factory()
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
            st["exceptions"].add(arg[0].__name__)
        elif event == "return":
            rec = st["rec"]
            normal = trace_return_is_normal(frame)
            if normal is False and arg is None and len(st["exceptions"]) == 1:
                rec["outcome"] = ("exn", next(iter(st["exceptions"])))
            elif normal is True:
                try:
                    rec["outcome"] = ("val", st["enc"].enc_result(arg))
                except Unencodable as e:
                    stats["skip_unencodable_ret"] += 1
                    r = stats.setdefault("unencodable_reasons", {})
                    k = "%s: result %s" % (rec["name"].split(".")[-1],
                                           e.args[0] if e.args else "?")
                    r[k] = r.get(k, 0) + 1
                    rec = None
            else:
                # A finally clause can handle a second exception then resume the
                # first one. The last exception event is not its escaping type.
                stats['skip_ambiguous_trace_return'] = stats.get('skip_ambiguous_trace_return', 0) + 1
                reasons = stats.setdefault('trace_return_gaps', {})
                reason = rec['name'] + ': unsupported-return-or-ambiguous-unwind'
                reasons[reason] = reasons.get(reason, 0) + 1
                rec = None
            state_by_frame.pop(id(frame), None)
            if rec is not None:
                try:
                    records.append(finish_record(st['enc'], rec))
                except Unencodable as e:
                    stats['skip_unencodable_post'] = stats.get('skip_unencodable_post', 0) + 1
                    reasons = stats.setdefault('unencodable_reasons', {})
                    reason = rec['name'] + ': post-state ' + str(e)
                    reasons[reason] = reasons.get(reason, 0) + 1
        return local2

    def tracer2(frame, event, arg):
        if event != "call": return None
        code = frame.f_code
        hit = index.get((os.path.abspath(code.co_filename), code.co_firstlineno))
        if hit is None: return None
        rel, qual = hit
        key = "%s:<module>.%s" % (rel, qual)
        key = (raw_bodies or {}).get(key, key)
        if key not in wanted or counts.get(key, 0) >= limit_per_fn: return None
        if code.co_flags & (inspect.CO_GENERATOR | inspect.CO_COROUTINE | inspect.CO_ASYNC_GENERATOR):
            stats['skip_suspended_frame'] = stats.get('skip_suspended_frame', 0) + 1
            return None
        snap = snapshot(frame, qual, key)
        if snap is None: return None
        enc, slf, args = snap
        counts[key] = counts.get(key, 0) + 1
        enc.freeze()
        state_by_frame[id(frame)] = {
            "rec": {"name": key, "heap": enc.heap, "self": slf, "args": args,
                    "outcome": None},
            "enc": enc, "exceptions": set()}
        return local2

    old_path = list(sys.path)
    old_trace = sys.gettrace()
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
        sys.settrace(old_trace)
        sys.path[:] = old_path
    stats["test_runs"] = ran
    return records


def _raw_attr(cls, name):
    """The *descriptor* for `name`, not the value binding it would produce."""
    for c in cls.__mro__:
        if name in c.__dict__: return c.__dict__[name]
    return None


def find_module(rel):
    """The imported module for a corpus-relative source path, or None.

    Falling back to an explicit import matters more than it looks. `import cachetools`
    pulls in `cachetools.keys` and nothing else -- `_cached` and `_cachedmethod` are
    imported lazily inside functions -- so tracing the suite never put them in
    `sys.modules`, `find_class` returned None for every class they define, and 48
    functions were reported as blocked. The cause recorded against them was
    "constructor rejected ()/(1)/(2,1)", which was false: no constructor was ever
    reached, because the module holding the class had never been loaded.

    Importing a submodule of a package the suite already imported is not fabricating
    state -- it is loading code the corpus ships and the AST was exported from."""
    mod = rel[:-3].replace("/", ".").replace("\\", ".")
    if mod.endswith(".__init__"): mod = mod[:-9]
    m = sys.modules.get(mod)
    if m is not None:
        return m
    try:
        import importlib
        return importlib.import_module(mod)
    except Exception:                                       # noqa: BLE001
        return None


def find_class(rel, clsname):
    """Locate a class the test suite already imported, by module path and name."""
    m = find_module(rel)
    if m is None: return None
    obj = m
    for part in clsname.split("."):
        obj = getattr(obj, part, None)
        if obj is None: return None
    return obj if isinstance(obj, type) else None


class Timeout(Exception):
    """A harness deadline, never an exception observed from the source program."""


class DeadlineUnavailable(Timeout):
    """The platform/thread cannot install a native-call deadline."""


@contextlib.contextmanager
def time_limit(seconds):
    """Interrupt synthesized calls on the main thread, or refuse the call.

    This is a Python signal deadline, not process isolation. Corpus code that masks
    signals or catches the harness exception still needs an external process limit.
    """
    import signal
    import threading
    if (threading.current_thread() is not threading.main_thread()
            or not all(hasattr(signal, name) for name in
                       ('SIGALRM', 'ITIMER_REAL', 'setitimer', 'getitimer'))):
        raise DeadlineUnavailable('native-call deadline unavailable on this thread/platform')
    if seconds <= 0:
        raise ValueError('deadline must be positive')
    if signal.getitimer(signal.ITIMER_REAL)[0] != 0:
        raise DeadlineUnavailable('native-call deadline conflicts with an active timer')

    def handler(sig, frm):
        raise Timeout('native call exceeded its deadline')

    old = signal.signal(signal.SIGALRM, handler)
    try:
        signal.setitimer(signal.ITIMER_REAL, seconds)
        yield
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old)


def _ctor_attempts(cls, pool):
    """Argument tuples to try for `cls(...)`, best first.

    The old search was three hardcoded shapes -- `()`, `(1,)`, `(2, 1)` -- and it was the
    single largest blocker in the whole report: 54 functions, more than were being compared,
    failed as "no live instance". They are not blocked by the semantics. `_WrapperBase`
    takes four arguments and `cachedmethod`'s decorator takes a callable, so no tuple of
    small integers was ever going to construct one.

    So drive the search from the constructor's own parameter names, using the SAME observed
    -value pool the method-argument synthesis already uses, and fall back by name only for
    the shapes a cache library obviously needs. Anything constructed here still goes through
    the identical encode/refuse/compare path as a traced call, so this widens what the oracle
    can reach without widening what it will accept."""
    attempts = [(), (1,), (2, 1)]
    try:
        order = frame_param_order(cls.__init__.__code__)
    except Exception:                                       # noqa: BLE001
        return attempts
    if any(k in ("star", "dstar", "kwonly") for _, k in order):
        return attempts
    names = [n for n, _ in order][1:]
    if not names:
        return attempts
    synth = []
    for n in names:
        cand = pool.get(n) or []
        if cand:
            synth.append(cand[0]); continue
        synth.append(_ctor_fallback(n))
    attempts.insert(0, tuple(synth))
    # ... and the same shape with the trailing optional parameters dropped, since a
    # constructor that rejects a fabricated `lock` may still accept a shorter call.
    for k in range(len(synth) - 1, 0, -1):
        attempts.append(tuple(synth[:k]))
    return attempts


def _ctor_fallback(n):
    """A plausible value for a constructor parameter no run ever observed. By NAME only --
    guessing from a type annotation would be guessing about a contract the code may not
    keep, and a wrong instance is worse than no instance."""
    low = n.lower()
    if low in ("func", "method", "fn", "callable", "user_function"):
        return lambda *a, **k: None
    if low in ("key", "getsizeof", "timer", "ttu"):
        return lambda *a, **k: 1
    if low in ("lock", "cond", "condition"):
        import threading
        return threading.RLock() if low == "lock" else threading.Condition()
    if low in ("maxsize", "ttl", "size", "n", "count"):
        return 1
    if low in ("cache",):
        return {}
    if low in ("info",):
        return False
    return 1


def _direct_cases(fn, f, pool, ncases, out, encoder_factory=Encoder):
    """Call a plain callable with synthesized arguments and append the cases it yields."""
    try:
        order = frame_param_order(fn.__code__)
    except Exception:                                       # noqa: BLE001
        return 0
    if any(k in ("star", "dstar", "kwonly") for _, k in order):
        return 0
    names = [n for n, _ in order]
    if names != list(f["params"]):
        return 0
    made = 0
    for attempt in range(ncases * 3):
        if made >= ncases:
            break
        argv = []
        for n in names:
            cand = pool.get(n) or []
            argv.append(cand[attempt % len(cand)] if cand else random.randint(-8, 8))
        enc = encoder_factory()
        try:
            eargs = [enc.enc(a) for a in argv]
        except Unencodable:
            return made
        enc.freeze()
        try:
            with time_limit(2.0):
                got = fn(*argv)
            outcome = ("val", enc.enc_result(got))
        except Timeout:
            return made
        except Unencodable:
            continue
        except Exception as e:                              # noqa: BLE001
            outcome = ("exn", type(e).__name__)
        try:
            out.append(finish_record(enc, {"name": f["name"], "self": None,
                       "args": eargs, "outcome": outcome, "origin": "constructed"}))
        except Unencodable:
            continue
        made += 1
    return made


def _factory_args(fn, pool):
    """Arguments for calling a factory, drawn from observed values then by name."""
    try:
        order = frame_param_order(fn.__code__)
    except Exception:                                       # noqa: BLE001
        return []
    if any(k in ("star", "dstar", "kwonly") for _, k in order):
        return []
    out = []
    for n, _ in order:
        cand = pool.get(n) or []
        out.append(cand[0] if cand else _ctor_fallback(n))
    return out


def resolve_via_factory(mod, clsname, attr, pool):
    """The callable named `clsname.attr`, reached by CALLING the factory that defines it.

    A decorator's `wrapper` and the `Descriptor.Wrapper` classes cachetools builds inside
    `_condition`/`_locked`/`_unlocked` do not exist until their factory runs -- they are
    closures, not module attributes. Splitting the qualified name on the last dot had
    classified them as `Class.method`, so the report said "class not found", which is true
    and useless: nothing is wrong with the class, it simply has not been created yet.

    Returns a routine to call directly, a class to construct, or None. Never raises: a
    factory that rejects fabricated arguments is a missing case, not a failure."""
    segs = clsname.split(".")
    root = getattr(mod, segs[0], None)
    if root is None or not inspect.isroutine(root):
        return None
    try:
        with time_limit(2.0):
            obj = root(*_factory_args(root, pool))
    except Exception:                                       # noqa: BLE001
        return None
    for sname in segs[1:]:
        obj = getattr(obj, sname, None)
        if obj is None:
            return None
    target = getattr(obj, attr, None)
    if target is not None and (inspect.isroutine(target) or isinstance(target, type)):
        return target
    # the factory's RESULT may itself be the thing named `attr` (`_locked` returns
    # `wrapper`), in which case there is no attribute to look up
    if inspect.isroutine(obj) and getattr(obj, "__qualname__", "").split(".")[-1] == attr:
        return obj
    if isinstance(obj, type):
        return obj
    return None


def constructed_cases(methods, reached, live, pool, stats, ncases, encoder_factory=Encoder):
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
            tried = _ctor_attempts(cls, pool)
            for mk in tried:
                try:
                    with time_limit(2.0):
                        insts = [cls(*mk)]
                    break
                except Exception:                       # noqa: BLE001
                    continue
        if not insts:
            # Say WHICH of these it is. The old message was "no live instance and
            # constructor rejected ()/(1)/(2,1)" for all 54 functions in this bucket --
            # the largest single category in the report, larger than COMPARED -- and for
            # 50 of them it was FALSE: there is no class and no constructor was ever
            # tried. `_condition.wrapper` and `_locked_info.cache_info` are nested
            # FUNCTIONS, closures returned by a factory, which the caller-side split on
            # the last dot had classified as `Class.method`. A wrong cause is worse than
            # a coarse one: it sends the next person to widen a constructor search that
            # was never reached.
            if cls is None:
                # `rel` is a corpus-relative PATH, not a module -- resolve it before
                # asking what the parent name is, or every lookup silently returns None
                # and every cause comes out "class not found".
                m = find_module(rel)
                parent = clsname.rsplit(".", 1)[-1]
                pobj = getattr(m, parent, None) if m is not None else None
                if m is None:
                    why[qual] = "module for %s not imported by the suite" % rel
                    continue
                if pobj is not None and inspect.isroutine(pobj):
                    tgt = resolve_via_factory(m, clsname, attr, pool)
                    if tgt is not None and inspect.isroutine(tgt):
                        made = _direct_cases(tgt, f, pool, ncases, out, encoder_factory)
                        if made:
                            why.pop(qual, None)
                            continue
                        why[qual] = ("reached through %s(...), but no case survived "
                                     "encoding" % parent)
                        continue
                    why[qual] = ("nested function, not a method: needs %s(...) called and "
                                 "its result captured" % parent)
                else:
                    why[qual] = "class %s not found in the module" % clsname
            else:
                why[qual] = ("no live instance; constructor rejected %d argument shapes"
                             % len(tried))
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
            enc = encoder_factory()
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
            except Timeout as exc:
                why[qual] = str(exc) or "call did not terminate within 2s"; break
            except Unencodable as e:
                why[qual] = "unencodable result: %s" % (e.args[0],); break
            except Exception as e:                       # noqa: BLE001
                outcome = ("exn", type(e).__name__)
            try:
                out.append(finish_record(enc, {"name": f["name"], "self": slf,
                           "args": eargs, "outcome": outcome, "origin": "constructed"}))
            except Unencodable as e:
                why[qual] = "unencodable post-state: " + str(e)
                break
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

def c_runtime(src_root, funcs=None):
    if funcs is not None:
        import native_c
        return native_c.compile_sources(src_root, funcs, os.path.join(WORK, "native-units"))
    return _c_runtime_whole(src_root)


def _c_runtime_whole(src_root, funcs=None):
    """Compile C sources and expose scalar entry points through native workers.

    Same oracle, different runtime: the point of the Core language is that one semantics
    is checked against whichever real implementation produced the code."""
    import native_c
    srcs = sorted(p for ext in ("c", "cc", "cpp", "cxx")
                  for p in glob.glob(os.path.join(src_root, "**", "*." + ext), recursive=True))
    if not srcs: return None
    import tempfile, platform, shlex
    native_work = tempfile.mkdtemp(prefix="native-", dir=WORK)
    lib = os.path.join(native_work, "libautoform_diff_c" +
                       (".dylib" if sys.platform == "darwin" else ".so"))
    arch = ["-arch", platform.machine()] if sys.platform == "darwin" else []
    cpp = any(not s.endswith(".c") for s in srcs)
    symbols = {}
    if cpp and funcs:
        # Compile a C ABI thunk in the original translation unit, which also makes
        # file-static functions reachable. Parameter types come from Joern.
        units = []
        for source_index, source in enumerate(srcs):
            wrapper = os.path.join(native_work, "unit%d.cpp" % source_index)
            lines = ["#include <cstdint>", "#include " + json.dumps(os.path.abspath(source))]
            for idx, f in enumerate(funcs):
                if os.path.realpath(os.path.join(src_root, f.get("file", ""))) != os.path.realpath(source):
                    continue
                name = f.get("sourceName", f["name"])
                argtypes, ret = f.get("paramTypes", []), f.get("returnType", "")
                if not re.fullmatch(r"[A-Za-z_]\w*(?:::[A-Za-z_]\w*)*", name) or len(argtypes) != len(f["params"]):
                    continue
                if not ret or any(not re.fullmatch(r"[A-Za-z_][\w: ]*", t) for t in [ret, *argtypes]):
                    continue
                if not f.get("returnIntegerType") or any(not t for t in f.get("paramIntegerTypes", [])):
                    continue
                symbol = "autoform_native_%d" % idx
                cpp_types = {"i8": "int8_t", "u8": "uint8_t", "i16": "int16_t", "u16": "uint16_t",
                             "i32": "int32_t", "u32": "uint32_t", "i64": "int64_t", "u64": "uint64_t"}
                args = ", ".join(cpp_types[t] + " a%d" % i for i, t in enumerate(f["paramIntegerTypes"]))
                values = ", ".join("a%d" % i for i in range(len(argtypes)))
                lines.append('extern "C" auto %s(%s) { return %s(%s); }' % (symbol, args, name, values))
                symbols[f["name"]] = symbol
            with open(wrapper, "w") as fh:
                fh.write("\n".join(lines))
            units.append(wrapper)
        srcs = units
    r = subprocess.run(["c++" if cpp else "cc", "-shared", "-fPIC", "-O0", *arch, "-o", lib] + srcs +
                       shlex.split(os.environ.get("AUTOFORM_CFLAGS", "")),
                       capture_output=True, text=True, timeout=180)
    if r.returncode != 0:
        print("cc failed:", r.stderr[:300]); return None
    outcome = native_c.worker(dict(operation='probe', library=lib, symbols=[]))
    if outcome['status'] != 'ok':
        print('native load failed:', json.dumps(outcome)); return None

    def get(f):
        # The ABI is part of the oracle. Guessing int for pointers, long or uint64
        # manufactures divergences and can crash the process being measured.
        args = f.get("paramIntegerTypes", [])
        ret = f.get("returnIntegerType", "")
        if len(args) != len(f["params"]) or ret not in native_c.TYPES or any(t not in native_c.TYPES for t in args):
            return None
        symbol = symbols.get(f['name'], f['name'])
        if native_c.worker(dict(operation='probe', library=lib, symbols=[symbol]))['status'] != 'ok':
            return None
        return native_c.NativeFunction(lib, symbol, args, ret)
    return get


def call_in_child(fn, args):
    """Compatibility value interface; the report uses structured observations."""
    result = fn.observe(args)
    return result['values'][0] if result['status'] == 'ok' else None


def call_in_child_twice(fn, args):
    """Call the same function twice with the same arguments in one native worker.

    Returns (v1, v2), either of which is None if the child died.

    This is the allocation-dependence discriminator for the wasm UB oracle. A function
    that returns a freshly `malloc`ed pointer (`sdsempty`, `sds_malloc`) hands back a
    different value on the second call; a pure integer function hands back the same one.
    Without this test, every pointer-returning function looks like a native/wasm
    disagreement -- native reports a 64-bit heap address, wasm reports a 32-bit linear
    memory offset -- and the UB count fills up with results that are nothing but two
    different address spaces. That would be a self-flattering metric pointed the other
    way: an impressive-sounding pile of "UB found" that is entirely an artifact.
    """
    result = fn.observe(args, repeat=2)
    return tuple(result['values']) if result['status'] == 'ok' else (None, None)


def observe_c_plan(cget, plan, repeat=1):
    """Keep failed native attempts attributable to their exact function and input."""
    first, second, failures, counts = {}, {}, [], {}
    for index, (function, args) in enumerate(plan):
        fn = cget(function)
        result = fn.observe(args, repeat=repeat) if fn else dict(status='unavailable')
        status = result['status']
        counts[status] = counts.get(status, 0) + 1
        if status == 'ok':
            first[index] = result['values'][0]
            if repeat == 2:
                second[index] = result['values'][1]
        else:
            failures.append(dict(function=function['name'], file=function.get('file', ''),
                                 args=args, **result))
    return first, second, dict(planned=len(plan), outcomes=counts, failures=failures,
                              isolation='fresh process per case; repeated calls share one process')


from boundary_values import typed_boundary_pool  # noqa: E402  (shared with machine_regress)


def c_argument_cases(argtypes, ncases, random_arg, boundaries=False):
    """Reserve a case for zero/equality boundaries before random exploration.

    Small random samples missed both `<` versus `<=` and the zero-base,
    zero-exponent branch in the Linux RAID-6 mutation run. This is one guaranteed
    boundary within the requested budget, not exhaustive boundary coverage.

    With `boundaries`, every other remaining case draws each argument from
    `typed_boundary_pool` for its ABI type (seeded, so reproducible) instead of
    `random_arg`, which is where 64-bit overflow behaviour becomes observable.
    """
    for index in range(ncases):
        if index == 0:
            yield [0] * len(argtypes), 'boundary-zero'
        elif boundaries and index % 2 == 0:
            yield [random.choice(typed_boundary_pool(t)) for t in argtypes], 'boundary-typed'
        else:
            yield [t(random_arg()).value for t in argtypes], 'random'


def load_module(path, root):
    """The module for a source file.

    Ask for it BY PACKAGE NAME first. Loading a file by path gives it a synthetic top-level
    name (`cachetools__init___py`), which makes every RELATIVE import inside it fail --
    `from . import keys` has no package to be relative to. That is not an edge case: it is
    every package `__init__.py`, and here it silently cost `cached`, `cachedmethod` and
    `_cache` their cases, which then reported as "hole-free, no case built" as though the
    functions were unreachable rather than the loader broken.

    The path loader stays as the fallback, for a corpus that is not an importable package."""
    rel = os.path.relpath(path, root)
    m = find_module(rel)
    if m is not None and os.path.realpath(getattr(m, "__file__", "") or "") == os.path.realpath(path):
        return m
    # An installed package or stdlib module with the same name is not the corpus.
    # For standalone files use a private identity so e.g. numbers.py cannot resolve
    # to Python's already-imported standard library module.
    import hashlib
    name = "_autoform_source_" + hashlib.sha256(os.path.abspath(path).encode()).hexdigest()[:16]
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    sys.modules[name] = m
    sys.path.insert(0, root)
    try:
        spec.loader.exec_module(m)
        return m
    except Exception:
        return None


# ------------------------------------------------------------------ language dispatch
#
# The corpus decides which real runtime the oracle must talk to. Getting this wrong is
# not a missing feature but a *false* result: `cartographer/render_lean.py`'s
# `infer_dialect` used to default an unrecognised language to Python, and the oracle
# then cheerfully reported agreement. So the mapping is explicit, and an extension that
# is not in it is REFUSED rather than defaulted.

LANG_BY_EXT = {".py": "python", ".pyi": "python",
               ".c": "c", ".h": "c",
               ".cpp": "c", ".cc": "c", ".cxx": "c", ".hh": "c", ".hpp": "c",
               ".java": "java", ".go": "go",
               ".js": "js", ".mjs": "js", ".cjs": "js", ".jsx": "js",
               ".ts": "ts", ".tsx": "ts", ".mts": "ts", ".cts": "ts",
               ".kt": "kotlin", ".kts": "kotlin"}

# Integer operations carry their language and promoted width independently of the
# program dialect. This table does not claim every construct in a language is modeled.
# `dialect_is_exact` stays False for Java, Go and Kotlin even though each now has (or
# rides) its own constructor: the UNTAGGED integer path is one width per language (Java
# `int`, Go `int`), and a `long`/`int8` operation is exact only when the exporter tagged
# it. Kotlin additionally has structural string `==` where `.java` holes.
DIALECT_FOR = {"python": ("python", True), "c": ("cLike", True),
               "java": ("java", False),
               "go": ("go", False),
               "js": ("javascript", True),
               "ts": ("javascript", True),
               "kotlin": ("java", False)}

TOOLCHAIN = {"python": [], "c": ["cc"], "java": ["javac", "java"], "go": ["go"],
             "js": ["node"], "ts": ["node"], "kotlin": ["kotlinc"]}


def detect_language(funcs):
    """(language, extension histogram). Returns None rather than guessing."""
    exts = {}
    for f in funcs:
        ext = os.path.splitext(f.get("file", ""))[1].lower()
        if ext:
            exts[ext] = exts.get(ext, 0) + 1
    if not exts:
        return None, exts
    langs = {}
    for e, n in exts.items():
        k = LANG_BY_EXT.get(e)
        langs[k] = langs.get(k, 0) + n
    if None in langs or len(langs) != 1:
        return None, exts
    return next(iter(langs)), exts


def have(cmd):
    for d in os.environ.get("PATH", "").split(":"):
        p = os.path.join(d, cmd)
        if os.path.isfile(p) and os.access(p, os.X_OK):
            return p
    return None


def missing_tools(lang):
    if lang == "kotlin":
        return [] if runtime_backends.kotlin_toolchain() and have("javac") else ["Kotlin JVM compiler and JDK"]
    return [c for c in TOOLCHAIN.get(lang, []) if not have(c)]


def runtime_version(lang):
    commands = {"python": [sys.executable, "--version"], "c": ["cc", "--version"],
                "java": ["java", "-version"], "go": ["go", "version"],
                "js": ["node", "--version"], "ts": ["node", "--version"],
                "kotlin": ["kotlinc", "-version"]}
    try:
        if lang == "kotlin" and runtime_backends.kotlin_toolchain():
            commands[lang] = runtime_backends.kotlin_toolchain()[0] + ["-version"]
        p = subprocess.run(commands[lang], capture_output=True, text=True, timeout=15)
        return (p.stdout + p.stderr).strip()
    except (OSError, subprocess.TimeoutExpired) as exc:
        return "unavailable: " + str(exc)


# ------------------------------------------------------------------------ JVM backend

JAVA_PRIM = ("int", "long", "short", "byte", "char", "float", "double", "boolean", "java.lang.String")
STRING_POOL = ["", "0", "11", "1.8.0_281", "17.0.1", "java.lang.String",
               "android.os.Bundle", "com.example.Foo"]
JAVA_SIG = re.compile(r'^(?P<cls>[\w.$]+)\.(?P<meth>[\w$<>]+):(?P<ret>[\w.$\[\]]+)'
                      r'\((?P<args>.*)\)$')

JAVA_DRIVER = r"""import java.lang.reflect.*;
import java.util.*;

public class AutoformDriver {
  static String enc(Object o) {
    if (o == null) return "null|";
    if (o instanceof String)
      return "str|" + Base64.getEncoder().encodeToString(((String) o).getBytes());
    if (o instanceof Boolean) return "bool|" + o;
    if (o instanceof Character) return "int|" + (int) (Character) o;
    if (o instanceof Float || o instanceof Double)
      return "float|" + Long.toUnsignedString(Double.doubleToRawLongBits(((Number)o).doubleValue()));
    return "int|" + o;
  }
  public static void main(String[] a) throws Exception {
    Scanner sc = new Scanner(System.in);
    while (sc.hasNextLine()) {
      String line = sc.nextLine();
      if (line.isEmpty()) continue;
      String[] p = line.split("\\|", -1);
      String idx = p[0], cn = p[1], mn = p[2];
      int n = Integer.parseInt(p[3]);
      Class<?>[] ts = new Class<?>[n];
      Object[] vs = new Object[n];
      for (int i = 0; i < n; i++) {
        String t = p[4 + 2 * i], v = p[5 + 2 * i];
        if (t.equals("int"))          { ts[i] = int.class;     vs[i] = Integer.parseInt(v); }
        else if (t.equals("long"))    { ts[i] = long.class;    vs[i] = Long.parseLong(v); }
        else if (t.equals("short"))   { ts[i] = short.class;   vs[i] = Short.parseShort(v); }
        else if (t.equals("byte"))    { ts[i] = byte.class;    vs[i] = Byte.parseByte(v); }
        else if (t.equals("char"))    { ts[i] = char.class;    vs[i] = (char) Integer.parseInt(v); }
        else if (t.equals("float"))   { ts[i] = float.class;   vs[i] = Float.parseFloat(v); }
        else if (t.equals("double"))  { ts[i] = double.class;  vs[i] = Double.parseDouble(v); }
        else if (t.equals("boolean")) { ts[i] = boolean.class; vs[i] = Boolean.parseBoolean(v); }
        else { ts[i] = String.class; vs[i] = new String(Base64.getDecoder().decode(v)); }
      }
      try {
        Method m = Class.forName(cn).getDeclaredMethod(mn, ts);
        m.setAccessible(true);
        Object r = m.invoke(null, vs);
        System.out.println(idx + "|OK|" + enc(r));
      } catch (InvocationTargetException e) {
        System.out.println(idx + "|EXN|" + e.getCause().getClass().getSimpleName());
      } catch (Throwable t) {
        System.out.println(idx + "|ERR|" + t.getClass().getSimpleName());
      }
    }
  }
}
"""


JAVA_PACKAGE = re.compile(r'^\s*package\s+([\w.]+)\s*;', re.MULTILINE)


def java_package(path):
    """The `package` a .java file declares, or None for the default package."""
    try:
        with open(path, encoding='utf-8', errors='replace') as handle:
            head = handle.read(65536)
    except OSError:
        return None
    # Strip block and line comments so a commented-out declaration cannot win.
    head = re.sub(r'/\*.*?\*/', ' ', head, flags=re.DOTALL)
    head = re.sub(r'//[^\n]*', ' ', head)
    match = JAVA_PACKAGE.search(head)
    return match.group(1) if match else None


def java_source_roots(sources):
    """Derive `javac -sourcepath` roots by stripping each file's package path.

    Compiling a real Java repository one file at a time with no `-sourcepath` fails
    the moment a candidate references any other class in its own project: on Apache
    Spark only 6 of 44 candidate files compiled, and the rest reported
    `package org.apache.spark... does not exist` -- an intra-project reference, not a
    missing third-party jar. Since the AST already told us which files to compile, the
    source roots can be recovered without knowing the build system: a file declaring
    `package a.b.c` must sit in `&lt;root&gt;/a/b/c`, so walking that many directories up
    yields `&lt;root&gt;`. This is layout-agnostic on purpose -- Maven, Gradle, Bazel and
    flat trees all satisfy the same JLS rule -- and it needs no Maven/Gradle invocation,
    no network and no jars, so it degrades to today's behaviour rather than failing when
    a project genuinely depends on external libraries.
    """
    roots = set()
    for src in sources:
        directory = os.path.dirname(os.path.abspath(src))
        package = java_package(src)
        if not package:
            roots.add(directory)
            continue
        for part in reversed(package.split('.')):
            if os.path.basename(directory) != part:
                directory = None
                break
            directory = os.path.dirname(directory)
        # A file whose path disagrees with its own package declaration gives no
        # usable root; skip it rather than adding a misleading one.
        if directory:
            roots.add(directory)
    return sorted(roots)


def java_failure_category(stderr):
    """Bucket a javac failure so the report says WHY, not just how many."""
    text = stderr or ''
    if 'does not exist' in text and 'package' in text:
        return 'unresolved package (missing classpath or source root)'
    if 'cannot find symbol' in text:
        return 'unresolved symbol (missing classpath or source root)'
    if 'invalid source release' in text or 'invalid target release' in text:
        return 'javac release mismatch'
    if 'error: cannot access' in text:
        return 'unreadable dependency'
    return 'other javac error'


def java_backend(src_root, holefree, ncases, kotlin=False):
    """Compile each candidate's own file, then call it reflectively.

    The corpus (a gson subset) does not compile as a whole — most of gson is absent —
    so compilation is per file, and a file that will not build becomes a *reported*
    skip rather than a silent one. Only `static` methods whose whole signature is
    primitive-or-String are callable without building a receiver."""
    import base64
    work = os.path.join(WORK, "java")
    classes = os.path.join(work, "classes")
    os.makedirs(classes, exist_ok=True)
    info, skipped, cands = {}, {}, []
    for f in holefree:
        m = JAVA_SIG.match(f["name"])
        if not m:
            continue
        if "this" in f["params"]:
            skipped[f["name"]] = "instance method: needs a receiver"
            continue
        args = [a for a in m.group("args").split(",") if a]
        if len(args) != len(f["params"]):
            skipped[f["name"]] = "signature/parameter count disagree"
            continue
        if any(a not in JAVA_PRIM for a in args) or m.group("ret") not in JAVA_PRIM:
            skipped[f["name"]] = "non-primitive signature"
            continue
        src = os.path.join(src_root, f.get("file", ""))
        if not os.path.exists(src):
            skipped[f["name"]] = "source file not found under the corpus root"
            continue
        cands.append((f, m, args, src))
    info["primitive_static_candidates"] = len(cands)
    if not cands:
        return [], info, skipped
    compiled = set()
    classpath = classes
    if kotlin:
        names, failures, runtime = runtime_backends.compile_kotlin(src_root, cands, work)
        skipped.update(failures)
        cands = [(f, JAVA_SIG.match(names[f["name"]]), args, src)
                 for f, _, args, src in cands if f["name"] in names]
        compiled.update(c[3] for c in cands)
        classpath += os.pathsep + runtime
    candidate_sources = [] if kotlin else sorted({c[3] for c in cands})
    # Give javac the project's own source roots so intra-project references resolve.
    source_roots = java_source_roots(candidate_sources)
    sourcepath = ["-sourcepath", os.pathsep.join(source_roots)] if source_roots else []
    failure_causes = collections.Counter()
    for src in candidate_sources:
        # `-proc:none` keeps a project's annotation processors off our compile path;
        # implicit compilation stays ON so classes pulled in via -sourcepath land in
        # `classes/` and are present on the classpath when the driver runs.
        r = subprocess.run(["javac", "-nowarn", "-proc:none", *sourcepath,
                            "-d", classes, src],
                           capture_output=True, text=True)
        if r.returncode == 0:
            compiled.add(src)
        else:
            last = (r.stderr.strip().splitlines() or ["?"])[-1]
            failure_causes[java_failure_category(r.stderr)] += 1
            for f, _, _, s2 in cands:
                if s2 == src:
                    skipped[f["name"]] = "javac failed: " + last[:70]
    info["files_compiled"] = len(compiled)
    info["files_candidate"] = len(candidate_sources)
    if source_roots:
        info["source_roots"] = len(source_roots)
    # Without this, a run that compiled almost nothing reported only
    # `files_compiled: 6` and the reason lived in per-function skip strings that the
    # report truncates. "0 COMPARED" must say what stopped it.
    if failure_causes:
        info["files_failed"] = len(candidate_sources) - len(compiled)
        info["compile_failure_causes"] = dict(failure_causes.most_common())
    cands = [c for c in cands if c[3] in compiled]
    if not cands:
        return [], info, skipped
    open(os.path.join(work, "AutoformDriver.java"), "w").write(JAVA_DRIVER)
    r = subprocess.run(["javac", "-nowarn", "-d", classes,
                        os.path.join(work, "AutoformDriver.java")],
                       capture_output=True, text=True)
    if r.returncode != 0:
        info["driver"] = "failed to compile: " + r.stderr[:200]
        return [], info, skipped
    calls, plan = [], []
    for f, m, argtypes, _ in cands:
        for iteration in range(max(1, ncases)):
            vals, enc = [], []
            for t in argtypes:
                if t == "java.lang.String":
                    v = random.choice(STRING_POOL)
                    vals.append(("str", v))
                    enc += [t, base64.b64encode(v.encode()).decode()]
                elif t == "boolean":
                    v = random.choice([True, False])
                    vals.append(("bool", v))
                    enc += [t, "true" if v else "false"]
                elif t in ("float", "double"):
                    v = [0.0, 1.5, -2.25, 16777216.0, -0.0][iteration % 5]
                    vals.append(Encoder().enc(v))
                    enc += [t, str(v)]
                else:
                    bits = {"byte": 8, "short": 16, "char": 16, "int": 32, "long": 64}[t]
                    hi = (1 << (bits if t == "char" else bits - 1)) - 1
                    lo = 0 if t == "char" else -(1 << (bits - 1))
                    pool = [0, 1, hi, lo, 31, 32, 63, 64]
                    v = pool[(iteration + len(vals)) % len(pool)]
                    vals.append(("int", v))
                    enc += [t, str(v)]
            calls.append("|".join([str(len(calls)), m.group("cls"), m.group("meth"),
                                   str(len(argtypes))] + enc))
            plan.append((f["name"], vals))
    out = subprocess.run(["java", "-cp", classpath, "AutoformDriver"],
                         input="\n".join(calls) + "\n",
                         capture_output=True, text=True, timeout=300)
    got = {}
    for line in out.stdout.splitlines():
        p = line.split("|")
        if len(p) >= 2 and p[0].isdigit():
            got[int(p[0])] = p[1:]
    cases, unusable = [], {}
    for i, (name, vals) in enumerate(plan):
        r = got.get(i)
        if r is None:
            unusable[name] = "no answer from the JVM driver"
            continue
        if r[0] == "OK":
            kind = r[1]
            payload = r[2] if len(r) > 2 else ""
            if kind == "str":
                outcome = ("val", ("str", base64.b64decode(payload).decode()))
            elif kind == "bool":
                outcome = ("val", ("bool", payload == "true"))
            elif kind == "int":
                outcome = ("val", ("int", int(payload)))
            elif kind == "float":
                outcome = ("val", ("float", int(payload)))
            else:
                unusable[name] = "returned null: no faithful Core counterpart"
                continue
        elif r[0] == "EXN":
            outcome = ("exn", r[1])
        else:
            unusable[name] = "JVM driver error: " + (r[1] if len(r) > 1 else "?")
            continue
        cases.append({"name": name, "heap": [], "self": None,
                      "args": list(vals), "outcome": outcome, "origin": "random"})
    skipped.update(unusable)
    info["cases_built"] = len(cases)
    return cases, info, skipped


# Drivers consume Joern identities and signatures; no duplicate source parser.
def go_backend(src_root, holefree, ncases):
    return runtime_backends.go_backend(src_root, holefree, ncases, WORK)


def node_backend(src_root, holefree, ncases, lang):
    return runtime_backends.node_backend(src_root, holefree, ncases, lang, WORK)


# ---------------------------------------------------------------------------- main

def main():
    argv = [a for a in sys.argv[1:]]
    tests_override = None
    if "--tests" in argv:
        i = argv.index("--tests"); tests_override = argv[i + 1]; del argv[i:i + 2]
    # `--wasm` turns on the sandboxed second C implementation. It is OPT-IN, and
    # deliberately so: it changes which cases are attempted and which are withheld from
    # the Lean comparison, so it changes the denominator. A flag that silently altered
    # the basis would make new rates look comparable to old ones when they are not.
    wasm_mode = "--wasm" in argv
    if wasm_mode: argv.remove("--wasm")
    # `--language js|ts|java|go|kotlin|python|c` names the runtime explicitly. The
    # extension vote stays the default because it cannot be wrong silently -- it refuses
    # on a mixed or unknown corpus -- but a corpus whose files carry no extension the
    # table knows (a generated fixture, a `.mjs`-only package renamed by a bundler)
    # needs a way to say what it is. The override is RECORDED in conformance.json.
    lang_override = None
    if "--language" in argv:
        i = argv.index("--language"); lang_override = argv[i + 1]; del argv[i:i + 2]
    ast_path, src_root, lean_mod = argv[0], argv[1], argv[2]
    ncases = int(argv[3]) if len(argv) > 3 else 5
    # Static coverage and sampling use the same source bodies as the Lean ledger,
    # including refusals introduced when suspended generators are lowered.
    funcs = analysis_functions(deep_json.load(ast_path))
    module_tag = lean_mod
    repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    generated = os.path.join(repo, "Autoform", "Generated", lean_mod + ".lean")
    fingerprints = runtime_backends.source_fingerprints(src_root, funcs)
    ast_fingerprint = runtime_backends.sha256(ast_path)
    semantics_fingerprint = runtime_backends.semantics_fingerprints()

    # ---- which real runtime does this corpus need?
    lang, exts = detect_language(funcs)
    RUNTIME = {"python": "cpython", "c": "cc", "java": "jvm", "go": "go",
               "js": "node", "ts": "node", "kotlin": "kotlin"}
    if lang_override is not None:
        if lang_override not in RUNTIME:
            print("REFUSING to run: --language %r is not one of %s"
                  % (lang_override, sorted(RUNTIME)))
            return 2
        if lang is not None and lang != lang_override:
            print("  --language %s overrides the extension vote (%s); the override is "
                  "recorded in conformance.json" % (lang_override, lang))
        lang = lang_override
    if lang is None:
        print("REFUSING to run: cannot identify the corpus language from its file "
              "extensions %s. Defaulting to CPython would report agreement between the "
              "Lean semantics and a runtime that never ran this code." % sorted(exts))
        json.dump({"module": module_tag, "ast": os.path.abspath(ast_path),
                   "status": "REFUSED: unknown source language",
                   "extensions": exts, "agree": 0, "total": 0, "divergences": 0,
                   "inconclusive": 0, "rate": "n/a",
                   "coverage": {"population": len(funcs), "compared": 0,
                                "covered_metric": "compared",
                                "compared_fraction": 0.0}},
                  open("conformance.json", "w"), indent=1)
        return 2
    runtime = RUNTIME[lang]
    is_c = (lang == "c")
    want_dialect, exact = DIALECT_FOR[lang]
    missing = missing_tools(lang)
    print("language: %s (%s) -> runtime %s%s"
          % (lang, ", ".join("%s x%d" % (e, n) for e, n in sorted(exts.items())),
             runtime, "" if not missing else "  [MISSING: %s]" % ", ".join(missing)))
    if not exact:
        print("  dialect note: Core has no %s-specific dialect yet (only .python, "
              ".cLike, .javascript exist), so %s runs under an approximation "
              "outside the exported language-specific numeric operations." % (lang, lang))

    holefree = [f for f in funcs if not has_hole(f["body"])]
    # NOTE ON MEASUREMENT BASIS. `skip_varargs` used to exist here and was removed
    # deliberately: a `*args`/`**kwargs` callee binds a tuple and a dict, which Core
    # models exactly, so those calls are now *attempted* (bound positionally against
    # the AST's own parameter list) instead of skipped. That attempts far more and
    # lands more cases INCONCLUSIVE, so the conclusive denominator is not the same
    # denominator as before. Rates across the two bases are NOT comparable, and the
    # output says which basis produced it rather than leaving a reader to assume.
    stats = {"skip_unencodable_args": 0, "skip_unencodable_ret": 0,
             "skip_no_instance": 0, "test_runs": []}
    BASIS = "varargs-attempted-v2"
    BASIS_NOTE = ("Basis %s: `*args`/`**kwargs` callees are bound (tuple/dict) and "
                  "attempted rather than skipped; container subclasses and object dict "
                  "keys are refused; only adjudicated cases count in the denominator. "
                  "Rates from the earlier `varargs-skipped-v1` basis (e.g. 104/104) are "
                  "a different measurement and must not be compared." % "v2")

    if lang == "python":
        BASIS = "python-deadlines-v4"
        BASIS_NOTE = ("Varargs remain attempted. Functions whose only static holes are "
                      "unsupported exception-representation fallbacks are also sampled; "
                      "cases reaching a hole remain inconclusive. Static hole counts "
                      "are unchanged. Coverage and rates differ from the earlier "
                      "hole-free-only sampling population. Synthesized native calls now "
                      "use main-thread signal deadlines, including random free-function "
                      "calls; timed-out calls are skipped, never recorded as source "
                      "exceptions. Python's normal recursion limit is preserved. These "
                      "bounds may change the sample relative to python-exception-guards-v3.")

    # Each non-Python runtime backend samples its own domain and calls its own surface;
    # naming that basis per runtime is what stops a Node rate being read as if it were
    # measured the way the CPython trace was.
    if lang in ("js", "ts"):
        BASIS = "node-numeric-pool-v1"
        BASIS_NOTE = ("Node calls each module-scope function of the corpus on a fixed numeric "
                      "pool (0, 1, -1, 2^31-1, 2^32, 32, 64, -3.75, Infinity, NaN) cycled per "
                      "parameter -- NOT the corpus's own tests. Numbers are compared as IEEE "
                      "doubles (Core's small-integer representation of a JS Number is widened "
                      "before comparison). Functions returning objects, arrays or promises, "
                      "and functions not reachable at module scope, are skipped and COUNTED "
                      "under backend_skipped. TypeScript runs through "
                      "`node --experimental-strip-types`: erasable annotations only.")
    elif lang in ("java", "kotlin"):
        BASIS = "jvm-primitive-static-v1"
        BASIS_NOTE = ("Only static methods whose whole signature is primitive-or-String are "
                      "called, reflectively, on a fixed pool per type (0, 1, MAX, MIN, 31, 32, "
                      "63, 64 for integers; a fixed string list; 0.0, 1.5, -2.25, 2^24, -0.0 "
                      "for floats). Instance methods, non-primitive signatures and files that "
                      "do not compile against the corpus's own source roots are skipped and "
                      "COUNTED; no third-party classpath is supplied. Kotlin compiles a "
                      "@JvmStatic thunk per function and goes through the same driver.")
    elif lang == "go":
        BASIS = "go-package-func-v1"
        BASIS_NOTE = ("Package-level functions with scalar parameters (integers, bool, "
                      "string, float) and at most one scalar result are called from a "
                      "generated `_test.go` in a private copy of the module, on a fixed "
                      "per-type pool (0, 1, -1, MAX, MIN, 2, 31, 32, 63, 64 for integers). "
                      "Methods, variadics, multi-value returns and non-scalar types are "
                      "skipped and COUNTED under backend_skipped.")

    if is_c:
        BASIS = "c-native-typed-boundary-v4"
        BASIS_NOTE = ("C scalar inputs reserve the first case per function for all-zero "
                      "arguments, covering a zero/equality boundary. Every other remaining "
                      "case draws each argument from its ABI type's width boundaries "
                      "(powers of two straddling 32 and 64 bits, the type's extremes); the "
                      "rest use the seeded small-integer sampler and declared ABI "
                      "conversions. This is not exhaustive boundary coverage. Inputs differ "
                      "from the earlier zero-boundary basis (v3); rates are not directly "
                      "comparable.")
    if wasm_mode and is_c:
        # The denominator moves under `--wasm`: calls where native and wasm-clang
        # disagree are withheld from the Lean comparison and counted as `ub-suspected`
        # instead. That is a DIFFERENT measurement from the native-only C basis, and it
        # says so rather than letting a reader assume the rates line up.
        BASIS = "c-dual-oracle-typed-boundary-v5"
        BASIS_NOTE = (
            "Basis c-dual-oracle-typed-boundary-v5: C is executed under BOTH native `cc` and a "
            "freestanding wasm32 build, on identical inputs. Calls where the two "
            "conforming implementations return different values are recorded as "
            "`ub-suspected` and WITHHELD from the Lean comparison -- Core maps UB to "
            "`Expr.hole` (`NumResult.ub`), so scoring those against Lean would penalise "
            "the semantics for being correct. The conclusive denominator therefore "
            "excludes them and is NOT comparable to the native-only C basis. The first "
            "case per function has all-zero arguments; remaining arguments "
            "are additionally drawn from a boundary-biased pool (INT_MIN/INT_MAX, shift "
            "counts >= 32) rather than only randint(-20, 20), so the inputs differ from "
            "the native-only basis as well. Two separate categories are reported and "
            "NOT counted as UB: `width-sensitive` (functions using `long`/`size_t`, "
            "which are 32-bit on wasm32 and 64-bit natively) and `excluded_from_ub` "
            "(pointer returns and results unstable across two identical native calls).")

    # cases: dict(name, heap, self, args, outcome, origin)
    cases = []
    C_WASM_REPORT = []      # filled by the C backend below; surfaced in conformance.json

    backend_info, backend_skipped, backend_status = {}, {}, "available"
    if missing:
        backend_status = "UNSUPPORTED: toolchain absent (%s)" % ", ".join(missing)
        print("  backend UNSUPPORTED: %s not on PATH — this language has NO runtime "
              "check, which is a gap in the evidence, not a pass." % ", ".join(missing))
    elif lang in ("java", "kotlin", "go", "js", "ts"):
        if lang in ("java", "kotlin"):
            cases, backend_info, backend_skipped = java_backend(src_root, holefree,
                                                                ncases, kotlin=lang == "kotlin")
        elif lang == "go":
            cases, backend_info, backend_skipped = go_backend(src_root, holefree, ncases)
        else:
            cases, backend_info, backend_skipped = node_backend(src_root, holefree, ncases, lang)
        if not cases:
            backend_status = ("UNSUPPORTED: no testable surface — "
                              + str(backend_info.get("note", backend_info)))
        print("  backend %s: %s; %d cases built"
              % (runtime, json.dumps(backend_info)[:160], len(cases)))
    elif is_c:
        cget = c_runtime(src_root, holefree)
        backend_info = getattr(cget, "info", {})
        backend_status = backend_info.get("status", "available" if cget else "unsupported: native compilation failed")
        backend_skipped.update(getattr(cget, "skipped", {}))
        if backend_info:
            with open("native-build.json", "w") as build_report:
                json.dump(backend_info, build_report, indent=2)
            print("  native C: %d/%d translation units compiled; %d entry points" % (
                backend_info.get("files_compiled", 0), backend_info.get("files_attempted", 0),
                backend_info.get("entry_points", 0)))
        cands = [f for f in holefree
                 if not f.get("isInit")]
        # Fix the argument vectors up front so the native and wasm runs see EXACTLY the
        # same inputs. Generating them twice from the same seeded RNG would drift the
        # moment either side skips a function, and a cross-implementation comparison on
        # mismatched inputs is worse than none: it manufactures disagreements.
        # Under `--wasm` the arguments are drawn from a boundary-biased pool as well as
        # the small range. `randint(-20, 20)` can never trigger the behaviour this
        # oracle exists to find: signed overflow needs operands near INT_MAX, and
        # shift-past-width needs a count >= 32. Searching for UB with inputs that cannot
        # produce it and reporting "none found" would be an empty result dressed as a
        # clean one. This widens what is attempted, which is part of why the basis
        # changes.
        UB_POOL = [0, 1, -1, 2, 3, 7, 8, 16, 31, 32, 33, 63, 64, 65,
                   255, 256, 65535, 65536, 1 << 20,
                   (1 << 31) - 1, -(1 << 31), (1 << 31) - 2, -(1 << 31) + 1,
                   (1 << 30), -(1 << 30), 0x55555555 - (1 << 32), 0x7ffffffe]

        def c_arg():
            if wasm_mode and random.random() < 0.55:
                return random.choice(UB_POOL)
            return random.randint(-20, 20)

        plan, origins = [], []
        for f in cands:
            fn = cget(f) if cget else None
            if fn is None:
                backend_skipped.setdefault(f["name"], "native compile failed or ABI types unavailable")
                continue
            for args, origin in c_argument_cases(fn.argtypes, ncases, c_arg, boundaries=True):
                plan.append((f, args))
                origins.append(origin)
        backend_info['input_strategy'] = ('first case all-zero; every other remaining case '
                                          'per-type width boundaries; the rest seeded random')

        # Bound execution itself, not only the later Lean harness.
        if len(plan) > MAX_TOTAL_CASES:
            backend_info["planned_cases_before_cap"] = len(plan)
            backend_info["case_cap"] = MAX_TOTAL_CASES
            plan = plan[:MAX_TOTAL_CASES]

        # ---- native leg (the existing `cc` backend)
        native, native2, execution = observe_c_plan(cget, plan, repeat=2 if wasm_mode else 1)
        backend_info['native_execution'] = execution
        for status, count in execution['outcomes'].items():
            if status != 'ok':
                stats['skip_c_' + status] = count

        # ---- wasm leg (sandbox + second implementation)
        wres, wasm_report = {}, None
        if wasm_mode:
            tc = wasm_backend.toolchain()
            if not tc["ok"]:
                # LOUD. A missing toolchain is a gap in the evidence; it must never be
                # allowed to look like a clean run with nothing to report.
                wasm_report = {"status": "UNSUPPORTED: no wasm toolchain",
                               "reason": tc["reason"]}
                print("  wasm UNSUPPORTED: %s — the sandbox and the UB oracle did NOT "
                      "run. This is a missing check, not a pass." % tc["reason"])
            else:
                wdir = os.path.join(WORK, "wasm"); os.makedirs(wdir, exist_ok=True)
                srcs = glob.glob(os.path.join(src_root, "**", "*.c"), recursive=True)
                wpath, winfo = wasm_backend.compile_wasm(srcs, wdir, tc)
                if wpath is None:
                    wasm_report = {"status": "UNSUPPORTED: wasm build failed",
                                   "reason": winfo.get("error"), "build": winfo}
                    print("  wasm UNSUPPORTED: %s" % winfo.get("error"))
                else:
                    caller = wasm_backend.WasmCaller(wpath, tc, wdir)
                    wres = caller.run([{"id": k, "name": f["name"], "args": a}
                                       for k, (f, a) in enumerate(plan)])
                    wasm_report = {"status": "ran", "toolchain": tc, "build": winfo}

        # ---- adjudicate the two C implementations against each other
        wtally, ub_findings, trap_detail, excluded = {}, [], {}, []
        width_findings = []
        width_fns = (wasm_backend.width_sensitive_functions(src_root)
                     if wasm_mode and wres else set())
        for k, (f, args) in enumerate(plan):
            nat = native.get(k)
            if wasm_mode and wres:
                kind, det = wasm_backend.adjudicate(nat, wres.get(k),
                                                    native2.get(k))
                wtally[kind] = wtally.get(kind, 0) + 1
                if kind in ("address-valued", "nondeterministic"):
                    # Recorded, not hidden: these differ for a reason the harness can
                    # point at (two address spaces / an unstable native result), so
                    # they are neither UB evidence nor a fair Lean comparison.
                    if len(excluded) < 40:
                        excluded.append(dict(function=f["name"], args=args,
                                             why=kind, **det))
                    continue
                if kind == "trap":
                    tk = "%s: %s" % (f["name"], det.get("kind"))
                    trap_detail[tk] = trap_detail.get(tk, 0) + 1
                if kind == "ub-suspected":
                    ws = f["name"] in width_fns
                    if ws:
                        # Fully defined on both targets, just computed at different
                        # widths. Retallied so the UB headline stays honest.
                        wtally["ub-suspected"] -= 1
                        wtally["width-sensitive"] = wtally.get("width-sensitive", 0) + 1
                    (width_findings if ws else ub_findings).append({
                        "function": f["name"], "args": args,
                        "native": det["native"], "wasm": det["wasm"],
                        "width_sensitive": ws,
                        "reading": wasm_backend.classify_ub(f["name"], args,
                                                            det["native"], det["wasm"]),
                        "reading_is_a_hint": True})
                    # NOT a conformance divergence. Core maps UB to `Expr.hole`
                    # (`NumResult.ub`), so where two conforming C implementations
                    # disagree the hole is the CORRECT answer -- scoring this against
                    # Lean would penalise the semantics for being right. The case is
                    # withheld from the Lean comparison and counted in its own
                    # category, which is why the measurement basis changes below.
                    continue
            if nat is None:
                continue
            cases.append({"name": f["name"], "heap": [], "self": None,
                          "args": [("int", a) for a in args],
                          "outcome": ("val", ("int", nat)), "origin": origins[k],
                          "objs": {}})
        if wasm_report is not None:
            wasm_report.update(calls_planned=len(plan), tally=wtally,
                               trap_detail=dict(sorted(trap_detail.items(),
                                                       key=lambda kv: -kv[1])[:30]),
                               ub_suspected=len(ub_findings),
                               ub_findings=ub_findings[:60],
                               width_sensitive=len(width_findings),
                               width_findings=width_findings[:40],
                               width_note=(
                                   "Native/wasm disagreements in functions that use a "
                                   "pointer-width type (`long`, `size_t`, ...). wasm32 "
                                   "makes those 32-bit and the native build 64-bit, so "
                                   "these differ WITHOUT undefined behaviour -- it is "
                                   "the NumConfig width axis `Core/Numeric.lean` "
                                   "models. Kept out of `ub_suspected` so that number "
                                   "means what it says."),
                               excluded_from_ub=excluded,
                               excluded_note=(
                                   "Native/wasm value differences the harness can "
                                   "attribute to something other than the program's "
                                   "semantics: a pointer return (two address spaces) "
                                   "or a native result that is not stable across two "
                                   "identical calls. Counted here rather than in "
                                   "`ub_suspected`, and withheld from the Lean "
                                   "comparison, because neither number answers the "
                                   "same question."))
            if wasm_report["status"] == "ran" and not wtally:
                wasm_report["status"] = ("SKIPPED: wasm built but zero calls were "
                                         "comparable — nothing was checked")
            print("  wasm: %s; %d calls, tally %s, %d ub-suspected"
                  % (wasm_report["status"], len(plan), json.dumps(wtally),
                     len(ub_findings)))
            C_WASM_REPORT.append(wasm_report)
    elif lang == "python":
        wanted, methods, modlevel = set(), [], []
        candidates = python_sampling_candidates(funcs)
        raw_bodies = undecorated_bodies(funcs)
        for f in candidates:
            if f.get("undecoratedOf"):
                # Reached only by traced frames of the raw function object; a random
                # or constructed call through the source name reaches the decorated
                # binding instead, which is a different function (§8.7).
                if classify({"name": f["undecoratedOf"]}):
                    wanted.add(f["name"])
                continue
            c = classify(f)
            if not c: continue
            rel, qual, is_meth = c
            wanted.add(f["name"])
            (methods if is_meth else modlevel).append((f, rel, qual))

        # (1) the repository's own test suite — the highest-value source of arguments
        rel_files = sorted(set(f.get("file", "") for f in funcs))
        test_dirs = [tests_override] if tests_override else find_tests(src_root)
        src_root = resolve_src_root(src_root, rel_files)
        identities = class_identity_index(funcs, src_root)
        from native_heap import function_identities
        callable_ids = function_identities(funcs, src_root)
        encoder_factory = lambda: GraphEncoder(identities, callable_ids)
        if identities is not None:
            BASIS = 'python-class-slots-v6+class-values-v1'
            BASIS_NOTE += (' Recovered class metadata selects exact source-file and class-path '
                           'identities for native object snapshots. Unresolved identities, '
                           'local-class captures, bound callable state and container subclass '
                           'state are refused and counted. This changes the sampled population '
                           'relative to python-deadlines-v4.')
            BASIS_NOTE += ' Class-valued outcomes compare exact qualified identities.'
            stats['class_identity_encoding'] = 'qualified-source-declarations'
        else:
            # A legacy AST carries no `classDeclarations`; plain instances are
            # identified by short class name, which is also what Core's legacy
            # semantics stores in `Obj.cls`, and inherited attributes are named gaps on
            # the Lean side rather than exceptions. Say so in the basis.
            BASIS_NOTE += (' No recovered class metadata: plain instances are identified '
                           'by short class name on both sides, and attribute reads that '
                           'would need the class hierarchy are inconclusive gaps.')
            stats['class_identity_encoding'] = 'legacy-short-class-names'
        index = build_lineno_index(src_root, rel_files)
        traced = []
        params_by_name = {f["name"]: f["params"] for f in candidates}
        live, pool = {}, {}
        if test_dirs and index:
            print("test suite: %s" % ", ".join(test_dirs))
            traced = trace_tests(src_root, test_dirs, index, wanted, ncases, stats,
                                 params_by_name, live, pool, encoder_factory, raw_bodies)
        elif not test_dirs:
            print("test suite: none discovered under %s (pass --tests DIR)" % src_root)
        else:
            print("test suite: %s found, but none of the AST's source files resolve "
                  "under %s — nothing to instrument" % (", ".join(test_dirs), src_root))
        for r in traced:
            r["origin"] = "test-suite"
            cases.append(r)
        print("cases recorded from the test suite: %d" % len(traced))
        # pytest: 0 passed, 1 some tests failed (still traced). 2 interrupted, 3 internal
        # error, 4 usage error, 5 nothing collected -- the suite never ran, so every method
        # it would have reached reads as "no instance reached". Say so by name.
        for run in stats.get("test_runs", []):
            if run.get("error") or run.get("rc") not in (0, 1):
                print("  TEST SUITE DID NOT RUN: %s (%s) -- a test directory is imported as a "
                      "package, so it must be named like one (e.g. .../tests)"
                      % (run["dir"], run.get("error") or "exit %s" % run.get("rc")))
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
                enc = encoder_factory()
                enc.freeze()
                try:
                    with time_limit(2.0):
                        got = fn(*args)
                    out = ("val", enc.enc_result(got))
                except Timeout as exc:
                    reason = ('skip_native_deadline_unavailable' if isinstance(exc, DeadlineUnavailable)
                              else 'skip_native_timeout')
                    stats[reason] = stats.get(reason, 0) + 1
                    stats.setdefault('native_deadline_detail', []).append(
                        {'function': f['name'], 'reason': str(exc), 'origin': 'random'})
                    break
                except Unencodable:
                    stats["skip_unencodable_ret"] += 1; continue
                except Exception as e:                      # noqa: BLE001
                    out = ("exn", type(e).__name__)
                try:
                    cases.append(finish_record(enc, {"name": f["name"], "self": None,
                                 "args": [("int", a) for a in args], "outcome": out,
                                 "origin": "random"}))
                except Unencodable as e:
                    stats['skip_unencodable_post'] = stats.get('skip_unencodable_post', 0) + 1
                    reasons = stats.setdefault('unencodable_reasons', {})
                    reason = f['name'] + ': post-state ' + str(e)
                    reasons[reason] = reasons.get(reason, 0) + 1

        # (3) methods the suite never called: reuse an instance it built for a
        # sibling method, or build one, and synthesize arguments from observed values
        # A file containing only classes was never imported by the free-function
        # loop above. Its methods still need their defining module loaded.
        for rel in sorted({rel for _, rel, _ in methods}):
            load_module(os.path.join(src_root, rel), src_root)
        reached = set(c["name"] for c in cases)
        built = constructed_cases(methods, reached, live, pool, stats, ncases, encoder_factory)
        cases += built
        print("cases constructed for methods the suite never called: %d (%d functions)"
              % (len(built), len(set(c["name"] for c in built))))
        reached = set(c["name"] for c in cases)
        stats["skip_no_instance"] = sum(1 for f, _, _ in methods
                                        if f["name"] not in reached)

    if len(cases) > MAX_TOTAL_CASES:
        random.shuffle(cases)
        cases = cases[:MAX_TOTAL_CASES]

    if lang == 'python':
        BASIS += '+trace-returns-v1'
        BASIS_NOTE += (' Traced outcomes distinguish an executed return instruction from '
                       'exception unwinding, including returns of None after handled exceptions. '
                       'Ambiguous unwind types and suspended generator/coroutine frames are '
                       'counted as trace gaps, not fabricated call outcomes.')

    if lang == 'python' and identities is None:
        BASIS_NOTE += (' No final heap graph is recorded for a legacy AST: outcomes are '
                       'compared by result only, as before graph observations existed.')
    if lang == 'python' and identities is not None:
        BASIS += '+heap-graph-v1'
        BASIS_NOTE += (' Heap graphs preserve mutable list/dict/object identity, cycles, '
                       'detached input objects and fresh reachable objects. Scalar tags and '
                       'float bits, object fields and ordered dictionary payloads are compared. '
                       'Globals outside those roots, immutable-value identity, instance-dictionary '
                       'insertion order and internal mutation versions are outside this claim.')

    result = {"module": module_tag, "source_root": os.path.abspath(src_root),
              "interpreter_fuel": FUEL, "initializer_fuel": FUEL,
              "ast": os.path.abspath(ast_path), "runtime": runtime,
              "runtime_version": runtime_version(lang),
              "measurement_basis": BASIS, "measurement_basis_note": BASIS_NOTE,
              "language": lang, "language_override": lang_override, "extensions": exts,
              "backend": runtime, "backend_status": backend_status,
              "backend_info": backend_info,
              "backend_skipped": dict(list(backend_skipped.items())[:40]),
              "backend_skipped_total": len(backend_skipped),
              # The wasm leg is a SEPARATE ORACLE, reported alongside the Lean
              # comparison rather than folded into it. `ub_suspected` counts programs
              # two conforming C compilers disagree about; those are evidence about the
              # program under test, not about our semantics.
              "wasm_c_oracle": (C_WASM_REPORT[0] if C_WASM_REPORT else
                                ({"status": "not requested (pass --wasm)"} if is_c
                                 else {"status": "n/a: not a C corpus"})),
              "dialect_expected": want_dialect,
              "dialect_is_exact": exact,
              "dialect_note": (None if exact else
                               "%s uses .cLike control flow with language-specific "
                               "typed numeric operations." % lang),
              # PROVENANCE. `functions_covered` is built from tracing the corpus's own
              # test suite, so it moves when the CHECKOUT moves -- and a coverage number
              # that silently tracks an unpinned `--depth 1` clone is the same trap as a
              # metric computed from the artifact it describes. Two runs of this harness
              # reported 107 and 82 covered functions with identical harness code, an
              # identical AST and an identical seed; the only free variable was the
              # checkout. Record it, so the next such gap is a diff and not an argument.
              "corpus_commit": _corpus_commit(src_root),
              "functions_total": len(funcs), "functions_hole_free": len(holefree),
              "functions_covered": len(set(c["name"] for c in cases)),
              "cases": len(cases), "agree": 0, "total": 0, "divergences": 0,
              "inconclusive": 0, "rate": "n/a", "by_origin": {},
              "skipped": {k: v for k, v in stats.items() if k.startswith("skip")},
              "native_deadline_detail": stats.get("native_deadline_detail", []),
              "native_call_deadline": ({"mode": "SIGALRM", "seconds": 2.0,
                                         "unsupported": "skip", "recursion_limit": sys.getrecursionlimit()}
                                        if lang == "python" else None),
              "skipped_note": "call-event counts, not function counts: a function whose "
                              "case quota is already full still logs skips for every "
                              "further call. Bound coverage with `coverage`, never with "
                              "these.",
              "test_runs": stats["test_runs"], "divergence_detail": [],
              "runtime_cases": [],
              "unencodable_reasons": stats.get("unencodable_reasons", {}),
              "no_instance_detail": stats.get("no_instance_detail", {}),
              "param_mismatch_detail": stats.get("param_mismatch_detail", {}),
              "coverage": {
                  # `covered_metric` names the field a coverage-bounded claim should
                  # read. `compared` is the strong one: functions with at least one
                  # case the oracle actually adjudicated. `exercised` merely means a
                  # case was built, which an inconclusive outcome does not vindicate.
                  "population": len(funcs),
                  "population_kind": "functions in %s" % os.path.basename(ast_path),
                  "hole_free": len(holefree),
                  "exercised": len(set(c["name"] for c in cases)),
                  "compared": 0,
                  "covered_metric": "compared",
                  "compared_fraction": 0.0,
                  "exercised_fraction": (len(set(c["name"] for c in cases))
                                         / len(funcs)) if funcs else 0.0,
                  "compared_fraction_of_hole_free": 0.0,
                  "compared_hole_free": 0, "compared_with_holes": 0,
                  "by_status": {}, "status_counts": {}}}

    if not cases:
        print("module %s (%s, %s): NO COMPARABLE CASES — %s"
              % (module_tag, lang, runtime, backend_status))
        print("functions: %d total, %d hole-free, 0 exercised, 0 COMPARED (0%%). This "
              "language has no positive runtime evidence." % (len(funcs), len(holefree)))
        result["status"] = "INCONCLUSIVE: no runtime comparisons"
        json.dump(result, open("conformance.json", "w"), indent=1)
        return 2

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
    b = subprocess.run(["lake", "build", "Autoform.Generated.%s" % lean_mod,
                            "Autoform.Lang.Core.Observation"],
                       capture_output=True, text=True, env=env, cwd=repo)
    if b.returncode != 0:
        result["status"] = "FAILED: Lean build"
        result["build_error"] = (b.stdout + b.stderr)[-4000:]
        json.dump(result, open("conformance.json", "w"), indent=1)
        print(result["status"], result["build_error"])
        return 2
    gen = os.path.join(repo, "Autoform", "Generated", lean_mod + ".lean")
    # `scripts/mutate.py` edits the generated module in place and keeps the pristine
    # copy beside it. If that backup exists, the module under test is currently a
    # MUTANT: its divergences are injected faults, not evidence about the semantics.
    mutating = any(os.path.exists(str(p) + ".mutate-backup")
                   for p in generated_module.model_files(gen))
    result["mutation_in_progress"] = mutating
    if mutating:
        print("WARNING: %s.mutate-backup exists — a mutation run owns this module right "
              "now, so it is a MUTANT. Any divergence below is an injected fault; this "
              "run is not conformance evidence." % os.path.basename(gen))
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
    # Isolate the run from the rest of the project: copy the compiled `Autoform`
    # artifacts to a private directory and resolve imports from there first. Other
    # agents build — and `scripts/mutate.py` deliberately *mutates* — the same generated
    # module while this runs, and evaluating against a moving target produced phantom
    # divergences that reproduced nowhere (`Cache.__contains__` inverted,
    # `_DefaultSize.pop` returning 0: both were live mutants).
    snap_dir = os.path.join(WORK, "lean-snapshot")
    blib_root = os.path.join(repo, ".lake/build/lib/lean")

    def snapshot_generated(blib, snap):
        """Copy the root module's compiled artifacts and every part it imports
        (`render_lean.py --shard-functions`); a part left out would be loaded from the
        live tree, which is exactly the moving target the snapshot exists to avoid."""
        import shutil
        for f in generated_module.build_files(repo, lean_mod):
            if f.exists():
                dest = os.path.join(snap, os.path.relpath(f, blib))
                os.makedirs(os.path.dirname(dest), exist_ok=True)
                shutil.copy(f, dest)
    lean_env = dict(env)
    try:
        import shutil
        shutil.rmtree(snap_dir, ignore_errors=True)
        os.makedirs(snap_dir, exist_ok=True)
        blib = os.path.join(repo, ".lake/build/lib/lean")
        shutil.copytree(os.path.join(blib, "Autoform/Lang"),
                        os.path.join(snap_dir, "Autoform/Lang"))
        os.makedirs(os.path.join(snap_dir, "Autoform/Generated"), exist_ok=True)
        snapshot_generated(blib, snap_dir)
        base = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"],
                              capture_output=True, text=True, env=env, cwd=repo)
        lean_env["LEAN_PATH"] = snap_dir + ":" + base.stdout.strip()
        isolated = True
    except (OSError, shutil.Error) as e:                    # noqa: BLE001
        print("could not isolate the build (%s); evaluating against the live tree" % e)
        isolated = False

    header = ["import Autoform.Generated.%s" % lean_mod,
              "import Autoform.Lang.Core.Observation",
              # Each corpus owns its namespace (`Autoform.Generated.Cachetools.program`,
              # ...) so that proofs about two codebases can share an import graph. Opening
              # the parent only was silently fatal here: `program` did not resolve, the
              # generated harness failed to compile, and EVERY case came back
              # `lean-no-answer` -- 534 of 534 on cachetools, reported as INCONCLUSIVE
              # rather than as a broken harness. Conformance is not in CI, so nothing
              # caught it.
              "open Autoform.Core Autoform.Generated Autoform.Generated.%s" % lean_mod, "",
              "private def gp : Heap × Ref := initGlobals program %d %s" % (FUEL, inits),
              "private def h0 : Heap := gp.1",
              "private def gref : Ref := gp.2",
              "private def base : Nat := h0.length",
              # `builtinBases` must be carried, or `Expr.alloc` cannot know that
              # `class _HashedTuple(tuple)` has a builtin base and produces a plain
              # `Val.ref` instead of a `Val.bobj`. The oracle then reports
              # `representation:value-vs-object` and counts the case INCONCLUSIVE -- the
              # harness refusing to look at a value Core was fixed to produce correctly,
              # because the harness dropped the field on the way in.
              "private def dctx : Ctx := "
              "{ dialect := program.dialect, table := program.table, globals := gref, "
              "builtinBases := program.builtinBases, properties := program.properties, "
              "excClasses := program.excClasses, classDecls := program.classDecls }",
              "",
              "private structure DCase where",
              "  idx  : Nat",
              "  objs : List Obj",
              "  fn   : String",
              "  slf  : Option Val",
              "  args : List Val",
              "  chk  : List (Nat × String)",
              "  expected : EResult",
              "  post : Option HeapObservation", "",
              # A boxed function object (Core section 47) is REPORTED AS THE FUNCTION IT
              # CARRIES. `wrapper.cache_clear = f` makes `wrapper` a heap object, and Core
              # returns a `Val.ref` to it where CPython returns the function -- a shape
              # clash, not a disagreement. This is the same move `unwrap_bobj` makes on the
              # Python side, and it hides the same thing: object identity and the attributes
              # written to it. Neither side's test compares those here; if one ever does,
              # this has to compare them rather than unbox.
              "private def unboxRes (h : Heap) (r : EResult) : EResult :=",
              "  match r with",
              "  | .val (.ref a) => match unboxFn h a with",
              "                     | some fv => .val fv",
              "                     | none    => r",
              "  | _ => r", "",
              "private def drun (c : DCase) : Heap × EResult :=",
              "  let h := h0 ++ c.objs",
              "  -- the globals frame must survive, and each receiver must land where",
              "  -- the harness said it would",
              "  if (h.get gref).map (·.cls) != some \"<globals>\" then",
              "    (h, .hole \"harness:globals-frame-clobbered\")",
              "  else if c.chk.any (fun p => (h.get (base + p.1)).map (·.cls) "
              "!= some p.2) then",
              "    (h, .hole \"harness:receiver-alias\")",
              "  else",
              "    match dctx.resolve c.fn with",
              '    | none    => (h, .hole s!"entry:{c.fn}")',
              # `applyFunc` gained a `kws` parameter when Python's calling convention was
              # modelled. This call site kept five arguments, so `drun` failed to elaborate
              # -- but the `@@meta@@` line above it only mentions `base`/`gref` and still
              # printed, so the harness saw a live Lean process and reported every case as
              # `lean-no-answer`. An arity change silently disabled the only oracle that
              # compares the semantics to a real runtime.
              "    | some fn => let r := applyFunc dctx %d h fn c.slf c.args []" % FUEL,
              "                 (r.1, if c.post.isSome then r.2 else unboxRes r.1 r.2)", ""]
    footer = ["]", "",
              '#eval IO.println ("@@meta@@" ++ toString base ++ " " ++ toString gref)',
              '#eval cases.forM (fun c => do let r := drun c; '
              'IO.println ("@@" ++ toString c.idx ++ "@@" '
              '++ (repr r.2).pretty (width := 1000000)); '
              'match c.post with | none => pure () | some graph => '
              'IO.println ("@@heap@@" ++ toString c.idx ++ "@@" ++ '
              '(repr (graph.compare r.1 c.expected r.2)).pretty (width := 1000000)))']

    def case_lit(i, c):
        slf = "none" if c["self"] is None else "(some (%s))" % lean_val(c["self"])
        chk = ", ".join('(%d, %s)' % (k, json.dumps(cls))
                        for k, cell in enumerate(c["heap"]) for cls in [cell[0]])
        return ("  { idx := %d, objs := %s, fn := %s, slf := %s, args := [%s], "
                "chk := [%s], expected := %s, post := %s }"
                % (i, lean_heap(c["heap"]), json.dumps(c["name"]), slf,
                   ", ".join(lean_val(a) for a in c["args"]), chk,
                   outcome_lit(c['outcome']), graph_lit(c)))

    graph_answers = {}
    meta = {"base": 0, "gref": 0}
    # per-process scratch file: two harness runs (or two agents) sharing /tmp would
    # otherwise clobber each other's generated file mid-bisection
    scratch = os.path.join(WORK, "harness.lean")

    def lean_eval(idxs, depth=0, retried=False):
        """idxs -> {idx: repr line}. Missing keys are cases Lean could not answer."""
        if not idxs: return {}
        src = header + ["private def cases : List DCase := ["] \
            + [",\n".join(case_lit(i, cases[i]) for i in idxs)] + footer
        open(scratch, "w").write("\n".join(src) + "\n")
        if isolated:
            out = subprocess.run([os.path.expanduser("~/.elan/bin/lean"), scratch],
                                 capture_output=True, text=True, env=lean_env, cwd=repo)
        else:
            out = subprocess.run(["lake", "env", "lean", scratch],
                                 capture_output=True, text=True, env=env, cwd=repo)
        got = {}
        saw_meta = False
        for l in out.stdout.splitlines():
            m = re.match(r'@@meta@@(\d+) (\d+)', l)
            if m:
                meta["base"], meta["gref"] = int(m.group(1)), int(m.group(2))
                saw_meta = True
                continue
            gm = re.match(r'@@heap@@(\d+)@@(.*)', l)
            if gm and int(gm.group(1)) in idxs:
                graph_answers[int(gm.group(1))] = gm.group(2).strip('() ')
            m = re.match(r'@@(\d+)@@(.*)', l)
            if m and int(m.group(1)) in idxs: got[int(m.group(1))] = m.group(2)
        if not saw_meta:
            # PRINT THE REASON. Without this the whole oracle fails as "534 INCONCLUSIVE
            # (lean-no-answer)", which is indistinguishable from "the semantics could not
            # decide" -- an oracle that cannot run looks exactly like an oracle that ran
            # and abstained. That is how a namespace change disabled conformance entirely
            # while every other gate stayed green.
            first = (out.stderr or out.stdout or "").strip().splitlines()
            if first:
                print("  lean did not reach the first case (rc=%s): %s"
                      % (out.returncode, first[0][:200]))
        if not saw_meta and not retried:
            # No `@@meta@@` line: the file never reached the first case, so this is a
            # compile or environment failure, not a bad case. That happens for real —
            # another process rebuilding `Semantics.olean` removes it mid-run — so
            # rebuild and try once more before giving up on the whole chunk.
            subprocess.run(["lake", "build", "Autoform.Generated.%s" % lean_mod,
                            "Autoform.Lang.Core.Observation"],
                           capture_output=True, text=True, env=env, cwd=repo)
            if isolated:
                import shutil
                blib = os.path.join(repo, ".lake/build/lib/lean")
                shutil.rmtree(os.path.join(snap_dir, "Autoform"), ignore_errors=True)
                shutil.copytree(os.path.join(blib, "Autoform/Lang"),
                                os.path.join(snap_dir, "Autoform/Lang"))
                os.makedirs(os.path.join(snap_dir, "Autoform/Generated"),
                            exist_ok=True)
                snapshot_generated(blib, snap_dir)
            return lean_eval(idxs, depth, retried=True)
        if not saw_meta:
            # Bisecting an environment failure costs one lake invocation per case and
            # answers nothing.
            if depth == 0 or not meta.get("env_reported"):
                meta["env_reported"] = True
                print("lean environment failure, not bisecting:",
                      (out.stdout[:200] + " " + out.stderr[:300]).replace("\n", " ")[:300])
            return got
        if len(got) < len(idxs) and len(idxs) == 1 and os.environ.get(
                "AUTOFORM_DIFF_KEEP"):
            # debugging aid: keep the exact file the interpreter choked on
            import shutil
            keep = os.environ["AUTOFORM_DIFF_KEEP"]
            os.makedirs(keep, exist_ok=True)
            shutil.copy(scratch, os.path.join(keep, "fail_%d.lean" % idxs[0]))
        if len(got) < len(idxs) and len(idxs) > 1:
            mid = len(idxs) // 2
            got.update(lean_eval(idxs[:mid], depth + 1))
            got.update(lean_eval(idxs[mid:], depth + 1))
        elif len(got) < len(idxs) and depth == 0:
            print("lean could not evaluate any case:",
                  (out.stdout[:200] + out.stderr[:400]).replace("\n", " ")[:400])
        return got

    def olean_fingerprint():
        """Identify the compiled artifacts the answers actually came from.

        STRATEGY.md §19: a stale `.olean` answers with the *previous* semantics. That
        can also happen *during* a run — another process rebuilding `Semantics` while
        the chunks are being evaluated — and it produced a phantom divergence
        (`_DefaultSize.pop` returning 0 instead of 1) that reproduced nowhere
        afterwards. So fingerprint the artifacts and re-run if they moved."""
        import hashlib
        h = hashlib.sha256()
        root = snap_dir if isolated else os.path.join(repo, ".lake/build/lib/lean")
        compiled = [os.path.join(root, os.path.relpath(p, blib_root))
                    for p in generated_module.build_files(repo, lean_mod, (".olean",))]
        for p in [os.path.join(root, "Autoform/Lang/Core/Semantics.olean"),
                  os.path.join(root, "Autoform/Lang/Core/Observation.olean")] + compiled:
            try:
                h.update(open(p, "rb").read())
            except OSError:
                h.update(b"<missing>")
        return h.hexdigest()

    CHUNK = 20
    order = list(range(len(cases)))
    got, stable = {}, False
    for attempt in range(3):
        before = olean_fingerprint()
        got = {}
        graph_answers.clear()
        for i in range(0, len(order), CHUNK):
            got.update(lean_eval(order[i:i + CHUNK]))
        if olean_fingerprint() == before:
            stable = True; break
        print("WARNING: the compiled Lean artifacts changed while the cases were being "
              "evaluated (a concurrent build). Discarding and re-running.")
    result["build_stable"] = stable and not mutating
    result["provenance"] = {
        "ast_sha256": ast_fingerprint,
        "generated_sha256": generated_module.model_digest(generated),
        "source_sha256": fingerprints, "semantics_sha256": semantics_fingerprint}
    result["build_stable"] = result["build_stable"] and (
        runtime_backends.sha256(ast_path) == ast_fingerprint and
        runtime_backends.source_fingerprints(src_root, funcs) == fingerprints and
        runtime_backends.semantics_fingerprints() == semantics_fingerprint)
    if not stable or mutating:
        print("WARNING: results below were produced against a moving or mutated build "
              "and must not be treated as conformance evidence (build_stable=false).")
    if len(got) < len(cases):
        print("lean answered %d/%d cases; the rest are INCONCLUSIVE"
              % (len(got), len(cases)))

    agree = diverge = incon = 0
    compared_fns = set()          # functions the oracle actually adjudicated
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
        undecidable = None
        if py[0] == "val" and lr[0] == "val":
            # A value/object shape disagreement is not adjudicable: the transpiler
            # allocates a heap object for any constructed class (including subclasses
            # of tuple/dict), while the runtime hands us a container. The harness
            # cannot tell its own representation choice from a real disagreement, so
            # it declines to call it either way.
            if shape_clash(py[1], lr[1]):
                undecidable = "representation:value-vs-object"
            else:
                native_value, lean_value = py[1], lr[1]
                if lang in ("js", "ts") and native_value[0] in ("int", "float") and lean_value[0] in ("int", "float"):
                    # Core uses ints as an exact representation for small JS Numbers.
                    native_value = Encoder().enc(float(native_value[1])) if native_value[0] == "int" else native_value
                    lean_value = Encoder().enc(float(lean_value[1])) if lean_value[0] == "int" else lean_value
                ok = same(native_value, lean_value, meta["base"])
            desc = "%s=%s lean=%s" % (runtime, show(py[1]), show(lr[1]))
        elif py[0] == "exn" and lr[0] == "exn":
            lname = lr[1][1] if lr[1][0] == "str" else show(lr[1])
            ok = (lname == py[1])
            if not ok and lr[1][0] != "str":
                # Core raised at the same point but carries no name for the class
                # (`raise NotImplementedError` evaluates a builtin it has no model of).
                # Control flow agrees; the payload is unmodelled, not wrong.
                undecidable = "exception-payload-unmodelled"
            desc = "%s raised %s, lean raised %s" % (runtime, py[1], lname)
        elif py[0] == "exn":
            desc = "%s raised %s, lean returned %s" % (runtime, py[1], show(lr[1]))
        else:
            lname = lr[1][1] if lr[1][0] == "str" else show(lr[1])
            desc = "%s=%s, lean raised %s" % (runtime, show(py[1]), lname)
        if 'post_heap' in c:
            answer = graph_answers.get(i)
            desc += '; heap graph=' + str(answer)
            if undecidable is None:
                # The graph verdict refines an adjudicable result comparison. A case
                # the result comparison already declined to call (a value-vs-object
                # representation clash, an unmodelled exception payload) stays
                # inconclusive: `HeapObservation.compare` answers `some false` for a
                # `.ref` against a container cell too, and that is the same
                # representation choice, not a second disagreement.
                ok = answer == 'some true'
                undecidable = ('heap-comparison-budget-or-no-answer'
                               if answer not in ('some true', 'some false') else None)
            else:
                ok = False
        if undecidable is not None:
            incon += 1; bucket["incon"] += 1
            k = "%s: %s" % (c["name"], undecidable)
            incon_detail[k] = incon_detail.get(k, 0) + 1
            continue
        compared_fns.add(c["name"])
        if ok:
            agree += 1; bucket["agree"] += 1
            observation = {k: c[k] for k in ("name", "heap", "self", "args", "outcome")}
            if 'post_heap' in c:
                observation['post_heap'] = c['post_heap']
            observation.update(origin=origin, runtime=runtime, comparison="agree")
            result["runtime_cases"].append(observation)
        else:
            diverge += 1; bucket["diverge"] += 1
            msg = "  DIVERGENCE %s%s: %s [%s]" % (c["name"], argstr, desc, origin)
            print(msg[:300])
            result["divergence_detail"].append(
                {"function": c["name"], "args": argstr[:200], "detail": desc[:200],
                 "origin": origin,
                 # the exact inputs, so a divergence is a reproducible artifact rather
                 # than a line of prose
                 "case": {"self": c["self"], "args": c["args"],
                          "heap": json.loads(json.dumps(c["heap"]))[:6]},
                 # The compact legacy case above is a display preview. Preserve
                 # the complete graph and native expectation for exact replay.
                 "observation": json.loads(json.dumps(c)),
                 "lean_repr": line[:400]})

    total = agree + diverge
    rate = "%d%%" % (100 * agree // total) if total else "n/a"
    # ---- coverage, as a first-class output: which functions the oracle actually
    # adjudicated, which it merely touched, and why the rest were out of reach.
    status = {}
    for f in funcs:
        status[f["name"]] = ("not-translated-fully (holes): no native case built"
                             if has_hole(f["body"]) else "hole-free, no case built")
    for c in cases:
        status[c["name"]] = "cases built, all inconclusive"
    for n in compared_fns:
        status[n] = "compared"
    for n, why in stats.get("no_instance_detail", {}).items():
        for f in funcs:
            if f["name"].endswith("." + n) and status.get(f["name"], "").startswith(
                    "hole-free"):
                status[f["name"]] = "hole-free, no case built: " + why
    # why each un-compared function is un-compared, split into the two categories that
    # matter for a coverage-bounded claim: gaps the project intends to close, and gaps
    # in the oracle's own value model that no amount of semantics work removes.
    VALUE_MODEL = ("float", "set", "opaque", "complex", "bytes", "frozenset",
                   "container-subclass", "object-as-dict-key", "wide",
                   "self-not-object", "representation")
    labels = {}
    for k, v in incon_detail.items():
        fn, lab = k.split(": ", 1)
        labels.setdefault(fn, set()).add(lab.split(":")[0])
    for f in funcs:
        n = f["name"]
        if n in compared_fns or has_hole(f["body"]): continue
        labs = labels.get(n, set())
        if labs and labs <= {"representation", "exception-payload-unmodelled"}:
            status[n] = "blocked (value model): " + ", ".join(sorted(labs))
        elif labs:
            status[n] = "blocked (semantics/transpiler): runtime holes " + \
                        ", ".join(sorted(labs))
        else:
            why = status.get(n, "")
            hit = [w for w in VALUE_MODEL if w in why]
            status[n] = ("blocked (value model): " + hit[0] if hit
                         else "blocked (unexercised): " + why.split(": ", 1)[-1])
    counts = {}
    for v in status.values():
        k = v.split(":")[0]
        counts[k] = counts.get(k, 0) + 1
    cov = result["coverage"]
    cov["compared"] = len(compared_fns)
    cov["compared_fraction"] = len(compared_fns) / len(funcs) if funcs else 0.0
    cov.update(compared_hole_coverage(holefree, compared_fns))
    cov["by_status"] = status
    cov["status_counts"] = counts
    perm = sum(v for k, v in counts.items() if k.startswith("blocked (value model)"))
    cov["ceiling"] = {
        "compared_now": len(compared_fns),
        "blocked_by_value_model": perm,
        "reachable_in_principle": len(funcs) - perm,
        "reachable_fraction": (len(funcs) - perm) / len(funcs) if funcs else 0.0,
        "note": "Blocked-by-value-model functions need a Core value the interpreter "
                "does not have (floats, sets, opaque C objects) — no transpiler work "
                "reaches them. Everything else is blocked by holes, either in the AST "
                "or hit at runtime, and becomes reachable as those close."}
    result["inconclusive_detail"] = incon_detail
    result.update(agree=agree, total=total, divergences=diverge, inconclusive=incon,
                  rate=rate, by_origin=per_origin)
    print("\nmodule %s (%s, %s)" % (module_tag, os.path.abspath(src_root), runtime))
    print("measurement basis: %s" % BASIS)
    print("functions: %d total, %d hole-free, %d exercised, %d COMPARED (%.0f%% of "
          "all, %.0f%% of hole-free)"
          % (len(funcs), len(holefree), result["functions_covered"],
             len(compared_fns), 100 * result["coverage"]["compared_fraction"],
             100 * result["coverage"]["compared_fraction_of_hole_free"]))
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
    if isolated:
        import shutil
        shutil.rmtree(snap_dir, ignore_errors=True)
    return 1 if diverge else (2 if not total or not result["build_stable"] else 0)


if __name__ == "__main__":
    # The oracle is headless. A corpus function that reads the terminal (`click.prompt`,
    # `getpass`) must see EOF, not this process's stdin: a prompt that blocks would hang
    # every run and one that echoes fills the log with password warnings.
    try:
        sys.stdin = open(os.devnull)
    except OSError:
        pass
    # AST decoding and traversal use explicit stacks. Keep native execution on the
    # main thread so signal deadlines work and source recursion retains Python's
    # normal limit, instead of changing it process-wide to 300,000.
    sys.exit(main())
