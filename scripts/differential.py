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
                       [--no-cache] [--cache-dir DIR]

Incremental by default (`oracle_cache.py`): a function whose translation, reachable
callees, module bodies, environment and recorded cases are all unchanged since the last
run is reported from `.autoform-work/oracle/<Module>/` and SAID to be, with the time the
verdict was computed; the summary counts it apart from the comparisons made now.
`--no-cache` ignores the stored verdicts and re-compares everything.
"""
import os, sys
import json, subprocess, random, importlib.util, re, glob, io
import contextlib, inspect, functools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wasm_backend
import generated_module
import runtime_backends
import external_bases
import oracle_cache
import deep_json
import sandbox
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
# The sandboxed re-execution (see `sandbox_reexec`) hands this process a private box that
# holds its TMPDIR; the box is ours to remove.
if os.environ.get("AUTOFORM_SANDBOX_BOX"):
    _atexit.register(lambda: __import__("shutil").rmtree(os.environ["AUTOFORM_SANDBOX_BOX"],
                                                         ignore_errors=True))

# Test-suite-derived cases must be reproducible too. Set-iteration and dict-key hashing
# feed which calls the suite makes and in which order, so an unseeded interpreter gives
# a different sample of cases (and a different set of divergences) on every run.
#
# The interpreter. The Python leg runs the corpus's suite IN THIS PROCESS (`trace_tests`),
# so the interpreter that runs this script is the runtime the model is compared with, and
# it must be one that can import the project. `AUTOFORM_ORACLE_PYTHON` names it (`autoform
# pr/source --python`); this script is stdlib-only plus its own siblings, so it re-executes
# itself under that interpreter. Measured on a 103-file package whose dependencies were
# not installed in the tool's interpreter: every module that imported them failed, the
# suite never ran, and all five seeded regressions read "not compared". The interpreter
# actually used is recorded in conformance.json (`oracle_interpreter`).
ORACLE_PYTHON_ENV = "AUTOFORM_ORACLE_PYTHON"


def oracle_interpreter_target(environ=None, executable=None):
    """The interpreter this script must re-execute under, or None to stay put."""
    environ = os.environ if environ is None else environ
    executable = sys.executable if executable is None else executable
    wanted = environ.get(ORACLE_PYTHON_ENV)
    if not wanted:
        return None
    wanted = os.path.abspath(os.path.expanduser(wanted))
    # Not `realpath`: a virtualenv's `bin/python` is a symlink to the base interpreter,
    # and resolving it would declare the base interpreter (without the project's
    # packages) to be the one asked for.
    if os.path.abspath(executable) == wanted or environ.get("AUTOFORM_ORACLE_PYTHON_EXEC") == wanted:
        return None
    return wanted


if __name__ == "__main__":
    _target = oracle_interpreter_target()
    if _target is not None:
        if not (os.path.isfile(_target) and os.access(_target, os.X_OK)):
            print("REFUSING to run: %s=%s is not an executable interpreter"
                  % (ORACLE_PYTHON_ENV, _target))
            json.dump({"status": "REFUSED: oracle interpreter unavailable",
                       "oracle_interpreter": {"requested": _target, "setting": ORACLE_PYTHON_ENV},
                       "argv": sys.argv[1:], "agree": 0, "total": 0, "divergences": 0,
                       "inconclusive": 0, "rate": "n/a"},
                      open("conformance.json", "w"), indent=1)
            sys.exit(2)
        os.execve(_target, [_target, os.path.abspath(__file__)] + sys.argv[1:],
                  dict(os.environ, PYTHONHASHSEED="0", AUTOFORM_ORACLE_PYTHON_EXEC=_target))

if os.environ.get("PYTHONHASHSEED") != "0" and not os.environ.get("AUTOFORM_NO_REEXEC"):
    os.execve(sys.executable, [sys.executable] + sys.argv,
              dict(os.environ, PYTHONHASHSEED="0"))


def oracle_interpreter_record():
    """What ran the native side of this oracle, for conformance.json."""
    requested = os.environ.get(ORACLE_PYTHON_ENV)
    return {"path": sys.executable, "version": sys.version.split()[0],
            "implementation": sys.implementation.name,
            "prefix": sys.prefix,
            "setting": (ORACLE_PYTHON_ENV if requested else
                        "default: the interpreter that ran differential.py"),
            "requested": os.path.abspath(os.path.expanduser(requested)) if requested else None}

FUEL = 5000
# Keep the generated Lean file compile-bounded. `AUTOFORM_CASE_CAP` overrides it for a run
# that wants every built case compared: the CommonsLang3 mutation gate found 59 of 125
# conformance theorems vacuous on domains the 600 cap had thinned to one or two cases.
# The value in force is recorded in conformance.json (`case_cap.limit`), next to the raw
# setting it was parsed from (`case_cap.requested`, None when the default applied).


def positive_int_from_env(name, raw, default):
    """`raw` (the value of environment variable `name`) as a positive int, or `default`
    when it is unset or blank. Anything else is REFUSED with a clear message rather than
    parsed: `int("")` raised at import time (taking synth_specs.py and every test that
    imports this module down with it), `0` silently dropped every case, and a negative
    value trimmed the tail of the list. A cap that is not a positive integer has no
    meaning this oracle can act on."""
    if raw is None or not raw.strip():
        return default
    try:
        value = int(raw.strip())
    except ValueError:
        raise SystemExit("REFUSING to run: %s=%r is not an integer (unset it for the "
                         "default %d)" % (name, raw, default))
    if value < 1:
        raise SystemExit("REFUSING to run: %s=%r must be a positive integer (unset it for "
                         "the default %d)" % (name, raw, default))
    return value


CASE_CAP_SETTING = os.environ.get("AUTOFORM_CASE_CAP")
MAX_TOTAL_CASES = positive_int_from_env("AUTOFORM_CASE_CAP", CASE_CAP_SETTING, 600)
# Wall-clock bound on one `lean` chunk evaluation (seconds). A chunk that runs past it is
# reported INCONCLUSIVE with that reason, never bisected (bisecting a 20-case chunk that
# hangs would cost up to 20 further timeouts and answer nothing).
LEAN_CHUNK_TIMEOUT = positive_int_from_env("AUTOFORM_LEAN_CHUNK_TIMEOUT",
                                           os.environ.get("AUTOFORM_LEAN_CHUNK_TIMEOUT"), 1800)
MAX_DEPTH = 8              # value-encoding depth limit
MAX_ELEMS = 512            # value-encoding breadth limit (a resource
                           # bound, not a fidelity one: containers are
                           # encoded whole or refused, never truncated)
LITERAL_INPUTS = False     # `--literal-inputs`
EXTRA_LITERALS = {}        # `--literals FILE`: function name -> extra strings
# id(case record) -> (lines, arcs) its own frame executed (`--changed-lines`, Python).
CASE_COVERAGE = {}
COVERAGE_KEYS = set()      # the functions whose cases are traced for it


# ------------------------------------------------------------ change coverage

class ArcRecorder:
    """The lines and line-to-line arcs the frames of one code object execute while the
    `with` block runs (`--changed-lines`). An arc ends at 0 on a normal return; an
    exception breaks the chain, so a test that raises is neither branch outcome."""

    def __init__(self, code):
        self.code, self.lines, self.arcs = code, set(), set()

    def __enter__(self):
        self.old = sys.gettrace()
        sys.settrace(self._call)
        return self

    def __exit__(self, *exc):
        sys.settrace(self.old)
        return False

    def _call(self, frame, event, arg):
        if event != "call" or frame.f_code is not self.code:
            return None
        prev = [None]

        def local(frame, event, arg):
            arc_event(prev, frame, event, self.lines, self.arcs)
            return local
        return local


def arc_event(prev, frame, event, lines, arcs):
    """One trace event of a recorded frame into `lines`/`arcs` (`prev` holds the last line)."""
    if event == "line":
        line = frame.f_lineno
        lines.add(line)
        if prev[0] is not None:
            arcs.add((prev[0], line))
        prev[0] = line
    elif event == "exception":
        prev[0] = None
    elif event == "return":
        if prev[0] is not None:
            arcs.add((prev[0], 0))
        prev[0] = None


def _function_node(tree, qual):
    """The `def` named by a dotted qualified name (`C.f`, `outer.inner`) in a module AST."""
    import ast as pyast
    found = None

    def visit(node, scope):
        nonlocal found
        for child in pyast.iter_child_nodes(node):
            if isinstance(child, (pyast.FunctionDef, pyast.AsyncFunctionDef, pyast.ClassDef)):
                name = ".".join(scope + [child.name])
                if name == qual and not isinstance(child, pyast.ClassDef):
                    found = child
                visit(child, scope + [child.name])
            else:
                visit(child, scope)
    visit(tree, [])
    return found


def change_obligations(source, qual, changed):
    """What the compared inputs must execute for a change to `qual` to count as reached:
    every changed line that starts a statement of its own body, and both outcomes of
    every `if`/`while`/`elif` whose test is on a changed line. Returns `(lines,
    branches)`, `branches` as `(test lines, first body line)`, or None when the function
    is not found. A boolean operator inside a test is covered at the outcome level only."""
    import ast as pyast
    try:
        tree = pyast.parse(source)
    except (SyntaxError, ValueError):
        return None
    node = _function_node(tree, qual)
    if node is None:
        return None
    lines, branches = set(), []
    stack = list(node.body)
    while stack:
        stmt = stack.pop()
        if isinstance(stmt, (pyast.FunctionDef, pyast.AsyncFunctionDef, pyast.ClassDef)):
            continue      # its own code object: not this frame's lines
        if isinstance(stmt, pyast.stmt) and stmt.lineno in changed:
            lines.add(stmt.lineno)
        if isinstance(stmt, (pyast.If, pyast.While)):
            test = set(range(stmt.test.lineno, (stmt.test.end_lineno or stmt.test.lineno) + 1))
            test.add(stmt.lineno)
            if test & changed:
                branches.append((sorted(test), stmt.body[0].lineno))
        for child in pyast.iter_child_nodes(stmt):
            if isinstance(child, pyast.stmt):
                stack.append(child)
            elif isinstance(child, (pyast.excepthandler, getattr(pyast, "match_case", ()))):
                stack.extend(child.body)
    return sorted(lines), branches


def change_coverage(f, src_root, changed, observed):
    """`change_coverage` for one function: which obligations (`change_obligations`) the
    compared cases' `(lines, arcs)` (`observed`) met. `covered` is True when all were
    met, False when one was not, None when nothing could be measured."""
    rel = f.get("file") or ""
    qual = f["name"].split(":<module>.", 1)[-1]
    record = {"changed_lines": sorted(changed)}
    try:
        with open(os.path.join(src_root, rel), encoding="utf-8") as handle:
            source = handle.read()
    except OSError as exc:
        return dict(record, covered=None, note="source unreadable: %s" % exc)
    found = change_obligations(source, qual, changed)
    if found is None:
        return dict(record, covered=None, note="the function was not found in the source")
    lines, branches = found
    if not observed:
        return dict(record, covered=None, note="no compared case was traced")
    ran = set().union(*(l for l, _ in observed))
    arcs = set().union(*(a for _, a in observed))
    missed = [l for l in lines if l not in ran]
    outcomes = []
    for test, body in branches:
        if body in test:
            outcomes.append({"line": test[0], "measurable": False})
            continue
        taken = any(a in test and b == body for a, b in arcs)
        not_taken = any(a in test and b not in test and b != body for a, b in arcs)
        outcomes.append({"line": test[0], "taken": taken, "not_taken": not_taken})
    gaps = [o for o in outcomes if o.get("measurable", True) and not (o["taken"] and o["not_taken"])]
    if not lines and not outcomes:
        return dict(record, covered=None, note="no statement of its body is on a changed line")
    notes = ["changed line %d never executed" % l for l in missed]
    notes += ["the condition at line %d never evaluated %s" % (
        o["line"], "true" if not o["taken"] else "false") if o["taken"] != o["not_taken"]
        else "the condition at line %d never completed" % o["line"] for o in gaps]
    return dict(record, statement_lines=lines, unexecuted_lines=missed, branches=outcomes,
                covered=not missed and not gaps,
                note="; ".join(notes) if notes else "every changed statement and branch outcome was executed")


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


def focus_population(funcs, focus, same_named=False):
    """The functions a runtime backend builds cases for under `--focus`.

    Every backend compiles and drives each candidate it is given, so building cases for
    the whole population and only then keeping the focused ones (what `--focus` used to
    do) costs the whole corpus: on a 7,349-function Java service the per-file `javac`
    loop alone outlasted a 1800 s stage timeout. The cut is made BEFORE candidate
    selection instead. A focused function loses nothing it needs: a JVM receiver is
    built by its class's own constructor inside the JVM (not by a translated `<init>`),
    and a Python constructed case builds its instance natively. The one cross-function
    decision a backend makes is C's entry-point ambiguity check (two definitions of one
    source name in one file are refused), so with `same_named` every function sharing a
    focused function's file and source name is kept and that refusal is still made.
    Without `--focus` the population is unchanged."""
    if focus is None:
        return funcs
    keys = {(f.get("file"), f.get("sourceName", f["name"])) for f in funcs
            if same_named and f["name"] in focus}
    return [f for f in funcs if f["name"] in focus
            or (f.get("file"), f.get("sourceName", f["name"])) in keys]


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


def show_arg(v, lang):
    """An argument as the report shows it. A JVM reference argument the driver passed as
    null is Core's `unit`; it is shown as `null`, the input the runtime was given."""
    if lang in ("java", "kotlin") and v and v[0] == "unit":
        return "null"
    return show(v)


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
        cov = st.get("cov")
        if cov is not None:
            arc_event(cov[2], frame, event, cov[0], cov[1])
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
                    if cov is not None:
                        CASE_COVERAGE[id(records[-1])] = (cov[0], cov[1])
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
        # A nested function that reads its enclosing scope (`co_freevars`, the closure's
        # cells) cannot be called faithfully from a traced snapshot: the case carries the
        # arguments but not the captured values, and Core would read each free name as an
        # unbound global. Found on Jinja2: `select_autoescape.autoescape(None)` returns its
        # captured `default_for_string` ('STRING') in CPython and `unit` in the model.
        # Refused and counted. `__class__` (the cell zero-argument `super()` reads) is not
        # a capture the body evaluates as a name, so it does not refuse a method.
        free = [v for v in code.co_freevars if v != "__class__"]
        if free:
            stats['skip_closure_captures'] = stats.get('skip_closure_captures', 0) + 1
            detail = stats.setdefault('closure_capture_detail', {})
            detail[key] = sorted(free)
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
        if key in COVERAGE_KEYS:
            state_by_frame[id(frame)]["cov"] = (set(), set(), [None])
        return local2

    old_path = list(sys.path)
    old_trace = sys.gettrace()
    sys.path.insert(0, os.path.abspath(src_root))
    for d in test_dirs:
        sys.path.insert(0, os.path.dirname(os.path.abspath(d)))
    ran = []
    try:
        sys.settrace(tracer2)
        for d in test_dirs:
            ran.append(run_test_dir(d))
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
    state -- it is loading code the corpus ships and the AST was exported from.

    A module that does not import is recorded in `IMPORT_ERRORS` with its exception.
    It used to be reported as "not imported by the suite", which on a package whose
    dependencies were missing from the oracle interpreter named the wrong cause for every
    method in it. Under a `src/` layout the AST path (`src/pkg/m.py`) is not the import
    name (`pkg.m`): the module the suite imported for that FILE is found first, then the
    path's dotted suffixes are tried, each accepted only if it loads that same file."""
    mod = rel[:-3].replace("/", ".").replace("\\", ".")
    if mod.endswith(".__init__"): mod = mod[:-9]
    m = sys.modules.get(mod)
    if m is not None:
        return m
    want = os.path.normpath(rel)

    def same_file(module):
        f = getattr(module, "__file__", None) or ""
        return os.path.normpath(f).endswith(os.sep + want) or os.path.normpath(f) == want
    for loaded in list(sys.modules.values()):
        if loaded is not None and same_file(loaded):
            return loaded
    import importlib
    parts = mod.split(".")
    tried = []
    for i in range(len(parts)):
        name = ".".join(parts[i:])
        tried.append(name)
        try:
            got = importlib.import_module(name)
        except ModuleNotFoundError as e:
            # Not found under this name: try a shorter one. Any OTHER missing module is
            # the file's own import failing (a dependency), which is the answer.
            if e.name and (name == e.name or name.startswith(e.name + ".")):
                continue
            IMPORT_ERRORS[rel] = "%s: %s: %s" % (name, type(e).__name__, str(e)[:300])
            return None
        except Exception as e:                              # noqa: BLE001
            IMPORT_ERRORS[rel] = "%s: %s: %s" % (name, type(e).__name__, str(e)[:300])
            return None
        if i == 0 or same_file(got):
            return got
    IMPORT_ERRORS.setdefault(rel, "no importable module name (tried %s)" % ", ".join(tried))
    return None


# corpus-relative source path -> "module: ExceptionType: message" for a module whose import
# raised. Reported in conformance.json (`import_errors`) and in the per-function status.
IMPORT_ERRORS = {}


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


def coverage_recorder(f, fn):
    """An `ArcRecorder` for `fn`'s own frames when `f` is traced for change coverage,
    else a no-op context."""
    import contextlib
    if f["name"] not in COVERAGE_KEYS:
        return contextlib.nullcontext()
    code = getattr(inspect.unwrap(fn), "__code__", None) if callable(fn) else None
    return ArcRecorder(code) if code is not None else contextlib.nullcontext()


def keep_coverage(case, recorder):
    if isinstance(recorder, ArcRecorder):
        CASE_COVERAGE[id(case)] = (recorder.lines, recorder.arcs)


# Python parameter types (`paramTypes`) the literal inputs treat as strings, and as
# unknown (strings and integers both drawn); any other annotation keeps the integers.
PY_STRING_TYPES = {"__builtin.str"}
PY_UNTYPED = {"", "ANY", "typing.Any", "typing.Optional", "typing.Union"}


def literal_cases(f, fn, funcs, ncases, stats, encoder_factory=Encoder):
    """`--literal-inputs` cases for a module-level function: a string-typed parameter
    draws from strings built from the function's and its file's literals
    (`runtime_backends.string_inputs`), an unannotated one from those and the mined
    integers' neighbourhoods, any other the small integers the random cases use. Seeded
    by the function's name (its own generator, so the global sequence other cases draw
    from is unchanged), so the same export always yields the same inputs. Origin
    `literal`."""
    params = list(f["params"])
    types = list(f.get("paramTypes") or [])
    if len(types) != len(params):
        types = [""] * len(params)
    kinds = ["str" if t in PY_STRING_TYPES else "any" if t in PY_UNTYPED else "int" for t in types]
    if "str" not in kinds and "any" not in kinds:
        return []
    strings, ints = runtime_backends.mined_literals(f, funcs, EXTRA_LITERALS.get(f["name"], ()))
    pool_s = runtime_backends.string_inputs(strings)
    pool_any = pool_s + runtime_backends.integer_inputs(ints or [0])
    rng = random.Random("autoform-literal-inputs:" + f["name"])
    out, seen = [], set()
    for _ in range(ncases * 3):
        if len(out) >= ncases:
            break
        args = [rng.choice(pool_s) if k == "str" else rng.choice(pool_any) if k == "any"
                else rng.randint(-20, 20) for k in kinds]
        key = tuple((type(a).__name__, a) for a in args)
        if key in seen:
            continue
        seen.add(key)
        enc = encoder_factory()
        try:
            eargs = [enc.enc(a) for a in args]
        except Unencodable:
            continue
        enc.freeze()
        recorder = coverage_recorder(f, fn)
        try:
            with time_limit(2.0), recorder:
                got = fn(*args)
            outcome = ("val", enc.enc_result(got))
        except Timeout as exc:
            stats.setdefault('native_deadline_detail', []).append(
                {'function': f['name'], 'reason': str(exc), 'origin': 'literal'})
            break
        except Unencodable:
            stats["skip_unencodable_ret"] += 1
            continue
        except Exception as e:                              # noqa: BLE001
            outcome = ("exn", type(e).__name__)
        try:
            out.append(finish_record(enc, {"name": f["name"], "self": None, "args": eargs,
                                           "outcome": outcome, "origin": "literal"}))
            keep_coverage(out[-1], recorder)
        except Unencodable:
            continue
    return out


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
                    why[qual] = (("module for %s failed to import: %s" % (rel, IMPORT_ERRORS[rel]))
                                 if rel in IMPORT_ERRORS else
                                 "module for %s not imported by the suite" % rel)
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
            recorder = coverage_recorder(f, raw)
            try:
                with time_limit(2.0), recorder:
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
                keep_coverage(out[-1], recorder)
            except Unencodable as e:
                why[qual] = "unencodable post-state: " + str(e)
                break
            made += 1
        if made: why.pop(qual, None)
    return out


# `AUTOFORM_ORACLE_PYTEST_ADDOPTS=ignore` runs the suite without the project's pytest
# `addopts` (`-o addopts=`). Opt-in, and recorded (`test_runner`, measurement basis): the
# project's options can select or deselect tests, so dropping them changes which calls are
# traced. It exists for options that need a plugin the oracle interpreter lacks (`--cov`
# without pytest-cov makes pytest exit 4 before any test runs).
PYTEST_ADDOPTS_ENV = "AUTOFORM_ORACLE_PYTEST_ADDOPTS"


def pytest_args(test_dir, environ=None):
    """The pytest command line the oracle runs, and what it changed about the project's.

    `--continue-on-collection-errors`: a test module that fails to import (a dependency
    absent from the oracle interpreter) otherwise stops the whole session at collection
    (exit 2) and no test runs. The modules that collected still run; the ones that did not
    are reported by name with their exception (`collection_errors`)."""
    environ = os.environ if environ is None else environ
    args = [test_dir, "-q", "-p", "no:cacheprovider", "--no-header",
            "--continue-on-collection-errors"]
    mode = (environ.get(PYTEST_ADDOPTS_ENV) or "project").strip().lower()
    if mode not in ("project", "ignore"):
        raise ValueError("%s must be 'project' or 'ignore', not %r" % (PYTEST_ADDOPTS_ENV, mode))
    if mode == "ignore":
        args += ["-o", "addopts="]
    return args, {"runner": "pytest", "argv": args[1:], "project_addopts":
                  "ignored (%s=ignore)" % PYTEST_ADDOPTS_ENV if mode == "ignore" else "applied",
                  "collection_errors": "continue"}


def run_suite(test_dir, runner=None):
    """Run one test directory with whatever runner the project uses.

    `runner`, when given, is filled with the runner and command line actually used."""
    runner = {} if runner is None else runner
    try:
        import pytest
    except ImportError:
        pytest = None
    if pytest is not None:
        args, record = pytest_args(test_dir)
        runner.update(record, pytest_version=getattr(pytest, "__version__", "?"))
        return int(pytest.main(args))
    import unittest
    runner.update(runner="unittest", note="pytest is not importable in the oracle interpreter")
    loader = unittest.TestLoader()
    suite = loader.discover(test_dir, top_level_dir=os.path.dirname(test_dir))
    return 0 if unittest.TextTestRunner(verbosity=0).run(suite).wasSuccessful() else 1


_ANSI = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")


def collection_errors(output):
    """`{test module: last exception line}` for the modules pytest could not collect."""
    found, current = {}, None
    for line in _ANSI.sub("", output).splitlines():
        m = re.match(r"_+ ERROR collecting (.+?) _+$", line.strip())
        if m:
            current = m.group(1)
            found.setdefault(current, "?")
            continue
        if re.match(r"[_=]{3,} ", line.strip()):
            current = None
        elif current is not None and line.startswith("E   "):
            found[current] = line[4:].strip()[:300]
    return found


def run_test_dir(d):
    """Run one test directory (output captured) and describe what happened.

    The runner's output is kept (its last lines, and the modules it could not collect):
    an exit code alone cannot tell a usage error from a missing dependency, and the
    output used to be discarded."""
    buf = io.StringIO()
    runner = {}
    try:
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
            rc = run_suite(d, runner)
        run = {"dir": d, "rc": rc}
    except Exception as e:                       # noqa: BLE001
        run = {"dir": d, "error": repr(e)[:200]}
    output = buf.getvalue()
    run["runner"] = runner
    run["output_tail"] = [l for l in _ANSI.sub("", output).splitlines() if l.strip()][-8:]
    errs = collection_errors(output)
    if errs:
        run["collection_errors"] = errs
    return run


PYTEST_EXIT = {2: "interrupted, or errors during collection",
               3: "pytest internal error",
               4: "pytest usage error: it rejected its command line before running any test "
                  "(often project `addopts` naming a plugin this interpreter lacks, e.g. --cov "
                  "without pytest-cov; set %s=ignore to run without them, which is recorded)"
                  % PYTEST_ADDOPTS_ENV,
               5: "no tests were collected"}


def diagnose_test_run(run):
    """A one-line account of a test run that did not (fully) run, or None.

    pytest's exit codes say different things and each needs its own message: the old
    report printed "a test directory is imported as a package" for every code other
    than 0/1, which on a usage error (exit 4) sent the reader to rename directories."""
    tail = " | ".join(run.get("output_tail") or [])[-600:]
    if run.get("error"):
        # Measured: a project's `--cov-config setup.cfg` addopt raised coverage's
        # ConfigError out of pytest.main, because the oracle runs from its report
        # directory, not the project root, and the path is relative to the cwd.
        hint = ""
        if (run.get("runner") or {}).get("project_addopts") == "applied":
            hint = (" -- if an option in the project's pytest addopts raised it (a path relative "
                    "to the project root: the oracle runs from its report directory), "
                    "%s=ignore runs without them, which is recorded" % PYTEST_ADDOPTS_ENV)
        return "TEST SUITE DID NOT RUN: %s raised %s%s%s" % (
            run["dir"], run["error"], hint, (" -- last output: " + tail) if tail else "")
    rc = run.get("rc")
    errs = run.get("collection_errors") or {}
    if rc in (0, 1):
        if not errs:
            return None
        return ("TEST MODULES NOT COLLECTED in %s (the rest ran): %d -- %s"
                % (run["dir"], len(errs), "; ".join("%s: %s" % kv for kv in sorted(errs.items())[:8])))
    if (run.get("runner") or {}).get("runner", "pytest") == "pytest":
        what = PYTEST_EXIT.get(rc, "unrecognised pytest exit code")
    else:
        what = "the runner reported failure"
    hint = ""
    if "import file mismatch" in tail or "ImportPathMismatchError" in tail:
        hint = (" -- a test directory is imported as a package, so it must be named like "
                "one (e.g. .../tests)")
    if errs:
        hint += " -- not collected: " + "; ".join("%s: %s" % kv for kv in sorted(errs.items())[:8])
    return "TEST SUITE DID NOT RUN: %s (exit %s: %s)%s%s" % (
        run["dir"], rc, what, hint, (" -- last output: " + tail) if tail else "")


# ----------------------------------------------------------------------- C runtime

def c_runtime(src_root, funcs=None, population=None):
    """`population`: the whole export, against which a C++ entry point's qualified name
    must be unique when it is called by name rather than by its exact type."""
    if funcs is not None:
        import native_c
        return native_c.compile_sources(src_root, funcs, os.path.join(WORK, "native-units"),
                                        population=population)
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


def c_argument_cases(argtypes, ncases, random_arg, boundaries=False, literals=()):
    """Reserve a case for zero/equality boundaries before random exploration.

    Small random samples missed both `<` versus `<=` and the zero-base,
    zero-exponent branch in the Linux RAID-6 mutation run. This is one guaranteed
    boundary within the requested budget, not exhaustive boundary coverage.

    With `boundaries`, every other remaining case draws each argument from
    `typed_boundary_pool` for its ABI type (seeded, so reproducible) instead of
    `random_arg`, which is where 64-bit overflow behaviour becomes observable.

    `literals` (`--literal-inputs`: the function's integer literals and their neighbours)
    takes every fourth case after the first, drawn with its own generator seeded by the
    literals, so both revisions of an unchanged pool draw the same; empty, nothing changes.
    """
    pick = random.Random("autoform-literal-inputs:" + ",".join(map(str, literals))) if literals else None
    for index in range(ncases):
        if index == 0:
            yield [0] * len(argtypes), 'boundary-zero'
        elif literals and index % 4 == 3:
            yield [t(pick.choice(literals)).value for t in argtypes], 'boundary-literal'
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
    except Exception as e:                                  # noqa: BLE001
        # The by-name import's failure (if any) is the informative one; keep it.
        IMPORT_ERRORS.setdefault(rel, "%s (by path): %s: %s" % (rel, type(e).__name__, str(e)[:300]))
        return None


# ------------------------------------------------------------------ language dispatch
#
# The corpus decides which real runtime the oracle must talk to. Getting this wrong is
# not a missing feature but a *false* result: `cartographer/render_lean.py`'s
# `infer_dialect` used to default an unrecognised language to Python, and the oracle
# then cheerfully reported agreement. So the mapping is explicit, and an extension that
# is not in it is REFUSED rather than defaulted.

# The table is `runtime_backends.LANG_BY_EXT`, next to the backends, so `pr_mode.py` routes
# by the same mapping without importing this script (which re-executes itself on import).
LANG_BY_EXT = runtime_backends.LANG_BY_EXT

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

TOOLCHAIN = runtime_backends.TOOLCHAIN


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
# Parameter types the driver can supply a value for. `CharSequence` is the parameter
# type of most of commons-lang3's `StringUtils` surface (`isEmpty(CharSequence)`,
# `indexOf(CharSequence, int)`, ...); a `String` IS a `CharSequence` (JLS §4.10.2, java.lang
# .String implements it), so the driver passes a String through a `CharSequence.class`
# parameter slot -- reflection resolves the method by the declared parameter type, not the
# argument's class. A Java `CharSequence` RESULT is accepted too (`returns` in
# `java_backend`): a returned String is encoded as one, and a returned CharSequence that is
# not a String has no faithful encoding, so that case is refused by name, not guessed.
JAVA_ARG_TYPES = JAVA_PRIM + ("java.lang.CharSequence",)
# Extra `javac -sourcepath` roots for a corpus exported as a SUBSET of a larger tree
# (the commons-lang3 re-land exports nine files of `org.apache.commons.lang3`; their
# same-package references -- `ArrayUtils`, `ObjectUtils`, `CharSequenceUtils` -- live in the
# full source release the subset was copied from). The roots are recorded in
# `backend_info.extra_source_roots` so conformance.json says what was on the compile path.
JAVA_SOURCEPATH_ENV = "AUTOFORM_JAVA_SOURCEPATH"
# The project's own dependency classpath (what `gradle dependencies`/`mvn
# dependency:build-classpath` print; `dir/*` wildcards as javac takes them). Without it a
# real service compiles almost nothing: measured on a 1,472-file Gradle service, 7 of 378
# candidate files, every failure "unresolved package". The processor path replaces
# `-proc:none` so Lombok-generated members exist when the candidate is compiled. Both are
# recorded in `backend_info`; neither is ever guessed.
JAVA_CLASSPATH_ENV = "AUTOFORM_JAVA_CLASSPATH"
JAVA_PROCESSORPATH_ENV = "AUTOFORM_JAVA_PROCESSORPATH"
STRING_POOL = runtime_backends.STRING_POOL
JAVA_SIG = re.compile(r'^(?P<cls>[\w.$]+)\.(?P<meth>[\w$<>]+):(?P<ret>[\w.$\[\]]+)'
                      r'\((?P<args>.*)\)$')
# Boxed parameter types, drawn ONLY from the JVM's box cache (JLS §5.1.7: boxing an int,
# short, byte or long in -128..127, a char in 0..127 or a boolean yields the same object
# every time). Core spells a box as the primitive's value, so `a == b` on two boxes is a
# value comparison in Core and a reference comparison in the JVM; inside the cache the two
# agree, outside it they need not. `null` is not drawn for a box: Core has no unboxing
# `NullPointerException` (`if (flag)` on a null `Boolean` would read as `false`).
# Boxed floating-point values have no cache at all and are not parameters here; as a
# RESULT any box compares by value, so `Double`/`Float` are accepted there.
# `BigDecimal` has no Core counterpart and stays refused.
JAVA_BOXED = {"java.lang.Integer": "int", "java.lang.Long": "long", "java.lang.Short": "short",
              "java.lang.Byte": "byte", "java.lang.Character": "char",
              "java.lang.Boolean": "boolean"}
JAVA_BOXED_RETURNS = tuple(JAVA_BOXED) + ("java.lang.Double", "java.lang.Float")
JAVA_BOX_POOL = {"char": [0, 1, 31, 32, 63, 64, 127]}
JAVA_BOX_INT_POOL = [0, 1, -1, 127, -128, 31, 32, 63, 64]
# A heap cell holding a class's static fields (`javaStaticKey` in Core's globals frame
# names it). The `<module>` prefix is what makes a read of a field the JVM did not report
# a named hole (`module-attr:<f>`) rather than `unit` on the simple-name path.
JAVA_STATIC_HOLDER = "<module>static:"
# How many functions of a candidate's call tree are scanned for the static fields it reads.
# A read outside the scanned tree is a hole in the model (`field:<f>:non-object` or
# `field:<f>:static-not-captured`), never a guessed value.
JAVA_CALL_TREE_LIMIT = 400
JVM_DRIVER_TIMEOUT = 300   # seconds for one AutoformDriver run over every planned call


def java_static_key(cls):
    """The globals-frame key Core's `javaStaticKey` reads; the two must not disagree."""
    return "<static>" + cls


PROJECT_CLASS = re.compile(r'[A-Za-z_][\w$]*(?:\.[A-Za-z_][\w$]*)+')


def kotlin_enum_candidate(t):
    """A signature type that MAY be a project enum: a qualified class outside the platform
    libraries. Only the driver knows; a class that is not an enum is refused by name."""
    return bool(PROJECT_CLASS.fullmatch(t)) and not t.startswith(
        ("java.", "javax.", "jdk.", "sun.", "kotlin.", "kotlinx."))


def this_uses(body, owner=None, by_name=None):
    """How a Kotlin member's exported body uses its receiver: `field` when `this` is the
    base of a field read or write, `value` when `this` is used any other way (compared,
    returned, passed, a method-call receiver).

    A call of a member of its own class (`owner`) passes the receiver first, whether the
    source spelled it `one(by)` or `this.one(by)`: the callee runs on the same receiver,
    so its uses (`by_name`, the whole export) are this body's too -- an `object` whose
    sibling writes a property must start as a heap object even if this body never names
    a field. `dropped` when such a call has no receiver argument (a qualified `Obj.m()`:
    the export passes only the real arguments, so the callee would bind `this` to the
    first of them), `unfollowed` when the callee is not in the export."""
    by_name = by_name or {}
    uses, followed = set(), set()

    def this(node):
        return isinstance(node, dict) and node.get("k") == "name" and node.get("v") == "this"

    def walk(node):
        if isinstance(node, list):
            for x in node:
                walk(x)
            return
        if not isinstance(node, dict):
            return
        k = node.get("k")
        if this(node):
            uses.add("value")
            return
        if k == "field" and this(node.get("a")):
            uses.add("field")
            return
        if k == "setField" and this(node.get("r")):
            uses.add("field")
            walk(node.get("v"))
            return
        if k == "call" and owner and str(node.get("f", "")).startswith(owner + "."):
            callee, args = by_name.get(node["f"]), node.get("args") or []
            if callee is None:
                uses.add("unfollowed")
            elif len(args) != len(callee.get("params") or []):
                uses.add("dropped")
            elif args and this(args[0]):
                # Zero-argument owner-prefixed calls (a local function, a
                # synthetic <lambda> method) have no receiver to drop: the
                # arg-count check above passed, so this is a plain call.
                if node["f"] not in followed:
                    followed.add(node["f"])
                    walk(callee.get("body"))
                walk(args[1:])
                return
        for v in node.values():
            walk(v)

    walk(body)
    return uses


def singleton_encoding(kind, uses):
    """`heap`, `value`, or the refusal, for a Kotlin receiver of `kind` (as the driver
    reports it) whose body uses `this` as `uses` (`this_uses`) says.

    The model has two spellings for a singleton: the receiver `this` (a heap object whose
    fields are the properties) and the name `fnref "p.Obj"` / `fnref "p.E$ENTRY"` (a
    `Val.fn`, with no fields). A case can start Lean from only one of them, so a body that
    needs both -- reads `this.code` AND compares `this == RED` -- has no faithful starting
    state. A companion has no `fnref` spelling at all."""
    if "dropped" in uses:
        return ("calls a member of its own class through a qualified name; the export "
                "drops that receiver argument")
    if "unfollowed" in uses:
        return "calls a member of its own class that the export does not include"
    if kind == "class":
        return "heap"
    if "value" in uses:
        if kind == "companion":
            return "companion receiver used as a value: the model has no name for it"
        if "field" in uses:
            return ("%s receiver is both a field holder and a value: the model spells it "
                    "two ways and a case can start from only one" % kind)
        return "value"
    return "heap"


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
    // TWO ENUM ENCODINGS, one per language (the payload after `enum|` differs):
    //  * Kotlin (`enc`, here): an entry is the model's own spelling, a function value
    //    `fnref "<enum binary name>$<ENTRY>"` -- the Kotlin export writes `ON` inside the
    //    enum as fnref "p.Mode$ON", so the harness passes it as `Val.fn`.
    //  * Java (`encEnum`, below): `<enum binary name>#<NAME>`, a reference to the heap
    //    cell laid out for that constant (`constants`), so `==` is cell identity.
    // Java call paths encode an Enum with `encEnum` BEFORE reaching `enc`, so this
    // branch is only ever taken for Kotlin (`kt:` members, `kstate`).
    if (o instanceof Enum) return "enum|" + entry((Enum<?>) o);
    if (!(o instanceof Number)) return "ref|" + o.getClass().getName();
    return "int|" + o;
  }
  static String entry(Enum<?> e) { return e.getDeclaringClass().getName() + "$" + e.name(); }
  static void field(String head, Set<String> seen, Field f, Object target) throws Exception {
    if (!seen.add(f.getName())) { System.out.println(head + f.getName() + "|dup|"); return; }
    f.setAccessible(true);
    Object v = f.get(target);
    boolean scalar = f.getType().isPrimitive() || v == null || v.getClass() == String.class
                     || v instanceof Enum;
    System.out.println(head + f.getName() + "|" + (scalar ? enc(v) : "ref|" + v.getClass().getName()));
  }
  // A Kotlin receiver's state, in `state`'s line format. Instance fields up to (not
  // including) Object or Enum, plus the storage Kotlin gives the receiver's properties
  // elsewhere: an `object`'s properties are static fields of its own class (its INSTANCE
  // field excepted), a companion's are static fields of the class that declares it (the
  // companion field and enum entries excepted). An enum entry's `name` and `ordinal` are
  // read through their accessors (java.base does not open Enum's private fields).
  static void kstate(String idx, String when, Object o, String kind, Class<?> c) throws Exception {
    Set<String> seen = new HashSet<>();
    String head = "S" + idx + "|" + when + "|";
    for (Class<?> k = o.getClass(); k != null && k != Object.class && k != Enum.class; k = k.getSuperclass()) {
      // A platform superclass (an exception's Throwable) keeps private state that
      // java.base does not open to reflection: say so instead of failing the call.
      if (k.getName().startsWith("java.") || k.getName().startsWith("javax.")) {
        System.out.println(head + k.getName() + "|platform|");
        break;
      }
      for (Field f : k.getDeclaredFields())
        if (!Modifier.isStatic(f.getModifiers()) && !f.isSynthetic()) field(head, seen, f, o);
    }
    List<Class<?>> holders = new ArrayList<>();
    if (kind.equals("object") || kind.equals("companion")) holders.add(c);
    if (kind.equals("companion")) holders.add(c.getDeclaringClass());
    for (Class<?> h : holders)
      for (Field f : h.getDeclaredFields()) {
        if (!Modifier.isStatic(f.getModifiers()) || f.isSynthetic() || f.isEnumConstant()) continue;
        if (f.getType() == c && (f.getName().equals("INSTANCE") || h != c)) continue;
        field(head, seen, f, null);
      }
    if (kind.equals("enum")) {
      Enum<?> e = (Enum<?>) o;
      System.out.println(head + (seen.add("name") ? "name|" + enc(e.name()) : "name|dup|"));
      System.out.println(head + (seen.add("ordinal") ? "ordinal|int|" + e.ordinal() : "ordinal|dup|"));
    }
  }
  // The receiver of a Kotlin member: {receiver, kind, the model's name for it}, or
  // {null, reason}. An enum's entry `k` (mod the entry count); an `object`'s INSTANCE (a
  // static final field of its own type, all constructors private); a companion (the
  // declaring class's static final field of its type, named as the companion is);
  // otherwise a fresh object from a non-private no-arg constructor, which Kotlin
  // generates when every primary-constructor parameter has a default.
  static Object[] receiver(Class<?> c, int k) throws Exception {
    if (c.isEnum()) {
      Object[] es = c.getEnumConstants();
      if (es.length == 0) return new Object[]{null, "enum has no entries"};
      Enum<?> e = (Enum<?>) es[k % es.length];
      if (e.getClass() != c) return new Object[]{null, "enum entry " + e.name() + " has its own class body"};
      return new Object[]{e, "enum", entry(e)};
    }
    boolean hidden = c.getDeclaredConstructors().length > 0;
    for (Constructor<?> x : c.getDeclaredConstructors()) hidden &= Modifier.isPrivate(x.getModifiers());
    for (Field f : c.getDeclaredFields())
      if (hidden && f.getName().equals("INSTANCE") && f.getType() == c
          && Modifier.isStatic(f.getModifiers()) && Modifier.isFinal(f.getModifiers())) {
        f.setAccessible(true);
        return new Object[]{f.get(null), "object", c.getName()};
      }
    Class<?> outer = c.getDeclaringClass();
    if (outer != null)
      for (Field f : outer.getDeclaredFields())
        if (f.getType() == c && f.getName().equals(c.getSimpleName())
            && Modifier.isStatic(f.getModifiers()) && Modifier.isFinal(f.getModifiers())) {
          f.setAccessible(true);
          return new Object[]{f.get(null), "companion", c.getName()};
        }
    if (Modifier.isAbstract(c.getModifiers())) return new Object[]{null, "abstract class"};
    Constructor<?> x;
    try { x = c.getDeclaredConstructor(); }
    catch (NoSuchMethodException e) { return new Object[]{null, "no no-arg constructor"}; }
    if (Modifier.isPrivate(x.getModifiers())) return new Object[]{null, "no-arg constructor is private"};
    x.setAccessible(true);
    try { return new Object[]{x.newInstance(), "class", c.getName()}; }
    catch (InvocationTargetException e) { return new Object[]{null, "constructor threw " + e.getCause().getClass().getSimpleName()}; }
  }
  // The enum types whose constants this call's state names, in the order they were met.
  // Each one's constants become heap cells (`K`/`F` lines), so an enum value -- an
  // argument, a static, a field, the result -- is a reference to one of them.
  static LinkedHashSet<Class<?>> mat = new LinkedHashSet<>();
  static String encEnum(Enum<?> e) {
    Class<?> d = e.getDeclaringClass();
    mat.add(d);
    return "enum|" + d.getName() + "#" + e.name();
  }
  static String simple(Object v) { return v.getClass().getName(); }
  // JLS 5.1.7: boxing int/short/byte/char/boolean in this range yields the SAME object,
  // so `==` on two such boxes agrees with Core's value comparison; outside it, it need not.
  static boolean cached(Object v) {
    if (v instanceof Integer || v instanceof Short || v instanceof Byte || v instanceof Long) {
      long x = ((Number) v).longValue(); return -128 <= x && x <= 127;
    }
    if (v instanceof Character) return (Character) v <= 127;
    return v instanceof Boolean;
  }
  static boolean boxed(Object v) {
    return v instanceof Integer || v instanceof Short || v instanceof Byte || v instanceof Long
        || v instanceof Character || v instanceof Boolean;
  }
  // A value in a REFERENCE-typed slot (a static field, an enum constant's field, a map
  // value). `bad|<reason>` when Core has no faithful counterpart for it.
  static String encRef(Object v) {
    if (v == null) return "null|";
    if (v instanceof String) return enc(v);
    if (v instanceof Enum) return encEnum((Enum<?>) v);
    if (v instanceof Float || v instanceof Double)
      return "bad|boxed " + simple(v) + " (no box cache: == on it is reference equality)";
    if (boxed(v)) return cached(v) ? enc(v) : "bad|boxed " + simple(v) + " " + v + " outside the JVM box cache (== on it is reference equality)";
    if (v instanceof Collection || v instanceof Map) return encCollection(v);
    return "bad|" + simple(v);
  }
  // A set element or map key: compared by `equals`, which Core's `Val.beq` matches for a
  // String (content) and an enum constant (identity) and nothing else here.
  static String encKey(Object v) {
    if (v == null) return "null|";
    if (v instanceof String) return enc(v);
    if (v instanceof Enum) return encEnum((Enum<?>) v);
    return "bad|element " + simple(v) + " (only String and enum elements are compared faithfully)";
  }
  // A SEEDED element (the driver built the collection, so the element is a String, an
  // enum constant or a cached box by construction, and a box element was refused before
  // the call when the call tree queries a collection by equality -- `seedPool`). A
  // static's element accepts less: nothing but the driver builds it.
  static String encElem(Object v) {
    if (v == null) return "null|";
    if (v instanceof String) return enc(v);
    if (v instanceof Enum) return encEnum((Enum<?>) v);
    if (boxed(v)) return cached(v) ? enc(v)
        : "bad|boxed " + simple(v) + " " + v + " outside the JVM box cache";
    return "bad|element " + simple(v) + " (only String, enum and cached-box elements are seeded)";
  }
  static Object member(Object o, String... names) {
    for (Class<?> k = o.getClass(); k != null; k = k.getSuperclass())
      for (String n : names)
        try { Field f = k.getDeclaredField(n); f.setAccessible(true); return f.get(o); }
        catch (Throwable t) { /* next */ }
    return null;
  }
  static final Set<String> PLAIN = Set.of("java.util.HashSet", "java.util.LinkedHashSet",
      "java.util.HashMap", "java.util.LinkedHashMap", "java.util.ArrayList", "java.util.Arrays$ArrayList");
  // null when `c` is a read-only collection whose lookups are `equals`-based; else why not.
  static String vet(Object c) {
    String n = c.getClass().getName();
    if (n.startsWith("java.util.ImmutableCollections$") || n.startsWith("java.util.Collections$Empty")
        || n.startsWith("java.util.Collections$Singleton")) return null;
    if (n.startsWith("java.util.Collections$Unmodifiable")) {
      Object inner = member(c, "m", "c");
      if (inner == null) return "the collection behind " + n + " is not readable";
      String in = inner.getClass().getName();
      if (in.equals("java.util.LinkedHashMap") && Boolean.TRUE.equals(member(inner, "accessOrder")))
        return "an access-ordered LinkedHashMap behind " + n;
      if (PLAIN.contains(in)) return null;
      String r = vet(inner);
      return r == null ? null : r + " behind " + n;
    }
    return "mutable " + n + " (only read-only static collections are bound)";
  }
  static String oob(List<?> l, int i) {
    try { l.get(i); return "none"; } catch (Throwable t) { return t.getClass().getName(); }
  }
  static String b64(String s) { return Base64.getEncoder().encodeToString(s.getBytes()); }
  // `coll|S|...` (Set), `coll|L|...` (List), `coll|M|...` (Map: key, value, key, ...):
  // newline-joined element encodings, in the collection's own iteration order.
  // `seeded` swaps the element encoder: a driver-SEEDED collection may hold a cached box
  // element, a program's static may not.
  static String encCollection(Object c) { return encCollection(c, false); }
  static String encCollection(Object c, boolean seeded) {
    String why = vet(c);
    if (why != null) return "bad|" + why;
    StringBuilder sb = new StringBuilder();
    String tag;
    if (c instanceof Map) {
      tag = "M";
      for (Map.Entry<?, ?> e : ((Map<?, ?>) c).entrySet()) {
        String k = encKey(e.getKey()), v = encRef(e.getValue());
        if (k.startsWith("bad|")) return k;
        if (v.startsWith("bad|")) return v;
        sb.append(k).append('\n').append(v).append('\n');
      }
    } else if (c instanceof Set || c instanceof List) {
      tag = c instanceof Set ? "S" : "L";
      if (c instanceof List) {
        List<?> l = (List<?>) c;
        String hi = oob(l, l.size()), lo = oob(l, -1);
        if (!hi.equals("java.lang.IndexOutOfBoundsException") || !lo.equals(hi))
          return "bad|" + simple(c) + ".get out of range throws " + hi + " (Core: IndexOutOfBoundsException)";
      }
      for (Object e : (Collection<?>) c) {
        String k = seeded ? encElem(e) : encKey(e);
        if (k.startsWith("bad|")) return k;
        sb.append(k).append('\n');
      }
    } else return "bad|" + simple(c);
    return "coll|" + tag + "|" + b64(sb.toString());
  }
  // Whether `k` is a box class the JVM may hand out cached, so `encElem` holds its values.
  static boolean boxedClass(Class<?> k) {
    return k == Integer.class || k == Long.class || k == Short.class || k == Byte.class
        || k == Character.class || k == Boolean.class;
  }
  // Two fixed seeds of one element (or map value) kind, inside the JVM box cache so
  // every encoding of them is value-based. `eq` refuses a box: the call tree queries a
  // collection by equality (`contains`), and Core's int encoding conflates the box
  // kinds `equals` separates (an Integer 1 element, a Long 1 query: false on the JVM,
  // true in Core). Returns {seeds, null} or {null, reason}.
  static Object[] seedPool(Type t, boolean eq) {
    if (!(t instanceof Class))
      return new Object[]{null, t.getTypeName() + " is not a concrete class: no element type to seed"};
    Class<?> k = (Class<?>) t;
    if (k == String.class) return new Object[]{new String[]{"A", "B"}, null};
    if (boxedClass(k)) {
      if (eq) return new Object[]{null, "boxed " + k.getName() + " elements: the call tree "
          + "queries a collection by equality, and Core's int encoding conflates the box "
          + "kinds that `equals` separates"};
      Object[] s = k == Integer.class ? new Object[]{1, 2}
          : k == Long.class ? new Object[]{1L, 2L}
          : k == Short.class ? new Object[]{(short) 1, (short) 2}
          : k == Byte.class ? new Object[]{(byte) 1, (byte) 2}
          : k == Character.class ? new Object[]{'a', 'b'}
          : new Object[]{Boolean.TRUE, Boolean.FALSE};
      return new Object[]{s, null};
    }
    if (k.isEnum()) {
      Object[] cs = k.getEnumConstants();
      if (cs.length == 0) return new Object[]{null, "enum " + k.getName() + " has no constants"};
      // The signature could not ask for these constants (the element type is erased,
      // JLS 4.6): the seeding asks for them itself, so the `A` line's `enum|` elements
      // name cells `constants` lays out for this call.
      mat.add(k);
      return new Object[]{cs, null};
    }
    return new Object[]{null, k.getName() + " elements: only String, a cached box and an enum "
        + "constant are held faithfully"};
  }
  // The immutable value seeded for a `jcoll:` parameter: `draw` 0, 1 or 2 elements,
  // the element kind read from the method's own generic parameter type -- the
  // signature erased it (JLS 4.6). A `Collection` parameter is seeded as a List (a
  // List is a Collection); Core receives it as an unboxed `.list`/`.dict` whose
  // mutating methods are holes, as `add` on an immutable collection throws.
  // List.of/Set.of/Map.of build every value but two kinds, each still read-only:
  //  - the EMPTY list is `Collections.emptyList()`: `List.of()` is a ListN whose
  //    out-of-range `get` throws ArrayIndexOutOfBoundsException, not Core's
  //    IndexOutOfBoundsException, so `encCollection` would refuse every empty draw;
  //  - a TWO-element set or map is an unmodifiable LinkedHashSet/LinkedHashMap:
  //    `Set.of`/`Map.of` iterate in an order salted per JVM start
  //    (`ImmutableCollections.SALT`), so base and head would not run the same input.
  // A map key is a String or an enum constant, the two kinds `encKey` compares by
  // `equals` faithfully; a map value is fetched by key, so any kind encElem holds is
  // safe there. Returns {value, null} or {null, reason}.
  static Object[] seed(Type g, Class<?> iface, int draw, boolean eq) {
    boolean set = iface == Set.class, map = iface == Map.class;
    if (!(g instanceof ParameterizedType))
      return new Object[]{null, "raw " + g.getTypeName() + ": the element type is erased "
          + "(JLS 4.6), so no element can be seeded"};
    Type[] as = ((ParameterizedType) g).getActualTypeArguments();
    if (as.length != (map ? 2 : 1))
      return new Object[]{null, g.getTypeName() + ": unexpected type arguments"};
    Object[] r = seedPool(as[map ? 1 : 0], eq && !map);
    if (r[1] != null) return r;
    Object[] es = (Object[]) r[0];
    if (map) {
      if (as[0] instanceof Class && boxedClass((Class<?>) as[0]))
        return new Object[]{null, "boxed " + ((Class<?>) as[0]).getName() + " map keys: a "
            + "lookup compares keys by `equals`, and Core's int encoding conflates the box "
            + "kinds that `equals` separates"};
      Object[] kr = seedPool(as[0], false);
      if (kr[1] != null) return kr;
      Object[] ks = (Object[]) kr[0];
      int n = Math.min(draw, Math.min(ks.length, es.length));
      if (n == 0) return new Object[]{Map.of(), null};
      if (n == 1) return new Object[]{Map.of(ks[0], es[0]), null};
      LinkedHashMap<Object, Object> two = new LinkedHashMap<>();
      two.put(ks[0], es[0]);
      two.put(ks[1], es[1]);
      return new Object[]{Collections.unmodifiableMap(two), null};
    }
    int n = Math.min(draw, es.length);
    if (set) {
      if (n == 0) return new Object[]{Set.of(), null};
      if (n == 1) return new Object[]{Set.of(es[0]), null};
      return new Object[]{Collections.unmodifiableSet(new LinkedHashSet<>(List.of(es[0], es[1]))), null};
    }
    if (n == 0) return new Object[]{Collections.emptyList(), null};
    if (n == 1) return new Object[]{List.of(es[0]), null};
    return new Object[]{List.of(es[0], es[1]), null};
  }
  // Seeds every `jcoll:` parameter of the resolved method, reporting each encoding on
  // an `A` line; false -- after printing `idx|ARG|<reason>` -- when one cannot be built
  // or encoded, so the call is not made and nothing is guessed.
  static boolean seedAll(String idx, Method mt, Object[] vs, List<Object[]> jcoll) {
    try {
      Type[] gt = mt.getGenericParameterTypes();
      for (Object[] jc : jcoll) {
        int pos = (Integer) jc[0];
        Object[] r = seed(gt[pos], (Class<?>) jc[2],
                          Integer.parseInt((String) jc[1]) % 3, (Boolean) jc[3]);
        if (r[1] != null) { System.out.println(idx + "|ARG|" + r[1]); return false; }
        String enc = encCollection(r[0], true);
        if (enc.startsWith("bad|")) { System.out.println(idx + "|ARG|" + enc.substring(4)); return false; }
        vs[pos] = r[0];
        System.out.println("A" + idx + "|" + pos + "|" + enc);
      }
      return true;
    } catch (Throwable t) {
      System.out.println(idx + "|ARG|seeding the collection threw " + t.getClass().getSimpleName());
      return false;
    }
  }
  // A value read from a field of declared type `t`.
  static String encField(Class<?> t, Object v) { return t.isPrimitive() ? enc(v) : encRef(v); }
  // The receiver's instance fields, one `S<idx>|<when>|<name>|<kind>|<payload>` line each,
  // walked up to (not including) Object. A non-null value that is not a primitive, a
  // String or an enum constant is reported as `ref|<class>` and a name declared twice as
  // `dup|`: the harness refuses both instead of guessing an encoding.
  static void state(String idx, String when, Object o) throws Exception {
    Set<String> seen = new HashSet<>();
    for (Class<?> k = o.getClass(); k != null && k != Object.class; k = k.getSuperclass())
      for (Field f : k.getDeclaredFields()) {
        if (Modifier.isStatic(f.getModifiers()) || f.isSynthetic()) continue;
        String head = "S" + idx + "|" + when + "|" + f.getName() + "|";
        if (!seen.add(f.getName())) { System.out.println(head + "dup|"); continue; }
        f.setAccessible(true);
        Object v = f.get(o);
        if (v instanceof Enum) { System.out.println(head + encEnum((Enum<?>) v)); continue; }
        boolean scalar = f.getType().isPrimitive() || v == null || v.getClass() == String.class;
        System.out.println(head + (scalar ? enc(v) : "ref|" + v.getClass().getName()));
      }
  }
  static ClassLoader loader = AutoformDriver.class.getClassLoader();
  // A source-level name (`a.b.Outer.Inner`) or a binary one (`a.b.Outer$Inner`).
  static Class<?> load(String name) {
    String n = name;
    while (true) {
      try { return Class.forName(n, false, loader); } catch (Throwable t) { /* try nesting */ }
      int dot = n.lastIndexOf('.');
      if (dot < 0) return null;
      n = n.substring(0, dot) + "$" + n.substring(dot + 1);
    }
  }
  // JLS 8.3 / 9.3: a static field of C, of its superinterfaces, or of its superclass.
  static Field staticField(Class<?> c, String name) {
    for (Class<?> k = c; k != null; k = k.getSuperclass()) {
      try {
        Field f = k.getDeclaredField(name);
        return Modifier.isStatic(f.getModifiers()) ? f : null;
      } catch (NoSuchFieldException e) { /* inherited? */ }
      for (Class<?> i : k.getInterfaces()) { Field f = staticField(i, name); if (f != null) return f; }
    }
    return null;
  }
  // `G<idx>|<when>|<requested class>|<binary name>|<field>|<kind>|<payload>`
  static void statics(String idx, String when, List<String[]> st) {
    for (String[] s : st) {
      String head = "G" + idx + "|" + when + "|" + s[0] + "|";
      Class<?> c = load(s[0]);
      if (c == null) { System.out.println(head + "|" + s[1] + "|bad|class not loadable"); continue; }
      head += c.getName() + "|" + s[1] + "|";
      Field f = staticField(c, s[1]);
      if (f == null) { System.out.println(head + "bad|no static field of that name"); continue; }
      try { f.setAccessible(true); System.out.println(head + encField(f.getType(), f.get(null))); }
      catch (Throwable t) { System.out.println(head + "bad|reading it threw " + t.getClass().getSimpleName()); }
    }
  }
  // Every constant of every enum in `mat` (growing while its fields name more enums):
  // `K<idx>|<when>|<enum>|<NAME>` then `F<idx>|<when>|<enum>|<NAME>|<field>|<kind>|<payload>`,
  // or `X<idx>|<when>|<enum>|<reason>` for an enum that has no faithful cell.
  static void constants(String idx, String when) {
    List<Class<?>> order = new ArrayList<>();
    for (int i = 0; i < mat.size(); i++) {
      order = new ArrayList<>(mat);
      Class<?> e = order.get(i);
      String head = idx + "|" + when + "|" + e.getName() + "|";
      Object[] cs = e.getEnumConstants();
      if (cs == null) { System.out.println("X" + head + "not an enum"); continue; }
      String why = null;
      for (Object c : cs) if (c.getClass() != e) why = "constant " + ((Enum<?>) c).name() + " has a class body";
      if (why != null) { System.out.println("X" + head + why); continue; }
      for (Object c : cs) {
        String name = ((Enum<?>) c).name();
        System.out.println("K" + head + name);
        for (Class<?> k = e; k != null && k != Enum.class; k = k.getSuperclass())
          for (Field f : k.getDeclaredFields()) {
            if (Modifier.isStatic(f.getModifiers()) || f.isSynthetic()) continue;
            String v;
            try { f.setAccessible(true); v = encField(f.getType(), f.get(c)); }
            catch (Throwable t) { v = "bad|unreadable field"; }
            System.out.println("F" + head + name + "|" + f.getName() + "|" + v);
          }
      }
    }
  }
  public static void main(String[] a) throws Exception {
    Scanner sc = new Scanner(System.in);
    while (sc.hasNextLine()) {
      String line = sc.nextLine();
      if (line.isEmpty()) continue;
      mat.clear();
      String[] p = line.split("\\|", -1);
      String idx = p[0], cn = p[1], mn = p[2];
      int n = Integer.parseInt(p[3]);
      Class<?>[] ts = new Class<?>[n];
      Object[] vs = new Object[n];
      String bad = null, badArg = null;
      List<Object[]> jcoll = new ArrayList<>();  // {position, draw, interface, eq}
      for (int i = 0; i < n; i++) {
        String t = p[4 + 2 * i], v = p[5 + 2 * i];
        // `ktenum:E` (Kotlin) asks for entry `v` (mod the entry count) of enum E, never null;
        // the entry chosen is reported as `A<idx>|<position>|<model name E$ENTRY>`. Java's
        // `enum:E` (below) draws a constant or null and reports the constant's NAME: the
        // two languages encode an enum differently (see `enc`).
        if (t.startsWith("ktenum:")) {
          try {
            Class<?> ec = Class.forName(t.substring(7));
            ts[i] = ec;
            Object[] es = ec.isEnum() ? ec.getEnumConstants() : null;
            if (es == null) badArg = "parameter type " + ec.getName() + " is not an enum";
            else if (es.length == 0) badArg = "enum " + ec.getName() + " has no entries";
            else {
              vs[i] = es[Integer.parseInt(v) % es.length];
              System.out.println("A" + idx + "|" + i + "|" + entry((Enum<?>) vs[i]));
            }
          } catch (Throwable e) { badArg = "parameter type not loadable: " + e.getClass().getSimpleName(); }
        }
        else if (t.equals("int"))     { ts[i] = int.class;     vs[i] = Integer.parseInt(v); }
        else if (t.equals("long"))    { ts[i] = long.class;    vs[i] = Long.parseLong(v); }
        else if (t.equals("short"))   { ts[i] = short.class;   vs[i] = Short.parseShort(v); }
        else if (t.equals("byte"))    { ts[i] = byte.class;    vs[i] = Byte.parseByte(v); }
        else if (t.equals("char"))    { ts[i] = char.class;    vs[i] = (char) Integer.parseInt(v); }
        else if (t.equals("float"))   { ts[i] = float.class;   vs[i] = Float.parseFloat(v); }
        else if (t.equals("double"))  { ts[i] = double.class;  vs[i] = Double.parseDouble(v); }
        else if (t.equals("boolean")) { ts[i] = boolean.class; vs[i] = Boolean.parseBoolean(v); }
        // Boxed parameters get the `valueOf` box -- the one autoboxing would pass.
        else if (t.equals("java.lang.Integer"))   { ts[i] = Integer.class;   vs[i] = Integer.valueOf(v); }
        else if (t.equals("java.lang.Long"))      { ts[i] = Long.class;      vs[i] = Long.valueOf(v); }
        else if (t.equals("java.lang.Short"))     { ts[i] = Short.class;     vs[i] = Short.valueOf(v); }
        else if (t.equals("java.lang.Byte"))      { ts[i] = Byte.class;      vs[i] = Byte.valueOf(v); }
        else if (t.equals("java.lang.Character")) { ts[i] = Character.class; vs[i] = Character.valueOf((char) Integer.parseInt(v)); }
        else if (t.equals("java.lang.Boolean"))   { ts[i] = Boolean.class;   vs[i] = Boolean.valueOf(v); }
        else if (t.startsWith("enum:")) {
          // `enum:<type>` with a draw `k`: constant `k mod (n+1)`, or null when that is n.
          Class<?> e = load(t.substring(5));
          if (e == null || !e.isEnum()) { bad = "parameter type " + t.substring(5) + " is not an enum"; break; }
          ts[i] = e;
          Object[] cs = e.getEnumConstants();
          int j = Integer.parseInt(v) % (cs.length + 1);
          vs[i] = j == cs.length ? null : cs[j];
          mat.add(e);
          System.out.println("A" + idx + "|" + i + "|" + (vs[i] == null ? "" : ((Enum<?>) vs[i]).name()));
        }
        else if (t.startsWith("jcoll:")) {
          // A collection parameter. The interface names the reflection slot; the VALUE
          // is seeded after the method is resolved (`seedAll` below), from the method's
          // own generic parameter type -- the signature erased the element kind
          // (JLS 4.6). `:q` marks a call tree that queries a collection by equality
          // (`contains`), which a seeded box element must not face: Core's int
          // encoding conflates the box kinds `equals` keeps.
          try {
            String spec = t.substring(6);
            boolean q = spec.endsWith(":q");
            Class<?> iface = Class.forName(q ? spec.substring(0, spec.length() - 2) : spec);
            ts[i] = iface;
            jcoll.add(new Object[]{i, v, iface, q});
          } catch (Throwable e) { badArg = "parameter type not loadable: " + e.getClass().getSimpleName(); }
        }
        else {
          ts[i] = t.equals("java.lang.CharSequence") ? CharSequence.class : String.class;
          vs[i] = v.equals("!") ? null : new String(Base64.getDecoder().decode(v));
        }
      }
      if (bad != null) { System.out.println(idx + "|BAD|" + bad); continue; }
      if (badArg != null) { System.out.println(idx + "|ARG|" + badArg); continue; }
      // After the arguments: the static fields to report (`<k>|<class>|<field>|...`) and
      // the enum types to lay out before the call (`<m>|<enum>|...`).
      int q = 4 + 2 * n;
      List<String[]> st = new ArrayList<>();
      int k = q < p.length ? Integer.parseInt(p[q++]) : 0;
      for (int j = 0; j < k; j++) { st.add(new String[] {p[q], p[q + 1]}); q += 2; }
      int m = q < p.length ? Integer.parseInt(p[q++]) : 0;
      for (int j = 0; j < m; j++) {
        Class<?> e = load(p[q++]);
        if (e != null && e.isEnum()) mat.add(e);
        else System.out.println("X" + idx + "|pre|" + p[q - 1] + "|not an enum");
      }
      // `new:C` asks for an instance method on a receiver built by C's own no-arg
      // constructor; its fields are reported before and after the call.
      // `kt:C:k` asks for a Kotlin member on the receiver `receiver(C, k)` chooses; its
      // kind and model name are reported as `R<idx>|<kind>|<name>`, its state by `kstate`.
      boolean inst = cn.startsWith("new:"), kt = cn.startsWith("kt:");
      // `enum:E#k` asks for an instance method of (Java) enum E on its constant `k mod n`.
      boolean onEnum = cn.startsWith("enum:");
      Object recv = null;
      String kind = null;
      Class<?> c = null;
      try {
        String[] kq = kt ? cn.substring(3).split(":") : null;
        c = Class.forName(kt ? kq[0] : inst ? cn.substring(4)
                          : onEnum ? cn.substring(5, cn.indexOf('#')) : cn);
        Method mt = c.getDeclaredMethod(mn, ts);
        mt.setAccessible(true);
        // Before any state: seeding lays out an element enum's constants (`mat`), so
        // the `A` line's enum cells are numbered with the call's other constants.
        if (!jcoll.isEmpty() && !seedAll(idx, mt, vs, jcoll)) continue;
        if (kt) {
          Object[] got = receiver(c, Integer.parseInt(kq[1]));
          if (got[0] == null) { System.out.println(idx + "|CTOR|" + got[1]); continue; }
          recv = got[0]; kind = (String) got[1];
          System.out.println("R" + idx + "|" + kind + "|" + got[2]);
          kstate(idx, "pre", recv, kind, c);
          Object r = mt.invoke(recv, vs);
          kstate(idx, "post", recv, kind, c);
          System.out.println(idx + "|OK|" + enc(r));
          continue;
        }
        if (onEnum) {
          Object[] cs = c.getEnumConstants();
          if (cs == null || cs.length == 0) { System.out.println(idx + "|BAD|receiver class is not an enum with constants"); continue; }
          recv = cs[Integer.parseInt(cn.substring(cn.indexOf('#') + 1)) % cs.length];
          mat.add(c);
          System.out.println("A" + idx + "|-1|" + ((Enum<?>) recv).name());
        }
        if (inst) {
          Constructor<?> ct;
          try { ct = c.getDeclaredConstructor(); }
          catch (NoSuchMethodException e) { System.out.println(idx + "|CTOR|no no-arg constructor"); continue; }
          if (Modifier.isPrivate(ct.getModifiers())) { System.out.println(idx + "|CTOR|no-arg constructor is private"); continue; }
          if (Modifier.isAbstract(c.getModifiers())) { System.out.println(idx + "|CTOR|abstract class"); continue; }
          ct.setAccessible(true);
          try { recv = ct.newInstance(); }
          catch (InvocationTargetException e) { System.out.println(idx + "|CTOR|constructor threw " + e.getCause().getClass().getSimpleName()); continue; }
          state(idx, "pre", recv);
        }
        // The static state the model is given is read HERE, immediately before the call,
        // so it is the state the call starts from (initialisers included).
        statics(idx, "pre", st);
        constants(idx, "pre");
        Object r = mt.invoke(recv, vs);
        String out = r instanceof Enum ? encEnum((Enum<?>) r) : enc(r);
        if (inst) state(idx, "post", recv);
        statics(idx, "post", st);
        constants(idx, "post");
        System.out.println(idx + "|OK|" + out);
      } catch (InvocationTargetException e) {
        try {
          if (kt) { if (recv != null) kstate(idx, "post", recv, kind, c); }
          else { if (inst) state(idx, "post", recv); statics(idx, "post", st); constants(idx, "post"); }
        }
        catch (Throwable t) { /* refused: no post-state */ }
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


def java_source_text(path):
    """A .java file with comments and string/char literals blanked, or '' if unreadable."""
    try:
        with open(path, encoding='utf-8', errors='replace') as handle:
            text = handle.read()
    except OSError:
        return ''
    text = re.sub(r'/\*.*?\*/', ' ', text, flags=re.DOTALL)
    text = re.sub(r'//[^\n]*', ' ', text)
    return re.sub(r'"(?:[^"\\\n]|\\.)*"|\'(?:[^\'\\\n]|\\.)*\'', '""', text)


def java_body_refs(body):
    """Static-looking reads, writes and direct callees of one exported body.

    `C.f` reaches the AST in two spellings: `.field (.fnref "pkg.C") "f"` when the class
    is implicit (a static of the method's own class) and `.field (.name "C") "f"` when the
    source wrote the class's simple name (`OrderUseCase.Rental`). Both are collected;
    whether a simple name denotes a class is decided later (`JavaNames`)."""
    reads, calls = set(), set()
    stack = [body]
    while stack:
        node = stack.pop()
        if isinstance(node, dict):
            if node.get("k") == "field" and isinstance(node.get("a"), dict) \
                    and isinstance(node.get("f"), str):
                base = node["a"]
                if base.get("k") in ("fnref", "name") and isinstance(base.get("v"), str):
                    reads.add(("fq" if base["k"] == "fnref" else "simple", base["v"], node["f"]))
            elif node.get("k") == "setField" and isinstance(node.get("r"), dict) \
                    and node["r"].get("k") == "name" and isinstance(node["r"].get("v"), str):
                # `S.f = v` through a simple name writes the holder object in Core.
                reads.add(("write", node["r"]["v"], node.get("f")))
            elif node.get("k") == "call" and isinstance(node.get("f"), str):
                calls.add(node["f"])
            stack.extend(v for v in node.values() if isinstance(v, (dict, list)))
        elif isinstance(node, list):
            stack.extend(node)
    return reads, calls


def java_enum_types(types, roots):
    """{signature type: binary name} for the types the corpus's own sources declare as an
    `enum`. A candidate filter only: the driver checks `Class.isEnum()` and refuses by
    name when it is not one, so a misread here costs a case, never a wrong value."""
    found = {}
    for t in types:
        parts = t.replace("$", ".").split(".")
        for i in range(1, len(parts)):
            rel = os.path.join(*parts[:i], parts[i] + ".java")
            path = next((os.path.join(r, rel) for r in roots
                         if os.path.isfile(os.path.join(r, rel))), None)
            if path is None:
                continue
            if re.search(r'\benum\s+%s\b' % re.escape(parts[-1]), java_source_text(path)):
                found[t] = ".".join(parts[:i + 1]) + "".join("$" + p for p in parts[i + 1:])
            break
    return found


class JavaNames:
    """Which class the simple name `S` in a read `S.f` denotes.

    Per file, by the JLS §6.4.1 shadowing order, statically: a class declared in the
    file (or a member class of one, when the corpus exports it), else a single-type
    import, else a class of the file's own package, else -- only in a file with no
    on-demand import -- `java.lang.S`. An on-demand import is not resolved. Core has ONE
    globals frame, so a name can only be bound to one class for the whole program: `S` is
    bound only when every file of the corpus that reads `S.<f>` resolves it to the same
    class, and is otherwise left unbound (its reads stay holes)."""

    def __init__(self, src_root, funcs, roots):
        self.src_root, self.roots = src_root, roots
        self.classes = collections.defaultdict(set)
        self.known = set()
        self.uses = collections.defaultdict(set)
        for f in funcs:
            m = JAVA_SIG.match(f["name"])
            if m:
                self.classes[f.get("file")].add(m.group("cls"))
                self.known.add(m.group("cls"))
            for kind, base, _ in java_body_refs(f.get("body"))[0]:
                if kind == "simple":
                    self.uses[base].add(f.get("file"))
        self.headers, self.bound_names = {}, {}

    def header(self, file):
        if file not in self.headers:
            text = java_source_text(os.path.join(self.src_root, file or ""))
            pkg = JAVA_PACKAGE.search(text)
            single, ondemand = {}, False
            for imp in re.finditer(r'^\s*import\s+(static\s+)?([\w.]+)(\.\*)?\s*;', text, re.M):
                if imp.group(1):
                    continue
                if imp.group(3):
                    ondemand = True
                else:
                    single[imp.group(2).rsplit(".", 1)[-1]] = imp.group(2)
            self.headers[file] = (pkg.group(1) if pkg else "", single, ondemand)
        return self.headers[file]

    def resolve_in(self, file, name):
        here = set()
        for cls in self.classes.get(file, ()):
            chain = cls.split("$")
            for i in range(len(chain)):
                prefix = "$".join(chain[:i + 1])
                if re.split(r'[.$]', prefix)[-1] == name:
                    here.add(prefix)
                if prefix + "$" + name in self.known:
                    here.add(prefix + "$" + name)
        if len(here) > 1:
            return None
        if here:
            return here.pop()
        pkg, single, ondemand = self.header(file)
        if name in single:
            return single[name]
        same = (pkg + "." if pkg else "") + name
        rel = os.path.join(*(pkg.split(".") if pkg else []), name + ".java")
        if same in self.known or any(os.path.isfile(os.path.join(r, rel)) for r in self.roots):
            return same
        return None if ondemand else "java.lang." + name

    def bound(self, name):
        """The class `name` denotes in every file that reads `name.<f>`, or None."""
        if name not in self.bound_names:
            # A lower-case name is a variable by Java convention; not treating it as a
            # class only leaves reads unbound (holes), it never binds a wrong class.
            meanings = ({self.resolve_in(file, name) for file in self.uses.get(name, ())}
                        if name[:1].isupper() else {None})
            self.bound_names[name] = (next(iter(meanings))
                                      if len(meanings) == 1 and None not in meanings else None)
        return self.bound_names[name]


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


def java_backend(src_root, holefree, ncases, kotlin=False, universe=None):
    """Compile each candidate's own file, then call it reflectively.

    The corpus (a gson subset) does not compile as a whole — most of gson is absent —
    so compilation is per file, and a file that will not build becomes a *reported*
    skip rather than a silent one. Methods whose whole signature is primitive-or-String
    are called: `static` ones directly, and Java instance methods on a receiver the JVM
    builds with the class's own no-arg constructor. A Java method may return `void`
    (static or instance) or a `CharSequence` (compared when it is a String).

    The receiver is NOT rebuilt by running the translated `<init>` in Lean. The model
    does not allocate Java objects with their constructor (`new C()` is the hole
    `op:alloc:ctor-shape`, and `.alloc` of a default-package class does not resolve its
    `<init>`), and Core does not give an unassigned field its JLS §4.12.5 default (`0`,
    `false`): it reads as `unit`. A receiver rebuilt that way would differ from the JVM's
    for every class with an uninitialised primitive field. Instead the driver reports
    the constructed receiver's instance fields, the case starts Lean from exactly that
    object (the same move the Python leg makes when it snapshots a constructed
    instance), and the fields AFTER the call are compared as a heap observation, so a
    method's writes are checked too, not only its result. A receiver holding a non-null
    value that is not a primitive or a String, a field name declared twice in the
    hierarchy, no accessible no-arg constructor, an abstract class, or a constructor
    that throws is a named refusal.

    Java beyond primitive-or-String: a cached box (`JAVA_BOXED`), an enum the corpus
    declares (each constant is a heap cell holding its instance fields, so `==` is cell
    identity; a parameter is a constant or null, a result is the cell of the constant
    returned, an instance method of the enum runs on a constant's cell), and a null
    String. Core does not run `<clinit>`, so the static fields the call tree reads
    (`universe`: the whole export, for callees and simple-name resolution) are read
    from the JVM just before the call and given to Core in holder cells the globals
    frame names (`java_static_key`); a static Core cannot hold faithfully is left
    unbound -- its read is a hole -- and counted under `static_fields_not_bound`.

    A collection-interface parameter (List/Set/Collection/Map, Java only) is seeded
    by the driver with a small immutable value (0/1/2 elements, List.of/Set.of/Map.of
    except the empty list and a two-element set or map, whose JDK forms throw the
    wrong exception or iterate in a per-JVM order; drawn by the iteration, in a fixed
    order, so base and head run identical inputs), the element kind read back from
    the method's generic parameter type -- the signature erased it (JLS 4.6). An enum
    element's constants are laid out for the call (the signature could not name
    them), so `==` on it is cell identity. Core receives it exactly as a read-only
    static collection: an unboxed `.list`/`.dict`, so a mutating method on it is a
    hole. An element the model cannot hold (a raw type, a non-enum class), a box
    element in a call tree that queries a collection by equality, or a boxed map key
    refuses the case with its reason. An array parameter (a varargs) keeps refusing,
    now by name: `.length` is the `op:sizeOf:array-length` hole and an out-of-range
    index raises IndexError in Core."""
    import base64
    work = os.path.join(WORK, "java")
    classes = os.path.join(work, "classes")
    os.makedirs(classes, exist_ok=True)
    info, skipped, cands = {}, {}, []
    members, enum_typed = set(), 0
    universe = holefree if universe is None else universe
    # Beyond primitive-or-String (Java only; the Kotlin thunks stay primitive): a boxed
    # type, and an enum the corpus declares. Enum detection needs the corpus's source
    # roots, derived from every exported file, not only the candidates'.
    extended = set()
    collections_typed = set()
    # A collection INTERFACE as a parameter type (Java only; the Kotlin thunks stay
    # primitive). The signature erases the element type (JLS 4.6), so the driver seeds
    # the value only after the method is resolved, reading the element kind from the
    # method's own generic parameter type: 0/1/2 immutable elements in a fixed order
    # (`seed` in the driver), encoded exactly as a read-only static collection is --
    # an unboxed `.list`/`.dict`, so a mutating method on it is the hole
    # `mcall:*:unboxed-container`. An element the model cannot hold refuses the case
    # by name. A collection RESULT still refuses: only the collection methods are
    # modeled, not a collection that flows into arbitrary code.
    collection_params = ("java.util.List", "java.util.Set", "java.util.Collection", "java.util.Map")
    if not kotlin:
        sigs = [JAVA_SIG.match(f["name"]) for f in holefree]
        wanted = {t for m in sigs if m
                  for t in [a for a in m.group("args").split(",") if a] + [m.group("ret")]
                  if t not in JAVA_ARG_TYPES and t not in JAVA_BOXED_RETURNS
                  and t not in ("void", "ANY") and "[" not in t and not t.startswith("java.")}
        # An instance method of a corpus enum runs on one of its constants.
        wanted |= {m.group("cls") for m, f in zip(sigs, holefree)
                   if m and f["params"][0:1] == ["this"]}
        all_roots = java_source_roots(sorted({os.path.join(src_root, f["file"])
                                              for f in universe if f.get("file")}))
        enums = java_enum_types(sorted(wanted), all_roots) if wanted else {}
    else:
        enums, all_roots = {}, []
    for f in holefree:
        m = JAVA_SIG.match(f["name"])
        if not m:
            if ":<unresolvedSignature>(" in f["name"]:
                # kotlin2cpg names a function this way when it could not type a parameter
                # or the result, usually a type from a dependency not on the classpath.
                skipped[f["name"]] = ("unresolved signature: the frontend could not type a "
                                      "parameter or the result (typically a dependency type not on the classpath)")
            continue
        args = [a for a in m.group("args").split(",") if a]
        instance = f["params"][0:1] == ["this"]
        # A Kotlin top-level extension function (`fun T.f()`) also has `this` first, but
        # its receiver is an ordinary first argument: Joern lists its type in the
        # signature, and the owner is the package, not the receiver's class.
        extension = (kotlin and instance and len(args) == len(f["params"])
                     and (f.get("paramTypes") or [None])[0] != m.group("cls"))
        instance = instance and not extension
        if "this" in f["params"][1:]:
            skipped[f["name"]] = "instance method: needs a receiver"
            continue
        if kotlin and m.group("meth").startswith("<lambda>"):
            # A lambda is compiled to a synthetic method: no source name calls it directly,
            # so counting it as a static candidate promised cases that cannot be built.
            skipped[f["name"]] = "lambda: not callable by name"
            continue
        if instance and m.group("meth") in ("<init>", "<clinit>"):
            skipped[f["name"]] = "constructor: builds receivers, is not called as a method"
            continue
        if len(args) != len(f["params"]) - instance:
            own = list(f["params"][1:]) if instance else list(f["params"])
            if kotlin and instance and len(args) == len(own) + 1:
                # `fun T.f(...)` declared inside a class: Joern puts the extension
                # receiver's type first in the signature but names no parameter for it.
                skipped[f["name"]] = (
                    "member extension function: the signature's first type (%s) is an "
                    "extension receiver the exported parameter list does not name (%d "
                    "type(s) for %d parameter(s): %s); a call needs both the class instance "
                    "and a %s receiver, which the driver does not build"
                    % (args[0].rsplit(".", 1)[-1], len(args), len(own), ", ".join(own) or "none",
                       args[0].rsplit(".", 1)[-1]))
                continue
            skipped[f["name"]] = (
                "signature/parameter count disagree: the exported signature lists %d "
                "parameter type(s) (%s), the exported parameter list has %d (%s)%s"
                % (len(args), ", ".join(a.rsplit(".", 1)[-1] for a in args) or "none",
                   len(f["params"]) - instance, ", ".join(own) or "none",
                   "; a receiver `this` is not counted" if instance else ""))
            continue
        # `void` is a result for any Java method: the driver's `enc(null)` is `unit`, which
        # the outcome check below accepts only when the signature says `void`, and a throw
        # is an exception outcome either way (`Validate.isTrue(boolean, ...)`, static, is
        # exactly that pair). A static call carries no post-state, so a static `void` is
        # compared on unit-versus-exception only, as every static's result is today.
        # Kotlin keeps `void` for members only -- its top-level thunks were not examined.
        # A Java `CharSequence` result is accepted where a String one is: `enc` encodes a
        # returned String, and any other CharSequence comes back `ref|<class>` and is
        # refused per case by name (`returned a ...: no faithful Core encoding`).
        returns = JAVA_PRIM + (("void",) if instance or not kotlin else ()) \
            + (() if kotlin else ("java.lang.CharSequence",))
        boxed_args = () if kotlin else tuple(JAVA_BOXED)
        boxed_rets = () if kotlin else JAVA_BOXED_RETURNS
        coll_args = () if kotlin else collection_params
        # Varargs export as an array (`String...` is `java.lang.String[]`), and the model
        # has no faithful one: `a.length` exports as `sizeOf`, which the exporter holes
        # under the Java dialect (`op:sizeOf:array-length` -- it used to fold to a byte
        # count, silently mistranslating the loop bound), so any body reading it is
        # non-comparable, and an out-of-range index raises `IndexError` in Core where the
        # JVM raises `ArrayIndexOutOfBoundsException`. Refuse before the signature kinds
        # are checked. (Kotlin keeps its generic refusal below: its arrays were not
        # examined.)
        array = None if kotlin else next((t for t in args + [m.group("ret")] if "[" in t), None)
        if array:
            skipped[f["name"]] = (
                "array signature: %s -- the model has no faithful Java array "
                "(`.length` is the `op:sizeOf:array-length` hole; an out-of-range "
                "index raises IndexError in Core, ArrayIndexOutOfBoundsException on "
                "the JVM)" % array)
            continue
        # A Kotlin member: a project class in the signature may be an enum, which the model
        # spells `fnref "<enum>$<ENTRY>"`; the driver decides, and refuses any other class
        # by name. Members are called without a thunk; a top-level function's thunk would
        # have to name the type, and one the thunk cannot see would sink its whole file.
        # (Java's corpus enums, `enums`, are heap cells instead; the two never mix.)
        enum_ok = kotlin_enum_candidate if kotlin and instance else (lambda t: False)
        bad = [a for a in args if a not in JAVA_ARG_TYPES and a not in boxed_args
               and a not in coll_args and a not in enums and not enum_ok(a)]
        ret = m.group("ret")
        if not bad and ret not in returns and ret not in boxed_rets and ret not in enums \
                and not enum_ok(ret):
            bad = [ret]
        if bad:
            first = bad[0]
            skipped[f["name"]] = ("non-primitive signature" if kotlin else
                                  "non-primitive signature: %s is not primitive, String, "
                                  "a cached box or a corpus enum" % first)
            continue
        src = os.path.join(src_root, f.get("file", ""))
        if not os.path.exists(src):
            skipped[f["name"]] = "source file not found under the corpus root"
            continue
        if any(t in enums or t in JAVA_BOXED_RETURNS for t in args + [ret]):
            extended.add(f["name"])
        if any(t in collection_params for t in args):
            collections_typed.add(f["name"])
        if instance:
            members.add(f["name"])
        if any(map(enum_ok, args + [ret])):
            enum_typed += 1
        cands.append((f, m, args, src))
    info["primitive_static_candidates"] = len(cands) - len(members)
    info["primitive_instance_candidates"] = len(members)
    if kotlin:
        info["kotlin_enum_typed_candidates"] = enum_typed
    if not kotlin:
        # The subset of those candidates whose signature uses a box or an enum, and the
        # instance methods of an enum (run on one of its constants).
        info["boxed_or_enum_signature_candidates"] = len(extended)
        info["collection_signature_candidates"] = len(collections_typed)
        info["enum_receiver_candidates"] = sum(
            1 for f, m, _, _ in cands if f["params"][0:1] == ["this"] and m.group("cls") in enums)
    if not cands:
        return [], info, skipped
    compiled = set()
    classpath = classes
    if kotlin:
        kotlin_files = {c[3] for c in cands}
        names, failures, runtime = runtime_backends.compile_kotlin(src_root, cands, work, info)
        skipped.update(failures)
        cands = [(f, JAVA_SIG.match(names[f["name"]]), args, src)
                 for f, _, args, src in cands if f["name"] in names]
        compiled.update(c[3] for c in cands)
        info["files_candidate"] = len(kotlin_files)
        if "compile_failing_files" in info:
            info["files_failed"] = len(kotlin_files - compiled)
        classpath += os.pathsep + runtime
    candidate_sources = [] if kotlin else sorted({c[3] for c in cands})
    # Give javac the project's own source roots so intra-project references resolve.
    source_roots = java_source_roots(candidate_sources)
    extra_roots = [r for r in os.environ.get(JAVA_SOURCEPATH_ENV, "").split(os.pathsep) if r]
    for root in extra_roots:
        if not os.path.isdir(root):
            info["driver"] = "%s names a missing directory: %s" % (JAVA_SOURCEPATH_ENV, root)
            return [], info, skipped
    if extra_roots:
        info["extra_source_roots"] = extra_roots
    source_roots = source_roots + [r for r in extra_roots if r not in source_roots]
    sourcepath = ["-sourcepath", os.pathsep.join(source_roots)] if source_roots else []
    dependencies = os.environ.get(JAVA_CLASSPATH_ENV, "").strip(os.pathsep)
    processors = os.environ.get(JAVA_PROCESSORPATH_ENV, "").strip(os.pathsep)
    if dependencies:
        info["dependency_classpath"] = dependencies.split(os.pathsep)
        sourcepath += ["-cp", dependencies]
        classpath += os.pathsep + dependencies
    if processors:
        info["processor_path"] = processors.split(os.pathsep)
    processing = ["-processorpath", processors] if processors else ["-proc:none"]
    failure_causes = collections.Counter()
    for src in candidate_sources:
        # `-proc:none` keeps a project's annotation processors off our compile path;
        # implicit compilation stays ON so classes pulled in via -sourcepath land in
        # `classes/` and are present on the classpath when the driver runs.
        r = sandbox.sandboxed(["javac", "-nowarn", *processing, *sourcepath,
                               "-d", classes, src], cwd=work, work=work).run(
            capture_output=True, text=True, start_new_session=True)
        if r.returncode == 0:
            compiled.add(src)
        else:
            last = (r.stderr.strip().splitlines() or ["?"])[-1]
            failure_causes[java_failure_category(r.stderr)] += 1
            for f, _, _, s2 in cands:
                if s2 == src:
                    skipped[f["name"]] = "javac failed: " + last[:70]
    info["files_compiled"] = len(compiled)
    if not kotlin:
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
    r = sandbox.sandboxed(["javac", "-nowarn", "-d", classes,
                           os.path.join(work, "AutoformDriver.java")], cwd=work, work=work).run(
        capture_output=True, text=True, start_new_session=True)
    if r.returncode != 0:
        info["driver"] = "failed to compile: " + r.stderr[:200]
        return [], info, skipped
    # The static state each candidate's call tree reads (Java only). A read `C.f` is
    # bound when the class is explicit (`.fnref`) or a simple name that `JavaNames`
    # binds; the JVM reports the value immediately before the call, and the case gives
    # Core exactly that value in a holder object the globals frame names
    # (`javaStaticKey`). Reads the scan does not reach stay holes in the model.
    names = JavaNames(src_root, universe, all_roots) if not kotlin else None
    by_name = {f["name"]: f for f in universe}
    refs_of = {}

    def tree_reads(f):
        seen, todo, reads = {f["name"]}, [f], set()
        while todo and len(seen) <= JAVA_CALL_TREE_LIMIT:
            g = todo.pop()
            if g["name"] not in refs_of:
                refs_of[g["name"]] = java_body_refs(g.get("body"))
            r, callees = refs_of[g["name"]]
            reads |= r
            for c in sorted(callees):
                if c in by_name and c not in seen:
                    seen.add(c)
                    todo.append(by_name[c])
        requests, simple = set(), {}
        # A static WRITE through a bound simple name would change one holder while a
        # read through another spelling of an inherited field sees another: no static
        # state is given to such a call tree, so its static reads stay holes.
        if any(kind == "write" and names.bound(base) for kind, base, _ in reads):
            return None, {}
        for kind, base, field in reads:
            if kind == "write":
                continue
            cls = base if kind == "fq" else names.bound(base)
            if cls:
                requests.add((cls, field))
                if kind == "simple":
                    simple[base] = cls
        return sorted(requests), simple

    def tree_queries(f):
        """Whether any function of f's call tree queries a collection by EQUALITY
        (`contains`, the one equality query Core answers for a list): Core encodes
        every numeric box kind as one int, so a cross-kind query could diverge (an
        Integer element `equals` a Long of the same value: false on the JVM, true in
        Core) -- a seeded BOX element is then refused. A String (content) or an enum
        (identity) element is exact, and a map key is a String or an enum by the same
        rule. A tree past JAVA_CALL_TREE_LIMIT is not fully scanned: fail CLOSED, the
        unseen `contains` may be anywhere."""
        seen, todo = {f["name"]}, [f]
        while todo:
            if len(seen) > JAVA_CALL_TREE_LIMIT:
                return True
            g = todo.pop()
            stack = [g.get("body")]
            while stack:
                node = stack.pop()
                if isinstance(node, dict):
                    if node.get("k") == "mcall" and node.get("m") == "contains":
                        return True
                    stack.extend(v for v in node.values() if isinstance(v, (dict, list)))
                elif isinstance(node, list):
                    stack.extend(node)
            if g["name"] not in refs_of:
                refs_of[g["name"]] = java_body_refs(g.get("body"))
            for c in sorted(refs_of[g["name"]][1]):
                if c in by_name and c not in seen:
                    seen.add(c)
                    todo.append(by_name[c])
        return False

    calls, plan = [], []
    statics_requested = static_writers = 0
    for f, m, argtypes, _ in cands:
        requests, simple = tree_reads(f) if not kotlin else ([], {})
        queries = (tree_queries(f)
                   if any(t in collection_params for t in argtypes) else False)
        if requests is None:
            requests, static_writers = [], static_writers + 1
        statics_requested += bool(requests)
        wanted_enums = sorted({enums[t] for t in argtypes + [m.group("ret")] if t in enums}
                              | ({enums[m.group("cls")]} if f["params"][0:1] == ["this"]
                                 and m.group("cls") in enums else set()))
        env = [str(len(requests))] + [x for req in requests for x in req] \
            + [str(len(wanted_enums))] + wanted_enums
        spool, mined_ints = STRING_POOL, []
        if LITERAL_INPUTS:
            # The literals of the function and its file (`--literal-inputs`), from the
            # export, so the cross-revision run and its control draw the same strings.
            # `stats=info`: a literal Lean cannot represent (a lone surrogate) is dropped
            # and counted in `literals_unencodable` instead of raising at `v.encode()`.
            mined, mined_ints = runtime_backends.mined_literals(f, universe, EXTRA_LITERALS.get(f["name"], ()),
                                                                stats=info)
            spool = list(dict.fromkeys(STRING_POOL + runtime_backends.string_inputs(mined)))
            mined_ints = runtime_backends.integer_inputs(mined_ints)
        for iteration in range(max(1, ncases)):
            vals, enc = [], []
            for t in argtypes:
                if t in ("java.lang.String", "java.lang.CharSequence"):
                    # Java: `null` is an exceptional input for a reference parameter.
                    # Not Kotlin, whose `String` parameters are non-null by type.
                    if spool is STRING_POOL:
                        v = random.choice(spool + ([] if kotlin else [None]))
                    else:
                        # A longer pool must not make null rarer than the fixed pool did
                        # (1 in 9): a regression on the null input is as likely to be seen.
                        v = (None if not kotlin and random.random() < 1 / (len(STRING_POOL) + 1)
                             else random.choice(spool))
                    vals.append(("unit",) if v is None else ("str", v))
                    enc += [t, "!" if v is None else base64.b64encode(v.encode()).decode()]
                elif t == "boolean" or t == "java.lang.Boolean":
                    v = random.choice([True, False])
                    vals.append(("bool", v))
                    enc += [t, "true" if v else "false"]
                elif t in enums:
                    # The driver picks constant `k mod (n+1)`, or null when that is n, and
                    # says which; the value becomes a reference to that constant's cell.
                    vals.append(("enumarg", len(vals), enums[t]))
                    enc += ["enum:" + enums[t], str(iteration + len(vals))]
                elif t in JAVA_BOXED:
                    pool = JAVA_BOX_POOL.get(JAVA_BOXED[t], JAVA_BOX_INT_POOL)
                    v = pool[(iteration + len(vals)) % len(pool)]
                    vals.append(("int", v))
                    enc += [t, str(v)]
                elif t in ("float", "double"):
                    v = [0.0, 1.5, -2.25, 16777216.0, -0.0][iteration % 5]
                    vals.append(Encoder().enc(v))
                    enc += [t, str(v)]
                elif t in collection_params:
                    # A seeded collection: the draw is a function of the iteration and
                    # position (as for an enum), so base and head run identical inputs;
                    # the driver builds the value (0/1/2 elements) and reports the encoding
                    # on an `A` line. `:q` marks a call tree that queries a collection by
                    # equality -- the driver then refuses a BOXED element, whose kind
                    # Core's int encoding conflates.
                    vals.append(("collarg", len(vals)))
                    enc += ["jcoll:" + t + (":q" if queries else ""),
                            str(iteration + len(vals))]
                elif t not in JAVA_ARG_TYPES:
                    # A Kotlin enum parameter: the driver picks the entry and reports it
                    # in the Kotlin spelling (`ktenum:`, never null; Java's corpus enums
                    # took the `enum:` branch above and become heap cells).
                    vals.append(None)
                    enc += ["ktenum:" + t, str(iteration + len(vals))]
                else:
                    bits = {"byte": 8, "short": 16, "char": 16, "int": 32, "long": 64}[t]
                    hi = (1 << (bits if t == "char" else bits - 1)) - 1
                    lo = 0 if t == "char" else -(1 << (bits - 1))
                    pool = [0, 1, hi, lo, 31, 32, 63, 64]
                    # KNOWN DEFECT, deliberately NOT fixed here: the mined ints are
                    # appended AFTER the eight fixed values and the draw is
                    # `pool[(iteration + position) % len(pool)]`, so a mined constant is
                    # reached only once `iteration + position >= 8`; with the usual
                    # per-function case count most mined ints are never drawn, and
                    # `--literal-inputs` adds little for integer parameters. Changing the
                    # order or the draw changes which inputs every recorded JVM run
                    # used: it needs a basis bump to literal-inputs-v2 and re-measurement.
                    pool += [x for x in mined_ints if lo <= x <= hi and x not in pool]
                    v = pool[(iteration + len(vals)) % len(pool)]
                    vals.append(("int", v))
                    enc += [t, str(v)]
            instance = f["name"] in members
            on_enum = enums.get(m.group("cls")) if instance else None
            # A Kotlin member runs on the receiver the driver finds for its class (`kt:`);
            # an enum's entry is chosen by the iteration, so the entries are spread. A Java
            # enum's instance method runs on constant `iteration mod n` (`enum:`).
            target = (("kt:%s:%d" % (m.group("cls"), iteration)) if instance and kotlin
                      else ("enum:%s#%d" % (on_enum, iteration)) if on_enum
                      else ("new:" if instance else "") + m.group("cls"))
            calls.append("|".join([str(len(calls)), target,
                                   m.group("meth"), str(len(argtypes))] + enc
                                  + ([] if kotlin else env)))
            plan.append((f["name"], vals, instance, m.group("cls").rsplit(".", 1)[-1],
                         m.group("ret") == "void", simple, on_enum,
                         this_uses(f.get("body"), m.group("cls"), by_name) if instance and kotlin
                         else None))
    if not kotlin:
        info["candidates_reading_statics"] = statics_requested
        info["candidates_writing_statics"] = static_writers
    # `--add-opens`: the driver reads the collection behind a `Collections.unmodifiable*`
    # view to check it compares by `equals` (a TreeMap with a comparator does not).
    launch = sandbox.sandboxed(["java", "--add-opens", "java.base/java.util=ALL-UNNAMED",
                                "-cp", classpath, "AutoformDriver"], cwd=work, work=work)
    info["sandbox"] = launch.record
    driver_failure = None
    try:
        out = launch.run(input="\n".join(calls) + "\n", capture_output=True, text=True,
                         timeout=JVM_DRIVER_TIMEOUT, start_new_session=True)
    except subprocess.TimeoutExpired as e:
        # A hung driver used to escape as a traceback and no conformance.json at all.
        # Every planned call is unusable with this reason -- partial answers from a run
        # that was killed mid-way are not read, so a stuck case cannot look like a run
        # that compared the rest cleanly.
        driver_failure = "driver timed out after %d s" % JVM_DRIVER_TIMEOUT
        info["driver_timed_out_after_s"] = JVM_DRIVER_TIMEOUT
        out = subprocess.CompletedProcess(launch.argv, None, stdout="",
                                          stderr=runtime_backends.output_tail(e.stderr))
        print("  JVM %s" % driver_failure)
    info["driver_returncode"] = out.returncode
    if out.returncode or (out.stderr or "").strip():
        info["driver_stderr_tail"] = runtime_backends.output_tail(out.stderr)
        if out.returncode:
            print("  JVM driver exited with rc=%s; see conformance.json driver_stderr_tail"
                  % out.returncode)
    phases = lambda: {"pre": [], "post": []}
    got, state = {}, collections.defaultdict(phases)
    statics, consts = collections.defaultdict(phases), collections.defaultdict(phases)
    cfields = collections.defaultdict(lambda: collections.defaultdict(list))
    badenum = collections.defaultdict(dict)
    enumargs = collections.defaultdict(dict)
    kinds = {}
    for line in out.stdout.splitlines():
        p = line.split("|")
        tag, idx = p[0][:1], p[0][1:]
        if len(p) >= 2 and p[0].isdigit():
            got[int(p[0])] = p[1:]
        elif not idx.isdigit() or len(p) < 3:
            continue
        elif tag == "S" and len(p) >= 4 and p[1] in ("pre", "post"):
            state[int(idx)][p[1]].append((p[2], p[3], "|".join(p[4:])))
        elif tag == "A":
            # Java: the constant's NAME ("" for null; position -1 is an enum receiver);
            # a seeded collection argument reports its whole `coll|...` encoding.
            # Kotlin: the entry's model name `<enum>$<ENTRY>`, a `Val.fn`.
            enumargs[int(idx)][int(p[1])] = "|".join(p[2:])
        elif tag == "R" and len(p) == 3:
            # Kotlin: the receiver's kind and the model's name for it.
            kinds[int(idx)] = (p[1], p[2])
        elif tag == "G" and len(p) >= 7:
            statics[int(idx)][p[1]].append((p[2], p[3], p[4], p[5], "|".join(p[6:])))
        elif tag == "K" and len(p) >= 4:
            consts[int(idx)][p[1]].append((p[2], p[3]))
        elif tag == "F" and len(p) >= 7:
            cfields[int(idx)][(p[1], p[2], p[3])].append((p[4], p[5], "|".join(p[6:])))
        elif tag == "X" and len(p) >= 4:
            badenum[int(idx)].setdefault(p[2], "|".join(p[3:]))

    def value(kind, payload, cells=None):
        """A driver-encoded value as a case value; None when it has no Core encoding.
        `cells` maps (enum, constant) to the heap cell of that constant."""
        if kind == "str":
            return ("str", base64.b64decode(payload).decode())
        if kind == "bool":
            return ("bool", payload == "true")
        if kind == "int":
            return ("int", int(payload))
        if kind == "float":
            return ("float", int(payload))
        if kind == "null":
            return ("unit",)
        if kind == "enum" and kotlin:
            # Kotlin: the model's own spelling of an entry, `Val.fn "<enum>$<ENTRY>"`.
            return ("fn", payload)
        if kind == "enum" and cells is not None:
            # Java: a reference to the heap cell laid out for constant `<enum>#<NAME>`.
            enum, _, const = payload.partition("#")
            return ("ref", cells[(enum, const)]) if (enum, const) in cells else None
        if kind == "coll" and cells is not None:
            # A read-only collection is an UNBOXED `.list`/`.dict`: Core's mutating
            # methods on an unboxed container are holes, as `add` on `Set.of` throws.
            shape, _, data = payload.partition("|")
            items = []
            for elem in base64.b64decode(data).decode().split("\n")[:-1]:
                k, _, rest = elem.partition("|")
                v = value(k, rest, cells)
                if v is None:
                    return None
                items.append(v)
            if shape == "M":
                return ("dict", list(zip(items[0::2], items[1::2])))
            return ("list", items)
        return None

    def receiver(cls, fields, cells):
        """One heap cell from reported fields, or the reason it cannot be one."""
        cell = []
        for fname, kind, payload in fields:
            if kind == "dup":
                return "receiver field %r is declared twice in the class hierarchy" % fname
            if kind == "platform":
                return "receiver extends %s: its private state is not readable" % fname
            v = value(kind, payload, cells)
            if v is None:
                return "receiver field %r holds a %s: no faithful Core encoding" % (
                    fname, payload or kind)
            cell.append((fname, v))
        return [cls, cell]

    def static_state(i, first):
        """Pre- and post-call cells for call `i`'s static holders and enum constants, the
        constants' cell indices, and the globals bindings; or a refusal string.

        Layout after the receiver (index `first`): one holder per class with a reported
        static, then every constant of every enum the state names, in the JVM's order."""
        layout = {}
        for enum, const in consts[i]["pre"]:
            if enum not in badenum[i]:
                layout.setdefault((enum, const), None)
        holders = sorted({canon for _, canon, _, kind, _ in statics[i]["pre"]
                          if canon and kind != "bad"})
        for k, key in enumerate(layout):
            layout[key] = first + len(holders) + k
        pre_cells, post_cells, refused = [], [], collections.Counter()
        for when, out_cells in (("pre", pre_cells), ("post", post_cells)):
            fields = collections.defaultdict(list)
            for req, canon, field, kind, payload in statics[i][when]:
                v = None if kind == "bad" else value(kind, payload, layout)
                if v is None:
                    if when == "pre":
                        refused[payload if kind == "bad" else "no Core encoding"] += 1
                    continue
                if canon in holders:
                    fields[canon].append((field, v))
            out_cells += [[JAVA_STATIC_HOLDER + c, sorted(fields[c])] for c in holders]
            for enum, const in layout:
                cell = []
                for fname, kind, payload in cfields[i][(when, enum, const)]:
                    v = value(kind, payload, layout)
                    if v is None:
                        return ("enum constant %s.%s field %r: %s"
                                % (enum, const, fname, payload or "no Core encoding"))
                    cell.append((fname, v))
                out_cells.append([enum.rsplit(".", 1)[-1], cell])
        if [c[0] for c in pre_cells] != [c[0] for c in post_cells] or \
                [[k for k, _ in c[1]] for c in pre_cells] != [[k for k, _ in c[1]] for c in post_cells]:
            return "static state after the call was not reported in full"
        glob = []
        for req, canon, _, kind, _ in statics[i]["pre"]:
            if canon in holders:
                ref = ("ref", first + holders.index(canon))
                for key in {java_static_key(canon), java_static_key(req)}:
                    if (key, ref) not in glob:
                        glob.append((key, ref))
        return pre_cells, post_cells, layout, glob, refused

    cases, unusable = [], {}
    static_refusals, with_enums = collections.Counter(), 0
    receiver_kinds = collections.Counter()
    for i, (name, vals, instance, cls, void, simple, on_enum, uses) in enumerate(plan):
        r = got.get(i)
        if r is None:
            unusable[name] = driver_failure or "no answer from the JVM driver"
            continue
        if r[0] == "CTOR":
            unusable[name] = "receiver not built: " + (r[1] if len(r) > 1 else "?")
            continue
        if r[0] == "BAD":
            unusable[name] = r[1] if len(r) > 1 else "?"
            continue
        if r[0] == "ARG":
            unusable[name] = "argument not built: " + (r[1] if len(r) > 1 else "?")
            continue
        if None in vals:
            # Kotlin enum arguments: the entry the driver chose, as a `Val.fn`.
            vals = [("fn", enumargs[i][j]) if v is None and j in enumargs[i] else v
                    for j, v in enumerate(vals)]
            if None in vals:
                unusable[name] = "enum argument not reported by the JVM driver"
                continue
        first = 1 if instance and not on_enum else 0
        built = static_state(i, first)
        if isinstance(built, str):
            unusable[name] = built
            continue
        pre_cells, post_cells, layout, glob, refused = built
        static_refusals.update(refused)
        # Simple names (`Codes.CODES`) are bound to the holder of the class they denote.
        canon_of = {req: canon for req, canon, _, _, _ in statics[i]["pre"] if canon}
        for simple_name, cls_name in sorted(simple.items()):
            key = java_static_key(canon_of.get(cls_name, cls_name))
            ref = next((v for k, v in glob if k == key), None)
            if ref is not None:
                glob.append((simple_name, ref))
        args, why = [], None
        for v in vals:
            if v[0] == "enumarg":
                const = enumargs[i].get(v[1])
                if const == "":
                    v = ("unit",)
                elif (v[2], const) not in layout:
                    why = ("enum argument has no heap cell: %s"
                           % badenum[i].get(v[2], "constant not reported"))
                    break
                else:
                    v = ("ref", layout[(v[2], const)])
            elif v[0] == "collarg":
                # The driver seeded the collection and reported its encoding on an
                # `A` line; Core gets exactly the value the JVM was given, as for a
                # read-only static collection (`layout` names the cells of any enum
                # element the collection holds).
                payload = enumargs[i].get(v[1], "")
                kind, _, rest = payload.partition("|")
                built = value(kind, rest, layout) if kind else None
                if built is None:
                    why = "collection argument not built: " + (
                        rest if kind == "bad"
                        else "no faithful Core encoding" if kind
                        else "not reported by the JVM driver")
                    break
                v = built
            args.append(v)
        if why:
            unusable[name] = why
            continue
        if r[0] == "OK":
            outcome = value(r[1], "|".join(r[2:]) if len(r) > 2 else "", layout)
            if outcome is None and r[1] == "enum":
                unusable[name] = "returned an enum constant whose type was not laid out before the call"
                continue
            if outcome is None and r[1] == "ref":
                unusable[name] = "returned a %s: no faithful Core encoding" % (
                    r[2] if len(r) > 2 else "?")
                continue
            if outcome is None or (outcome == ("unit",) and not void):
                unusable[name] = "returned null: no faithful Core counterpart"
                continue
            outcome = ("val", outcome)
        elif r[0] == "EXN":
            outcome = ("exn", r[1])
        else:
            unusable[name] = "JVM driver error: " + (r[1] if len(r) > 1 else "?")
            continue
        case = {"name": name, "heap": pre_cells, "self": None,
                "args": args, "outcome": outcome, "origin": "random"}
        if glob:
            case["globals"] = glob
        if instance and kotlin:
            if i not in kinds:
                unusable[name] = "receiver kind not reported by the JVM driver"
                continue
            kind, model_name = kinds[i]
            encoding = singleton_encoding(kind, uses)
            if encoding not in ("value", "heap"):
                unusable[name] = encoding
                continue
            if encoding == "value":
                receiver_kinds[kind + " (value)"] += 1
                # `this` is only ever a VALUE in this body, and the model spells this
                # singleton `fnref model_name`: the case passes exactly that value. No
                # field is read or written through `this`, so there is no heap state.
                case.update(self=("fn", model_name), args=[("fn", model_name)] + args,
                            origin="constructed")
                cases.append(case)
                continue
        if on_enum:
            # The receiver IS one of the constants' cells; its fields after the call are
            # the constants' post-state, compared as a heap observation.
            const = enumargs[i].get(-1)
            if (on_enum, const) not in layout:
                unusable[name] = "enum receiver has no heap cell: %s" % badenum[i].get(
                    on_enum, "constant not reported")
                continue
            me = ("ref", layout[(on_enum, const)])
            case.update(self=me, post_heap=post_cells, args=[me] + args, origin="constructed")
        elif instance:
            pre = receiver(cls, state[i]["pre"], layout)
            post = receiver(cls, state[i]["post"], layout)
            if isinstance(pre, str) or isinstance(post, str):
                unusable[name] = pre if isinstance(pre, str) else post
                continue
            if [k for k, _ in pre[1]] != [k for k, _ in post[1]]:
                unusable[name] = "receiver state after the call was not reported in full"
                continue
            # The rendered method takes `this` as its first parameter and reads `self`;
            # both name the one receiver object.
            case.update(heap=[pre] + pre_cells, self=("ref", 0), post_heap=[post] + post_cells,
                        args=[("ref", 0)] + args, origin="constructed")
            if kotlin:
                receiver_kinds[kinds[i][0] + " (heap)"] += 1
        with_enums += bool(layout)
        cases.append(case)
    skipped.update(unusable)
    if kotlin:
        info["kotlin_receiver_cases"] = dict(sorted(receiver_kinds.items()))
    info["cases_built"] = len(cases)
    if not kotlin:
        info["cases_with_static_state"] = sum(1 for c in cases if c.get("globals"))
        info["cases_with_enum_cells"] = with_enums
        if static_refusals:
            info["static_fields_not_bound"] = dict(static_refusals.most_common(12))
    return cases, info, skipped


# Drivers consume Joern identities and signatures; no duplicate source parser.
def go_backend(src_root, holefree, ncases):
    return runtime_backends.go_backend(src_root, holefree, ncases, WORK)


def node_backend(src_root, holefree, ncases, lang, universe=None):
    literals = None
    if LITERAL_INPUTS:
        def literals(f):
            mined, _ = runtime_backends.mined_literals(f, universe or holefree,
                                                       EXTRA_LITERALS.get(f["name"], ()))
            return runtime_backends.string_inputs(mined)
    return runtime_backends.node_backend(src_root, holefree, ncases, lang, WORK, literals=literals,
                                         universe=universe)


# ---------------------------------------------------------------------------- main

def sandbox_record():
    """The confinement of the running oracle process, for conformance.json."""
    inherited = sandbox.active()
    if inherited:
        return dict(inherited, inherited=True)
    if sandbox.policy() == "off":
        return sandbox.off_record()
    return sandbox.none_record("differential.main() was entered in process; the oracle "
                               "re-executes itself under the sandbox only from its "
                               "command-line entry (python scripts/differential.py ...)")


def sandbox_reexec():
    """Re-execute the whole oracle inside the sandbox.

    The Python leg runs the corpus's test suite under `sys.settrace` in THIS process, so
    the process itself is what has to be confined: no network, writes only to the
    report directory (cwd), the Lean build tree (`.lake`), the oracle cache and a private
    TMPDIR. Without a mechanism the run is REFUSED, with a conformance.json that says so
    (a stale report from an earlier run must not be read as this run's result), unless
    `AUTOFORM_SANDBOX=off`, which the report records."""
    if sandbox.active() or sandbox.policy() == "off":
        return
    repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    argv = sys.argv[1:]
    cache = (os.path.abspath(argv[argv.index("--cache-dir") + 1]) if "--cache-dir" in argv
             else os.path.join(repo, ".autoform-work"))
    os.makedirs(cache, exist_ok=True)
    writable = [os.getcwd(), os.path.join(repo, ".lake"), cache]
    # The trees the `unshare` fallback binds read-only: the corpus and its test suite
    # (the mechanisms that deny writes everywhere else do not need the list).
    subject = [a for i, a in enumerate(argv) if os.path.isdir(a)
               and (i == 0 or argv[i - 1] != "--cache-dir")]
    if os.environ.get("AUTOFORM_DIFF_KEEP"):
        os.makedirs(os.environ["AUTOFORM_DIFF_KEEP"], exist_ok=True)
        writable.append(os.environ["AUTOFORM_DIFF_KEEP"])
    box = _tempfile.mkdtemp(prefix="autoform_sandbox_%d_" % os.getpid())
    try:
        launch = sandbox.sandboxed([sys.executable, *sys.argv], cwd=os.getcwd(), work=box,
                                   writable=writable, read_only=subject)
    except sandbox.SandboxUnavailable as exc:
        __import__("shutil").rmtree(box, ignore_errors=True)
        print("REFUSING to run: " + str(exc))
        json.dump({"status": "REFUSED: no sandbox", "sandbox": sandbox.none_record(str(exc)),
                   "argv": sys.argv[1:], "agree": 0, "total": 0, "divergences": 0,
                   "inconclusive": 0, "rate": "n/a"},
                  open("conformance.json", "w"), indent=1)
        sys.exit(2)
    env = dict(launch.env, AUTOFORM_SANDBOX_BOX=box)
    os.execve(launch.argv[0], launch.argv, env)


CAP_FLOOR = 2              # cases each function keeps under the case cap, when it has them


def c_plan_cap_record(plan, limit):
    """Accounting for the C backend's `plan[:limit]` cut, computed BEFORE the cut and
    without changing it: how many planned calls fall past the cap, which functions lose
    any call, and which lose every call. `plan` is the C backend's list of
    `(function, args)` pairs. All zero/empty when the plan fits."""
    kept = {f["name"] for f, _ in plan[:limit]}
    tail = [f["name"] for f, _ in plan[limit:]]
    return {"dropped_c_plan": len(tail),
            "functions_affected_c_plan": sorted(set(tail)),
            "functions_dropped_c_plan": sorted(set(tail) - kept)}


def cap_cases(cases, limit, rng=random):
    """`cases` cut to `limit`, and how many byte-identical duplicates went first.

    Suite-traced cases are kept first, as before (they are the evidence the Python
    oracle exists for). Within each origin a function's first `CAP_FLOOR` cases (in a
    shuffled order) are seated before any function's further cases, so a cap that drops
    cases does not drop whole functions: the CommonsLang3 run's plain random draw kept
    600 of 1087 cases and lost about 20 functions with the rest. Before the cut, a
    non-suite case identical to an earlier one -- name, inputs, heap, outcome, origin,
    all of it -- is dropped. Identical means the same `repr` (types and dict keys kept
    apart) AND the same plain-data JSON (no object whose `repr` could hide state, no
    NaN whose bits `repr` folds); a case that fails either is never a duplicate.
    Suite-traced cases are never deduplicated (their record ids key the changed-lines
    trace). `rng` is the module's seeded `random` unless a caller passes its own, so
    the same recording keeps the same cases."""
    if len(cases) <= limit:
        return list(cases), 0
    seen, unique = set(), []
    for c in cases:
        if c.get("origin") != "test-suite":
            try:
                key = (repr(c), json.dumps(c, sort_keys=True, allow_nan=False))
            except (TypeError, ValueError):
                key = None
            if key is not None:
                if key in seen:
                    continue
                seen.add(key)
        unique.append(c)
    duplicates = len(cases) - len(unique)
    shuffled = list(unique)
    rng.shuffle(shuffled)
    # Suite-traced cases first (stable, so the draw stays random within an origin); a
    # function's floor is counted in that order, so its suite cases fill it first.
    shuffled.sort(key=lambda c: c.get("origin") != "test-suite")
    seated, tiers = collections.Counter(), []
    for c in shuffled:
        tiers.append(((c.get("origin") != "test-suite", seated[c["name"]] >= CAP_FLOOR), c))
        seated[c["name"]] += 1
    # Seat order: suite floor, suite rest, other floor, other rest (`sorted` is stable).
    tiers.sort(key=lambda t: t[0])
    return [c for _, c in tiers[:limit]], duplicates


def skip_record(skipped, focus, sample=40):
    """The `backend_skipped*` fields of conformance.json. `backend_skipped` is a SAMPLE of
    at most `sample` per-function reasons (focused functions first, so a `--focus` caller
    reads its own); `backend_skipped_by_reason` counts EVERY skip by its reason's head --
    the text before the first `:`, so `non-primitive signature: X is ...` buckets with
    every other refused type -- and is the figure to aggregate. Counting the sample
    instead reported 25/13/2 of a 232-skip run."""
    by_reason = collections.Counter(str(reason).split(":", 1)[0].strip()
                                    for reason in skipped.values())
    return {"backend_skipped": dict(sorted(skipped.items(),
                                           key=lambda kv: kv[0] not in (focus or ()))[:sample]),
            "backend_skipped_sampled": len(skipped) > sample,
            "backend_skipped_total": len(skipped),
            "backend_skipped_by_reason": dict(sorted(by_reason.items(),
                                                     key=lambda kv: (-kv[1], kv[0])))}


def main():
    argv = [a for a in sys.argv[1:]]
    tests_override = None
    if "--tests" in argv:
        i = argv.index("--tests"); tests_override = argv[i + 1]; del argv[i:i + 2]
    # `--focus FILE` (JSON list of function names) keeps only the recorded/constructed/random
    # cases of those functions, BEFORE the case cap, so a change's functions are not
    # crowded out of the cap by the rest of the suite (the cap draws at random within an
    # origin). The runtime backends are also given only the focused functions
    # (`focus_population`), so a large corpus is not compiled and driven in full.
    # Recorded in conformance.json (`focus`); without it nothing changes.
    focus = None
    if "--focus" in argv:
        i = argv.index("--focus")
        with open(argv[i + 1], encoding="utf-8") as handle:
            focus = set(json.load(handle))
        del argv[i:i + 2]
    # `--wasm` turns on the sandboxed second C implementation. It is OPT-IN, and
    # deliberately so: it changes which cases are attempted and which are withheld from
    # the Lean comparison, so it changes the denominator. A flag that silently altered
    # the basis would make new rates look comparable to old ones when they are not.
    wasm_mode = "--wasm" in argv
    if wasm_mode: argv.remove("--wasm")
    # `--literal-inputs`: also draw string (and integer) inputs from the literals of each
    # function's body and file (`runtime_backends.mined_literals`), and `--literals FILE`
    # (JSON: function name -> extra strings, pr mode's head-revision literals) adds to
    # them. OPT-IN and recorded in the basis: it changes the sample. `--changed-lines
    # FILE` (JSON: source file -> changed line numbers of the tree being run) makes the
    # Python leg record which of those lines and branch outcomes the compared cases
    # executed (`change_coverage` in conformance.json).
    global LITERAL_INPUTS, EXTRA_LITERALS
    LITERAL_INPUTS = "--literal-inputs" in argv
    if LITERAL_INPUTS: argv.remove("--literal-inputs")
    if "--literals" in argv:
        i = argv.index("--literals")
        with open(argv[i + 1], encoding="utf-8") as handle:
            EXTRA_LITERALS = json.load(handle)
        del argv[i:i + 2]
        LITERAL_INPUTS = True
    # `--universe FILE`: a wider export than the model (pr mode's whole base export when
    # the model is the compared functions' cut), read by the JVM and Node backends for
    # name resolution, static reads and literal mining only. Nothing is compared from it.
    universe = None
    if "--universe" in argv:
        i = argv.index("--universe")
        universe = analysis_functions(deep_json.load(argv[i + 1]))
        del argv[i:i + 2]
    changed_lines = None
    if "--changed-lines" in argv:
        i = argv.index("--changed-lines")
        with open(argv[i + 1], encoding="utf-8") as handle:
            changed_lines = {k: set(v) for k, v in json.load(handle).items()}
        del argv[i:i + 2]
    # `--language js|ts|java|go|kotlin|python|c` names the runtime explicitly. The
    # extension vote stays the default because it cannot be wrong silently -- it refuses
    # on a mixed or unknown corpus -- but a corpus whose files carry no extension the
    # table knows (a generated fixture, a `.mjs`-only package renamed by a bundler)
    # needs a way to say what it is. The override is RECORDED in conformance.json.
    lang_override = None
    if "--language" in argv:
        i = argv.index("--language"); lang_override = argv[i + 1]; del argv[i:i + 2]
    # `--no-cache` forces every function back through the interpreter; `--cache-dir`
    # relocates the per-function verdict store (default `<repo>/.autoform-work/oracle`).
    use_cache = "--no-cache" not in argv
    if not use_cache: argv.remove("--no-cache")
    cache_dir = None
    if "--cache-dir" in argv:
        i = argv.index("--cache-dir"); cache_dir = argv[i + 1]; del argv[i:i + 2]
    ast_path, src_root, lean_mod = argv[0], argv[1], argv[2]
    ncases = int(argv[3]) if len(argv) > 3 else 5
    # What confines THIS process. The Python leg traces the corpus's test suite in
    # process, so the oracle re-executes itself inside the sandbox from its command-line
    # entry (`sandbox_reexec`); a `main()` entered in process (the test suite's fixture)
    # is not confined and says so. Each driver it spawns records its own launch.
    SANDBOX = sandbox_record()
    print("sandbox: %s%s" % (SANDBOX["mechanism"],
                             "" if SANDBOX.get("enforced") else " (NOT enforced: %s)" % SANDBOX.get("reason")))
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
                   "status": "REFUSED: unknown source language", "sandbox": SANDBOX,
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
        # v2: a returned dense Array or plain object is compared STRUCTURALLY (Node
        # encodes it as a list / string-keyed dict, Core's boxed result is read through
        # its payload, `unboxDeep`), where v1 skipped every such function; and the module
        # bindings a call tree reads are given to Core (`runtime_backends.node_reads`),
        # where v1 let Core read them as `undefined`.
        # An instance method of a module-scope class with a no-argument constructor is
        # attempted on a receiver the driver builds, its state compared before and after
        # the call (earlier v2 runs refused every instance method as "receiver fixture
        # required"): the attempted population is larger than such a run's.
        BASIS = "node-numeric-pool-v2"
        BASIS_NOTE = ("Node calls each module-scope function of the corpus on a fixed numeric "
                      "pool (0, 1, -1, 2^31-1, 2^32, 32, 64, -3.75, Infinity, NaN) cycled per "
                      "parameter -- NOT the corpus's own tests. Numbers are compared as IEEE "
                      "doubles (Core's small-integer representation of a JS Number is widened "
                      "before comparison). A returned dense Array or plain object (prototype "
                      "Object.prototype or null, enumerable string-keyed data properties, no "
                      "integer-like key) is compared by structure: element by element, and "
                      "key by key regardless of key order; object identity and aliasing "
                      "inside the result are not compared. The module-level bindings the "
                      "call tree reads are read from Node immediately before each call and "
                      "bound in Core's globals frame (an array or object as a boxed cell); a "
                      "binding the wire cannot carry refuses the case. An instance method of "
                      "a module-scope class whose constructor takes no arguments is called on "
                      "a fresh receiver Node builds with that constructor: the object's own "
                      "enumerable data properties are reported immediately before the call "
                      "and again after it (every array or plain object it or a module binding "
                      "holds as its own cell, so an alias is one address in the model), Core "
                      "starts from exactly that reported state, and the post-call state of "
                      "the receiver and of those cells is compared as well as the result. "
                      "Refused by name: a constructor that throws or takes arguments, a "
                      "getter or setter, an accessor, symbol or non-enumerable own property, "
                      "an inherited getter, setter or data property the body touches, a "
                      "private (#) member the body touches (not observable), and a property "
                      "value the wire cannot carry. Functions returning class "
                      "instances, other objects or promises, and functions not reachable at "
                      "module scope, are skipped and COUNTED under backend_skipped. "
                      "TypeScript runs through "
                      "`node --experimental-strip-types`: erasable annotations only.")
    elif lang in ("java", "kotlin"):
        # The two JVM languages share a driver but NOT a measurement basis: Java encodes a
        # corpus enum as heap cells and binds static state, Kotlin calls members on
        # singletons/entries and spells an enum as `Val.fn "<enum>$<ENTRY>"`. Their
        # attempted populations differ, so each has its own basis.
        # v2 (2026-10-10): `CharSequence` parameters are attempted (v1 refused them as
        # non-primitive), so the attempted population and the rates are not comparable
        # with a v1 report.
        # v3: Java instance methods with a primitive-or-String (or `void`) signature are
        # attempted on a receiver built by the class's no-arg constructor (v2 refused
        # every instance method), so the population differs from a v2 report.
        # java v4 (`jvm-signatures-statics-v4`): Java signatures with boxes and corpus
        # enums are attempted, a Java String parameter may be null, and the static fields
        # a call tree reads are given to Core as the JVM reports them; populations and
        # inputs differ from v3.
        # java v5 (`jvm-signatures-statics-v5`): static `void` methods and `CharSequence`
        # results are attempted, the case cap seats CAP_FLOOR cases per function (exact
        # duplicates dropped first) before a random fill, and every skip is counted by
        # reason (`backend_skipped_by_reason`), not only the 40 sampled.
        # kotlin v4 (`jvm-kotlin-receivers-v4`): Kotlin members are attempted (v3 refused
        # every one), and a project class in a member's signature is attempted as an enum,
        # so the population differs from a v3 Kotlin report.
        JVM_POOLS = ("Methods whose whole signature is primitive-or-String are called, "
                     "reflectively, on a fixed pool per type (0, 1, MAX, MIN, 31, 32, "
                     "63, 64 for integers; a fixed string list; 0.0, 1.5, -2.25, 2^24, -0.0 "
                     "for floats). A `CharSequence` parameter receives a String from the "
                     "same list. ")
        JVM_SKIPPED = ("Files that do not compile against the corpus's own source roots "
                       "(plus any roots named in AUTOFORM_JAVA_SOURCEPATH, recorded under "
                       "backend_info.extra_source_roots, and the dependency classpath and "
                       "processor path named by AUTOFORM_JAVA_CLASSPATH / "
                       "AUTOFORM_JAVA_PROCESSORPATH when supplied) are skipped and COUNTED.")
        if lang == "java":
            BASIS = "jvm-signatures-statics-v5"  # v5: void statics, CharSequence results, stratified case cap, full skip counts
            BASIS_NOTE = (JVM_POOLS +
                          "A String/CharSequence parameter may also be "
                          "null; a boxed Integer/Long/Short/Byte/Character/Boolean parameter "
                          "is drawn inside the JVM box cache (so `==` on boxes agrees with "
                          "value equality) and is never null; an enum the corpus declares is "
                          "drawn from its constants or null, each constant a heap cell holding "
                          "its instance fields; a boxed or enum RESULT is compared, as is a "
                          "`void` one (static or instance) and a `CharSequence` one that is a "
                          "String (any other CharSequence is refused per case). The static "
                          "fields the call tree reads (`C.f` with the class implicit or a "
                          "simple name bound the same way in every file) are read from the JVM "
                          "immediately before the call and bound in Core's globals frame: "
                          "scalars, Strings, enum constants, boxes inside the cache, and "
                          "read-only Set.of/Map.of/List.of/Collections.unmodifiable*/empty*/"
                          "singleton* collections of String or enum elements over an "
                          "equals-based collection; anything else is left unbound and counted "
                          "(backend_info.static_fields_not_bound), so its read is a hole. An "
                          "instance method (a `void` one included) runs on a "
                          "fresh receiver built by its class's non-private no-arg constructor "
                          "(an enum's instance method on one of its constants); "
                          "the receiver's instance fields, as the JVM reports them after "
                          "construction, are the object Lean starts from, and its fields after "
                          "the call are compared as well as the result (origin `constructed`). "
                          "A receiver holding a non-null reference that is not a String or an "
                          "enum constant, or that cannot be built, is refused by name, as are "
                          "other non-primitive signatures. " + JVM_SKIPPED)
        else:
            BASIS = "jvm-kotlin-receivers-v4"
            BASIS_NOTE = (JVM_POOLS +
                          "A Kotlin String parameter is never null (non-null by type), and no "
                          "static state is bound. A top-level function is called through a "
                          "compiled @JvmStatic thunk (an extension function's thunk calls it "
                          "on its first argument), primitive-or-String only. "
                          "A Kotlin member runs, without a thunk, on the receiver the JVM "
                          "driver finds for its class: an "
                          "`object`'s INSTANCE, a companion object, enum entries (spread across the "
                          "cases), or a fresh object from a non-private no-arg constructor (Kotlin "
                          "generates one when every primary-constructor parameter has a default). Its "
                          "state is the instance fields plus where Kotlin stores the receiver's "
                          "properties (an `object`'s are static fields of its class, a companion's of "
                          "the class that declares it, an enum entry's `name`/`ordinal` come from its "
                          "accessors); that state is the object Lean starts from and is compared after "
                          "the call. An enum value -- argument, result or field -- is the model's own "
                          "spelling `Val.fn \"<enum>$<ENTRY>\"` (never a heap cell, unlike Java); "
                          "an `object` or enum entry whose body "
                          "uses `this` only as a value is passed in that spelling instead of as an "
                          "object (a sibling member called on the same receiver counts its uses too), "
                          "and a body that needs both spellings, a companion used as a value, a "
                          "member calling a sibling through a qualified name (the export drops "
                          "the receiver), a receiver extending a platform class, a returned object and a "
                          "non-enum class in the signature are refused by name. " + JVM_SKIPPED)
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
    c_plan_cap = {}         # the C backend's pre-execution cut, when that backend ran
    # `--focus` narrows what the backends compile and run, not only what is kept.
    sampled = focus_population(holefree, focus, same_named=is_c)
    if missing:
        backend_status = "UNSUPPORTED: toolchain absent (%s)" % ", ".join(missing)
        print("  backend UNSUPPORTED: %s not on PATH — this language has NO runtime "
              "check, which is a gap in the evidence, not a pass." % ", ".join(missing))
    elif lang in ("java", "kotlin", "go", "js", "ts"):
        if lang in ("java", "kotlin"):
            cases, backend_info, backend_skipped = java_backend(src_root, sampled,
                                                                ncases, kotlin=lang == "kotlin",
                                                                universe=universe or funcs)
        elif lang == "go":
            cases, backend_info, backend_skipped = go_backend(src_root, sampled, ncases)
        else:
            cases, backend_info, backend_skipped = node_backend(src_root, sampled, ncases, lang,
                                                                universe=universe or funcs)
        if not cases:
            backend_status = ("UNSUPPORTED: no testable surface%s — "
                              % ("" if focus is None else " among the --focus functions")
                              + str(backend_info.get("note", backend_info)))
        print("  backend %s: %s; %d cases built"
              % (runtime, json.dumps(backend_info)[:160], len(cases)))
    elif is_c:
        cget = c_runtime(src_root, sampled, population=funcs)
        backend_info = getattr(cget, "info", {})
        backend_status = backend_info.get("status", "available" if cget else "unsupported: native compilation failed")
        backend_skipped.update(getattr(cget, "skipped", {}))
        if backend_info:
            with open("native-build.json", "w") as build_report:
                json.dump(backend_info, build_report, indent=2)
            print("  native C: %d/%d translation units compiled; %d entry points" % (
                backend_info.get("files_compiled", 0), backend_info.get("files_attempted", 0),
                backend_info.get("entry_points", 0)))
        cands = [f for f in sampled
                 if not f.get("isInit") and (focus is None or f["name"] in focus)]
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
            literals = (runtime_backends.integer_inputs(runtime_backends.mined_literals(f)[1])
                        if LITERAL_INPUTS else ())
            for args, origin in c_argument_cases(fn.argtypes, ncases, c_arg, boundaries=True,
                                                 literals=literals):
                plan.append((f, args))
                origins.append(origin)
        backend_info['input_strategy'] = ('first case all-zero; every other remaining case '
                                          'per-type width boundaries; the rest seeded random')

        # Bound execution itself, not only the later Lean harness. The cut is the plain
        # head of the plan (what it keeps is pinned by the recorded basis); what it drops
        # is now ACCOUNTED, in `case_cap` and the summary line, instead of leaving
        # `dropped: 0` on a run that never executed part of its plan.
        c_plan_cap = c_plan_cap_record(plan, MAX_TOTAL_CASES)
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
        if changed_lines and focus is not None:
            COVERAGE_KEYS.update(f["name"] for f in funcs
                                 if f["name"] in focus and f.get("file") in changed_lines)
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
        # The fingerprint must describe the tree the cases are recorded from. Taken
        # before this correction (as it is at the top of main) it covers nothing when no
        # AST path resolves under the uncorrected root, and the stability check at the
        # end then fails a healthy run with exit 2 -- CI read 94/94 agree as "not
        # evidence" that way on 2026-10-10. Re-take it against the corrected root.
        fingerprints = runtime_backends.source_fingerprints(src_root, funcs)
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
            diagnosis = diagnose_test_run(run)
            if diagnosis:
                run["diagnosis"] = diagnosis
                print("  " + diagnosis)
        if test_dirs and not traced:
            print("  (the suite produced no usable calls under %s — if it failed to even "
                  "collect, point %s (`autoform pr/source --python`) at an interpreter "
                  "that has the project's dependencies installed)"
                  % (sys.executable, ORACLE_PYTHON_ENV))

        # `--focus`: random and constructed cases are built for the focused functions
        # only. The traced suite run above is unchanged: it still records every wanted
        # function, because the instances and argument values it observes on siblings
        # are what a focused method's constructed cases are built from.
        if focus is not None:
            modlevel = [m for m in modlevel if m[0]["name"] in focus]
            methods = [m for m in methods if m[0]["name"] in focus]

        # (2) random integers for module-level functions (supplement, not substitute)
        for f, rel, qual in modlevel:
            mod = load_module(os.path.join(src_root, rel), src_root)
            if mod is None or not hasattr(mod, qual): continue
            fn = getattr(mod, qual)
            for _ in range(ncases):
                args = [random.randint(-20, 20) for _ in f["params"]]
                enc = encoder_factory()
                enc.freeze()
                recorder = coverage_recorder(f, fn)
                try:
                    with time_limit(2.0), recorder:
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
                    keep_coverage(cases[-1], recorder)
                except Unencodable as e:
                    stats['skip_unencodable_post'] = stats.get('skip_unencodable_post', 0) + 1
                    reasons = stats.setdefault('unencodable_reasons', {})
                    reason = f['name'] + ': post-state ' + str(e)
                    reasons[reason] = reasons.get(reason, 0) + 1
            if LITERAL_INPUTS:
                cases += literal_cases(f, fn, funcs, ncases, stats, encoder_factory)

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

    focus_record = None
    if focus is not None:
        kept = [c for c in cases if c["name"] in focus]
        focus_record = {"functions": sorted(focus), "cases_before": len(cases), "cases_kept": len(kept),
                        "backend_population": len(sampled),
                        "note": "runtime backends built cases for the focused functions only "
                                "(C: plus same-named definitions in their files, for the "
                                "ambiguity check); `cases_before` still counts suite-traced "
                                "Python cases of other functions, which the trace records"}
        print("focus: %d of %d recorded cases belong to the %d named function(s)"
              % (len(kept), len(cases), len(focus)))
        cases = kept
    case_cap = {"limit": MAX_TOTAL_CASES, "requested": CASE_CAP_SETTING,
                "recorded": len(cases), "dropped": 0}
    case_cap.update(c_plan_cap)
    if c_plan_cap.get("dropped_c_plan"):
        print("case cap: the C backend planned %d calls past the cap and never ran them "
              "(%d function(s) affected, %d lost whole)"
              % (c_plan_cap["dropped_c_plan"], len(c_plan_cap["functions_affected_c_plan"]),
                 len(c_plan_cap["functions_dropped_c_plan"])))
    if len(cases) > MAX_TOTAL_CASES:
        # The cap used to be a silent random sample over everything recorded: on the
        # cachetools 7.1.6 defect hunt (docs/evidence-cachetools.md) 523 suite-traced
        # cases competed with 3,900 synthesized ones for 600 seats, and the regression
        # test's calls lost the draw while the summary said "600 cases to compare now".
        # Suite-traced cases are the evidence this oracle exists for (source 1 above),
        # so they are kept first; the draw is still random within an origin, and what
        # was dropped is recorded and printed rather than implied. Within an origin each
        # function keeps up to CAP_FLOOR cases before any function gets more, and exact
        # duplicate cases go first (`cap_cases`), so the cap thins functions rather than
        # dropping them whole.
        before = collections.Counter(c.get("origin") for c in cases)
        functions_before = {c["name"] for c in cases}
        cases, duplicates = cap_cases(cases, MAX_TOTAL_CASES)
        after = collections.Counter(c.get("origin") for c in cases)
        case_cap.update(dropped=case_cap["recorded"] - len(cases),
                        duplicates_dropped=duplicates, per_function_floor=CAP_FLOOR,
                        functions_dropped=len(functions_before - {c["name"] for c in cases}),
                        dropped_by_origin={k: before[k] - after.get(k, 0) for k in before
                                           if before[k] - after.get(k, 0)})
        print("case cap: %d recorded, %d kept (suite-traced first, %d per function before "
              "any more), dropped %s (%d exact duplicates, %d functions lost whole)"
              % (case_cap["recorded"], len(cases), CAP_FLOOR,
                 ", ".join("%d %s" % (n, k) for k, n in sorted(case_cap["dropped_by_origin"].items())),
                 duplicates, case_cap["functions_dropped"]))

    if lang == 'python':
        BASIS += '+trace-returns-v1'
        BASIS_NOTE += (' Traced outcomes distinguish an executed return instruction from '
                       'exception unwinding, including returns of None after handled exceptions. '
                       'Ambiguous unwind types and suspended generator/coroutine frames are '
                       'counted as trace gaps, not fabricated call outcomes.')

    if lang == 'python' and stats.get('test_runs'):
        BASIS += '+closure-captures-v1'
        BASIS_NOTE += (' Suite-traced calls of a nested function that reads enclosing-scope '
                       'variables are refused (skip_closure_captures): a case carries arguments, '
                       'not the captured cells.')

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

    ORACLE_INTERPRETER = oracle_interpreter_record() if lang == 'python' else None
    if lang == 'python':
        # Which interpreter ran the suite and the native calls decides which modules
        # import at all, so it is part of what "compared" meant.
        if ORACLE_INTERPRETER["requested"]:
            BASIS += '+oracle-interpreter-v1'
        BASIS_NOTE += (' Native side: %s (Python %s, %s).'
                       % (ORACLE_INTERPRETER["path"], ORACLE_INTERPRETER["version"],
                          ORACLE_INTERPRETER["setting"]))
    runners = [r.get("runner") or {} for r in stats.get("test_runs", [])]
    if lang == 'python' and any(r.get("runner") == "pytest" for r in runners):
        BASIS += '+pytest-continue-collection-v1'
        BASIS_NOTE += (' The suite runs with --continue-on-collection-errors: a test module '
                       'that fails to import is reported (test_runs[].collection_errors) and '
                       'the others still run.')
        if any(str(r.get("project_addopts", "")).startswith("ignored") for r in runners):
            BASIS += '+pytest-addopts-ignored-v1'
            BASIS_NOTE += (' The project\'s pytest addopts were IGNORED (-o addopts=, %s=ignore): '
                           'options that select, deselect or parametrize tests did not apply.'
                           % PYTEST_ADDOPTS_ENV)

    if LITERAL_INPUTS:
        BASIS += '+' + runtime_backends.LITERAL_INPUTS_BASIS
        BASIS_NOTE += (' --literal-inputs: string-typed and unannotated parameters also draw '
                       'strings built from the literals of the function and its file (and '
                       'integers next to its integer literals); seeded per function, so the '
                       'same export yields the same inputs.')

    result = {"module": module_tag, "source_root": os.path.abspath(src_root),
              "sandbox": SANDBOX, "oracle_interpreter": ORACLE_INTERPRETER,
              "import_errors": dict(sorted(IMPORT_ERRORS.items())[:60]),
              "import_errors_total": len(IMPORT_ERRORS),
              "interpreter_fuel": FUEL, "initializer_fuel": FUEL,
              "ast": os.path.abspath(ast_path), "runtime": runtime,
              "runtime_version": runtime_version(lang),
              "measurement_basis": BASIS, "measurement_basis_note": BASIS_NOTE,
              "language": lang, "language_override": lang_override, "extensions": exts,
              "backend": runtime, "backend_status": backend_status,
              "backend_info": backend_info,
              # Focused functions first, so a `--focus` caller (pr mode) always reads
              # the reason its own functions were skipped; `backend_skipped` is a
              # sample (`backend_skipped_sampled`), `backend_skipped_by_reason` counts
              # every skip (`skip_record`).
              **skip_record(backend_skipped, focus),
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
              "cases": len(cases), "case_cap": case_cap, "focus": focus_record,
              "agree": 0, "total": 0, "divergences": 0,
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

    # ---- which of those cases need the interpreter NOW, and which already have a
    # verdict about byte-identical inputs (`oracle_cache.py`)?
    #
    # A cached verdict is never folded into "compared": it is reported as cached, with
    # the time it was computed, in the summary, in `coverage.by_status` and on every
    # observation it contributes. An oracle that silently re-reported old agreement
    # would be indistinguishable from one that ran.
    repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    cache_root = (os.path.abspath(cache_dir) if cache_dir
                  else str(oracle_cache.default_root(repo, lean_mod)))
    cache_env = oracle_cache.environment_digests(
        repo, result["runtime_version"], semantics_fingerprint)
    cases_by_name = {}
    for i, c in enumerate(cases):
        cases_by_name.setdefault(c["name"], []).append(c)
    cache_plan = oracle_cache.plan(funcs, cases_by_name, cache_env,
                                   rendered=generated_module.model_files(generated),
                                   sources=fingerprints)
    cached_entries, cache_miss_reason = {}, {}
    for name, planned in sorted(cache_plan.items()):
        if not use_cache:
            cache_miss_reason[name] = "--no-cache"
            continue
        entry, why = oracle_cache.lookup(cache_root, name, planned)
        if entry is not None:
            cached_entries[name] = entry
        else:
            cache_miss_reason[name] = why
    fresh = [i for i, c in enumerate(cases) if c["name"] not in cached_entries]
    cached_idx = [i for i, c in enumerate(cases) if c["name"] in cached_entries]
    miss_counts = {}
    for why in cache_miss_reason.values():
        miss_counts[why] = miss_counts.get(why, 0) + 1
    print("oracle cache (%s): %d functions / %d cases reported from cache, %d functions "
          "/ %d cases to compare now%s"
          % (cache_root if use_cache else "--no-cache: not consulted",
             len(cached_entries), len(cached_idx),
             len(cases_by_name) - len(cached_entries), len(fresh),
             "" if not miss_counts else " (%s)" % ", ".join(
                 "%s: %d" % kv for kv in sorted(miss_counts.items(), key=lambda kv: -kv[1]))))
    result["cache"] = {
        "root": cache_root, "consulted": use_cache, "schema": oracle_cache.SCHEMA,
        "functions_compared_now": len(cases_by_name) - len(cached_entries),
        "functions_from_cache": len(cached_entries),
        "cases_compared_now": len(fresh), "cases_from_cache": len(cached_idx),
        "cached_from": sorted({e["computed_at"] for e in cached_entries.values()}),
        "miss_reasons": miss_counts,
        "misses": dict(sorted(cache_miss_reason.items())),
        "environment": cache_env,
        "note": "Verdicts from cache were computed by an earlier run on byte-identical "
                "inputs (function and its rendered definition, reachable callees, module "
                "bodies and the rest of the rendered module, semantics, renderer, harness, "
                "toolchain, runtime version, the runtime source of the function and its "
                "callees, and recorded cases). They are NOT comparisons "
                "made by this run; `functions_compared_now` and the COMPARED figure in "
                "the summary count only those."}

    # ---- ask Lean for its answer on exactly the cases that need it
    #
    # Evaluated in chunks with bisection on failure: a single case can bring the whole
    # Lean interpreter down (a stale generated module, an unimplemented constructor),
    # and losing an entire run to one bad case would be a false negative. Cases we
    # cannot get an answer for are INCONCLUSIVE, never agreement.
    env = dict(os.environ,
               PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])
    # A stale `.olean` silently answers with the *previous* semantics — which shows up
    # as fictitious divergences. Rebuild the module before trusting anything it says.
    # Nothing to evaluate now means nothing to build: the cached verdicts were produced
    # against artifacts whose digests are part of their keys.
    b = (subprocess.run(["lake", "build", "Autoform.Generated.%s" % lean_mod,
                         "Autoform.Lang.Core.Observation"],
                        capture_output=True, text=True, env=env, cwd=repo)
         if fresh else None)
    if b is not None and b.returncode != 0:
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
    isolated = False
    try:
        import shutil
        if fresh:
            shutil.rmtree(snap_dir, ignore_errors=True)
            os.makedirs(snap_dir, exist_ok=True)
            blib = os.path.join(repo, ".lake/build/lib/lean")
            shutil.copytree(os.path.join(blib, "Autoform/Lang"),
                            os.path.join(snap_dir, "Autoform/Lang"))
            os.makedirs(os.path.join(snap_dir, "Autoform/Generated"), exist_ok=True)
            snapshot_generated(blib, snap_dir)
            base = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"],
                                  capture_output=True, text=True, env=env, cwd=repo)
            if base.returncode != 0 or not base.stdout.strip():
                # An ignored failure here made LEAN_PATH "<snapshot>:" and every chunk
                # INCONCLUSIVE with a message about the cases, not about the path.
                print("could not isolate the build: `lake env printenv LEAN_PATH` failed "
                      "(rc=%s): %s; evaluating against the live tree"
                      % (base.returncode, (base.stderr or base.stdout).strip()[:200]))
            else:
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
              "  post : Option HeapObservation",
              # Bindings written into the globals frame before the call: a Java class's
              # static-state holder under `javaStaticKey` (and the simple names that
              # denote that class). Empty for every other case.
              "  glob : List (String × Val) := []", "",
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
              # JavaScript only: a returned array or object literal is a boxed list / dict
              # (`Dialect.boxesContainers`), and the Node driver reports one by STRUCTURE
              # (`enc` in runtime_backends.NODE_DRIVER), so the result is read through its
              # payloads -- to a fixed depth, past which a `.ref` is left and the case is
              # the `representation:value-vs-object` gap rather than a guess.
              "private def unboxDeep (h : Heap) : Nat → Val → Val",
              "  | 0, v => v",
              "  | n+1, .ref a => match h.payload a with",
              "      | .list vs  => .list (vs.map (unboxDeep h n))",
              "      | .dict kvs => .dict (kvs.map (fun kv => (unboxDeep h n kv.1, unboxDeep h n kv.2)))",
              "      | _ => .ref a",
              "  | n+1, .list vs  => .list (vs.map (unboxDeep h n))",
              "  | n+1, .dict kvs => .dict (kvs.map (fun kv => (unboxDeep h n kv.1, unboxDeep h n kv.2)))",
              "  | _, v => v", "",
              "private def unboxResult (h : Heap) (r : EResult) : EResult :=",
              "  match unboxRes h r with",
              "  | .val v => if program.dialect == .javascript then .val (unboxDeep h 34 v) else .val v",
              "  | r' => r'", "",
              # JavaScript only, and only where a heap observation is compared (a Node
              # instance-method case, `runtime_backends.node_receiver`): every JS Number is
              # a double, and Core keeps a small one as an exact `.int`, so both sides of
              # the graph check are read with each `.int` as the double it denotes -- the
              # same widening the result comparison gives a Node result. Without it a
              # field Core holds as `.int 1` and Node reports as `1` from `2 * 0.5` would
              # be a disagreement about representation, not about the program. An identity
              # for every other dialect.
              "private def jsWiden : Nat → Val → Val",
              "  | 0, v => v",
              "  | _+1, .int i => match (Dialect.javascript.toFConfig).ofInt i with",
              "                   | .ok x => .float x",
              "                   | _ => .int i",
              # A NaN's payload is not a JS-observable value: one NaN, whatever its bits.
              "  | _+1, .float x => .float (if x.isNaN then Fl.nan x.fmt else x)",
              "  | n+1, .list vs => .list (vs.map (jsWiden n))",
              "  | n+1, .tuple vs => .tuple (vs.map (jsWiden n))",
              "  | n+1, .dict kvs => .dict (kvs.map (fun kv => (jsWiden n kv.1, jsWiden n kv.2)))",
              "  | _, v => v", "",
              "private def jsWidenHeap (h : Heap) : Heap :=",
              "  if program.dialect == .javascript then",
              "    h.map (fun o => { o with",
              "      fields := o.fields.map (fun kv => (kv.1, jsWiden 34 kv.2)),",
              "      payload := match o.payload with",
              "        | .list vs  => .list (vs.map (jsWiden 34))",
              "        | .tuple vs => .tuple (vs.map (jsWiden 34))",
              "        | .dict kvs => .dict (kvs.map (fun kv => (jsWiden 34 kv.1, jsWiden 34 kv.2)))",
              "        | .none     => .none })",
              "  else h", "",
              "private def jsWidenRes (r : EResult) : EResult :=",
              "  match r with",
              "  | .val v => if program.dialect == .javascript then .val (jsWiden 34 v) else r",
              "  | _ => r", "",
              "private def drun (c : DCase) : Heap × EResult :=",
              "  let h := c.glob.foldl (fun h kv => h.setField gref kv.1 kv.2) (h0 ++ c.objs)",
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
              "                 (r.1, if c.post.isSome then r.2 else unboxResult r.1 r.2)", ""]
    footer = ["]", "",
              '#eval IO.println ("@@meta@@" ++ toString base ++ " " ++ toString gref)',
              '#eval cases.forM (fun c => do let r := drun c; '
              'IO.println ("@@" ++ toString c.idx ++ "@@" '
              '++ (repr r.2).pretty (width := 1000000)); '
              'match c.post with | none => pure () | some graph => '
              'IO.println ("@@heap@@" ++ toString c.idx ++ "@@" ++ '
              '(repr (HeapObservation.compare { graph with heap := jsWidenHeap graph.heap } '
              '(jsWidenHeap r.1) (jsWidenRes c.expected) (jsWidenRes r.2))).pretty '
              '(width := 1000000)))']

    def case_lit(i, c):
        slf = "none" if c["self"] is None else "(some (%s))" % lean_val(c["self"])
        chk = ", ".join('(%d, %s)' % (k, json.dumps(cls))
                        for k, cell in enumerate(c["heap"]) for cls in [cell[0]])
        glob = ", ".join("(%s, %s)" % (json.dumps(k), lean_val(v))
                         for k, v in c.get("globals", []))
        return ("  { idx := %d, objs := %s, fn := %s, slf := %s, args := [%s], "
                "chk := [%s], expected := %s, post := %s%s }"
                % (i, lean_heap(c["heap"]), json.dumps(c["name"]), slf,
                   ", ".join(lean_val(a) for a in c["args"]), chk,
                   outcome_lit(c['outcome']), graph_lit(c),
                   ", glob := [%s]" % glob if glob else ""))

    graph_answers = {}
    meta = {"base": 0, "gref": 0}
    chunk_failures = {}           # case index -> why its chunk produced no answer
    chunk_failure_log = []        # one record per failed chunk, for conformance.json
    # per-process scratch file: two harness runs (or two agents) sharing /tmp would
    # otherwise clobber each other's generated file mid-bisection
    scratch = os.path.join(WORK, "harness.lean")

    def lean_eval(idxs, depth=0, retried=False):
        """idxs -> {idx: repr line}. Missing keys are cases Lean could not answer."""
        if not idxs: return {}
        src = header + ["private def cases : List DCase := ["] \
            + [",\n".join(case_lit(i, cases[i]) for i in idxs)] + footer
        open(scratch, "w").write("\n".join(src) + "\n")
        cmd = ([os.path.expanduser("~/.elan/bin/lean"), scratch] if isolated
               else ["lake", "env", "lean", scratch])
        try:
            out = subprocess.run(cmd, capture_output=True, text=True,
                                 env=lean_env if isolated else env, cwd=repo,
                                 timeout=LEAN_CHUNK_TIMEOUT)
        except subprocess.TimeoutExpired as e:
            # Unbounded before: one hung chunk hung the whole oracle. The chunk's cases
            # are INCONCLUSIVE with this reason (not `lean-no-answer`, which is what a
            # per-case interpreter failure says), and nothing is bisected.
            reason = ("lean-chunk-timeout (%d case(s) not answered within %d s; "
                      "AUTOFORM_LEAN_CHUNK_TIMEOUT)" % (len(idxs), LEAN_CHUNK_TIMEOUT))
            print("  " + reason)
            chunk_failure_log.append({"cases": len(idxs), "depth": depth, "reason": reason,
                                      "stderr_tail": runtime_backends.output_tail(e.stderr, 400)})
            for i in idxs:
                chunk_failures[i] = reason
            return {}
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
            rebuild = subprocess.run(["lake", "build", "Autoform.Generated.%s" % lean_mod,
                                      "Autoform.Lang.Core.Observation"],
                                     capture_output=True, text=True, env=env, cwd=repo)
            # The rebuild's outcome used to be discarded: a failed rebuild then surfaced
            # only as the retry's "lean did not reach the first case", one step removed
            # from its cause. Keep the tail, and say so when it failed.
            meta.setdefault("retry_builds", []).append(
                {"returncode": rebuild.returncode,
                 "output_tail": runtime_backends.output_tail(rebuild.stderr + rebuild.stdout)})
            if rebuild.returncode:
                last = (rebuild.stderr + rebuild.stdout).strip().splitlines()[-1:]
                print("  retry `lake build` failed (rc=%s): %s"
                      % (rebuild.returncode, last[0][:200] if last else ""))
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
    order = list(fresh)           # cached functions never reach the interpreter
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
    if chunk_failure_log:
        result["lean_chunk_failures"] = chunk_failure_log
    if meta.get("retry_builds"):
        result["lean_retry_builds"] = meta["retry_builds"]
    result["provenance"] = {
        "ast_sha256": ast_fingerprint,
        "generated_sha256": generated_module.model_digest(generated),
        "source_sha256": fingerprints, "semantics_sha256": semantics_fingerprint}
    moved = [name for name, same in (
        ("AST", runtime_backends.sha256(ast_path) == ast_fingerprint),
        ("source tree", runtime_backends.source_fingerprints(src_root, funcs) == fingerprints),
        ("Autoform/Lang/Core", runtime_backends.semantics_fingerprints() == semantics_fingerprint),
    ) if not same]
    result["build_stable"] = result["build_stable"] and not moved
    if not stable or mutating:
        print("WARNING: results below were produced against a moving or mutated build "
              "and must not be treated as conformance evidence (build_stable=false).")
    elif moved:
        # Never fail silently: exit 2 with a healthy-looking summary is unreadable.
        print("WARNING: the %s changed while this run was in progress; the results "
              "below describe a tree that no longer exists (build_stable=false)."
              % " and ".join(moved))
    if len(got) < len(fresh):
        print("lean answered %d/%d cases; the rest are INCONCLUSIVE"
              % (len(got), len(fresh)))

    def adjudicate(c, line, answer):
        """One case's verdict from the interpreter's answer: `agree`, `diverge`, or
        `incon` with the label that says why. Pure in its inputs, so a verdict can be
        stored and replayed when every input it was computed from is unchanged."""
        if line is None:
            return {"kind": "incon",
                    "label": "lean-no-answer (interpreter failed on this case)"}
        try:
            lr = parse_result(line)
        except Exception:                                  # noqa: BLE001
            print("  unparsable %s: %s" % (c["name"], line[:80]))
            return {"kind": "incon", "label": "unparsable-lean-answer"}
        py = c["outcome"]
        if lr[0] in ("hole", "outOfFuel"):
            # ignorance is never agreement
            return {"kind": "incon",
                    "label": lr[1] if lr[0] == "hole" else "outOfFuel"}
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
            return {"kind": "incon", "label": undecidable, "desc": desc[:200],
                    "lean_repr": line[:400]}
        return {"kind": "agree" if ok else "diverge", "desc": desc[:200],
                "lean_repr": line[:400]}

    agree = diverge = incon = 0
    compared_fns = set()          # functions the oracle actually adjudicated
    compared_now, compared_cached = set(), set()
    incon_detail: dict = {}
    per_origin = {}
    verdicts_by_name = {}         # name -> {case digest: verdict}, for the cache
    uncacheable = set()           # functions with an interpreter failure this run
    kinds = {}                    # case index -> verdict kind, for the summary
    verdict_kind = kinds.get
    for i, c in enumerate(cases):
        origin = c.get("origin", "?")
        bucket = per_origin.setdefault(origin, {"agree": 0, "diverge": 0, "incon": 0})
        entry = cached_entries.get(c["name"])
        cdigest = oracle_cache.case_digest(c)
        if entry is not None:
            verdict = dict(entry["verdicts"][cdigest])
            verdict["cached_from"] = entry["computed_at"]
        else:
            verdict = adjudicate(c, got.get(i), graph_answers.get(i))
            if got.get(i) is None and i in chunk_failures:
                # Say "the chunk timed out" differently from "the interpreter failed on
                # this case" (CONTRIBUTING.md rule 6). Still INCONCLUSIVE, still uncached.
                verdict = {"kind": "incon", "label": chunk_failures[i]}
            if got.get(i) is None:
                uncacheable.add(c["name"])
            verdicts_by_name.setdefault(c["name"], {})[cdigest] = verdict
        cached_from = verdict.get("cached_from")
        kinds[i] = verdict["kind"]
        if verdict["kind"] == "incon":
            incon += 1; bucket["incon"] += 1
            k = "%s: %s" % (c["name"], verdict["label"])
            incon_detail[k] = incon_detail.get(k, 0) + 1
            continue
        compared_fns.add(c["name"])
        (compared_cached if cached_from else compared_now).add(c["name"])
        argstr = "(%s)" % ", ".join(show_arg(a, lang) for a in c["args"])
        if verdict["kind"] == "agree":
            agree += 1; bucket["agree"] += 1
            observation = {k: c[k] for k in ("name", "heap", "self", "args", "outcome")}
            if 'post_heap' in c:
                observation['post_heap'] = c['post_heap']
            # The JVM planner binds Java/Kotlin statics (and simple class names) to
            # their holder cells via a globals frame (`case['globals']`, built by
            # static_state). The agreeing observation must carry those bindings:
            # a case that executes a static field read cannot replay without them.
            if 'globals' in c:
                observation['globals'] = c['globals']
            observation.update(origin=origin, runtime=runtime, comparison="agree")
            if cached_from:
                observation["cached_from"] = cached_from
            result["runtime_cases"].append(observation)
        else:
            diverge += 1; bucket["diverge"] += 1
            msg = "  DIVERGENCE %s%s: %s [%s]%s" % (
                c["name"], argstr, verdict["desc"], origin,
                " (cached from %s)" % cached_from if cached_from else "")
            print(msg[:300])
            result["divergence_detail"].append(
                {"function": c["name"], "args": argstr[:200], "detail": verdict["desc"],
                 "origin": origin, "cached_from": cached_from,
                 # the exact inputs, so a divergence is a reproducible artifact rather
                 # than a line of prose
                 "case": {"self": c["self"], "args": c["args"],
                          "heap": json.loads(json.dumps(c["heap"]))[:6]},
                 # The compact legacy case above is a display preview. Preserve
                 # the complete graph and native expectation for exact replay.
                 "observation": json.loads(json.dumps(c)),
                 "lean_repr": verdict.get("lean_repr", "")})

    # Record this run's verdicts for the next one -- only verdicts the interpreter
    # actually produced, against artifacts that held still. A mutant module, a tree
    # that moved mid-run, or a case Lean never answered leaves no entry: the next run
    # re-compares that function rather than inheriting a doubt.
    stored = 0
    if stable and not mutating and not moved:
        for name, verdicts in verdicts_by_name.items():
            if name in uncacheable or name not in cache_plan:
                continue
            try:
                oracle_cache.store(cache_root, name, cache_plan[name], verdicts,
                                   module=lean_mod)
                stored += 1
            except OSError as e:
                print("  oracle cache: could not store %s (%s)" % (name, e))
                break
    result["cache"].update(functions_stored=stored,
                           not_stored=sorted(uncacheable),
                           functions_adjudicated_now=len(compared_now),
                           functions_adjudicated_from_cache=len(compared_cached))

    # ---- change coverage (`--changed-lines`, Python): did any COMPARED case execute the
    # changed statements and both outcomes of a changed condition? A pass on inputs that
    # never reached the change says nothing about it.
    if changed_lines is not None:
        observed_by, origin_of = {}, {}
        for i, c in enumerate(cases):
            if kinds.get(i) in ("agree", "diverge") and id(c) in CASE_COVERAGE:
                observed_by.setdefault(c["name"], []).append(CASE_COVERAGE[id(c)])
                origin_of.setdefault(c["name"], []).append(c.get("origin", "?"))
        coverage_out = {}
        for f in funcs:
            if lang == "python" and f["name"] in COVERAGE_KEYS:
                seen = observed_by.get(f["name"], [])
                record = change_coverage(f, src_root, changed_lines[f["file"]], seen)
                # Which origins alone would have reached the change (the suite's inputs,
                # the random integers, the literal-derived strings).
                origins = origin_of.get(f["name"], [])
                record["covered_by_origin"] = {
                    o: change_coverage(f, src_root, changed_lines[f["file"]],
                                       [x for x, y in zip(seen, origins) if y == o]).get("covered")
                    for o in sorted(set(origins))}
                coverage_out[f["name"]] = record
            elif focus is not None and f["name"] in focus and f.get("file") in changed_lines:
                coverage_out[f["name"]] = {"covered": None, "note": "change coverage is "
                                           "measured for Python only (%s)" % lang}
        result["change_coverage"] = coverage_out

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
    # A verdict replayed from the cache says so in the status itself, with the time it
    # was computed, so a reader of `by_status` cannot mistake it for a comparison this
    # run made. The `status_counts` key stays `compared` (split at the first colon).
    for n, entry in cached_entries.items():
        if n in status and status[n] in ("compared", "cases built, all inconclusive"):
            status[n] += ": cached from %s" % entry["computed_at"]
    for n, why in stats.get("no_instance_detail", {}).items():
        for f in funcs:
            if f["name"].endswith("." + n) and status.get(f["name"], "").startswith(
                    "hole-free"):
                status[f["name"]] = "hole-free, no case built: " + why
    if IMPORT_ERRORS and lang == "python":
        for f in funcs:
            c = classify(f)
            if c and c[0] in IMPORT_ERRORS and status.get(f["name"]) in (
                    "hole-free, no case built", "not-translated-fully (holes): no native case built"):
                status[f["name"]] += ": module failed to import: " + IMPORT_ERRORS[c[0]]
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
    cov["compared_now"] = len(compared_now)
    cov["compared_from_cache"] = len(compared_cached)
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
    # The COMPARED figure is what the "Conformance oracle is alive" CI step reads. It
    # counts functions the interpreter adjudicated IN THIS RUN; functions reported from
    # the cache are named separately with the time their verdict was computed, so a
    # warm cache can never make a run that compared nothing look alive.
    if cached_entries:
        stamps = result["cache"]["cached_from"]
        print("functions: %d total, %d hole-free, %d exercised, %d COMPARED now, %d "
              "cached from %s (%d adjudicated in all: %.0f%% of all, %.0f%% of hole-free)"
              % (len(funcs), len(holefree), result["functions_covered"],
                 len(compared_now), len(compared_cached),
                 stamps[0] if len(stamps) == 1 else "%s .. %s" % (stamps[0], stamps[-1]),
                 len(compared_fns), 100 * result["coverage"]["compared_fraction"],
                 100 * result["coverage"]["compared_fraction_of_hole_free"]))
    else:
        print("functions: %d total, %d hole-free, %d exercised, %d COMPARED (%.0f%% of "
              "all, %.0f%% of hole-free)"
              % (len(funcs), len(holefree), result["functions_covered"],
                 len(compared_fns), 100 * result["coverage"]["compared_fraction"],
                 100 * result["coverage"]["compared_fraction_of_hole_free"]))
    dropped = case_cap.get("dropped", 0)
    dropped_c = case_cap.get("dropped_c_plan", 0)
    print("conformance: %d/%d agree (%s) vs %s, %d divergences, %d INCONCLUSIVE "
          "(hole / outOfFuel / unrepresentable)%s%s%s"
          % (agree, total, rate, runtime, diverge, incon,
             "" if not dropped else
             " [%d cases dropped by the case cap, not compared: see conformance.json case_cap]"
             % dropped,
             "" if not dropped_c else
             " [%d planned C calls past the case cap never executed, %d function(s) lost "
             "whole: see conformance.json case_cap]"
             % (dropped_c, len(case_cap.get("functions_dropped_c_plan", []))),
             "" if not cached_entries else
             " [%d cases compared now, %d replayed from cache]"
             % (sum(1 for i in fresh if verdict_kind(i) != "incon"),
                sum(1 for i in cached_idx if verdict_kind(i) != "incon"))))
    print("oracle cache: %d functions stored under %s%s"
          % (stored, cache_root,
             "" if not uncacheable else "; not stored (no interpreter answer): %d"
             % len(uncacheable)))
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
    sandbox_reexec()
    sys.exit(main())
