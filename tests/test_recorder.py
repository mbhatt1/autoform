"""The test-suite recorder in `scripts/differential.py` (`trace_tests`).

The conformance oracle replays calls recorded from a corpus's OWN test suite. Every
case here is a way the recorder wrote down something other than what CPython did --
each one a manufactured divergence, or worse a manufactured agreement, waiting for the
semantics to catch up:

* `try: d[k] except KeyError: pass` returns None; it was recorded as raising KeyError.
* a generator's `return` trace event fires at every `yield`; each yielded element was
  recorded as the call's result (and agreed with an AST that translates `yield` as
  `return` -- two wrong models agreeing).
* the module's own code object (`<module>`, first line 1) was recorded as a call to
  whatever `def` sits on line 1.
* same-named `def`s in one scope were all attributed to the last one's translation.
* `self` was stripped from nested functions the exporter keeps it on, refusing every
  call as a parameter mismatch.
* refused calls were global counters only, never attributed to their function.
"""
from __future__ import annotations

import os
import sys
import textwrap

import pytest


def _write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as fh:
        fh.write(textwrap.dedent(text))


@pytest.fixture
def corpus(tmp_path, request):
    """A one-module package plus a test that calls into it, under a unique name so
    nested pytest runs and `sys.modules` never see a stale copy."""
    pkg = "rec_%s" % request.node.name.replace("[", "_").replace("]", "_")[:40]

    def make(src, test):
        root = tmp_path / "src"
        _write(str(root / pkg / "__init__.py"), src)
        _write(str(tmp_path / "tests" / ("test_%s.py" % pkg)),
               "import %s as pk\n\n" % pkg + textwrap.dedent(test))
        return str(root), str(tmp_path / "tests"), "%s/__init__.py" % pkg

    yield make
    for m in [m for m in sys.modules if m == pkg or m.startswith(pkg + ".")
              or m == "test_" + pkg]:
        del sys.modules[m]


def _trace(differential, root, tests, rel, quals, params=None, limit=5):
    idx = differential.build_lineno_index(root, [rel])
    wanted = {"%s:<module>.%s" % (rel, q) for q in quals}
    stats = {"skip_unencodable_args": 0, "skip_unencodable_ret": 0, "test_runs": []}
    pbn = {"%s:<module>.%s" % (rel, q): p for q, p in (params or {}).items()}
    recs = differential.trace_tests(root, [tests], idx, wanted, limit, stats, pbn,
                                    {}, {})
    assert stats["test_runs"] and stats["test_runs"][0].get("rc") == 0, stats["test_runs"]
    by = {}
    for r in recs:
        by.setdefault(r["name"].split("<module>.")[1], []).append(r)
    ledger = {k.split("<module>.")[1]: v for k, v in stats["trace_ledger"].items()}
    return by, ledger


def test_a_swallowed_exception_is_a_normal_return(differential, corpus):
    root, tests, rel = corpus("""
        def swallow(d, k):
            try:
                d[k]
            except KeyError:
                pass
        """, """
        def test_it():
            assert pk.swallow({}, 1) is None
        """)
    by, _ = _trace(differential, root, tests, rel, ["swallow"])
    assert [r["outcome"] for r in by["swallow"]] == [("val", ("unit",))]


def test_an_escaping_exception_is_recorded_through_finally(differential, corpus):
    root, tests, rel = corpus("""
        def escapes(d, k):
            try:
                return d[k]
            finally:
                d["seen"] = 1
        """, """
        import pytest
        def test_it():
            with pytest.raises(KeyError):
                pk.escapes({}, 2)
        """)
    by, _ = _trace(differential, root, tests, rel, ["escapes"])
    assert [r["outcome"] for r in by["escapes"]] == [("exn", "KeyError")]


def test_a_generator_is_refused_and_counted_not_recorded(differential, corpus):
    root, tests, rel = corpus("""
        def gen(n):
            for i in range(n):
                yield i
        """, """
        def test_it():
            assert list(pk.gen(3)) == [0, 1, 2]
        """)
    by, ledger = _trace(differential, root, tests, rel, ["gen"])
    assert "gen" not in by
    reasons = ledger["gen"]["refused"]
    assert any(k.startswith("generator") for k in reasons), reasons


def test_the_module_body_is_not_a_call_to_the_def_on_line_one(differential, corpus):
    root, tests, rel = corpus("""def first(x):
            return x + 1
        """, """
        def test_it():
            assert pk.first(1) == 2
        """)
    by, _ = _trace(differential, root, tests, rel, ["first"])
    assert [r["args"] for r in by["first"]] == [[("int", 1)]]


def test_redefinitions_map_to_the_exporters_numbering(differential, corpus):
    root, tests, rel = corpus("""
        def pick(n):
            if n == 0:
                def f():
                    return "zero"
            elif n == 1:
                def f():
                    return "one"
            else:
                def f():
                    return "many"
            return f()
        """, """
        def test_it():
            assert [pk.pick(i) for i in range(3)] == ["zero", "one", "many"]
        """)
    by, _ = _trace(differential, root, tests, rel,
                   ["pick.f<redefined>0", "pick.f<redefined>1", "pick.f"])
    got = {q: [r["outcome"] for r in rs] for q, rs in by.items()}
    assert got == {"pick.f<redefined>0": [("val", ("str", "zero"))],
                   "pick.f<redefined>1": [("val", ("str", "one"))],
                   "pick.f": [("val", ("str", "many"))]}
    assert differential.classify({"name": "%s:<module>.pick.f<redefined>1" % rel})
    assert differential.classify({"name": "%s:<module>.pick.<lambda>0" % rel}) is None


def test_self_is_positional_where_the_ast_keeps_it(differential, corpus):
    root, tests, rel = corpus("""
        class C:
            def __init__(self):
                self.v = 3

            def meth(self, k):
                return self.v + k

        def methodkey(self, k):
            return k
        """, """
        def test_it():
            c = pk.C()
            assert c.meth(1) == 4
            assert pk.methodkey(c, 7) == 7
        """)
    by, ledger = _trace(differential, root, tests, rel, ["C.meth", "methodkey"],
                        params={"C.meth": ["k"], "methodkey": ["self", "k"]})
    meth, = by["C.meth"]
    assert meth["self"][0] == "ref" and meth["args"] == [("int", 1)]
    mk, = by["methodkey"]
    assert mk["self"] is None
    assert mk["args"][0][0] == "ref" and mk["args"][1] == ("int", 7)
    assert not ledger["methodkey"]["refused"]


def test_refusals_are_attributed_to_their_function(differential, corpus):
    root, tests, rel = corpus("""
        def wrap(x):
            return {x} if isinstance(x, int) else x

        def g(x):
            return {1} if x == 0 else x
        """, """
        def test_it():
            assert pk.wrap({1}) == {1}
            assert pk.wrap(4) == {4}
            assert pk.g(0) == {1}
            assert pk.g(5) == 5
        """)
    by, ledger = _trace(differential, root, tests, rel, ["wrap", "g"], limit=1)
    assert "wrap" not in by
    assert ledger["wrap"]["calls"] == 2 and ledger["wrap"]["recorded"] == 0
    assert ledger["wrap"]["refused"] == {"unencodable-arg: set": 1,
                                         "unencodable-result: set": 1}
    # `g(0)` was refused at RETURN and gave its quota slot back, so with limit=1 the
    # encodable second call was still recorded rather than lost to the quota
    assert ledger["g"] == {"calls": 2, "recorded": 1, "over_quota": 0,
                           "refused": {"unencodable-result: set": 1}}
    assert [r["args"] for r in by["g"]] == [[("int", 5)]]


def test_nested_classes_with_one_short_name_are_kept_apart(differential):
    def make(tag):
        class Wrapper:
            pass
        Wrapper.__qualname__ = "%s.<locals>.Wrapper" % tag
        return Wrapper
    a, b = make("_locked"), make("_unlocked")
    assert differential.class_key(a) != differential.class_key(b)
    assert differential.class_key(a).endswith(":_locked.Wrapper")
    assert differential.module_of("pkg/sub/__init__.py") == "pkg.sub"
    assert differential.module_of("pkg/sub/m.py") == "pkg.sub.m"


def test_a_user_descriptor_instance_is_an_object_not_a_function(differential):
    class Descriptor:
        def __init__(self):
            self.n = 1

        def __get__(self, obj, objtype=None):
            return self
    enc = differential.Encoder()
    assert enc.enc(Descriptor())[0] == "ref"
    import functools
    with pytest.raises(differential.Unencodable):
        differential.Encoder().enc(functools.partial(len))


def test_the_case_budget_never_drops_a_function_silently(differential):
    cases = [{"name": "a", "i": i} for i in range(5)] + \
            [{"name": "b", "i": 0}] + [{"name": "c", "i": i} for i in range(3)]
    kept, cut = differential.cap_cases(cases, 4)
    assert sorted(c["name"] for c in kept) == ["a", "a", "b", "c"]
    assert cut == {"a": 3, "c": 2}
    kept, cut = differential.cap_cases(cases, 100)
    assert len(kept) == len(cases) and cut == {}


def test_floats_encode_by_bit_pattern_and_round_trip(differential):
    enc = differential.Encoder()
    v = enc.enc(2.0)
    assert v == ("float", 0x4000000000000000)
    assert differential.lean_val(v) == "Val.float (Fl.ofBits 4611686018427387904)"
    line = ("Autoform.Core.EResult.val (Autoform.Core.Val.float { fmt := { prec := 53, "
            "emax := 1023, expBits := 11 }, bits := 4611686018427387904 })")
    r = differential.parse_result(line)
    assert r == ("val", ("float", 0x4000000000000000))
    assert differential.same(v, r[1], 0)
    # -0.0 is a different value from 0.0, and an int is not a float
    assert not differential.same(enc.enc(-0.0), ("float", 0), 0)
    assert not differential.same(("int", 2), r[1], 0)
    with pytest.raises(differential.Unencodable):
        differential.Encoder().enc({1.5: 1})


def test_a_closure_is_replayed_with_its_captures(differential, corpus):
    root, tests, rel = corpus("""
        def make(n):
            def add(x):
                return x + n
            return add
        """, """
        def test_it():
            assert pk.make(3)(4) == 7
        """)
    by, _ = _trace(differential, root, tests, rel, ["make.add"],
                   params={"make.add": ["x"]})
    rec, = by["make.add"]
    assert rec["cap"] == [("n", ("int", 3))]
    assert rec["args"] == [("int", 4)] and rec["outcome"] == ("val", ("int", 7))


def test_objects_of_a_function_local_class_carry_its_captures(differential,
                                                               monkeypatch):
    # `trace_tests` scopes captures to the corpus's own packages; this class lives here
    monkeypatch.setattr(differential, "CORPUS_PACKAGES", None)

    def factory(k):
        class Local:
            def get(self):
                return k
        return Local()
    enc = differential.Encoder()
    ref = enc.enc(factory(9))
    assert enc.captured[ref[1]] == [("k", ("int", 9))]
    lit = differential.lean_heap(enc.heap, enc.captured)
    assert 'captured := [("k", Val.int (9))]' in lit


def test_an_instance_made_through_a_generic_alias_still_encodes(differential):
    class Box:
        __class_getitem__ = classmethod(lambda cls, item: __import__("types")
                                        .GenericAlias(cls, item))

        def __init__(self):
            self.v = 1

        @property
        def p(self):
            return self.v
    b = Box[int]()                       # sets b.__orig_class__ = Box[int]
    enc = differential.Encoder()
    ref = enc.enc(b)
    fields = dict(enc.heap[ref[1]][1])
    assert fields["v"] == ("int", 1)
    assert fields["__orig_class__"][0] == "fn"


def test_a_recorder_fault_never_fails_the_traced_suite(differential, corpus,
                                                      monkeypatch):
    root, tests, rel = corpus("""
        def f(x):
            return x
        """, """
        def test_it():
            assert pk.f(1) == 1
        """)

    def boom(self, v, depth=0, in_key=False):
        raise RuntimeError("recorder bug")
    monkeypatch.setattr(differential.Encoder, "enc", boom)
    # `_trace` asserts the suite exited 0: the exception must not reach the test
    by, ledger = _trace(differential, root, tests, rel, ["f"])
    assert "f" not in by
    assert ledger["f"]["refused"] == {"recorder-error: RuntimeError": 1}


def test_kept_calls_are_spread_across_call_shapes(differential):
    def rec(i, cls):
        return {"name": "f", "self": ("ref", 0), "args": [("int", i)],
                "heap": [(cls, [])], "outcome": ("val", ("int", i))}
    # the suite's first four calls are all on one receiver class
    recs = [rec(i, "A") for i in range(4)] + [rec(9, "Sub")]
    kept, dropped = differential.diversify(recs, 2)
    assert [(r["heap"][0][0], r["args"][0][1]) for r in kept] == [("A", 0), ("Sub", 9)]
    assert dropped == {"f": 3}


def test_unmapped_entries_say_why(differential):
    assert "module initializer" in differential.unmapped_reason("m.py:<module>")
    assert "lambda" in differential.unmapped_reason("m.py:<module>.f.<lambda>0")
    assert differential.unmapped_reason("m.py:<module>.f") is None
    assert differential.unmapped_reason("m.py:<module>.f<redefined>0") is None
