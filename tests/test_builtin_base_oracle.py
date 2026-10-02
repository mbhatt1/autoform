"""The conformance oracle's handling of classes with a builtin base (`Val.bobj`).

`class _HashedTuple(tuple)` (cachetools/keys.py) translates to
`Val.bobj "_HashedTuple" (Val.tuple ...)`. Before this, `scripts/differential.py`
encoded CPython's `_HashedTuple` as a *plain* tuple and stripped the class off Core's
answer before comparing, so a Core result that had LOST the class (a plain tuple where
CPython returns a `_HashedTuple`) was scored as agreement, and so was the reverse.
These tests pin the class-preserving encoding and comparison, and the refusals that
keep it from becoming a silent wrong answer.
"""
from __future__ import annotations

import os
import re

import pytest

from conftest import ROOT


@pytest.fixture()
def D(differential):
    """The harness with `_HashedTuple` recorded as a `tuple` subclass, as the committed
    `ast-Cachetools.json` records it; restored afterwards."""
    saved = dict(differential.BUILTIN_BASES)
    differential.BUILTIN_BASES.clear()
    differential.BUILTIN_BASES.update({"_HashedTuple": "tuple", "S": "str"})
    yield differential
    differential.BUILTIN_BASES.clear()
    differential.BUILTIN_BASES.update(saved)


class _HashedTuple(tuple):
    """The upstream class, verbatim in the parts that matter here."""
    __hashvalue = None

    def __hash__(self, hash=tuple.__hash__):
        hashvalue = self.__hashvalue
        if hashvalue is None:
            self.__hashvalue = hashvalue = hash(self)
        return hashvalue

    def __add__(self, other, add=tuple.__add__):
        return _HashedTuple(add(self, other))


T0 = ("tuple", [("int", 0)])


class TestBuiltinBasesTable:
    def test_reads_classBases_from_the_ast(self, differential):
        funcs = [{"name": "m.py:<module>", "classBases": {"_HashedTuple": "tuple"}},
                 {"name": "m.py:<module>.f"}]
        assert differential.builtin_bases_of(funcs) == {"_HashedTuple": "tuple"}

    def test_conflicting_bases_are_dropped_as_render_lean_drops_them(self, differential):
        funcs = [{"name": "a.py:<module>", "classBases": {"K": "tuple"}},
                 {"name": "b.py:<module>", "classBases": {"K": "list", "L": "str"}}]
        assert differential.builtin_bases_of(funcs) == {"L": "str"}

    def test_committed_cachetools_ast_records_HashedTuple(self, differential):
        import json
        funcs = json.load(open(os.path.join(ROOT, "ast-Cachetools.json")))
        assert differential.builtin_bases_of(funcs) == {"_HashedTuple": "tuple"}

    def test_refused_dunders_mirror_the_lean_list(self, differential):
        """The encoder's refusal list must be Core's, or an override Core refuses to
        model could be handed to Core inside a `bobj` and silently bypassed."""
        src = open(os.path.join(ROOT, "Autoform/Lang/Core/Semantics.lean")).read()
        m = re.search(r"def builtinBaseRefusedDunders : List String :=\s*\[(.*?)\]",
                      src, re.S)
        assert m, "Semantics.lean no longer defines builtinBaseRefusedDunders"
        lean = re.findall(r'"([^"]+)"', m.group(1))
        assert tuple(lean) == differential.BUILTIN_BASE_REFUSED_DUNDERS


class TestEncoding:
    def test_recorded_class_keeps_its_class(self, D):
        assert D.Encoder().enc(_HashedTuple((0,))) == ("bobj", "_HashedTuple", T0)

    def test_old_behaviour_dropped_the_class(self, differential):
        """Reconstruction: with no `builtinBases` known, the instance encodes as a bare
        tuple, which is what every run before this change compared against."""
        saved = dict(differential.BUILTIN_BASES)
        differential.BUILTIN_BASES.clear()
        try:
            assert differential.Encoder().enc(_HashedTuple((0,))) == T0
        finally:
            differential.BUILTIN_BASES.update(saved)

    def test_plain_tuple_is_untouched(self, D):
        assert D.Encoder().enc((0,)) == T0

    def test_memoised_hash_attribute_does_not_leak_into_the_payload(self, D):
        k = _HashedTuple((0,))
        hash(k)                                   # sets `_HashedTuple__hashvalue`
        assert vars(k)
        assert D.Encoder().enc(k) == ("bobj", "_HashedTuple", T0)

    def test_nested_and_as_dict_key(self, D):
        k = _HashedTuple((1, 2))
        enc = D.Encoder().enc({k: (k,)})
        bk = ("bobj", "_HashedTuple", ("tuple", [("int", 1), ("int", 2)]))
        assert enc == ("dict", [(bk, ("tuple", [bk]))])

    def test_payload_is_read_through_the_base_not_the_override(self, D):
        class S(str):
            def __str__(self):
                return "lie"
        assert D.Encoder().enc(S("ab")) == ("bobj", "S", ("str", "ab"))

    @pytest.mark.parametrize("dunder", ["__getitem__", "__len__", "__iter__",
                                        "__contains__", "__eq__", "__bool__"])
    def test_a_bypassed_override_is_refused(self, D, dunder):
        H = type("_HashedTuple", (tuple,), {dunder: lambda self, *a: 0,
                                            "__hash__": tuple.__hash__})
        with pytest.raises(D.Unencodable, match="builtin-base-override"):
            D.Encoder().enc(H((0,)))

    def test_same_name_different_base_is_refused(self, D):
        H = type("_HashedTuple", (list,), {})
        with pytest.raises(D.Unencodable, match="builtin-base-mismatch"):
            D.Encoder().enc(H([0]))

    def test_lean_literal(self, D):
        v = D.Encoder().enc(_HashedTuple((0,)))
        assert D.lean_val(v) == 'Val.bobj "_HashedTuple" (Val.tuple [Val.int (0)])'


class TestComparison:
    def lean(self, D, s):
        return D.parse_result(s)[1]

    def test_agreement_needs_class_and_payload(self, D):
        ln = self.lean(D, 'EResult.val (Val.bobj "_HashedTuple" (Val.tuple [Val.int 0]))')
        assert D.same(("bobj", "_HashedTuple", T0), ln, 0) is True

    def test_payload_disagreement(self, D):
        ln = self.lean(D, 'EResult.val (Val.bobj "_HashedTuple" (Val.tuple [Val.int 1]))')
        assert D.same(("bobj", "_HashedTuple", T0), ln, 0) is False

    def test_class_disagreement(self, D):
        ln = self.lean(D, 'EResult.val (Val.bobj "Other" (Val.tuple [Val.int 0]))')
        assert D.same(("bobj", "_HashedTuple", T0), ln, 0) is False

    def test_core_lost_the_class_is_a_divergence(self, D):
        """CPython `hashkey(0)` is a `_HashedTuple`; a Core answer of a bare `(0,)` is
        observably different (`type`, `__add__`). The old harness scored it agreement."""
        ln = self.lean(D, "EResult.val (Val.tuple [Val.int 0])")
        assert D.same(("bobj", "_HashedTuple", T0), ln, 0) is False
        assert D.shape_clash(("bobj", "_HashedTuple", T0), ln) is False

    def test_core_invented_a_class_is_a_divergence(self, D):
        ln = self.lean(D, 'EResult.val (Val.bobj "_HashedTuple" (Val.tuple [Val.int 0]))')
        assert D.same(T0, ln, 0) is False

    def test_opaque_ref_against_a_recorded_class_is_not_inconclusive(self, D):
        """Before builtin bases were modelled this was `representation:value-vs-object`.
        For a class both sides now model as a value, a `ref` from Core is a real
        disagreement and must be counted as one."""
        assert D.shape_clash(("bobj", "_HashedTuple", T0), ("ref", 0)) is False
        assert D.same(("bobj", "_HashedTuple", T0), ("ref", 0), 0) is False

    def test_unrecorded_container_vs_ref_is_still_inconclusive(self, D):
        assert D.shape_clash(T0, ("ref", 0)) is True

    def test_bobj_inside_containers(self, D):
        b = ("bobj", "_HashedTuple", T0)
        ln = self.lean(D, 'EResult.val (Val.tuple [Val.bobj "_HashedTuple" '
                          '(Val.tuple [Val.int 0])])')
        assert D.same(("tuple", [b]), ln, 0) is True
        assert D.same(("tuple", [T0]), ln, 0) is False
