#!/usr/bin/env python3
"""Contracts for external base classes: what a stdlib ABC contributes to a class namespace.

A corpus class whose base is not in the corpus (`class Cache(collections.abc.MutableMapping)`)
used to make the whole hierarchy unresolved: no attribute of any `Cache` instance could be
looked up, the oracle refused to encode such receivers, and 60,000 of cachetools' traced
calls were dropped. The honest alternative to "unresolved" is a *contract*: the exact set
of attribute names the external base provides beyond `object`, plus the abstract methods a
subclass must implement before it can be instantiated. With that, lookup through the base
is decidable -- an in-corpus member found first is the answer, a contracted name is a named
hole (its code is not translated), and a miss is CPython's `AttributeError`.

This file is the single source of truth. `Autoform/Lang/Core/ExternalBases.lean` is
emitted from it (`--emit-lean`; `tests/test_external_bases.py` fails if the two differ),
and `scripts/differential.py` verifies every contract against the live class before it
encodes a receiver whose MRO contains it, so a CPython whose ABCs differ from the pinned
sets refuses the case instead of comparing against a wrong model.

The sets were frozen from CPython 3.11.13 with `python3 scripts/external_bases.py
--freeze`: every name the ABC or one of its ancestors defines (`vars`, `object`
excluded, so overrides of `object` names count) and `cls.__abstractmethods__`. ABCs that
declare instance storage (`MappingView` and the views, `__slots__ = ('_mapping',)`) are not
contracted: the oracle snapshots instances field by field and would not see the base's. The ABCs' metaclass is
`ABCMeta`, which does not alter instance attribute lookup or a subclass namespace; the only
construction-time behaviour it adds -- refusing to instantiate a class with unimplemented
abstract methods, in `object.__new__` -- is what `abstract` is for.

Deliberately only `collections.abc`. `typing.Generic` rewrites subclass attributes in
`__init_subclass__`, `enum.Enum`'s metaclass rewrites the namespace, and the exception
hierarchy has its own representation in Core; none of those is a namespace contract.
"""
import argparse
import json
import os
import sys
from pathlib import Path

PINNED_PYTHON = "3.11"

# name -> (provides, abstract); both sorted.
CONTRACTS = {
    "collections.abc.AsyncGenerator": (
        ["__abstractmethods__", "__aiter__", "__anext__", "__class_getitem__", "__doc__", "__module__", "__slots__", "__subclasshook__", "_abc_impl", "aclose", "asend", "athrow"],
        ["asend", "athrow"]),
    "collections.abc.AsyncIterable": (
        ["__abstractmethods__", "__aiter__", "__class_getitem__", "__doc__", "__module__", "__slots__", "__subclasshook__", "_abc_impl"],
        ["__aiter__"]),
    "collections.abc.AsyncIterator": (
        ["__abstractmethods__", "__aiter__", "__anext__", "__class_getitem__", "__doc__", "__module__", "__slots__", "__subclasshook__", "_abc_impl"],
        ["__anext__"]),
    "collections.abc.Awaitable": (
        ["__abstractmethods__", "__await__", "__class_getitem__", "__doc__", "__module__", "__slots__", "__subclasshook__", "_abc_impl"],
        ["__await__"]),
    "collections.abc.ByteString": (
        ["__abstractmethods__", "__class_getitem__", "__contains__", "__doc__", "__getitem__", "__iter__", "__len__", "__module__", "__reversed__", "__slots__", "__subclasshook__", "_abc_impl", "count", "index"],
        ["__getitem__", "__len__"]),
    "collections.abc.Callable": (
        ["__abstractmethods__", "__call__", "__class_getitem__", "__doc__", "__module__", "__slots__", "__subclasshook__", "_abc_impl"],
        ["__call__"]),
    "collections.abc.Collection": (
        ["__abstractmethods__", "__class_getitem__", "__contains__", "__doc__", "__iter__", "__len__", "__module__", "__slots__", "__subclasshook__", "_abc_impl"],
        ["__contains__", "__iter__", "__len__"]),
    "collections.abc.Container": (
        ["__abstractmethods__", "__class_getitem__", "__contains__", "__doc__", "__module__", "__slots__", "__subclasshook__", "_abc_impl"],
        ["__contains__"]),
    "collections.abc.Coroutine": (
        ["__abstractmethods__", "__await__", "__class_getitem__", "__doc__", "__module__", "__slots__", "__subclasshook__", "_abc_impl", "close", "send", "throw"],
        ["__await__", "send", "throw"]),
    "collections.abc.Generator": (
        ["__abstractmethods__", "__class_getitem__", "__doc__", "__iter__", "__module__", "__next__", "__slots__", "__subclasshook__", "_abc_impl", "close", "send", "throw"],
        ["send", "throw"]),
    "collections.abc.Hashable": (
        ["__abstractmethods__", "__doc__", "__hash__", "__module__", "__slots__", "__subclasshook__", "_abc_impl"],
        ["__hash__"]),
    "collections.abc.Iterable": (
        ["__abstractmethods__", "__class_getitem__", "__doc__", "__iter__", "__module__", "__slots__", "__subclasshook__", "_abc_impl"],
        ["__iter__"]),
    "collections.abc.Iterator": (
        ["__abstractmethods__", "__class_getitem__", "__doc__", "__iter__", "__module__", "__next__", "__slots__", "__subclasshook__", "_abc_impl"],
        ["__next__"]),
    "collections.abc.Mapping": (
        ["__abstractmethods__", "__class_getitem__", "__contains__", "__doc__", "__eq__", "__getitem__", "__hash__", "__iter__", "__len__", "__module__", "__reversed__", "__slots__", "__subclasshook__", "_abc_impl", "get", "items", "keys", "values"],
        ["__getitem__", "__iter__", "__len__"]),
    "collections.abc.MutableMapping": (
        ["_MutableMapping__marker", "__abstractmethods__", "__class_getitem__", "__contains__", "__delitem__", "__doc__", "__eq__", "__getitem__", "__hash__", "__iter__", "__len__", "__module__", "__reversed__", "__setitem__", "__slots__", "__subclasshook__", "_abc_impl", "clear", "get", "items", "keys", "pop", "popitem", "setdefault", "update", "values"],
        ["__delitem__", "__getitem__", "__iter__", "__len__", "__setitem__"]),
    "collections.abc.MutableSequence": (
        ["__abstractmethods__", "__class_getitem__", "__contains__", "__delitem__", "__doc__", "__getitem__", "__iadd__", "__iter__", "__len__", "__module__", "__reversed__", "__setitem__", "__slots__", "__subclasshook__", "_abc_impl", "append", "clear", "count", "extend", "index", "insert", "pop", "remove", "reverse"],
        ["__delitem__", "__getitem__", "__len__", "__setitem__", "insert"]),
    "collections.abc.MutableSet": (
        ["__abstractmethods__", "__and__", "__class_getitem__", "__contains__", "__doc__", "__eq__", "__ge__", "__gt__", "__hash__", "__iand__", "__ior__", "__isub__", "__iter__", "__ixor__", "__le__", "__len__", "__lt__", "__module__", "__or__", "__rand__", "__ror__", "__rsub__", "__rxor__", "__slots__", "__sub__", "__subclasshook__", "__xor__", "_abc_impl", "_from_iterable", "_hash", "add", "clear", "discard", "isdisjoint", "pop", "remove"],
        ["__contains__", "__iter__", "__len__", "add", "discard"]),
    "collections.abc.Reversible": (
        ["__abstractmethods__", "__class_getitem__", "__doc__", "__iter__", "__module__", "__reversed__", "__slots__", "__subclasshook__", "_abc_impl"],
        ["__iter__", "__reversed__"]),
    "collections.abc.Sequence": (
        ["__abstractmethods__", "__class_getitem__", "__contains__", "__doc__", "__getitem__", "__iter__", "__len__", "__module__", "__reversed__", "__slots__", "__subclasshook__", "_abc_impl", "count", "index"],
        ["__getitem__", "__len__"]),
    "collections.abc.Set": (
        ["__abstractmethods__", "__and__", "__class_getitem__", "__contains__", "__doc__", "__eq__", "__ge__", "__gt__", "__hash__", "__iter__", "__le__", "__len__", "__lt__", "__module__", "__or__", "__rand__", "__ror__", "__rsub__", "__rxor__", "__slots__", "__sub__", "__subclasshook__", "__xor__", "_abc_impl", "_from_iterable", "_hash", "isdisjoint"],
        ["__contains__", "__iter__", "__len__"]),
    "collections.abc.Sized": (
        ["__abstractmethods__", "__doc__", "__len__", "__module__", "__slots__", "__subclasshook__", "_abc_impl"],
        ["__len__"]),
}

# Methods of a contracted base whose CODE is modelled, not just named. Only what a measured
# need required: `MutableMapping.popitem`, which `cachetools.Cache.__setitem__` calls to
# make room (the 7.1.6 replace-grow path, docs/evidence-cachetools.md). Each entry is the
# CPython source text of the method (`source`, verbatim from `Lib/_collections_abc.py` of
# the pinned version, the file `verify` re-reads) and its Core translation (`core`), which
# is what `cartographer/export_ast.sc` emits for that exact text inside a class of the same
# name -- produced by running the exporter, not written by hand, and re-checked by
# `tests/test_external_bases.py` against a fresh export when Joern is available. The
# method is emitted into `Autoform/Lang/Core/ExternalMethods.lean` under the reserved name
# `<external>module.qualname.method`, which no source language can spell; every other
# contracted name stays an opaque member.
METHODS = {
    "collections.abc.MutableMapping": {
        "popitem": {
            "source": "    def popitem(self):\n        '''D.popitem() -> (k, v), remove and return some (key, value) pair\n           as a 2-tuple; but raise KeyError if D is empty.\n        '''\n        try:\n            key = next(iter(self))\n        except StopIteration:\n            raise KeyError from None\n        value = self[key]\n        del self[key]\n        return key, value\n",
            "core": json.loads('{"k": "seq", "a": {"k": "exprS", "e": {"k": "str", "v": "D.popitem() -> (k, v), remove and return some (key, value) pair\\n           as a 2-tuple; but raise KeyError if D is empty.\\n        "}}, "b": {"k": "seq", "a": {"k": "skip"}, "b": {"k": "seq", "a": {"k": "tryCatch", "body": {"k": "assign", "x": "key", "e": {"k": "call", "f": "next", "args": [{"k": "call", "f": "iter", "args": [{"k": "name", "v": "self"}]}]}}, "x": "$exprV$2", "handler": {"k": "ifte", "c": {"k": "inOp", "neg": false, "a": {"k": "name", "v": "$exprV$2"}, "b": {"k": "tupleE", "items": [{"k": "str", "v": "StopIteration"}]}}, "t": {"k": "raise", "e": {"k": "unop", "op": "py:exception:KeyError", "a": {"k": "tupleE", "items": []}}}, "e": {"k": "raise", "e": {"k": "name", "v": "$exprV$2"}}}}, "b": {"k": "seq", "a": {"k": "skip"}, "b": {"k": "seq", "a": {"k": "assign", "x": "value", "e": {"k": "index", "a": {"k": "name", "v": "self"}, "b": {"k": "name", "v": "key"}}}, "b": {"k": "seq", "a": {"k": "skip"}, "b": {"k": "seq", "a": {"k": "delIndex", "a": {"k": "name", "v": "self"}, "i": {"k": "name", "v": "key"}}, "b": {"k": "seq", "a": {"k": "skip"}, "b": {"k": "seq", "a": {"k": "ret", "e": {"k": "tupleE", "items": [{"k": "name", "v": "key"}, {"k": "name", "v": "value"}]}}, "b": {"k": "skip"}}}}}}}}}}'),
        },
    },
}

PREFIX = "<external>"


def external_name(cls):
    """`module.qualname` of a live class, the key `CONTRACTS` is indexed by."""
    return "%s.%s" % (cls.__module__, cls.__qualname__)


def chain(cls):
    """The external class and its ancestors, `object` excluded."""
    return [c for c in cls.__mro__ if c is not object]


def live_contract(cls):
    """The contract the running interpreter would state for `cls`: every name the class
    or an ancestor DEFINES (so an override of an `object` name such as `__eq__` or
    `__init__` is included -- `dir(cls) - dir(object)` would hide exactly those), and the
    abstract methods a subclass must implement."""
    return (sorted({n for c in chain(cls) for n in vars(c)}),
            sorted(getattr(cls, "__abstractmethods__", ())))


def has_storage(cls):
    """Does the class or an ancestor declare instance storage (`__slots__` other than `()`)?
    The oracle snapshots instances field by field, so such a base cannot be contracted."""
    return any(vars(c).get("__slots__", None) != () for c in chain(cls))


def live_method_source(cls, method):
    """The source text of `cls.method` as the running interpreter's stdlib file spells it,
    or None if it cannot be read. `collections.abc` is frozen in CPython 3.11, so
    `inspect.getsource` refuses; the module's `.py` is still shipped in the stdlib
    directory, and the method is located in it with `ast` (exact line span)."""
    import ast
    import sysconfig
    code = getattr(getattr(cls, method, None), "__code__", None)
    if code is None:
        return None
    path = code.co_filename
    if path.startswith("<frozen ") and path.endswith(">"):
        path = os.path.join(sysconfig.get_paths()["stdlib"], path[len("<frozen "):-1] + ".py")
    try:
        text = Path(path).read_text(encoding="utf-8")
    except OSError:
        return None
    lines = text.splitlines(keepends=True)
    for node in ast.walk(ast.parse(text)):
        if isinstance(node, ast.ClassDef) and node.name == cls.__qualname__:
            for item in node.body:
                if isinstance(item, ast.FunctionDef) and item.name == method:
                    return "".join(lines[item.lineno - 1:item.end_lineno])
    return None


def verify(cls):
    """`None` if `cls` is contracted and the live class matches the pinned contract,
    else the reason it cannot be used as a contracted external base. A base with modelled
    methods (`METHODS`) additionally needs each method's live source to be the pinned
    text, since the model IS a translation of that text."""
    name = external_name(cls)
    pinned = CONTRACTS.get(name)
    if pinned is None:
        return "external-base-uncontracted:" + name
    if has_storage(cls):
        return "external-base-storage:" + name
    if live_contract(cls) != tuple(pinned):
        return "external-base-contract-mismatch:" + name
    for method, entry in sorted(METHODS.get(name, {}).items()):
        if live_method_source(cls, method) != entry["source"]:
            return "external-base-method-source-mismatch:%s.%s" % (name, method)
    return None


def lean_text():
    out = ["import Std", "",
           "/-! Generated by `scripts/external_bases.py --emit-lean`. Do not edit by hand:",
           "the Python file is the source of truth and `tests/test_external_bases.py` compares",
           "the two. Contracts frozen from CPython %s; `scripts/differential.py` verifies each" % PINNED_PYTHON,
           "against the live class before encoding a receiver whose MRO contains it. -/", "",
           "namespace Autoform.Core", "",
           "/-- What an external base contributes to a class namespace: the attribute names it",
           "provides beyond `object` (each one a named hole when reached, because its code is",
           "not translated) and the abstract methods a subclass must define to be instantiable. -/",
           "structure ExternalBase where",
           "  provides : List String",
           "  abstract : List String",
           "  deriving Repr, Inhabited, BEq", "",
           "/-- The marker a contracted base carries in `ClassDecl.bases`: `<external>` and the",
           "class's `module.qualname`. No source language can spell it. -/",
           'def externalBasePrefix : String := "%s"' % PREFIX, "",
           "def externalBaseContracts : List (String × ExternalBase) :="]
    rows = []
    for name in sorted(CONTRACTS):
        provides, abstract = CONTRACTS[name]
        rows.append("  (%s,\n   { provides := [%s],\n     abstract := [%s] })"
                    % (json.dumps(PREFIX + name),
                       ", ".join(json.dumps(p) for p in provides),
                       ", ".join(json.dumps(a) for a in abstract)))
    out.append("  [" + ",\n".join(rows)[2:] + "]")
    out += ["",
            "/-- The contract of a base name, if it is a contracted external base. Exact key",
            "match on the marker, so the kernel decides it without any prefix test. -/",
            "def externalContract (name : String) : Option ExternalBase :=",
            "  (externalBaseContracts.find? (·.1 == name)).map Prod.snd", "",
            "/-- Contracted names whose CODE is modelled (`ExternalMethods.lean`): `(base, name)`.",
            "Lookup through the base answers these with the method",
            "`externalMethodName base name` instead of an opaque member. -/",
            "def externalModelled : List (String × String) :=",
            "  [" + ", ".join("(%s, %s)" % (json.dumps(PREFIX + b), json.dumps(m))
                            for b in sorted(METHODS) for m in sorted(METHODS[b])) + "]", "",
            "/-- The reserved function name of a modelled external method. -/",
            "def externalMethodName (base attr : String) : String := base ++ \".\" ++ attr", "",
            "end Autoform.Core", ""]
    return "\n".join(out)


def methods_lean_text():
    """`Autoform/Lang/Core/ExternalMethods.lean`: the modelled methods as Core functions,
    rendered by the corpus renderer (`cartographer/render_lean.py`) from `METHODS`."""
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "cartographer"))
    import render_lean
    out = ["import Autoform.Lang.Core.Syntax", "",
           "/-! Generated by `scripts/external_bases.py --emit-lean`. Do not edit by hand.",
           "The methods of contracted external bases whose code is modelled: each is the",
           "exporter's translation of the pinned CPython %s source text recorded in" % PINNED_PYTHON,
           "`scripts/external_bases.py` (`METHODS`), which `verify` compares with the live",
           "stdlib before the oracle encodes a receiver through the base. -/", "",
           "namespace Autoform.Core", "namespace ExternalMethods", ""]
    names = []
    for base in sorted(METHODS):
        for method in sorted(METHODS[base]):
            ident = "m_" + "".join(c if c.isalnum() else "_" for c in base + "_" + method)
            names.append(ident)
            func = {"name": PREFIX + base + "." + method, "file": "<external>",
                    "params": [], "body": METHODS[base][method]["core"],
                    "pythonSignature": {"positionalOnly": [], "keywordOnly": [],
                                        "required": [], "isMethod": True}}
            out += render_lean.render_func(func, ident)
    out += ["/-- Every modelled external method. -/",
            "def all : List Func := [%s]" % ", ".join(names), "",
            "end ExternalMethods", "",
            "/-- The modelled external method of this reserved name, if any. -/",
            "def externalMethod (name : String) : Option Func :=",
            "  ExternalMethods.all.find? (·.name == name)", "",
            "end Autoform.Core", ""]
    return "\n".join(out)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--emit-lean", metavar="PATH",
                    help="write the Lean mirror (Autoform/Lang/Core/ExternalBases.lean)")
    ap.add_argument("--freeze", action="store_true",
                    help="print the contracts the running interpreter states, as Python")
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if the running interpreter disagrees with the pinned contracts")
    args = ap.parse_args(argv)
    if args.freeze:
        import collections.abc as abc
        for attr in sorted(dir(abc)):
            cls = getattr(abc, attr)
            if isinstance(cls, type) and not attr.startswith("_"):
                if has_storage(cls):
                    print("# storage, not contracted:", external_name(cls))
                    continue
                print(json.dumps(external_name(cls)), json.dumps(live_contract(cls)))
        return 0
    if args.emit_lean:
        Path(args.emit_lean).write_text(lean_text(), encoding="utf-8")
        print("wrote", args.emit_lean, "(%d contracts)" % len(CONTRACTS))
        methods_path = Path(args.emit_lean).with_name("ExternalMethods.lean")
        methods_path.write_text(methods_lean_text(), encoding="utf-8")
        print("wrote", methods_path, "(%d modelled methods)"
              % sum(len(m) for m in METHODS.values()))
    if args.check:
        import importlib
        bad = []
        for name in sorted(CONTRACTS):
            module, _, qual = name.rpartition(".")
            cls = getattr(importlib.import_module(module), qual)
            reason = verify(cls)
            if reason:
                bad.append(reason)
        print("%d contracts; %d disagree with Python %s" % (len(CONTRACTS), len(bad), sys.version.split()[0]))
        for reason in bad:
            print("  " + reason)
        return 1 if bad else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
