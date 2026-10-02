"""Two wrong translations in `ast-Cachetools.json` that a differential run once reported as
conformance or divergence (docs/conformance.md, findings 1 and 2). Both were fixed in
`cartographer/export_ast.sc`; these tests read the committed AST, so a re-export with an
exporter that regresses either one fails here without Joern or the corpus.

1. **Generators.** `pysrc2cpg` lowers `yield` to a RETURN node, and the exporter emitted
   `ret` for it: "return the first live key" for `TTLCache.__iter__`. A generator must be a
   hole (`gen:generator`) so it can never be hole-free.
2. **Calls through a local or captured name.** `cache(self)` inside `_locked.wrapper`
   (where `cache` is `_locked`'s parameter) was bound to `_WrapperBase.cache`, a property
   of an unrelated class. No call may be bound to a qualified function whose short name
   is bound locally in the caller or an enclosing function, unless it is that scope's
   own nested `def` of the name.
"""
from __future__ import annotations

import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
AST = os.path.join(ROOT, "ast-Cachetools.json")


def _load():
    with open(AST) as fh:
        return json.load(fh)


def _walk(x):
    if isinstance(x, dict):
        yield x
        for v in x.values():
            yield from _walk(v)
    elif isinstance(x, list):
        for v in x:
            yield from _walk(v)


def _labels(f):
    return [n.get("label") for n in _walk(f) if n.get("k") in ("hole", "holeS")]


def _bound(f):
    s = set(f.get("params", []))
    s.update(f[k] for k in ("vararg", "kwarg") if f.get(k))
    s.update(n["x"] for n in _walk(f["body"])
             if n.get("k") == "assign" and isinstance(n.get("x"), str))
    return s


def misbound_calls(funcs):
    """(caller, callee, binding scope) for every call bound to a qualified function whose
    short name the caller's scope chain binds, other than that scope's own `def`."""
    by = {f["name"]: f for f in funcs}
    out = []
    for f in funcs:
        chain, cur = [f["name"]], f["name"]
        while "." in cur.split(":<module>.", 1)[-1]:
            cur = cur.rsplit(".", 1)[0]
            if cur in by:
                chain.append(cur)
        for n in _walk(f["body"]):
            if n.get("k") != "call" or ":" not in n.get("f", ""):
                continue
            q = n["f"]
            short = q.rsplit(".", 1)[-1]
            for sc in chain:
                if short in _bound(by[sc]):
                    if q != sc + "." + short:
                        out.append((f["name"], q, sc))
                    break
    return out


def test_generators_are_holes_not_returns():
    funcs = {f["name"]: f for f in _load()}
    for cls in ("TTLCache", "TLRUCache"):
        f = funcs["cachetools/__init__.py:<module>.%s.__iter__" % cls]
        labels = _labels(f)
        assert "gen:generator" in labels, (cls, labels)
        assert "gen:yield" in labels, (cls, labels)
        # the leading statement is the hole: nothing of the body runs at call time
        assert f["body"]["k"] == "seq" and f["body"]["a"] == {"k": "holeS", "label": "gen:generator"}


def test_no_call_is_bound_to_an_unrelated_function_of_a_local_name():
    assert misbound_calls(_load()) == []


def test_the_scan_detects_the_original_misbinding():
    """The scan must not pass by finding nothing: the shape the old exporter emitted."""
    funcs = [
        {"name": "m.py:<module>._locked", "params": ["method", "cache"],
         "body": {"k": "assign", "x": "wrapper", "e": {"k": "closure", "f": "m.py:<module>._locked.wrapper"}}},
        {"name": "m.py:<module>._locked.wrapper", "params": ["self"],
         "body": {"k": "ret", "e": {"k": "call", "f": "m.py:<module>._WrapperBase.cache",
                                     "args": [{"k": "name", "v": "self"}]}}},
        {"name": "m.py:<module>._WrapperBase.cache", "params": [], "body": {"k": "skip"}},
    ]
    assert misbound_calls(funcs) == [("m.py:<module>._locked.wrapper",
                                      "m.py:<module>._WrapperBase.cache",
                                      "m.py:<module>._locked")]
    funcs[1]["body"]["e"]["f"] = "cache"
    assert misbound_calls(funcs) == []
