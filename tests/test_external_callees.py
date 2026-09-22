"""`scripts/external_callees.py` ranks the calls that leave a translated program.

The ledger's verifiable core is hole-free AND call-closed; the gap between the two
counts is exactly the functions this script explains. Its resolvability rule must mirror
`Autoform/Ledger.lean`'s `Ctx.resolvable` -- unique dotted-suffix for free calls, any
suffix for method calls, modelled Python builtins resolvable -- or the table it prints
would recommend contracting callees the ledger already counts as closed (or miss ones it
does not)."""
import importlib.util
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]


@pytest.fixture(scope="module")
def mod():
    spec = importlib.util.spec_from_file_location(
        "external_callees", ROOT / "scripts" / "external_callees.py")
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def _fn(name, body, file="m.py"):
    return {"name": name, "file": file, "params": [], "body": body}


def _call(f, *args):
    return {"k": "call", "f": f, "args": list(args)}


def _mcall(recv, m, *args):
    return {"k": "mcall", "recv": recv, "m": m, "args": list(args)}


def _ret(e):
    return {"k": "ret", "e": e}


def test_resolver_mirrors_the_ledgers_three_arms(mod):
    names = ["m.py:<module>.helper", "m.py:<module>.A.clear", "m.py:<module>.B.clear", "plain"]
    r = mod.Resolver(names, "python")
    # unique dotted tail: resolvable as a free call
    assert r.free("helper")
    # ambiguous tail (A.clear / B.clear): `Ctx.resolve` returns none -> NOT resolvable
    assert not r.free("clear")
    # ...but the method path takes the first match
    assert r.method("clear")
    # exact key without a dot
    assert r.free("plain")
    # a substring that is not a dotted tail never matches
    assert not r.free("lper") and not r.method("lper")
    # a modelled Python builtin is resolvable on the free path, under .python only
    assert r.free("len")
    assert not mod.Resolver(names, "cLike").free("len")


def test_python_builtins_are_read_from_stdlib_not_hardcoded(mod):
    names = mod.python_free_names()
    assert {"len", "abs", "isinstance", "KeyError", "ValueError",
            "iter", "next", "<python-iter>", "<python-next>"} <= names


def test_external_callees_are_keyed_by_receiver_and_counted(mod, tmp_path):
    ast = [
        _fn("m.py:<module>.a", _ret(_call("strlen", {"k": "name", "v": "s"})), file="m.c"),
        _fn("m.py:<module>.b", _ret(_mcall({"k": "name", "v": "Math"}, "max")), file="m.c"),
        _fn("m.py:<module>.c", _ret(_mcall({"k": "call", "f": "g", "args": []}, "pop")), file="m.c"),
        # in-program callee: closed, contributes nothing
        _fn("m.py:<module>.d", _ret(_call("a")), file="m.c"),
        # a hole-y function is not "hole-free but open", but its sites still count
        _fn("m.py:<module>.e", {"k": "seq", "a": {"k": "holeS", "label": "x"},
                                "b": _ret(_call("strlen"))}, file="m.c"),
    ]
    p = tmp_path / "ast-T.json"
    p.write_text(json.dumps(ast))
    rep = mod.analyse(str(p))
    assert rep["dialect"] == "cLike"
    ext = rep["external_callees"]
    assert ext["strlen"] == {"sites": 2, "blocks": 1}
    assert ext["Math.max"] == {"sites": 1, "blocks": 1}
    assert ext[".pop"]["sites"] == 1
    # `c` has TWO external callees (`g` is not a table key either), so neither one alone
    # would close it: `blocks` credits only a function's sole open callee.
    assert ext[".pop"]["blocks"] == 0
    assert ext["g"] == {"sites": 1, "blocks": 0}
    assert rep["hole_free_but_open"] == 3
    assert rep["per_function"]["m.py:<module>.e"] == ["strlen"]


def test_ranking_prefers_what_unlocks_functions(mod):
    reports = [{"artifact": "ast-X.json", "dialect": "cLike",
                "external_callees": {"noisy": {"sites": 50, "blocks": 0},
                                     "useful": {"sites": 3, "blocks": 3}}}]
    ranking = mod.aggregate(reports)
    assert [r["callee"] for r in ranking] == ["useful", "noisy"]
    assert ranking[0]["corpora"] == ["X(cLike)"]


def test_cli_writes_json(mod, tmp_path, capsys):
    p = tmp_path / "ast-T.json"
    p.write_text(json.dumps([_fn("m.py:<module>.a", _ret(_call("strlen")), file="m.c")]))
    out = tmp_path / "r.json"
    assert mod.main([str(p), "--json", str(out), "--top", "5"]) == 0
    data = json.loads(out.read_text())
    assert data["ranking"][0]["callee"] == "strlen"
    assert "| 1 | `strlen` |" in capsys.readouterr().out


def test_generator_analysis_keeps_source_calls_and_resolves_helpers(mod, tmp_path):
    from generator_lowering import name, node
    generator = _fn("m.py:<module>.stream", node("yieldS", e=_call("remote")))
    generator["generator"] = {"locals": [], "captures": [], "parameters": []}
    expression = _fn("m.py:<module>.expression", _ret(node("genExpr", sink="tmp",
        generator={"locals": ["x"], "captures": []}, body=node("forIn", x="x",
            e=node("listE", items=[]), body=node("exprS", e=_mcall(
                name("tmp"), "append", _call("remote")))))))
    path = tmp_path / "ast-generators.json"
    path.write_text(json.dumps([generator, expression]))
    report = mod.analyse(str(path))
    assert report["functions"] == 2
    assert report["hole_free_but_open"] == 2
    assert report["external_callees"] == {"remote": {"sites": 2, "blocks": 2}}


def test_deep_source_does_not_exhaust_the_python_stack(mod, tmp_path):
    depth = 2500
    body = ('{"k":"seq","a":{"k":"skip"},"b":' * depth
            + '{"k":"ret","e":{"k":"call","f":"remote","args":[]}}'
            + '}' * depth)
    path = tmp_path / "ast-deep.json"
    path.write_text('[{"name":"deep","file":"m.c","params":[],"body":' + body + '}]')
    assert mod.analyse(str(path))["external_callees"] == {
        "remote": {"sites": 1, "blocks": 1}}
