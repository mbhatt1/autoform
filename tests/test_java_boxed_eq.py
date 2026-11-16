"""JVM boxed `==`/`!=`: Kotlin value equality, Java box identity, unboxing guards.

The exporter used to turn a comparison on a boxed JVM value into the static hole
`numeric:unknown-type:<op>` (Java `box == primitive`) or into a value comparison where
the JVM runs a reference comparison (Java `box == box`, whose value equality holds only
inside the box cache), so any function comparing boxes was never hole-free. Kotlin `==`
on a nullable number is `equals` (value equality, null-safe), and kotlin2cpg erases
nullability (`Int?` types as `int`), so the plain `Int` comparison was a typed `==` that
diverged on null.

Shapes per case, exported through Joern (`AUTOFORM_TEST_JOERN=1`): Java box==box
(`Double`/`Float` included) is the named hole `numeric:java-box-identity` (reference
identity is not modelled) with both operands still evaluated; Java box==primitive unboxes
-- a null box raises `NullPointerException` where javac unboxes it, a left box before the
right operand runs, a right box after it -- then compares after binary numeric promotion; Kotlin `==`/`!=` on nullable/erased numerics is
`a == null ? b == null : a.equals(b)` with `equals` as the typed comparison. `===`
compiles to the same call name but with type ANY; it keeps its pre-existing lowering
(the conflation is kotlin2cpg's, see docs/languages.md).
"""
import json
import os
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "tests" / "fixtures" / "java_boxed_eq"


def _joern():
    home = Path(os.environ.get("JOERN_HOME", Path.home() / "joern"))
    return home / "joern-cli" if (home / "joern-cli").is_dir() else home


def _run(args, cwd, timeout=900):
    r = subprocess.run([str(a) for a in args], cwd=str(cwd), capture_output=True, text=True,
                       timeout=timeout)
    assert r.returncode == 0, (r.stdout + r.stderr)[-3000:]
    return r.stdout


@pytest.fixture(scope="module")
def exported(tmp_path_factory):
    if os.environ.get("AUTOFORM_TEST_JOERN") != "1":
        pytest.skip("set AUTOFORM_TEST_JOERN=1 to export the JVM fixtures through Joern")
    joern = _joern()
    if not (joern / "joern").is_file():
        pytest.skip("Joern not found (JOERN_HOME)")
    tmp = tmp_path_factory.mktemp("boxeq")
    out = {}
    for lang in ("java", "kotlin"):
        cpg, ast = tmp / (lang + ".bin"), tmp / (lang + ".json")
        _run([joern / "joern-parse", FIXTURE / lang, "--output", cpg], tmp)
        _run([joern / "joern", "--script", ROOT / "cartographer/export_ast.sc",
              "--param", "cpgPath=%s" % cpg, "--param", "out=%s" % ast,
              "--param", "dataModel=lp64"], tmp)
        out[lang] = json.loads(ast.read_text())
    return out


def _func(funcs, short):
    hit = [f for f in funcs if f["name"].split(":")[0].split(".")[-1] == short]
    assert len(hit) == 1, (short, [f["name"] for f in funcs])
    return hit[0]


def _holes(body):
    out = []
    stack = [body]
    while stack:
        v = stack.pop()
        if isinstance(v, dict):
            if v.get("k") in ("hole", "holeS"):
                out.append(v["label"])
            stack.extend(v.values())
        elif isinstance(v, list):
            stack.extend(v)
    return out


def _n(v):
    return {"k": "name", "v": v}


def _i(v):
    return {"k": "int", "v": str(v)}


def _u():
    return {"k": "unit"}


def _b(op, a, b):
    return {"k": "binop", "op": op, "a": a, "b": b}


def _un(op, a):
    return {"k": "unop", "op": op, "a": a}


def _ifte(c, t, e):
    return {"k": "ifte", "c": c, "t": t, "e": e}


def _cond(c, t, e):
    return {"k": "cond", "c": c, "t": t, "e": e}


def _ret(e):
    return {"k": "ret", "e": e}


def _seq(*stmts):
    out = stmts[-1]
    for s in reversed(stmts[:-1]):
        out = {"k": "seq", "a": s, "b": out}
    return out


def _raise(name):
    return {"k": "raise", "e": {"k": "str", "v": name}}


def _assign(x, e):
    return {"k": "assign", "x": x, "e": e}


def _skip():
    return {"k": "skip"}


def _hole(label):
    return {"k": "hole", "label": label}


def _call(f):
    return {"k": "call", "f": f, "args": []}


def _npe(e):
    return _ifte(_b("==", e, _u()), _raise("NullPointerException"), _skip())


def _ktEquals(a, b, w):
    """`a == null ? b == null : a.equals(b)`, `equals` as the typed comparison."""
    return _cond(_b("==", a, _u()), _b("==", b, _u()),
                 _b("&&", _un("!", _b("==", b, _u())), _b("num:java:%s:==" % w, a, b)))


def _retOf(body):
    while body.get("k") != "ret":
        body = body["b"]
    return body["e"]


def test_only_the_identity_comparisons_stay_holes(exported):
    holed = {}
    for lang in ("java", "kotlin"):
        for f in exported[lang]:
            h = _holes(f["body"])
            if h:
                holed[f["name"].split(":")[0].split(".")[-1]] = h
    assert holed == {"intBox": ["numeric:java-box-identity"],
                     "intBoxNe": ["numeric:java-box-identity"],
                     "longBox": ["numeric:java-box-identity"],
                     "boolBox": ["numeric:java-box-identity"],
                     "charBox": ["numeric:java-box-identity"],
                     "dblBox": ["numeric:java-box-identity"],
                     "callRes": ["numeric:java-box-identity"]}, holed


def test_java_box_pair_is_a_named_hole(exported):
    funcs = exported["java"]
    for short in ("intBox", "intBoxNe", "longBox", "boolBox", "charBox", "dblBox"):
        assert _func(funcs, short)["body"] == _ret(_hole("numeric:java-box-identity")), short


def test_java_box_pair_still_evaluates_both_operands(exported):
    """Reference identity is not modelled, but the comparison still runs its operands,
    in source order, before the hole is reached."""
    body = _func(exported["java"], "callRes")["body"]
    text = json.dumps(body)
    assert text.count('"Box.getI:') == 2, text
    assert _retOf(body) == _hole("numeric:java-box-identity")


def test_java_box_vs_primitive_unboxes_with_npe_guard(exported):
    funcs = exported["java"]
    assert _func(funcs, "boxPrim")["body"] == \
        _seq(_npe(_n("a")), _ret(_b("num:java:i32:==", _n("a"), _n("b"))))
    assert _func(funcs, "primBox")["body"] == \
        _seq(_npe(_n("b")), _ret(_b("num:java:i32:==", _n("a"), _n("b"))))
    assert _func(funcs, "boxPrimNe")["body"] == \
        _seq(_npe(_n("a")), _ret(_b("num:java:i32:!=", _n("a"), _n("b"))))
    assert _func(funcs, "litBox")["body"] == \
        _seq(_npe(_n("a")), _ret(_b("num:java:i32:==", _n("a"), _i(5))))
    # `long` keeps its width; `char` against `char` promotes to `int` (JLS 5.6.2).
    assert _func(funcs, "longPrim")["body"] == \
        _seq(_npe(_n("a")), _ret(_b("num:java:i64:==", _n("a"), _n("b"))))
    assert _func(funcs, "charPrim")["body"] == \
        _seq(_npe(_n("a")), _ret(_b("num:java:i32:==", _n("a"), _n("b"))))
    # A `Boolean` unboxes to a value comparison, not a numeric one.
    assert _func(funcs, "boolPrim")["body"] == \
        _seq(_npe(_n("a")), _ret(_b("==", _n("a"), _n("b"))))
    # A `Double` unboxes too, then compares as `double == double` always has.
    assert _func(funcs, "dblPrim")["body"] == \
        _seq(_npe(_n("a")), _ret(_b("==", _n("a"), _n("b"))))
    # The guard is placed where the comparison sits, also as a call argument.
    assert _func(funcs, "argBox")["body"] == \
        _seq(_npe(_n("a")), _ret({"k": "call", "f": "Box.id:boolean(boolean)",
                                  "args": [_b("num:java:i32:==", _n("a"), _n("b"))]}))


def test_java_unboxing_raises_where_javac_unboxes(exported):
    """javac unboxes an operand as soon as it is evaluated: a null right box raises after
    the left operand has run, a null left box before the right operand runs."""
    funcs = exported["java"]
    body = _func(funcs, "rightBox")["body"]
    t = body["a"]["x"]
    assert body == _seq(_assign(t, _call("Box.getP:int()")), _npe(_n("a")),
                        _ret(_b("num:java:i32:==", _n(t), _n("a"))))
    body = _func(funcs, "leftPrelude")["body"]
    t = body["a"]["x"]
    assert body["a"] == _assign(t, _n("a"))
    assert body["b"]["a"] == _npe(_n(t))
    assert body["b"]["b"]["a"]["x"] == "x"
    assert _retOf(body) == _b("num:java:i32:==", _n(t), _n("x"))


def test_java_impure_box_operand_is_evaluated_once(exported):
    body = _func(exported["java"], "callPrim")["body"]
    text = json.dumps(body)
    assert text.count('"Box.getI:') == 1, text
    temp = body["a"]["x"]
    assert body == _seq(_assign(temp, _call("Box.getI:java.lang.Integer()")),
                        _npe(_n(temp)), _ret(_b("num:java:i32:==", _n(temp), _i(5))))


def test_java_comparisons_the_change_must_not_touch(exported):
    funcs = exported["java"]
    assert _func(funcs, "plain")["body"] == _ret(_b("num:java:i32:==", _n("a"), _n("b")))
    assert _func(funcs, "strBox")["body"] == _ret(_b("==", _n("a"), _n("b")))
    assert _func(funcs, "nullBox")["body"] == _ret(_b("==", _n("a"), _u()))
    # An unboxing assignment was already a cast; the fix is only about `==`.
    text = json.dumps(_func(funcs, "unboxAssign")["body"])
    assert "hole" not in text and '"cast:i32"' in text


def test_kotlin_nullable_equality_is_null_safe_value_equality(exported):
    funcs = exported["kotlin"]
    # `longLocal` compares its local `a` against its parameter `x` (Eq.kt), so its
    # right operand is `x`; every other case compares parameters or locals named a/b.
    for short, w, rhs in (("nulIntEq", "i32", "b"), ("nulLongEq", "i64", "b"),
                          ("nulCharEq", "i32", "b"), ("plainIntEq", "i32", "b"),
                          ("localNullable", "i32", "b"), ("longLocal", "i64", "x")):
        assert _retOf(_func(funcs, short)["body"]) == _ktEquals(_n("a"), _n(rhs), w), short
    assert _retOf(_func(funcs, "nulIntNe")["body"]) == _un("!", _ktEquals(_n("a"), _n("b"), "i32"))


def test_kotlin_literal_operand_is_guarded_on_the_other_side(exported):
    funcs = exported["kotlin"]
    guard = _b("&&", _un("!", _b("==", _n("a"), _u())),
               _b("num:java:i32:==", _n("a"), _i(5)))
    assert _retOf(_func(funcs, "intLitEq")["body"]) == guard
    assert _retOf(_func(funcs, "intLitNe")["body"]) == _un("!", guard)
    assert _retOf(_func(funcs, "callEq")["body"]) == _b(
        "&&", _un("!", _b("==", _n("a"), _u())), _b("num:java:i32:==", _n("a"), _i(3)))
    # A `java.lang.Integer?` parameter keeps its box type, but the comparison is the same.
    assert _retOf(_func(funcs, "fromJava")["body"]) == _b(
        "&&", _un("!", _b("==", _n("b"), _u())), _b("num:java:i32:==", _n("b"), _i(5)))


def test_kotlin_null_literal_is_a_null_test(exported):
    funcs = exported["kotlin"]
    assert _retOf(_func(funcs, "nullCheck")["body"]) == _b("==", _n("a"), _u())
    assert _retOf(_func(funcs, "nullCheckNe")["body"]) == _un("!", _b("==", _n("a"), _u()))


def test_kotlin_impure_operands_are_evaluated_before_the_guard(exported):
    body = _func(exported["kotlin"], "callCmp")["body"]
    text = json.dumps(body)
    assert text.count('"retNullable:int(int)"') == 2, text
    t0 = body["a"]["x"]
    t1 = body["b"]["a"]["x"]
    assert _retOf(body) == _ktEquals(_n(t0), _n(t1), "i32")


def test_kotlin_equality_as_call_argument_and_impure_right(exported):
    funcs = exported["kotlin"]
    arg = _retOf(_func(funcs, "argEq")["body"])
    assert arg["k"] == "call" and arg["args"] == [_ktEquals(_n("a"), _n("b"), "i32")], arg
    # The left operand is read before the right one's call runs.
    body = _func(funcs, "callRight")["body"]
    t0, t1 = body["a"]["x"], body["b"]["a"]["x"]
    assert body["a"] == _assign(t0, _n("a"))
    assert _retOf(body) == _ktEquals(_n(t0), _n(t1), "i32")


def test_kotlin_box_pair_and_booleans_stay_generic(exported):
    funcs = exported["kotlin"]
    # `b == b` on one box is `equals` here too, and the null-safe generic `==` is that.
    assert _retOf(_func(funcs, "boxCmp")["body"]) == _b("==", _n("b"), _n("b"))
    # `Boolean?` has no numeric width; the generic `==` is already null-safe value equality.
    assert _retOf(_func(funcs, "nulBoolEq")["body"]) == _b("==", _n("a"), _n("b"))


def test_kotlin_referential_equality_keeps_its_preexisting_lowering(exported):
    """kotlin2cpg compiles `===` to the same call name as `==` but with type ANY; it must
    not take the null-safe path. What it keeps is a known defect this change does not
    touch: `===` on `Int?` is reference identity, the typed `==` models value equality."""
    assert _retOf(_func(exported["kotlin"], "refEqInt")["body"]) == \
        _b("num:java:i32:==", _n("a"), _n("b"))
