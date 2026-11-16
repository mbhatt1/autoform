"""Kotlin `when`, `?:` and `if`/jump expressions against the JVM.

kotlin2cpg gives a subject `when` in expression position as `<operator>.when` (a BLOCK
with the subject, then one BLOCK per entry: conditions, body last) and drops the kind of
each condition -- `is T` leaves no node, `in e` an UNKNOWN `in` marker, `else` nothing.
In statement position it is a SWITCH with one JUMP_TARGET per entry and no condition
nodes at all, which the C/Java switch lowering read as "no entry ever matches" and so
skipped silently. `a ?: b` is `<operator>.elvis(a, b)`, and `?.` is spelled like `.`.
These were holes (`op:when`, `op:elvis`) or, for the statement form, a wrong program.

The exporter now lowers them to Core's `ifte`/`cond` (cartographer/compiler/
SourceCompiler.scala, `ktWhenV`, `ktWhenStmt`, `ktElvisV`), and `is T` type tests where
Core can decide them (`ktTypeTest`: a subject whose static type already is `T`, `Any`,
an analysed enum; Is.kt exercises them). This exports the fixtures, checks that every
lowered function is hole-free and that the shapes Core cannot decide stay NAMED holes
(`is` type tests of other types, enum entries, `catch`), then compiles the same files
with kotlinc and compares the Lean model with the JVM on every case: first match wins,
conditions after the match are not evaluated, `?:` evaluates its right side only on
null, `return`/`throw` on the right of `?:` leave the function. Needs Joern
(`AUTOFORM_TEST_JOERN=1`); the differential also needs a Kotlin compiler and `lake`.
Each missing piece is a named SKIP.
"""
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

SOURCE = (Path(__file__).resolve().parent / "fixtures" / "kotlin_control" / "W.kt").read_text()
IS_SOURCE = (Path(__file__).resolve().parent / "fixtures" / "kotlin_control" / "Is.kt").read_text()
IS_ALIAS_SOURCE = (Path(__file__).resolve().parent / "fixtures" / "kotlin_control" / "IsAlias.kt").read_text()

# (function, [(kind, value), ...]); kinds: int, long, char, bool, str, null.
CASES = (
    [("subj", [("int", v)]) for v in (1, 2, 3, 4, 5, 9, 10, 19, 20, 101, -1, 0)] +
    [("strWhen", [a]) for a in (("null", None), ("str", "a"), ("str", "b"), ("str", "c:d"),
                                ("str", "c"), ("str", ""))] +
    [("longWhen", [("long", v)]) for v in (1, -2, 0, 4294967297)] +
    [("charWhen", [("char", c)]) for c in "abyz@"] +
    [("boolWhen", [("bool", b)]) for b in (True, False)] +
    [("blockWhen", [("int", v)]) for v in (1, 2, 3, -5)] +
    [("firstMatch", [("int", v)]) for v in (5, 0, 11, -1)] +
    [("lazyWhen", [("int", x), ("int", d)]) for x, d in ((1, 0), (2, 0), (2, 5), (3, 5), (7, 1))] +
    [("stmtWhen", [("int", v)]) for v in (1, 2, 3, 4, 10, 20, 21, 0)] +
    [("stmtWhenNoElse", [("str", s)]) for s in ("x", "y", "z")] +
    [("stmtNullable", [a]) for a in (("int", 1), ("null", None), ("int", 5), ("int", 7))] +
    [("noSubj", [("int", v)]) for v in (-3, 0, 11)] +
    [("elvis", [a]) for a in (("null", None), ("str", "v"))] +
    [("elvisChain", [a, b]) for a in (("null", None), ("str", "a"))
                            for b in (("null", None), ("str", "b"))] +
    [("elvisReturn", [a]) for a in (("null", None), ("int", 5))] +
    [("nullableLong", [a]) for a in (("long", 1), ("long", -2), ("long", 15), ("null", None),
                                     ("long", 4294967297))] +
    [("elvisThrow", [a]) for a in (("null", None), ("str", "ok"))] +
    [("ifThrow", [("int", v)]) for v in (3, 0, -2)] +
    [("enumWhen", [("enum", e)]) for e in ("Color.RED", "Color.GREEN")] +
    [("enumOf", [("int", v)]) for v in (1, -1)] +
    [("enumIs", [a]) for a in (("enum", "Color.RED"), ("enum", "Color.GREEN"), ("null", None))] +
    [("enumStmt", [("enum", e)]) for e in ("Color.RED", "Color.GREEN")] +
    [("levelWhen", [a]) for a in (("enum", "Level.LOW"), ("enum", "Level.HIGH"), ("null", None))] +
    [("safeLen", [a]) for a in (("null", None), ("str", "abc"), ("str", ""))] +
    [("safeLenOr", [a]) for a in (("null", None), ("str", "abcd"))] +
    [("safeCallOnCall", [a]) for a in (("null", None), ("str", "ab"), ("str", "abcdef"))] +
    [("safeChain", [a]) for a in (("null", None), ("str", "xyz"), ("str", "toolong"))] +
    [("strProps", [("str", s)]) for s in ("", "a", "hello")] +
    [("isSelf", [a]) for a in (("null", None), ("str", "x"), ("str", ""))] +
    [("isSelfQ", [a]) for a in (("null", None), ("str", "x"))] +
    [("isSelfClass", [("null", None)])] +
    [("isAny", [a]) for a in (("null", None), ("str", "x"), ("int", 1), ("enum", "Mode.ON"))] +
    [("isAnyQ", [a]) for a in (("null", None), ("int", 1))] +
    [("isObject", [a]) for a in (("null", None), ("int", 1))] +
    [("isEnum", [a]) for a in (("enum", "Mode.ON"), ("enum", "Mode.OFF"), ("str", "x"),
                                ("int", 1), ("null", None))] +
    [("notEnum", [a]) for a in (("enum", "Mode.ON"), ("enum", "Mode.OFF"), ("str", "x"),
                                ("null", None))] +
    [("ifEnum", [a]) for a in (("enum", "Mode.ON"), ("null", None), ("str", "x"))] +
    [("whenEnum", [a]) for a in (("enum", "Mode.ON"), ("enum", "Mode.OFF"), ("null", None),
                                 ("str", "x"))] +
    [("whenSelf", [a]) for a in (("null", None), ("str", "x"))] +
    [("whenAny", [a]) for a in (("null", None), ("str", "x"), ("int", 1))] +
    [("whenNotEnum", [a]) for a in (("null", None), ("enum", "Mode.ON"), ("str", "x"))] +
    [("stmtWhenEnum", [a]) for a in (("enum", "Mode.ON"), ("enum", "Mode.OFF"), ("null", None),
                                     ("str", "x"))] +
    [("whenAlias", [a]) for a in (("enum", "Mode.ON"), ("null", None), ("str", "x"))] +
    [("isAlias", [a]) for a in (("enum", "Mode.OFF"), ("null", None), ("int", 1))]
)
LOWERED = sorted({f for f, _ in CASES})
# The `is T` tests Core cannot decide: a value type (`Int`/`Long` share `.int`, and no
# `.java`-dialect op reads a value tag), an analysed class (no class-hierarchy test), a
# platform or erased type (no type here to read); `whenString` and `stmtWhenIs` are the
# same classes of target in entry position, `stmtWhenIs` mixing in a lowered entry.
NAMED = {"isWhen": "op:when:is-type-test", "mixedWhen": "op:when:is-type-test",
         "tryWhen": "op:tryCatch", "isTest": "op:is-type-test",
         "plainIs": "op:is-type-test", "plainIsNot": "op:is-type-test",
         "isInt": "op:is-type-test", "isLong": "op:is-type-test",
         "isBool": "op:is-type-test", "isClass": "op:is-type-test",
         "ifString": "op:is-type-test", "whenString": "op:when:is-type-test",
         "isDate": "op:is:unknown-type", "genericIs": "op:is:unknown-type",
         "stmtWhenIs": "op:when:is-type-test", "bangIs": "op:notNullAssert"}


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
        pytest.skip("set AUTOFORM_TEST_JOERN=1 to export Kotlin through Joern")
    joern = _joern()
    if not (joern / "joern").is_file():
        pytest.skip("Joern not found (JOERN_HOME)")
    tmp = tmp_path_factory.mktemp("ktcontrol")
    src = tmp / "src"
    src.mkdir()
    (src / "W.kt").write_text(SOURCE)
    (src / "Is.kt").write_text(IS_SOURCE)
    (src / "IsAlias.kt").write_text(IS_ALIAS_SOURCE)
    _run([joern / "joern-parse", src, "--output", tmp / "cpg.bin"], tmp)
    _run([joern / "joern", "--script", ROOT / "cartographer/export_ast.sc",
          "--param", "cpgPath=%s" % (tmp / "cpg.bin"), "--param", "out=%s" % (tmp / "ast.json"),
          "--param", "dataModel=lp64"], tmp)
    return tmp, json.loads((tmp / "ast.json").read_text())


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


def test_lowered_functions_are_hole_free(exported):
    _, funcs = exported
    holed = {f: _holes(_func(funcs, f)["body"]) for f in LOWERED}
    assert {f: h for f, h in holed.items() if h} == {}


def test_undecidable_shapes_stay_named_holes(exported):
    _, funcs = exported
    for short, label in NAMED.items():
        assert label in _holes(_func(funcs, short)["body"]), short
    # The subject's equality with the `1` entry is still tried before the `is` hole.
    mixed = json.dumps(_func(funcs, "mixedWhen")["body"])
    assert '"op:when:is-type-test"' in mixed


def test_statement_when_is_not_silently_skipped(exported):
    """The statement form used to lower to a switch whose every guard was `false`."""
    _, funcs = exported
    for short in ("stmtWhen", "stmtWhenNoElse"):
        assert '"breakBlock"' not in json.dumps(_func(funcs, short)["body"]), short


def test_enum_entries_are_the_models_entry_values(exported):
    """`Color.RED` outside the enum and `LOW` inside it are one value, `fnref "k.Color$RED"`
    (the spelling the JVM oracle passes an entry in); no `when` on an analysed enum holes."""
    _, funcs = exported
    assert json.dumps(_func(funcs, "enumOf")["body"]).count('"k.Color$RED"') == 1
    nxt = json.dumps(_func(funcs, "next")["body"])
    assert '"k.Level$LOW"' in nxt and '"k.Level$HIGH"' in nxt
    for short in ("enumWhen", "enumStmt", "levelWhen", "next"):
        assert _holes(_func(funcs, short)["body"]) == [], short


def test_safe_call_receiver_is_evaluated_once(exported):
    """`pick(s)?.length`: the receiver call appears once, and the member reads its temporary."""
    _, funcs = exported
    body = json.dumps(_func(funcs, "safeCallOnCall")["body"])
    assert body.count('"k.pick:') == 1, body
    assert '"m": "length"' in body
    # The general position: `s?.length` is guarded, not a member of null.
    assert '"unit"' in json.dumps(_func(funcs, "safeLen")["body"])


def test_safe_calls_are_read_where_the_operator_belongs(exported):
    """A `?.` nested in a lambda argument is not the enclosing call's, and `v?.x` on a
    property of the implicit receiver is guarded; neither is an unread safe call."""
    _, funcs = exported
    assert _holes(_func(funcs, "nestedSafe")["body"]) == []
    body = _func(funcs, "len")["body"]
    assert _holes(body) == [] and '"unit"' in json.dumps(body)


def test_is_is_a_named_hole_not_identity(exported):
    """Kotlin `a is String` used to export as Python's identity `is` against the class value."""
    _, funcs = exported
    assert '"isOp"' not in json.dumps(_func(funcs, "isTest")["body"])


def test_is_type_tests_lower_where_core_can_decide(exported):
    """`x is T`: a subject whose static type already is `T` lowers to a null check
    (`isSelf`, `isSelfClass`), `Any`/`Object` to the same check (`isAny`, `isObject`),
    a `T?` target to `true` (`isSelfQ`, `isAnyQ`: null matches too), and an analysed
    enum to the disjunction of its entries (`isEnum`, `notEnum`, `ifEnum`, the `when`s)."""
    _, funcs = exported
    for short in ("isSelf", "isSelfQ", "isSelfClass", "isAny", "isAnyQ", "isObject",
                  "isEnum", "notEnum", "ifEnum", "whenEnum", "whenSelf", "whenAny",
                  "whenNotEnum", "stmtWhenEnum"):
        assert _holes(_func(funcs, short)["body"]) == [], short
    body = json.dumps(_func(funcs, "isEnum")["body"])
    assert '"k.Mode$ON"' in body and '"k.Mode$OFF"' in body
    # `isSelf` is `a != null`, not an identity `is` against the class value.
    assert '"isOp"' not in json.dumps(_func(funcs, "isSelf")["body"])
    assert '"unit"' in json.dumps(_func(funcs, "isSelf")["body"])
    assert '"v": true' in json.dumps(_func(funcs, "isSelfQ")["body"])
    # A statement `when` names per entry -- `!is Int` (a value type), `is java.util.Date`
    # (no type here) -- while its `is Mode` still lowers.
    mixed = _holes(_func(funcs, "stmtWhenIs")["body"])
    assert mixed.count("op:when:is-type-test") == 1
    assert mixed.count("op:when:is:unknown-type") == 1
    # A written name resolves through the file's imports (`Setting` is `k.Mode`).
    for short in ("whenAlias", "isAlias"):
        assert '"k.Mode$ON"' in json.dumps(_func(funcs, short)["body"]), short


def test_is_operator_read_between_subject_and_type(exported):
    """kotlin2cpg spells `!is` as `<operator>.is`; `a!! is Mode` is `is` (the `!!`
    belongs to the subject), so its test is one negation of the null check -- `!(s ==
    null)` -- not the two a search of the whole text for `!is` produced."""
    _, funcs = exported
    e = _func(funcs, "bangIs")["body"]["e"]
    assert e["k"] == "unop" and e["op"] == "!", e
    assert e["a"]["k"] == "binop" and e["a"]["op"] == "==", e
    assert e["a"]["b"] == {"k": "unit"}, e


def _lean_arg(kind, v):
    if kind == "enum":
        return '.fn "k.%s"' % v.replace(".", "$")
    if kind == "null":
        return ".unit"
    if kind == "str":
        return ".str %s" % json.dumps(v)
    if kind == "bool":
        return ".bool %s" % ("true" if v else "false")
    if kind == "char":
        return ".int %d" % ord(v)
    return ".int (%d)" % v


def _kt_arg(kind, v):
    if kind == "enum":
        return v
    if kind == "null":
        return "null"
    if kind == "str":
        return json.dumps(v)
    if kind == "bool":
        return "true" if v else "false"
    if kind == "char":
        return "'%s'" % v
    if kind == "long":
        return "%dL" % v
    return str(v)


def test_lowering_agrees_with_the_jvm(exported):
    tmp, funcs = exported
    import runtime_backends
    chain = runtime_backends.kotlin_toolchain()
    if chain is None or shutil.which("java") is None:
        pytest.skip("no Kotlin compiler (kotlinc, or Joern's embedded one) and java")
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    if not Path(lake).exists():
        pytest.skip("lake not found")
    compiler, extra, runtime = chain
    jdir = tmp / "jvm"
    jdir.mkdir(exist_ok=True)
    (jdir / "W.kt").write_text(SOURCE)
    (jdir / "Is.kt").write_text(IS_SOURCE)
    (jdir / "IsAlias.kt").write_text(IS_ALIAS_SOURCE)
    calls = "\n".join("    show { %s(%s) }" % (f, ", ".join(_kt_arg(k, v) for k, v in args))
                      for f, args in CASES)
    (jdir / "Main.kt").write_text(
        "package k\n\nfun show(f: () -> Any?) = try { val v = f()\n"
        "  println(if (v is Enum<*>) v.javaClass.name + \"$\" + v.name else v?.toString() ?: \"null\") }\n"
        "  catch (e: Throwable) { println(\"exn:\" + e.javaClass.simpleName) }\n\n"
        "fun main() {\n%s\n}\n" % calls)
    # `-include-runtime` puts the standard library in the jar itself: a packaged kotlinc
    # (Homebrew's keeps its jars under libexec/) can leave `runtime` empty.
    _run(compiler + extra + [jdir / "W.kt", jdir / "Is.kt", jdir / "IsAlias.kt", jdir / "Main.kt", "-include-runtime",
                             "-d", jdir / "main.jar"], jdir)
    jvm = _run(["java", "-cp", os.pathsep.join(p for p in (str(jdir / "main.jar"), runtime) if p),
                "k.MainKt"], jdir).splitlines()

    model = tmp / "KtControl.lean"
    _run([sys.executable, ROOT / "cartographer/render_lean.py", tmp / "ast.json", model,
          "KtControl"], ROOT)
    driver = model.read_text() + "\nopen Autoform.Core Autoform.Generated.KtControl\n"
    for f, args in CASES:
        driver += ('#eval IO.println (match runFunc program 4000 %s [%s] with '
                   '| .val (.int v) => toString v | .val (.str s) => s '
                   '| .val (.bool b) => toString b | .val .unit => "null" | .val (.fn n) => n '
                   '| .exn (.str n) => "exn:" ++ n | r => "unexpected " ++ reprStr r)\n'
                   % (json.dumps(_func(funcs, f)["name"]),
                      ", ".join(_lean_arg(k, v) for k, v in args)))
    (tmp / "Drive.lean").write_text(driver)
    lean = [l for l in _run([lake, "env", "lean", tmp / "Drive.lean"], ROOT,
                            timeout=1800).split("\n") if l.strip()]
    assert len(lean) == len(jvm) == len(CASES), (lean[-5:], jvm[-5:])
    bad = [(c, w, g) for c, w, g in zip(CASES, jvm, lean) if w != g]
    assert bad == [], bad
