"""Kotlin members in the JVM oracle: `object`s, companions, enum entries, no-arg classes.

`java_backend(kotlin=True)` used to refuse every Kotlin member ("needs a receiver"), so on
a real Kotlin service -- almost no top-level functions -- the oracle compared nothing.
The JVM driver now finds the receiver itself: an `object`'s INSTANCE, a companion object,
an enum's entries, or a fresh object from a non-private no-arg constructor. It reports
the receiver's state where Kotlin keeps it (instance fields; an `object`'s properties are
static fields of its class, a companion's are static fields of the class declaring it; an
enum entry's `name`/`ordinal` come from its accessors). Lean starts from exactly that
state and the state after the call is compared too.

An enum VALUE is the model's own spelling, `Val.fn "<enum>$<ENTRY>"` (Joern exports
`Mode.ON` inside the enum as `fnref "p.Mode$ON"`). A singleton whose body only uses `this`
as a value is passed in that spelling; one that needs both spellings has no faithful
starting state and is refused by name.

1. The driver alone (needs kotlinc and the JDK): receivers and states per kind, and every
   receiver or value that cannot be faithfully encoded is a NAMED refusal.
2. End to end (needs Joern, `AUTOFORM_TEST_JOERN=1`, kotlinc, the JDK and `lake`): the Joern
   export is rendered, every built case AGREES, and a deliberately wrong model of a
   companion's write DIVERGES. Each missing tool is a named SKIP.
3. A sibling member called through the implicit receiver, `one(by)`, used to be exported
   without its receiver argument, so the model's callee bound `this` to `by`, and the
   oracle refused every such member. It is now exported exactly as `this.one(by)` is
   (`fixtures/kotlin_receivers`, Joern-gated), and the oracle follows the callee's uses
   of the shared receiver instead of refusing.
"""
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
GENERATED = ROOT / "Autoform" / "Generated"
HAVE_KOTLIN = bool(shutil.which("kotlinc") and shutil.which("javac") and shutil.which("java"))

SOURCE = r"""package p

object Registry {
    var hits = 0
    val prefix = "r"
    fun bump(by: Int): Int { hits = hits + by; return hits }
    fun label(s: String): String = prefix + s
    fun me(): Boolean = this == Registry
}

class Box {
    var own = 1
    companion object {
        var made = 0
        fun twice(x: Int): Int = x * 2
        fun count(): Int { made = made + 1; return made }
    }
}

enum class Color(val code: String) {
    RED("r"), GREEN("g");
    fun tag(loud: Boolean): String = if (loud) code + "!" else code
    fun named(): String = name
    fun same(other: Color): Boolean = other == this
    companion object {
        fun first(): Color = RED
    }
}

enum class Mode { ON, OFF;
    fun isOn(): Boolean = this == ON
    fun flip(): Mode = if (this == ON) OFF else ON
    fun isOnArg(m: Mode): Boolean = m == ON
}

class Counter(var n: Int = 3) {
    var label: String = "c"
    fun inc(by: Int): Int { n = n + by; return n }
    fun reset(): Unit { n = 0; label = "r" }
}

fun String.shout(): String = this + "!"
"""

REFUSED_SOURCE = r"""package q

class Needs(val v: Int) { fun get(): Int = v }

object Calls {
    var n = 1
    fun one(by: Int): Int { n = n + by; return n }
    fun two(by: Int): Int = Calls.one(by) + 1
}

object Both {
    val k = 1
    fun f(): Boolean = this == Both && k == 1
}

class Host { companion object { fun me(): Boolean = this == Host.Companion } }

enum class Body { A { override fun v(): Int = 1 }; open fun v(): Int = 0; fun w(): Int = 2 }

class Plain { fun one(): Int = 1 }

object Takes { fun f(p: Plain): Int = 1 }

object Gives { fun f(): Plain = Plain() }

class Oops : Exception() { fun one(): Int = 1 }

object Holds { val xs = mutableListOf(1); fun one(): Int = 1 }
"""


def _this():
    return {"k": "name", "v": "this"}


def _field(f):
    return {"k": "field", "a": _this(), "f": f}


def _ret(e):
    return {"k": "ret", "e": e}


def _eq(a, b):
    return {"k": "binop", "op": "==", "a": a, "b": b}


def _fn(name, file, params, types, body):
    return {"name": name, "file": file, "params": params, "paramTypes": types, "body": body}


def _member(cls, sig, params, body, types=(), file="p/Fix.kt"):
    return _fn(cls + "." + sig, file, ["this"] + list(params), [cls] + list(types), body)


SKIP_BODY = {"k": "skip"}
MEMBERS = [
    _member("p.Registry", "bump:int(int)", ["by"], _ret(_field("hits")), ["int"]),
    _member("p.Registry", "label:java.lang.String(java.lang.String)", ["s"], _ret(_field("prefix")),
            ["java.lang.String"]),
    _member("p.Registry", "me:boolean()", [], _ret(_eq(_this(), {"k": "fnref", "v": "p.Registry"}))),
    _member("p.Box$Companion", "twice:int(int)", ["x"], _ret({"k": "name", "v": "x"}), ["int"]),
    _member("p.Box$Companion", "count:int()", [], _ret(_field("made"))),
    _member("p.Color", "tag:java.lang.String(boolean)", ["loud"], _ret(_field("code")), ["boolean"]),
    _member("p.Color", "named:java.lang.String()", [], _ret(_field("name"))),
    _member("p.Color", "same:boolean(p.Color)", ["other"], _ret(_eq({"k": "name", "v": "other"}, _this())),
            ["p.Color"]),
    _member("p.Color$Companion", "first:p.Color()", [], _ret({"k": "fnref", "v": "p.Color$RED"})),
    _member("p.Mode", "isOn:boolean()", [], _ret(_eq(_this(), {"k": "fnref", "v": "p.Mode$ON"}))),
    _member("p.Mode", "flip:p.Mode()", [], _ret(_eq(_this(), {"k": "fnref", "v": "p.Mode$ON"}))),
    _member("p.Mode", "isOnArg:boolean(p.Mode)", ["m"], _ret({"k": "name", "v": "m"}), ["p.Mode"]),
    _member("p.Counter", "inc:int(int)", ["by"], _ret(_field("n")), ["int"]),
    _member("p.Counter", "reset:void()", [], {"k": "setField", "r": _this(), "f": "n",
                                              "v": {"k": "int", "v": "0"}}),
    _fn("p.shout:java.lang.String(java.lang.String)", "p/Fix.kt", ["this"], ["java.lang.String"],
        _ret(_this())) | {"sourceName": "shout"},
]


def _refused(cls, sig, body=None, params=(), types=()):
    return _member("q." + cls, sig, params, body or _ret({"k": "int", "v": "1"}), types,
                   file="q/Refused.kt")


REFUSED = {
    _refused("Needs", "get:int()")["name"]: "receiver not built: no no-arg constructor",
    _refused("Calls", "two:int(int)")["name"]:
        "calls a member of its own class through a qualified name; the export drops that "
        "receiver argument",
    _refused("Both", "f:boolean()")["name"]:
        "object receiver is both a field holder and a value: the model spells it two ways "
        "and a case can start from only one",
    _refused("Host$Companion", "me:boolean()")["name"]:
        "companion receiver used as a value: the model has no name for it",
    _refused("Body", "w:int()")["name"]: "receiver not built: enum entry A has its own class body",
    _refused("Takes", "f:int(q.Plain)")["name"]:
        "argument not built: parameter type q.Plain is not an enum",
    _refused("Gives", "f:q.Plain()")["name"]: "returned a q.Plain: no faithful Core encoding",
    _refused("Oops", "one:int()")["name"]:
        "receiver extends java.lang.Exception: its private state is not readable",
    _refused("Holds", "one:int()")["name"]:
        "receiver field 'xs' holds a java.util.ArrayList: no faithful Core encoding",
}
REFUSED_FUNCS = [
    _refused("Needs", "get:int()"),
    # `Calls.one(by)`: the qualified call is exported with the real arguments only.
    _refused("Calls", "two:int(int)", _ret({"k": "call", "f": "q.Calls.one:int(int)",
                                            "args": [{"k": "name", "v": "by"}]}), ["by"], ["int"]),
    _refused("Both", "f:boolean()", _ret(_eq(_eq(_this(), {"k": "fnref", "v": "q.Both"}), _field("k")))),
    _refused("Host$Companion", "me:boolean()", _ret(_eq(_this(), {"k": "fnref", "v": "q.Host$Companion"}))),
    _refused("Body", "w:int()"),
    _refused("Takes", "f:int(q.Plain)", None, ["p"], ["q.Plain"]),
    _refused("Gives", "f:q.Plain()"),
    _refused("Oops", "one:int()"),
    _refused("Holds", "one:int()"),
]


def _tree(root):
    (root / "p").mkdir(parents=True)
    (root / "q").mkdir()
    (root / "p" / "Fix.kt").write_text(SOURCE)
    (root / "q" / "Refused.kt").write_text(REFUSED_SOURCE)


@pytest.mark.skipif(not HAVE_KOTLIN, reason="kotlinc or JDK unavailable")
def test_driver_finds_each_kotlin_receiver_and_names_every_refusal(tmp_path, differential,
                                                                    monkeypatch):
    monkeypatch.setattr(differential, "WORK", str(tmp_path / "work"))
    monkeypatch.delenv(differential.JAVA_CLASSPATH_ENV, raising=False)
    src = tmp_path / "src"
    _tree(src)
    ctor = _member("p.Box", "<init>:void()", [], SKIP_BODY)
    # The callee of `Calls.two` is in the export but not a candidate.
    callee = _refused("Calls", "one:int(int)", None, ["by"], ["int"])
    funcs = MEMBERS + REFUSED_FUNCS + [ctor]
    cases, info, skipped = differential.java_backend(str(src), funcs, 3, kotlin=True,
                                                     universe=funcs + [callee])
    assert skipped.pop(ctor["name"]).startswith("constructor:")
    assert skipped == REFUSED, skipped
    assert info["primitive_instance_candidates"] == len(MEMBERS) - 1 + len(REFUSED_FUNCS)
    assert info["primitive_static_candidates"] == 1  # the extension function
    by = {}
    for c in cases:
        by.setdefault(c["name"], []).append(c)
    assert set(by) == {f["name"] for f in MEMBERS}
    kinds = info["kotlin_receiver_cases"]
    assert kinds == {"class (heap)": 6, "companion (heap)": 9, "enum (heap)": 9,
                     "enum (value)": 9, "object (heap)": 6, "object (value)": 3}, kinds

    # An `object`: its properties are static fields of its class, read and written there.
    for c in by["p.Registry.bump:int(int)"]:
        pre, post = dict(c["heap"][0][1]), dict(c["post_heap"][0][1])
        assert c["heap"][0][0] == "Registry" and set(pre) == {"hits", "prefix"}
        assert post["hits"] == c["outcome"][1] and c["args"][0] == ("ref", 0)
    # The singleton used only as a value is the model's own name for it.
    assert all(c["args"] == [("fn", "p.Registry")] and c["outcome"] == ("val", ("bool", True))
               and c["heap"] == [] for c in by["p.Registry.me:boolean()"])
    # A companion: its property is a static field of the declaring class.
    counts = by["p.Box$Companion.count:int()"]
    assert [dict(c["post_heap"][0][1])["made"] for c in counts] == [c["outcome"][1] for c in counts]
    assert all(c["heap"][0][0] == "Box$Companion" for c in counts)
    # Enum entries: spread across cases, `name`/`ordinal` reported, values spelled `fn`.
    assert {dict(c["heap"][0][1])["name"] for c in by["p.Color.tag:java.lang.String(boolean)"]} \
        == {("str", "RED"), ("str", "GREEN")}
    for c in by["p.Color.named:java.lang.String()"]:
        cell = dict(c["heap"][0][1])
        assert c["outcome"] == ("val", cell["name"]) and cell["ordinal"][0] == "int"
    assert all(c["outcome"] == ("val", ("fn", "p.Color$RED")) for c in by["p.Color$Companion.first:p.Color()"])
    for c in by["p.Mode.flip:p.Mode()"]:
        flipped = {"p.Mode$ON": "p.Mode$OFF", "p.Mode$OFF": "p.Mode$ON"}[c["args"][0][1]]
        assert c["outcome"] == ("val", ("fn", flipped)) and c["self"] == c["args"][0]
    for c in by["p.Color.same:boolean(p.Color)"]:
        assert c["args"][0][0] == "fn" and c["args"][1][0] == "fn"
        assert c["outcome"] == ("val", ("bool", c["args"][0] == c["args"][1]))
    for c in by["p.Mode.isOnArg:boolean(p.Mode)"]:
        assert c["outcome"] == ("val", ("bool", c["args"][1] == ("fn", "p.Mode$ON")))
    # A class whose every constructor parameter has a default: the no-arg constructor.
    for c in by["p.Counter.inc:int(int)"]:
        assert c["heap"] == [["Counter", [("n", ("int", 3)), ("label", ("str", "c"))]]]
    for c in by["p.Counter.reset:void()"]:
        assert c["outcome"] == ("val", ("unit",))
        assert c["post_heap"] == [["Counter", [("n", ("int", 0)), ("label", ("str", "r"))]]]
    # A top-level extension function is called on its first argument.
    assert all(c["outcome"] == ("val", ("str", c["args"][0][1] + "!"))
               for c in by["p.shout:java.lang.String(java.lang.String)"])


def test_a_sibling_call_on_the_same_receiver_counts_the_callees_uses(differential):
    """`two` only calls `one(by)` (exported `call one [this, by]`), but `one` writes a
    property, so the singleton must start as a heap object, not as its `fnref` value."""
    owner = "q.Calls"
    one = _member(owner, "one:int(int)", ["by"], {"k": "setField", "r": _this(), "f": "n",
                                                  "v": {"k": "name", "v": "by"}}, ["int"])
    call_one = {"k": "call", "f": one["name"], "args": [_this(), {"k": "name", "v": "by"}]}
    two = _member(owner, "two:int(int)", ["by"], _ret(call_one), ["int"])
    by_name = {f["name"]: f for f in (one, two)}
    uses = differential.this_uses(two["body"], owner, by_name)
    assert uses == {"field"}
    assert differential.singleton_encoding("object", uses) == "heap"
    # A callee that compares `this` makes it a value use, as in the callee itself.
    me = _member(owner, "me:boolean()", [], _ret(_eq(_this(), {"k": "fnref", "v": owner})))
    via = _member(owner, "via:boolean()", [],
                  _ret({"k": "call", "f": me["name"], "args": [_this()]}))
    uses = differential.this_uses(via["body"], owner, {me["name"]: me})
    assert uses == {"value"} and differential.singleton_encoding("object", uses) == "value"
    # Recursion through the receiver terminates; another receiver is not this one.
    rec = _member(owner, "rec:int(q.Calls)", ["o"], _ret(
        {"k": "binop", "op": "+", "a": {"k": "call", "f": owner + ".rec:int(q.Calls)",
                                         "args": [_this(), {"k": "name", "v": "o"}]},
         "b": {"k": "call", "f": one["name"], "args": [{"k": "name", "v": "o"},
                                                        {"k": "int", "v": "1"}]}}), ["q.Calls"])
    assert differential.this_uses(rec["body"], owner, {rec["name"]: rec, **by_name}) == set()
    # A qualified `Calls.one(by)` is exported without the receiver: still refused by name.
    dropped = _ret({"k": "call", "f": one["name"], "args": [{"k": "name", "v": "by"}]})
    uses = differential.this_uses(dropped, owner, by_name)
    assert differential.singleton_encoding("class", uses) == (
        "calls a member of its own class through a qualified name; the export drops that "
        "receiver argument")
    assert differential.singleton_encoding("object", differential.this_uses(
        _ret(call_one), owner, {})) == "calls a member of its own class that the export does not include"


def _joern():
    home = Path(os.environ.get("JOERN_HOME", Path.home() / "joern"))
    return home / "joern-cli" if (home / "joern-cli").is_dir() else home


def _run(args, cwd, timeout=900, env=None):
    r = subprocess.run([str(a) for a in args], cwd=str(cwd), capture_output=True, text=True,
                       timeout=timeout, env=env)
    assert r.returncode == 0, (r.stdout + r.stderr)[-3000:]
    return r.stdout


@pytest.fixture
def exported(tmp_path):
    if os.environ.get("AUTOFORM_TEST_JOERN") != "1":
        pytest.skip("set AUTOFORM_TEST_JOERN=1 to export Kotlin through Joern")
    joern = _joern()
    if not (joern / "joern").is_file():
        pytest.skip("Joern not found (JOERN_HOME)")
    if not HAVE_KOTLIN:
        pytest.skip("kotlinc/javac/java not on PATH")
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    if not Path(lake).exists():
        pytest.skip("lake not found")
    src = tmp_path / "src"
    (src / "p").mkdir(parents=True)
    (src / "p" / "Fix.kt").write_text(SOURCE)
    _run([joern / "joern-parse", src, "--output", tmp_path / "cpg.bin"], tmp_path)
    _run([joern / "joern", "--script", ROOT / "cartographer/export_ast.sc",
          "--param", "cpgPath=%s" % (tmp_path / "cpg.bin"),
          "--param", "out=%s" % (tmp_path / "ast.json"), "--param", "dataModel=lp64"], tmp_path)
    return tmp_path


@pytest.fixture
def module():
    made = []
    yield made
    for target in made:
        target.unlink(missing_ok=True)
        for product in (ROOT / ".lake/build/lib/lean/Autoform/Generated").glob(target.stem + ".*"):
            product.unlink(missing_ok=True)


def _oracle(tmp, name, ast, src, module="DiffKotlinReceivers"):
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    env.pop("AUTOFORM_NO_REEXEC", None)
    env.pop("AUTOFORM_JAVA_CLASSPATH", None)
    work = tmp / ("run-" + name)
    work.mkdir()
    r = subprocess.run([sys.executable, str(ROOT / "scripts/differential.py"), str(ast), str(src),
                        module, "3", "--language", "kotlin", "--no-cache"],
                       capture_output=True, text=True, cwd=work, env=env, timeout=1800)
    report = json.loads((work / "conformance.json").read_text())
    return r, report


# Built by the driver AND compared by Lean. `Mode.flip`/`Mode.isOn` compare `this` with
# `fnref "p.Mode$ON"`; `Registry.me` with `fnref "p.Registry"`.
AGREE = {"p.Registry.bump:int(int)", "p.Registry.label:java.lang.String(java.lang.String)",
         "p.Registry.me:boolean()", "p.Box$Companion.twice:int(int)", "p.Box$Companion.count:int()",
         "p.Color.tag:java.lang.String(boolean)", "p.Color.named:java.lang.String()",
         "p.Color.same:boolean(p.Color)", "p.Color$Companion.first:p.Color()",
         "p.Mode.isOn:boolean()", "p.Mode.flip:p.Mode()", "p.Mode.isOnArg:boolean(p.Mode)",
         "p.Counter.inc:int(int)", "p.Counter.reset:void()"}


def test_kotlin_members_agree_and_a_wrong_companion_write_diverges(exported, module):
    tmp = exported
    target = GENERATED / "DiffKotlinReceivers.lean"
    module.append(target)
    _run([sys.executable, ROOT / "cartographer/render_lean.py", tmp / "ast.json", target,
          "DiffKotlinReceivers"], ROOT)
    r, report = _oracle(tmp, "honest", tmp / "ast.json", tmp / "src")
    assert r.returncode == 0, (r.stdout[-3000:], r.stderr[-2000:], report.get("status"))
    assert report["measurement_basis"] == "jvm-kotlin-receivers-v4"
    assert report["divergences"] == 0, report["divergence_detail"]
    agreed = {c["name"] for c in report["runtime_cases"] if c["comparison"] == "agree"}
    assert AGREE <= agreed, (AGREE - agreed, report["backend_skipped"], report["inconclusive_detail"])

    # A deliberately wrong model: the companion's `count` adds 2 where the source adds 1.
    # The written static (`made`) is compared as receiver state, and the result differs.
    text = target.read_text()
    count = text.index('name := "p.Box$Companion.count:int()"')
    lit = text.index('(.int 1)', count)
    target.write_text(text[:lit] + '(.int 2)' + text[lit + len('(.int 1)'):])
    r, report = _oracle(tmp, "wrong", tmp / "ast.json", tmp / "src")
    diverged = {d["function"] for d in report["divergence_detail"]}
    assert diverged == {"p.Box$Companion.count:int()"}, (diverged, r.stdout[-3000:])


SIBLINGS = ROOT / "tests" / "fixtures" / "kotlin_receivers"


def test_an_implicit_receiver_call_exports_as_the_explicit_this_call(exported, module):
    """`one(by)` and `this.one(by)` in an `object`, a class, a companion and an enum export
    the same body: the call passes the caller's `this` first, so the callee's `this` is
    the shared receiver, not `by`. The oracle then compares both members and agrees."""
    tmp = exported / "siblings"
    src = tmp / "src"
    shutil.copytree(SIBLINGS, src)
    joern = _joern()
    _run([joern / "joern-parse", src, "--output", tmp / "cpg.bin"], tmp)
    _run([joern / "joern", "--script", ROOT / "cartographer/export_ast.sc",
          "--param", "cpgPath=%s" % (tmp / "cpg.bin"),
          "--param", "out=%s" % (tmp / "ast.json"), "--param", "dataModel=lp64"], tmp)
    funcs = {f["name"]: f for f in json.loads((tmp / "ast.json").read_text())}
    pairs = [("s.Calls", "int(int)", "s.Calls.one:int(int)"),
             ("s.Counter", "int(int)", "s.Counter.inc:int(int)"),
             ("s.Counter$Companion", "int(int)", "s.Counter$Companion.twice:int(int)"),
             ("s.Mode", "boolean()", "s.Mode.isOn:boolean()")]
    for owner, sig, callee in pairs:
        implicit = funcs["%s.implicit:%s" % (owner, sig)]
        explicit = funcs["%s.explicit:%s" % (owner, sig)]
        assert implicit["body"] == explicit["body"], owner
        calls = []

        def walk(n):
            if isinstance(n, dict):
                if n.get("k") == "call" and n.get("f") == callee:
                    calls.append(n)
                for v in n.values():
                    walk(v)
            elif isinstance(n, list):
                for v in n:
                    walk(v)

        walk(implicit["body"])
        assert calls and all(c["args"][0] == _this() for c in calls), (owner, implicit["body"])
        assert all(len(c["args"]) == len(funcs[callee]["params"]) for c in calls)

    target = GENERATED / "DiffKotlinSiblings.lean"
    module.append(target)
    _run([sys.executable, ROOT / "cartographer/render_lean.py", tmp / "ast.json", target,
          "DiffKotlinSiblings"], ROOT)
    r, report = _oracle(tmp, "siblings", tmp / "ast.json", src, "DiffKotlinSiblings")
    assert r.returncode == 0, (r.stdout[-3000:], r.stderr[-2000:], report.get("status"))
    assert report["divergences"] == 0, report["divergence_detail"]
    agreed = {c["name"] for c in report["runtime_cases"] if c["comparison"] == "agree"}
    want = {"%s.%s:%s" % (o, k, sig) for o, sig, _ in pairs for k in ("implicit", "explicit")}
    assert want <= agreed, (want - agreed, report["backend_skipped"], report["inconclusive_detail"])
