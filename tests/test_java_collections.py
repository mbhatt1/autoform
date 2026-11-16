"""The JVM oracle's seeded collection parameters: List/Set/Collection/Map, and varargs.

`java_backend` refused any function whose signature named a collection interface
("non-primitive signature") -- on a real service the commonest refusal after compile
failures -- and `String...` varargs with the same generic reason. The model could
already hold a read-only static collection (`Set.of`, `Map.of`): an unboxed `.list`/
`.dict`, whose mutating methods are holes (`mcall:*:unboxed-container`).

1. The driver alone (needs the JDK): a List/Set/Collection/Map parameter is seeded
   with 0/1/2 immutable elements and encoded exactly as a read-only static collection
   is. The draw is a function of the iteration and position, and the order is fixed
   -- a two-element set or map is an unmodifiable LinkedHashSet/LinkedHashMap, since
   `Set.of`/`Map.of` iterate in an order salted per JVM start -- so two runs (base
   and head) build identical inputs. The empty list is `Collections.emptyList()`:
   `List.of()` is a ListN whose out-of-range `get` throws
   `ArrayIndexOutOfBoundsException`, where Core raises IndexOutOfBoundsException. An
   input the model cannot hold refuses the case with its reason: a raw parameter
   (the element type is erased, JLS 4.6), a box element in a call tree that queries a
   collection by equality (`contains`) and a boxed map key -- Core's int encoding
   conflates the box kinds `equals` separates. Mutating a seeded argument throws on
   the JVM, as on an immutable static. A `String...` varargs is still refused, now by
   name: `.length` is the `op:sizeOf:array-length` hole and an out-of-range index
   raises IndexError in Core.
2. End to end (needs Joern, `AUTOFORM_TEST_JOERN=1`, the JDK and `lake`): the Joern
   export of the fixture is rendered, every seeded case compares and AGREES, a
   mutation of a seeded argument is a hole on the model side (never a comparison),
   and a deliberately wrong model of the `contains` branch of a seeded Set DIVERGES.
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
HAVE_JDK = bool(shutil.which("javac") and shutil.which("java"))

COLL = r"""package p;

import java.util.*;

public final class Coll {
  public static String join(List<String> l) { return l.isEmpty() ? "-" : l.get(l.size() - 1); }
  public static String pick(Set<String> s) { return s.contains("A") ? "A" : "-"; }
  public static String seen(Collection<String> c) {
    return c.isEmpty() ? "-" : (c.size() == 1 ? "one" : "many");
  }
  public static String env(Map<String, String> m) {
    String v = m.get("B");
    return v != null ? v : (m.isEmpty() ? "-" : "one");
  }
  public static String tags(List<Level> l) {
    return l.isEmpty() ? "-" : (l.get(l.size() - 1) == Level.LOW ? "low" : "high");
  }
  public static int width(List<Integer> b) { return b.size() == 2 ? 2 : b.size(); }
  public static int hits(List<Integer> b) { return b.contains(2) ? 1 : 0; }
  public static String cat(String... parts) { return parts.length == 0 ? "" : parts[0]; }
  public static String raw(List raw) { return raw.isEmpty() ? "-" : "x"; }
  public static int keys(Map<Integer, String> m) { return m.size(); }
  public static int grow(List<String> l) {
    l.add("C");
    return l.size();
  }
}
"""
LEVEL = r"""package p;

public enum Level {
  LOW(1), HIGH(2);
  private final int w;
  Level(int w) { this.w = w; }
  public int weight() { return w; }
  public int doubled() { return w * 2; }
}
"""


def _fn(name, params, body, file="java/p/Coll.java"):
    return {"name": name, "file": file, "params": params, "body": body}


def _ret(e):
    return {"k": "ret", "e": e}


def _cond(c, t, e):
    return {"k": "cond", "c": c, "t": t, "e": e}


def _mcall(recv, m, *args):
    return {"k": "mcall", "recv": {"k": "name", "v": recv}, "m": m, "args": list(args)}


def _str(v):
    return {"k": "str", "v": v}


def _int(v):
    return {"k": "int", "v": v}


# Only `pick` and `hits` need a body (a `contains` call, so the driver marks the call
# tree as querying a collection by equality); the model is not run here, so the rest
# is a `skip`, and the bodies' other effects (static reads) stay out of the way.
FUNCS = [
    _fn("p.Coll.join:java.lang.String(java.util.List)", ["l"], {"k": "skip"}),
    _fn("p.Coll.pick:java.lang.String(java.util.Set)", ["s"],
        _ret(_cond(_mcall("s", "contains", _str("A")), _str("A"), _str("-")))),
    _fn("p.Coll.seen:java.lang.String(java.util.Collection)", ["c"], {"k": "skip"}),
    _fn("p.Coll.env:java.lang.String(java.util.Map)", ["m"], {"k": "skip"}),
    _fn("p.Coll.tags:java.lang.String(java.util.List)", ["l"], {"k": "skip"}),
    _fn("p.Coll.width:int(java.util.List)", ["b"], {"k": "skip"}),
    _fn("p.Coll.hits:int(java.util.List)", ["b"],
        _ret(_cond(_mcall("b", "contains", _int("2")), _int("1"), _int("0")))),
    _fn("p.Coll.cat:java.lang.String(java.lang.String[])", ["parts"], {"k": "skip"}),
    _fn("p.Coll.raw:java.lang.String(java.util.List)", ["raw"], {"k": "skip"}),
    _fn("p.Coll.keys:int(java.util.Map)", ["m"], {"k": "skip"}),
    _fn("p.Coll.grow:int(java.util.List)", ["l"], {"k": "skip"}),
]

# Every refusal names what it refused.
BOX_EQ = ("argument not built: boxed java.lang.Integer elements: the call tree queries "
          "a collection by equality, and Core's int encoding conflates the box kinds "
          "that `equals` separates")
RAW_ERASED = ("argument not built: raw java.util.List: the element type is erased "
              "(JLS 4.6), so no element can be seeded")
BOX_KEY = ("argument not built: boxed java.lang.Integer map keys: a lookup compares keys "
           "by `equals`, and Core's int encoding conflates the box kinds that `equals` "
           "separates")


def _write(root):
    pkg = root / "java" / "p"
    pkg.mkdir(parents=True)
    (pkg / "Coll.java").write_text(COLL)
    (pkg / "Level.java").write_text(LEVEL)


@pytest.mark.skipif(not HAVE_JDK, reason="JDK unavailable")
def test_driver_seeds_collection_parameters(tmp_path, differential, monkeypatch):
    _write(tmp_path / "src")
    monkeypatch.setattr(differential, "WORK", str(tmp_path / "work"))
    cases, info, skipped = differential.java_backend(str(tmp_path / "src"), FUNCS, 12)
    by = {}
    for c in cases:
        by.setdefault(c["name"].split(":")[0].rsplit(".", 1)[-1], []).append(c)
    # `cat` is refused at the filter (an array signature) before the count, so 10 of 11.
    assert info["collection_signature_candidates"] == 10, info
    assert set(by) == {"join", "pick", "seen", "env", "tags", "width", "grow"}, skipped
    # The draw is (iteration + position) % 3: sizes 1, 2, 0, 1, ... over the twelve
    # iterations, and every size binds, the empty list included.
    for name in ("join", "pick", "seen", "env", "tags", "width", "grow"):
        assert sorted(len(c["args"][0][1]) for c in by[name]) == [0] * 4 + [1] * 4 + [2] * 4, name
    # A seeded collection is encoded exactly as a read-only static is: an unboxed
    # `.list`/`.dict`, so mutating it is the hole `mcall:*:unboxed-container`.
    for c in by["join"]:
        kind, items = c["args"][0]
        assert kind == "list" and items in ([], [("str", "A")], [("str", "A"), ("str", "B")])
        assert c["outcome"] == ("val", ("str", items[-1][1] if items else "-"))
    for c in by["pick"]:
        # A fixed iteration order (not `Set.of`'s per-JVM salt).
        kind, items = c["args"][0]
        assert kind == "list" and items in ([], [("str", "A")], [("str", "A"), ("str", "B")])
        assert c["outcome"] == ("val", ("str", "A" if items else "-"))
    for c in by["seen"]:
        n = len(c["args"][0][1])
        assert c["outcome"] == ("val", ("str", "-" if n == 0 else "one" if n == 1 else "many"))
    for c in by["env"]:
        kind, pairs = c["args"][0]
        assert kind == "dict" and pairs in (
            [], [(("str", "A"), ("str", "A"))],
            [(("str", "A"), ("str", "A")), (("str", "B"), ("str", "B"))])
        expect = "-" if not pairs else "one" if len(pairs) == 1 else "B"
        assert c["outcome"] == ("val", ("str", expect))
    for c in by["tags"]:
        # An enum element is a reference to the constant's laid-out cell, so `==` is
        # cell identity -- on the seeded element as on `Level.LOW`.
        kind, items = c["args"][0]
        assert kind == "list" and [r[0] for r in items] == ["ref"] * len(items)
        ws = [dict(c["heap"][r[1]][1])["w"] for r in items]
        assert ws == [("int", 1), ("int", 2)][:len(items)]
        assert all(c["heap"][r[1]][0] == "Level" for r in items)
        expect = "-" if not items else "low" if len(items) == 1 else "high"
        assert c["outcome"] == ("val", ("str", expect))
    for c in by["width"]:
        # A cached box element: encoded as the int value (`hits`, the same element
        # kind under an equality query, refuses below).
        kind, items = c["args"][0]
        assert kind == "list" and items in ([], [("int", 1)], [("int", 1), ("int", 2)])
        assert c["outcome"] == ("val", ("int", len(items)))
    for c in by["grow"]:
        # The JVM throws on a write to the seeded argument, as on an immutable static.
        assert c["outcome"] == ("exn", "UnsupportedOperationException"), c["outcome"]
    # Every refusal names what it refused.
    assert skipped["p.Coll.cat:java.lang.String(java.lang.String[])"] == (
        "array signature: java.lang.String[] -- the model has no faithful Java array "
        "(`.length` is the `op:sizeOf:array-length` hole; an out-of-range index raises "
        "IndexError in Core, ArrayIndexOutOfBoundsException on the JVM)")
    assert skipped["p.Coll.hits:int(java.util.List)"] == BOX_EQ
    assert skipped["p.Coll.raw:java.lang.String(java.util.List)"] == RAW_ERASED
    assert skipped["p.Coll.keys:int(java.util.Map)"] == BOX_KEY
    assert not any(k.split(":")[0].rsplit(".", 1)[-1] in by for k in skipped), skipped

    # Base and head run in two JVMs: the seeded inputs must not depend on which one.
    again, _, _ = differential.java_backend(str(tmp_path / "src"), FUNCS, 12)
    assert [(c["name"], c["args"]) for c in again] == [(c["name"], c["args"]) for c in cases]


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
        pytest.skip("set AUTOFORM_TEST_JOERN=1 to export Java through Joern")
    joern = _joern()
    if not (joern / "joern").is_file():
        pytest.skip("Joern not found (JOERN_HOME)")
    if not HAVE_JDK:
        pytest.skip("javac/java not on PATH")
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    if not Path(lake).exists():
        pytest.skip("lake not found")
    _write(tmp_path / "src")
    _run([joern / "joern-parse", tmp_path / "src", "--output", tmp_path / "cpg.bin"], tmp_path)
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


def _oracle(tmp, name, ast, src):
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    env.pop("AUTOFORM_NO_REEXEC", None)
    work = tmp / ("run-" + name)
    work.mkdir()
    r = subprocess.run([sys.executable, str(ROOT / "scripts/differential.py"), str(ast), str(src),
                        "DiffJavaCollections", "12", "--language", "java", "--no-cache"],
                       capture_output=True, text=True, cwd=work, env=env, timeout=1800)
    report = json.loads((work / "conformance.json").read_text())
    return r, report


def test_seeded_collections_agree_and_a_wrong_contains_branch_diverges(exported, module):
    tmp = exported
    target = GENERATED / "DiffJavaCollections.lean"
    module.append(target)
    _run([sys.executable, ROOT / "cartographer/render_lean.py", tmp / "ast.json", target,
          "DiffJavaCollections"], ROOT)
    r, report = _oracle(tmp, "honest", tmp / "ast.json", tmp / "src")
    assert r.returncode == 0, (r.stdout[-3000:], r.stderr[-2000:], report.get("status"))
    assert report["measurement_basis"] == "jvm-signatures-statics-v5"
    assert report["divergences"] == 0, report["divergence_detail"]
    agreed = {c["name"].split(":")[0].rsplit(".", 1)[-1]
              for c in report["runtime_cases"] if c["comparison"] == "agree"}
    assert {"join", "pick", "seen", "env", "tags", "width"} <= agreed, (
        agreed, report["backend_skipped"], report["inconclusive_detail"])
    # The refusals stay refusals end to end: an array signature, a raw element type,
    # a box element under an equality query and a boxed map key never become
    # comparisons; nor does a write to a seeded argument -- a hole in the model
    # (`mcall:add:unboxed-container`), whatever the JVM threw.
    assert not {"cat", "raw", "hits", "keys", "grow"} & agreed
    grow = [k for k in report["inconclusive_detail"] if k.startswith("p.Coll.grow:")]
    assert grow and all(k.endswith(": mcall:add:unboxed-container") for k in grow), (
        report["inconclusive_detail"])

    # A deliberately wrong model: `pick` answers "Z" where the source answers "A" --
    # every seeded size that holds "A" diverges, the empty draw still agrees.
    ast = json.loads((tmp / "ast.json").read_text())
    funcs = ast.get("functions", ast) if isinstance(ast, dict) else ast
    entry = next(f for f in funcs if f["name"].startswith("p.Coll.pick:"))
    ternary = entry["body"]["e"]
    assert ternary["k"] == "cond" and ternary["t"]["k"] == "str", ternary
    ternary["t"]["v"] = "Z"
    (tmp / "wrong.json").write_text(json.dumps(ast))
    _run([sys.executable, ROOT / "cartographer/render_lean.py", tmp / "wrong.json", target,
          "DiffJavaCollections"], ROOT)
    r, report = _oracle(tmp, "wrong", tmp / "wrong.json", tmp / "src")
    diverged = {d["function"].split(":")[0].rsplit(".", 1)[-1] for d in report["divergence_detail"]}
    assert diverged == {"pick"}, (diverged, r.stdout[-3000:])
