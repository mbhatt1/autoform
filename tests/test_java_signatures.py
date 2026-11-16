"""The JVM oracle beyond primitive signatures: enums, boxes, null Strings, static state.

`java_backend` refused every method whose signature named a non-primitive type, and Core
could not read a Java static field at all (`<clinit>` is not exported, so `C.f` was the
hole `field:f:non-object`). A static `String` method that consults a `static final
Set.of(...)` -- the commonest shape of a lookup table -- was therefore never compared.

1. The driver alone (needs the JDK): an enum parameter is drawn from the enum's constants
   or null and becomes a reference to that constant's heap cell; an enum result is the
   cell of the constant returned; a boxed parameter is drawn inside the box cache; the
   static fields a call tree reads are reported just before the call and bound in the
   globals frame; every static Core cannot hold faithfully is left unbound and COUNTED
   with its reason.
2. End to end (needs Joern, `AUTOFORM_TEST_JOERN=1`, the JDK and `lake`): the Joern
   export of the fixture is rendered, every case compares and AGREES, and a deliberately
   wrong model of the null branch of a `Set.of` lookup DIVERGES.
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

CODES = r"""package p;

import java.util.*;

public final class Codes {
  public static final String FALLBACK = "F";
  private static final Set<String> MIRRORED = Set.of("A", "B");
  static final Map<String, String> ORG = Map.of("acct", "42");
  static final Set<String> VIEW = Collections.unmodifiableSet(new HashSet<>(List.of("x")));
  static final Set<String> FOLDED =
      Collections.unmodifiableSet(new TreeSet<>(String.CASE_INSENSITIVE_ORDER));
  static final List<String> SEQ = List.of("a", "b", "c");
  static final Integer BIG = 1000;
  static final Set<String> OPEN = new HashSet<>();

  private Codes() {}

  public static String from(String c) {
    if (c == null) return FALLBACK;
    if (MIRRORED.contains(c)) return c;
    return FALLBACK;
  }
  public static String org(String a) {
    String v = ORG.get(a);
    return v != null ? v : "none";
  }
  public static boolean viewed(String s) { return VIEW.contains(s); }
  public static boolean folded(String s) { return FOLDED.contains(s); }
  public static int seq(int i) { return SEQ.size() + i; }
  public static boolean big(int x) { return BIG == x; }
  public static boolean open(String s) { return OPEN.contains(s); }
  public static Level pick(Level l, Integer k) {
    if (l == null) return Level.LOW;
    // Not `k == 0`: the exporter has no numeric type for a box (`numeric:unknown-type`).
    return k == null ? l : Level.HIGH;
  }
  public static int weight(Level l) { return l == Level.HIGH ? 2 : 1; }
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


def _field(cls, f):
    return {"k": "field", "a": {"k": "fnref", "v": cls}, "f": f}


def _simple(cls, f):
    return {"k": "field", "a": {"k": "name", "v": cls}, "f": f}


def _fn(name, params, body, file="java/p/Codes.java"):
    return {"name": name, "file": file, "params": params, "body": body}


def _ret(e):
    return {"k": "ret", "e": e}


FUNCS = [
    _fn("p.Codes.from:java.lang.String(java.lang.String)", ["c"],
        {"k": "seq", "a": _ret(_field("p.Codes", "FALLBACK")),
         "b": _ret(_field("p.Codes", "MIRRORED"))}),
    _fn("p.Codes.org:java.lang.String(java.lang.String)", ["a"], _ret(_field("p.Codes", "ORG"))),
    _fn("p.Codes.viewed:boolean(java.lang.String)", ["s"], _ret(_field("p.Codes", "VIEW"))),
    _fn("p.Codes.folded:boolean(java.lang.String)", ["s"], _ret(_field("p.Codes", "FOLDED"))),
    _fn("p.Codes.seq:int(int)", ["i"], _ret(_field("p.Codes", "SEQ"))),
    _fn("p.Codes.big:boolean(int)", ["x"], _ret(_field("p.Codes", "BIG"))),
    _fn("p.Codes.open:boolean(java.lang.String)", ["s"], _ret(_field("p.Codes", "OPEN"))),
    _fn("p.Codes.pick:p.Level(p.Level,java.lang.Integer)", ["l", "k"],
        _ret(_simple("Level", "LOW"))),
    _fn("p.Codes.weight:int(p.Level)", ["l"], _ret(_simple("Level", "HIGH"))),
    _fn("p.Level.<init>:void(int)", ["this", "w"], {"k": "skip"}, "java/p/Level.java"),
    _fn("p.Level.doubled:int()", ["this"], {"k": "skip"}, "java/p/Level.java"),
]

NOT_BOUND = {
    "mutable java.util.TreeSet (only read-only static collections are bound) behind "
    "java.util.Collections$UnmodifiableSet": "FOLDED",
    "java.util.ImmutableCollections$ListN.get out of range throws "
    "java.lang.ArrayIndexOutOfBoundsException (Core: IndexOutOfBoundsException)": "SEQ",
    "boxed java.lang.Integer 1000 outside the JVM box cache (== on it is reference equality)": "BIG",
    "mutable java.util.HashSet (only read-only static collections are bound)": "OPEN",
}


def _write(root):
    pkg = root / "java" / "p"
    pkg.mkdir(parents=True)
    (pkg / "Codes.java").write_text(CODES)
    (pkg / "Level.java").write_text(LEVEL)


def _holder(case, field):
    for cell in case["heap"]:
        if cell[0] == "<module>static:p.Codes":
            return dict(cell[1]).get(field)
    return None


@pytest.mark.skipif(not HAVE_JDK, reason="JDK unavailable")
def test_driver_binds_static_state_enums_and_boxes(tmp_path, differential, monkeypatch):
    _write(tmp_path / "src")
    monkeypatch.setattr(differential, "WORK", str(tmp_path / "work"))
    cases, info, skipped = differential.java_backend(str(tmp_path / "src"), FUNCS, 12)
    by = {}
    for c in cases:
        by.setdefault(c["name"].split(":")[0].rsplit(".", 1)[-1], []).append(c)
    assert info["boxed_or_enum_signature_candidates"] == 2, info
    assert info["enum_receiver_candidates"] == 1, info
    assert set(by) == {"from", "org", "viewed", "folded", "seq", "big", "open", "pick",
                       "weight", "doubled"}, skipped
    # Every static the driver could not hold faithfully is counted with its reason.
    assert set(NOT_BOUND) <= set(info["static_fields_not_bound"]), info
    for c in by["from"]:
        # `Set.of` iterates in a per-JVM order; the cell keeps the order this JVM used.
        kind, items = _holder(c, "MIRRORED")
        assert kind == "list" and sorted(items) == [("str", "A"), ("str", "B")]
        assert _holder(c, "FALLBACK") == ("str", "F")
        assert ("<static>p.Codes", ("ref", 0)) in c["globals"]
        arg = c["args"][0]
        expected = "F" if arg == ("unit",) or arg[1] not in ("A", "B") else arg[1]
        assert c["outcome"] == ("val", ("str", expected))
    assert any(c["args"] == [("unit",)] for c in by["from"]), "null is an input"
    assert all(_holder(c, "ORG") == ("dict", [(("str", "acct"), ("str", "42"))]) for c in by["org"])
    assert all(_holder(c, "VIEW") == ("list", [("str", "x")]) for c in by["viewed"])
    for name in ("folded", "seq", "big", "open"):
        assert all(_holder(c, NOT_BOUND_FIELD) is None
                   for NOT_BOUND_FIELD in NOT_BOUND.values() for c in by[name])
    # Enums: each constant is a heap cell with its instance fields; `Level` (a simple
    # name) is bound to the same holder that names the constants.
    for c in by["pick"] + by["weight"]:
        cells = {cell[0]: cell for cell in c["heap"]}
        low = c["heap"].index(["Level", [("w", ("int", 1))]])
        high = c["heap"].index(["Level", [("w", ("int", 2))]])
        assert [cell[0] for cell in c["heap"]].count("Level") == 2, cells
        holder = dict(c["globals"])["Level"]
        assert c["heap"][holder[1]][0] == "<module>static:p.Level"
        assert dict(c["heap"][holder[1]][1])["LOW" if c in by["pick"] else "HIGH"] == \
            ("ref", low if c in by["pick"] else high)
    for c in by["pick"]:
        level, k = c["args"]
        assert k[0] == "int" and -128 <= k[1] <= 127
        low = c["heap"].index(["Level", [("w", ("int", 1))]])
        high = c["heap"].index(["Level", [("w", ("int", 2))]])
        want = low if level == ("unit",) else high
        assert c["outcome"] == ("val", ("ref", want)), c
    assert {c["args"][0][0] for c in by["pick"]} == {"ref", "unit"}
    # An instance method of an enum runs on one of its constants: `self` is that cell.
    for c in by["doubled"]:
        me = c["self"]
        assert me[0] == "ref" and c["args"] == [me] and c["origin"] == "constructed"
        w = dict(c["heap"][me[1]][1])["w"][1]
        assert c["outcome"] == ("val", ("int", 2 * w)) and c["post_heap"] == c["heap"]
    assert {dict(c["heap"][c["self"][1]][1])["w"] for c in by["doubled"]} == {("int", 1), ("int", 2)}


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
                        "DiffJavaSignatures", "12", "--language", "java", "--no-cache"],
                       capture_output=True, text=True, cwd=work, env=env, timeout=1800)
    report = json.loads((work / "conformance.json").read_text())
    return r, report


def test_static_lookups_and_enums_agree_and_a_wrong_null_branch_diverges(exported, module):
    tmp = exported
    target = GENERATED / "DiffJavaSignatures.lean"
    module.append(target)
    _run([sys.executable, ROOT / "cartographer/render_lean.py", tmp / "ast.json", target,
          "DiffJavaSignatures"], ROOT)
    r, report = _oracle(tmp, "honest", tmp / "ast.json", tmp / "src")
    assert r.returncode == 0, (r.stdout[-3000:], r.stderr[-2000:], report.get("status"))
    assert report["measurement_basis"] == "jvm-signatures-statics-v5"
    assert report["divergences"] == 0, report["divergence_detail"]
    agreed = {c["name"].split(":")[0].rsplit(".", 1)[-1]
              for c in report["runtime_cases"] if c["comparison"] == "agree"}
    # `folded`/`seq`/`big`/`open` read a static Core is not given: inconclusive, not agree.
    assert {"from", "org", "viewed", "pick", "weight"} <= agreed, (
        agreed, report["backend_skipped"], report["inconclusive_detail"])
    assert not {"folded", "seq", "big", "open"} & agreed
    # The agreeing observation must be replayable from its recorded fields alone:
    # every statics holder in its heap is named by a `javaStaticKey` frame binding,
    # and every binding's ref points at a holder cell in the recorded heap.
    # synth_specs.py folds exactly these bindings back into the globals frame.
    for c in report["runtime_cases"]:
        if c["comparison"] != "agree":
            continue
        holders = {cell[0][len("<module>static:"):] for cell in c["heap"]
                   if cell[0].startswith("<module>static:")}
        bindings = dict(c.get("globals") or [])
        assert all("<static>" + cls in bindings for cls in holders), c
        for key, ref in (c.get("globals") or []):
            assert ref[0] == "ref" and 0 <= ref[1] < len(c["heap"]), c
            assert c["heap"][ref[1]][0].startswith("<module>static:"), c
            if key.startswith("<static>"):
                assert c["heap"][ref[1]][0] == "<module>static:" + key[len("<static>"):], c

    # A deliberately wrong model: the null branch of `from` returns "A" where the source
    # returns FALLBACK. Only a null input reaches it.
    ast = json.loads((tmp / "ast.json").read_text())
    funcs = ast.get("functions", ast) if isinstance(ast, dict) else ast
    entry = next(f for f in funcs if f["name"].startswith("p.Codes.from:"))
    first = entry["body"]["a"] if entry["body"].get("k") == "seq" else entry["body"]
    assert first["k"] == "ifte" and first["t"]["k"] == "ret", first
    first["t"]["e"] = {"k": "str", "v": "A"}
    (tmp / "wrong.json").write_text(json.dumps(ast))
    _run([sys.executable, ROOT / "cartographer/render_lean.py", tmp / "wrong.json", target,
          "DiffJavaSignatures"], ROOT)
    r, report = _oracle(tmp, "wrong", tmp / "wrong.json", tmp / "src")
    diverged = {d["function"].split(":")[0].rsplit(".", 1)[-1] for d in report["divergence_detail"]}
    assert diverged == {"from"}, (diverged, r.stdout[-3000:])
