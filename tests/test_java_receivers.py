"""Java instance methods in the JVM oracle, on a receiver the JVM builds.

`java_backend` used to refuse every instance method ("needs a receiver"). It now calls a
Java instance method whose signature is primitive-or-String (or `void`) on a fresh object
built by the class's own non-private no-arg constructor. The driver reports that object's
instance fields before and after the call; the case starts Lean from exactly the reported
object and compares the fields after the call as well as the result. Rebuilding the
receiver by running the translated `<init>` in Lean would NOT be the same object: Core
leaves an unassigned field unset (it reads as `unit`) where the JVM gives it its JLS
§4.12.5 default, so `hits` below would differ before the method ran.

1. The driver alone (needs the JDK): receiver state is reported with JVM defaults, writes
   show up in the post-state, and every receiver that cannot be faithfully encoded or
   built is a NAMED refusal.
2. End to end (needs Joern, `AUTOFORM_TEST_JOERN=1`, the JDK and `lake`): the Joern export
   of the fixture is rendered, every instance method is COMPARED and AGREES, and a
   deliberately wrong model of a `void` method's write DIVERGES on the heap observation
   alone. Each missing tool is a named SKIP.
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

SOURCE = r"""
public class Counter {
  private int count;
  private int hits;
  private String label;
  private long total = 7L;
  private String none;
  public Counter() { this.count = 3; label = "c"; }
  public int get() { return count; }
  public int hitsPlus(int k) { return hits + k; }
  public int bump(int by) { count = count + by; total += by; return count; }
  public long sum(int k) { total = total * k; return total; }
  public String name(String suffix) { return label + suffix; }
  public boolean isBig(int t) { return this.count > t; }
  public void reset(int v) { count = v; label = "r"; }
  public boolean noneIsNull() { return none == null; }
}
"""
INSTANCE = ["Counter.get:int()", "Counter.hitsPlus:int(int)", "Counter.bump:int(int)",
            "Counter.sum:long(int)", "Counter.name:java.lang.String(java.lang.String)",
            "Counter.isBig:boolean(int)", "Counter.reset:void(int)",
            "Counter.noneIsNull:boolean()"]

REFUSED = {
    "Holder.java": ("class Holder { private java.util.List<String> xs = new java.util.ArrayList<>();"
                    " int one() { return 1; } }", "Holder.one:int()",
                    "receiver field 'xs' holds a java.util.ArrayList: no faithful Core encoding"),
    "NeedsArg.java": ("class NeedsArg { int v; NeedsArg(int v) { this.v = v; } int get() { return v; } }",
                      "NeedsArg.get:int()", "receiver not built: no no-arg constructor"),
    "Hidden.java": ("class Hidden { private Hidden() {} int one() { return 1; } }",
                    "Hidden.one:int()", "receiver not built: no-arg constructor is private"),
    "Shape.java": ("abstract class Shape { int one() { return 1; } }",
                   "Shape.one:int()", "receiver not built: abstract class"),
    "Boom.java": ("class Boom { Boom() { throw new IllegalStateException(); } int one() { return 1; } }",
                  "Boom.one:int()", "receiver not built: constructor threw IllegalStateException"),
    "Child.java": ("class Base { int x = 1; } class Child extends Base { int x = 2; int one() { return x; } }",
                   "Child.one:int()", "receiver field 'x' is declared twice in the class hierarchy"),
}


def _fn(name, file, params):
    return {"name": name, "file": file, "params": params, "body": {"k": "skip"}}


@pytest.mark.skipif(not HAVE_JDK, reason="JDK unavailable")
def test_driver_reports_the_receiver_it_built_and_names_every_refusal(tmp_path, differential):
    (tmp_path / "Counter.java").write_text(SOURCE)
    funcs = [_fn("Counter.<init>:void()", "Counter.java", ["this"])]
    for name in INSTANCE:
        nargs = 0 if name.endswith("()") else 1
        funcs.append(_fn(name, "Counter.java", ["this"] + ["a"][:nargs]))
    for file, (text, name, _) in REFUSED.items():
        (tmp_path / file).write_text(text + "\n")
        funcs.append(_fn(name, file, ["this"]))
    cases, info, skipped = differential.java_backend(str(tmp_path), funcs, 3)
    assert info["primitive_instance_candidates"] == len(INSTANCE) + len(REFUSED)
    assert info["primitive_static_candidates"] == 0
    assert skipped["Counter.<init>:void()"].startswith("constructor:")
    for _, name, reason in REFUSED.values():
        assert skipped.get(name) == reason, (name, skipped.get(name))
    assert {c["name"] for c in cases} == set(INSTANCE), skipped
    fresh = ["Counter", [("count", ("int", 3)), ("hits", ("int", 0)), ("label", ("str", "c")),
                         ("total", ("int", 7)), ("none", ("unit",))]]
    for c in cases:
        # Every case starts from the object the no-arg constructor built, defaults included.
        assert c["heap"] == [fresh] and c["self"] == ("ref", 0) and c["args"][0] == ("ref", 0)
        assert c["origin"] == "constructed"
        post = dict(c["post_heap"][0][1])
        if c["name"] == "Counter.bump:int(int)":
            by = c["args"][1][1]
            count = (3 + by + 2**31) % 2**32 - 2**31
            assert c["outcome"] == ("val", ("int", count))
            assert post["count"] == ("int", count) and post["total"] == ("int", 7 + by)
        if c["name"] == "Counter.reset:void(int)":
            assert c["outcome"] == ("val", ("unit",))
            assert post["count"] == c["args"][1] and post["label"] == ("str", "r")
        if c["name"] == "Counter.hitsPlus:int(int)":
            k = c["args"][1][1]
            assert c["outcome"] == ("val", ("int", k))


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
    src = tmp_path / "src"
    src.mkdir()
    (src / "Counter.java").write_text(SOURCE)
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


def _oracle(tmp, name, ast, src):
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    env.pop("AUTOFORM_NO_REEXEC", None)
    work = tmp / ("run-" + name)
    work.mkdir()
    r = subprocess.run([sys.executable, str(ROOT / "scripts/differential.py"), str(ast), str(src),
                        "DiffJavaReceivers", "4", "--language", "java", "--no-cache"],
                       capture_output=True, text=True, cwd=work, env=env, timeout=1800)
    report = json.loads((work / "conformance.json").read_text())
    return r, report


def test_instance_methods_agree_and_a_wrong_write_diverges(exported, module):
    tmp = exported
    target = GENERATED / "DiffJavaReceivers.lean"
    module.append(target)
    _run([sys.executable, ROOT / "cartographer/render_lean.py", tmp / "ast.json", target,
          "DiffJavaReceivers"], ROOT)
    r, report = _oracle(tmp, "honest", tmp / "ast.json", tmp / "src")
    assert r.returncode == 0, (r.stdout[-3000:], r.stderr[-2000:], report.get("status"))
    assert report["measurement_basis"] == "jvm-signatures-statics-v5"
    assert report["divergences"] == 0, report["divergence_detail"]
    agreed = {c["name"] for c in report["runtime_cases"] if c["comparison"] == "agree"}
    assert agreed == set(INSTANCE), (agreed, report["backend_skipped"],
                                     report["inconclusive_detail"])
    assert all("post_heap" in c for c in report["runtime_cases"])
    assert report["by_origin"]["constructed"]["agree"] >= len(INSTANCE)

    # A deliberately wrong model: `reset` writes "q" where the source writes "r". The
    # method returns `void`, so only the receiver's post-state can catch it.
    text = target.read_text()
    reset = text.index('name := "Counter.reset:void(int)"')
    lit = text.index('.str "r"', reset)
    target.write_text(text[:lit] + '.str "q"' + text[lit + len('.str "r"'):])
    r, report = _oracle(tmp, "wrong", tmp / "ast.json", tmp / "src")
    diverged = {d["function"] for d in report["divergence_detail"]}
    assert diverged == {"Counter.reset:void(int)"}, (diverged, r.stdout[-3000:])
    assert all("heap graph=some false" in d["detail"] for d in report["divergence_detail"])


@pytest.mark.skipif(not (HAVE_JDK and shutil.which("jar")), reason="JDK unavailable")
def test_the_dependency_classpath_is_what_lets_a_real_project_compile(tmp_path, differential, monkeypatch):
    """A candidate that imports a third-party class compiles only with the project's
    classpath supplied, and the classpath is recorded rather than implied."""
    dep = tmp_path / "dep"
    (dep / "lib").mkdir(parents=True)
    (dep / "classes").mkdir()   # javac 8 requires -d to exist
    (dep / "lib" / "Rates.java").write_text("package lib; public class Rates { public static int bp() { return 25; } }\n")
    subprocess.run(["javac", "-d", str(dep / "classes"), str(dep / "lib" / "Rates.java")], check=True)
    jar = tmp_path / "rates.jar"
    subprocess.run(["jar", "cf", str(jar), "-C", str(dep / "classes"), "."], check=True)
    src = tmp_path / "src"
    src.mkdir()
    (src / "Fee.java").write_text("public class Fee { public static int fee(int x) { return x * lib.Rates.bp(); } }\n")
    funcs = [_fn("Fee.fee:int(int)", "Fee.java", ["x"])]
    monkeypatch.delenv(differential.JAVA_CLASSPATH_ENV, raising=False)
    monkeypatch.setattr(differential, "WORK", str(tmp_path / "work-a"))
    cases, info, skipped = differential.java_backend(str(src), funcs, 2)
    assert cases == [] and skipped["Fee.fee:int(int)"].startswith("javac failed")
    assert info["compile_failure_causes"] == {"unresolved package (missing classpath or source root)": 1}
    monkeypatch.setenv(differential.JAVA_CLASSPATH_ENV, str(jar))
    monkeypatch.setattr(differential, "WORK", str(tmp_path / "work-b"))
    cases, info, skipped = differential.java_backend(str(src), funcs, 2)
    assert info["dependency_classpath"] == [str(jar)] and info["files_compiled"] == 1
    assert [c["outcome"] for c in cases] == [("val", ("int", 25 * c["args"][0][1])) for c in cases] and cases
