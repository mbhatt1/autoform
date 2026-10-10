"""Java `throw new C(args)` through the real exporter, the JVM and Core.

javasrc2cpg lowers a class instance creation into a BLOCK (`$obj = <operator>.alloc`,
`C.<init>($obj, args)`, `$obj`) in the throw's expression position. On commons-lang3 that
BLOCK was the single largest hole of the corpus (70 `expr:BLOCK-impure`, every one of them a
`throw new IllegalArgumentException(...)`). The exporter now translates a throw of a class the
corpus does NOT declare into `Stmt.raise (.str <SimpleName>)` after evaluating the constructor
arguments -- the payload the JVM oracle observes (`getSimpleName()`), and the payload Core gives
a builtin exception (`.exn (.str "ArithmeticException")`). A corpus-declared class keeps its
own constructor and stays on the ordinary path.

AUTOFORM_TEST_JOERN=1 enables the parse/export; the JDK and Lean are then required.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]

SOURCE = '''public class Guard {
  public static int positive(int x) {
    if (x <= 0) { throw new IllegalArgumentException("x must be positive"); }
    return x;
  }
  public static int described(int x) {
    if (x <= 0) { throw new IllegalArgumentException("x must be positive: " + x); }
    return x;
  }
  public static long nonZero(long x) {
    if (x == 0) { throw new java.util.NoSuchElementException(); }
    return x;
  }
  public static int own(int x) { throw new Failure(x); }
  static class Failure extends RuntimeException { Failure(int x) { super("" + x); } }
}
'''

RUNNER = '''public class Runner {
  static void show(String label, Runnable r) {
    try { r.run(); System.out.println(label + "|ok"); }
    catch (RuntimeException e) { System.out.println(label + "|" + e.getClass().getSimpleName()); }
  }
  public static void main(String[] a) {
    show("positive(3)", () -> Guard.positive(3));
    show("positive(0)", () -> Guard.positive(0));
    show("described(0)", () -> Guard.described(0));
    show("nonZero(5)", () -> Guard.nonZero(5));
    show("nonZero(0)", () -> Guard.nonZero(0));
  }
}
'''


def run(args, cwd, env, timeout=600):
    p = subprocess.run(list(map(str, args)), cwd=cwd, env=env, text=True,
                       capture_output=True, timeout=timeout)
    assert p.returncode == 0, p.stdout + p.stderr
    return p


def test_java_throw_of_a_jdk_exception_raises_its_simple_name(tmp_path):
    if not os.environ.get("AUTOFORM_TEST_JOERN"):
        pytest.skip("set AUTOFORM_TEST_JOERN=1 to parse/export through Joern")
    env = {k: os.environ[k] for k in ("PATH", "HOME", "LANG", "LC_ALL", "TMPDIR", "JAVA_HOME")
           if k in os.environ}
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
    env.setdefault("LANG", "C.UTF-8")
    env.setdefault("LC_ALL", "C.UTF-8")
    for exe in ("java", "javac"):
        assert shutil.which(exe, path=env["PATH"]), f"missing runtime: {exe}"
    if not shutil.which("lake", path=env["PATH"]):
        pytest.skip("Lean is not installed")
    joern_home = Path(os.environ.get("JOERN_HOME", Path.home() / "joern"))
    if (joern_home / "joern-cli").is_dir():
        joern_home /= "joern-cli"
    assert (joern_home / "joern").is_file(), "set JOERN_HOME to the joern-cli directory"

    src = tmp_path / "src"
    src.mkdir()
    (src / "Guard.java").write_text(SOURCE)

    # The JVM's answer first: the exception's simple name, which is all the oracle sees.
    classes = tmp_path / "classes"
    classes.mkdir()
    (tmp_path / "Runner.java").write_text(RUNNER)
    run(["javac", "-d", classes, src / "Guard.java", tmp_path / "Runner.java"], tmp_path, env)
    jvm = dict(line.split("|") for line in
               run(["java", "-cp", classes, "Runner"], tmp_path, env).stdout.split())
    assert jvm == {"positive(3)": "ok", "positive(0)": "IllegalArgumentException",
                   "described(0)": "IllegalArgumentException",
                   "nonZero(5)": "ok", "nonZero(0)": "NoSuchElementException"}

    run([joern_home / "joern-parse", src, "--language", "JAVASRC", "--output", "cpg.bin"],
        tmp_path, env)
    export = run([joern_home / "joern", "--script", ROOT / "cartographer/export_ast.sc",
                  "--param", "cpgPath=cpg.bin", "--param", "out=ast.json",
                  "--param", "dataModel=lp64"], tmp_path, env)
    # The Python handler sidecar is Python-only; a Java export must not warn about it.
    assert "python handler sidecar" not in export.stdout + export.stderr
    functions = {f["name"]: f for f in json.loads((tmp_path / "ast.json").read_text())}

    def holes(node, acc):
        if isinstance(node, dict):
            if node.get("k") == "hole":
                acc.append(node["label"])
            for v in node.values():
                holes(v, acc)
        elif isinstance(node, list):
            for v in node:
                holes(v, acc)
        return acc

    def raises(node, acc):
        if isinstance(node, dict):
            if node.get("k") == "raise":
                acc.append(node["e"])
            for v in node.values():
                raises(v, acc)
        elif isinstance(node, list):
            for v in node:
                raises(v, acc)
        return acc

    positive = functions["Guard.positive:int(int)"]
    described = functions["Guard.described:int(int)"]
    non_zero = functions["Guard.nonZero:long(long)"]
    own = functions["Guard.own:int(int)"]
    for f in (positive, described, non_zero):
        assert holes(f["body"], []) == [], f["name"]
    assert raises(positive["body"], []) == [{"k": "str", "v": "IllegalArgumentException"}]
    assert raises(described["body"], []) == [{"k": "str", "v": "IllegalArgumentException"}]
    assert raises(non_zero["body"], []) == [{"k": "str", "v": "NoSuchElementException"}]
    # The message expression is still evaluated, in order, before the raise: the string
    # concatenation survives as a statement rather than being dropped with the payload.
    assert '"exprS"' in json.dumps(described["body"])
    # A corpus-declared exception class is NOT reduced to its name: its constructor is
    # the program's own code, and the ordinary path (today a hole) keeps it.
    assert raises(own["body"], []) == [{"k": "hole", "label": "expr:BLOCK-impure"}], own["body"]

    # Core's answer, from the rendered module, on the same inputs as the JVM run.
    model = tmp_path / "Model.lean"
    run([sys.executable, ROOT / "cartographer/render_lean.py", tmp_path / "ast.json", model,
         "JavaThrow"], ROOT, env)
    driver = model.read_text() + '''
open Autoform.Core Autoform.Generated.JavaThrow
def outcome (r : EResult) : String :=
  match r with
  | .val (.int n) => "ok:" ++ toString n
  | .exn (.str s) => s
  | .hole l => "hole:" ++ l
  | other => reprStr other
def main : IO Unit := do
  IO.println (outcome (runFunc program 200 "Guard.positive:int(int)" [.int 3]))
  IO.println (outcome (runFunc program 200 "Guard.positive:int(int)" [.int 0]))
  IO.println (outcome (runFunc program 200 "Guard.described:int(int)" [.int 0]))
  IO.println (outcome (runFunc program 200 "Guard.nonZero:long(long)" [.int 5]))
  IO.println (outcome (runFunc program 200 "Guard.nonZero:long(long)" [.int 0]))
'''
    (tmp_path / "Check.lean").write_text(driver)
    core = run(["lake", "env", "lean", "--run", tmp_path / "Check.lean"], ROOT, env).stdout.split()
    # `described(0)` is the named gap, not a guess: Java `String + int` is string
    # conversion (JLS §5.1.11), which Core's `.java` `+` does not model (`str + str` and
    # `int + int` only), so evaluating the message is a dynamic `binop:+` hole and the
    # oracle counts the case inconclusive. The JVM threw IllegalArgumentException there.
    assert core == ["ok:3", "IllegalArgumentException", "hole:binop:+",
                    "ok:5", "NoSuchElementException"]
