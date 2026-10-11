"""Java `switch` (JLS §14.11) against the JVM.

javasrc2cpg names switch labels `case`/`default` (empty parserTypeName), which the
C-shaped lowering did not recognise: every Java case had no value and no case ever
matched, so a switch was silently skipped. The commons-lang3 oracle exposed it
(`StringUtils.repeat` returned `null`-as-unit) once `String.length` was modelled. This
exports classic switches (int, char, negative and string labels, fall-through, default
in the middle), compares the Lean model with the JVM on each input, and checks that the
shapes the lowering must refuse -- the arrow form, which does not fall through, and a
non-literal label -- are named holes. Needs Joern (`AUTOFORM_TEST_JOERN=1`), the JDK and
`lake`; each missing piece is a named SKIP.
"""
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]

SOURCE = r"""
public class W {
  static int ints(int x) {
    switch (x) {
      case 1: return 10;
      case 2: case 3: x += 5; break;
      default: return -1;
      case 4: x = x * 3;
    }
    return x;
  }
  static int strs(String s) {
    switch (s) { case "a:b": return 1; case "c": return 3; default: return 2; }
  }
  static int chars(char c) {
    int r = 0;
    switch (c) { case 'a': r = 1; case ':': r += 2; break; case 'z': r = 9; }
    return r;
  }
  static int negs(int x) { int r = 0; switch (x) { case -1: r = 5; break; default: r = 7; } return r; }
  static int arrow(int x) { switch (x) { case 1 -> { x = 10; } default -> x = -1; } return x; }
  static int named(int x) { int r = 0; switch (x) { case Integer.MAX_VALUE: r = 6; } return r; }
}
"""
CASES = [("ints", "int", v) for v in (0, 1, 2, 3, 4, 5, -7)] + \
        [("strs", "str", v) for v in ("a:b", "c", "", "a")] + \
        [("chars", "char", v) for v in (97, 58, 122, 98)] + \
        [("negs", "int", v) for v in (-1, 0, 1)]


def _joern():
    home = Path(os.environ.get("JOERN_HOME", Path.home() / "joern"))
    return home / "joern-cli" if (home / "joern-cli").is_dir() else home


def _run(args, cwd, timeout=600):
    r = subprocess.run([str(a) for a in args], cwd=str(cwd), capture_output=True, text=True,
                       timeout=timeout)
    assert r.returncode == 0, (r.stdout + r.stderr)[-3000:]
    return r.stdout


@pytest.fixture
def exported(tmp_path):
    if os.environ.get("AUTOFORM_TEST_JOERN") != "1":
        pytest.skip("set AUTOFORM_TEST_JOERN=1 to export Java through Joern")
    joern = _joern()
    if not (joern / "joern").is_file():
        pytest.skip("Joern not found (JOERN_HOME)")
    src = tmp_path / "src"
    src.mkdir()
    (src / "W.java").write_text(SOURCE)
    _run([joern / "joern-parse", src, "--output", tmp_path / "cpg.bin"], tmp_path)
    _run([joern / "joern", "--script", ROOT / "cartographer/export_ast.sc",
          "--param", "cpgPath=%s" % (tmp_path / "cpg.bin"), "--param", "out=%s" % (tmp_path / "ast.json"),
          "--param", "dataModel=lp64"], tmp_path)
    return tmp_path, json.loads((tmp_path / "ast.json").read_text())


def _func(funcs, short):
    hit = [f for f in funcs if f["name"].startswith("W.%s:" % short)]
    assert len(hit) == 1, [f["name"] for f in funcs]
    return hit[0]


def test_refused_shapes_are_named_holes(exported):
    _, funcs = exported
    assert "control:SWITCH:java-arrow" in json.dumps(_func(funcs, "arrow")["body"])
    assert "control:SWITCH:java-non-literal-label" in json.dumps(_func(funcs, "named")["body"])
    for short in ("ints", "strs", "chars", "negs"):
        assert '"hole' not in json.dumps(_func(funcs, short)["body"]), short


def test_classic_switch_agrees_with_the_jvm(exported):
    tmp, funcs = exported
    if shutil.which("javac") is None or shutil.which("java") is None:
        pytest.skip("javac/java not on PATH")
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    if not Path(lake).exists():
        pytest.skip("lake not found")
    drv = SOURCE.replace("public class W {", "public class W {\n  public static void main(String[] a) {\n" +
                         "".join("    System.out.println(%s(%s));\n" % (
                             f, '"%s"' % v if k == "str" else "(char) %d" % v if k == "char" else str(v))
                                 for f, k, v in CASES) + "  }\n", 1)
    jdir = tmp / "jvm"
    jdir.mkdir()
    (jdir / "W.java").write_text(drv)
    _run(["javac", "-d", jdir, jdir / "W.java"], jdir)
    jvm = _run(["java", "-cp", jdir, "W"], jdir).split()
    model = tmp / "Sw.lean"
    _run([sys.executable, ROOT / "cartographer/render_lean.py", tmp / "ast.json", model, "Sw"], ROOT)
    driver = model.read_text() + "\nopen Autoform.Core Autoform.Generated.Sw\n"
    for f, k, v in CASES:
        arg = ('.str %s' % json.dumps(v)) if k == "str" else ".int (%d)" % v
        driver += ('#eval IO.println (match runFunc program 2000 %s [%s] with '
                   '| .val (.int v) => toString v | r => "unexpected " ++ reprStr r)\n'
                   % (json.dumps(_func(funcs, f)["name"]), arg))
    (tmp / "Drive.lean").write_text(driver)
    lean = [l for l in _run([lake, "env", "lean", tmp / "Drive.lean"], ROOT, timeout=1200).split("\n") if l.strip()]
    assert len(lean) == len(jvm) == len(CASES), (lean[-5:], jvm[-5:])
    bad = [(c, w, g) for c, w, g in zip(CASES, jvm, lean) if w != g]
    assert bad == [], bad
