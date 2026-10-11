"""C `for` with elided clauses (C11 6.8.5.3) against the C compiler.

"Both clause-1 and expression-3 can be omitted. An omitted expression-2 is replaced by a
nonzero constant." The exporter used to hole every such loop (`control:FOR:elided-clause`);
`SourceCompiler.cForElided` now reads the clause slots from c2cpg's child `order`. This
exports every elision pattern, checks none holes, and compares the Lean model with the
natively compiled program on each input. Needs Joern (`AUTOFORM_TEST_JOERN=1`), `cc` and
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
int all_elided(int n) { int i = 0; for (;;) { if (i > n) break; i++; } return i; }
int no_cond(int n) { int s = 0; for (int i = 0;; i++) { if (i > n) break; s += i; } return s; }
int no_step(int n) { int s = 0; for (int i = 0; i < n;) { i++; s += i; } return s; }
int two_decls(int n) { int s = 0; for (int i = 0, j = 1;;) { if (i > n) break; i++; j++; s += j; } return s; }
int step_only(int n) { int i = 0, s = 0; for (;; i++) { if (i > n) break; if (i % 2) continue; s += i; } return s; }
int comma(int n) { int i, j; for (i = 0, j = 0;; i++, j++) { if (i > n) break; } return j; }
int cond_only(int n) { int i = 0, s = 0; for (; i < n;) { i++; s += i; } return s; }
int init_only(int n) { int i; for (i = 0;;) { if (i > n) break; i += 2; } return i; }
int returns(int n) { for (;;) { if (n <= 0) return 7; n -= 3; } }
"""
FUNCS = ["all_elided", "no_cond", "no_step", "two_decls", "step_only", "comma", "cond_only",
         "init_only", "returns"]
INPUTS = [-1, 0, 1, 2, 5, 10]


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
        pytest.skip("set AUTOFORM_TEST_JOERN=1 to export C through Joern")
    joern = _joern()
    if not (joern / "joern").is_file():
        pytest.skip("Joern not found (JOERN_HOME)")
    src = tmp_path / "src"
    src.mkdir()
    (src / "loops.c").write_text(SOURCE)
    _run([joern / "joern-parse", src, "--output", tmp_path / "cpg.bin"], tmp_path)
    _run([joern / "joern", "--script", ROOT / "cartographer/export_ast.sc",
          "--param", "cpgPath=%s" % (tmp_path / "cpg.bin"), "--param", "out=%s" % (tmp_path / "ast.json"),
          "--param", "dataModel=lp64"], tmp_path)
    return tmp_path, json.loads((tmp_path / "ast.json").read_text())


def test_every_elision_pattern_translates_hole_free(exported):
    _, funcs = exported
    by_name = {f["name"]: f for f in funcs}
    for name in FUNCS:
        body = json.dumps(by_name[name]["body"])
        assert '"hole' not in body, (name, body[:400])


def test_model_agrees_with_cc(exported):
    tmp, _ = exported
    cc = shutil.which("cc")
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    if cc is None:
        pytest.skip("no C compiler (cc) on PATH")
    if not Path(lake).exists():
        pytest.skip("lake not found")
    main = SOURCE + "\n#include <stdio.h>\nint main(void) {\n"
    for f in FUNCS:
        for n in INPUTS:
            main += '  printf("%%d\\n", %s(%d));\n' % (f, n)
    main += "  return 0;\n}\n"
    (tmp / "native.c").write_text(main)
    _run([cc, "-O0", "-o", tmp / "native", tmp / "native.c"], tmp)
    native = _run([tmp / "native"], tmp).split()
    model = tmp / "Loops.lean"
    _run([sys.executable, ROOT / "cartographer/render_lean.py", tmp / "ast.json", model, "Loops"], ROOT)
    driver = model.read_text() + "\nopen Autoform.Core Autoform.Generated.Loops\n"
    for f in FUNCS:
        for n in INPUTS:
            driver += ('#eval IO.println (match runFunc program 4000 "%s" [.int (%d)] with '
                       '| .val (.int v) => toString v | r => "unexpected " ++ reprStr r)\n' % (f, n))
    (tmp / "Drive.lean").write_text(driver)
    lean = _run([lake, "env", "lean", tmp / "Drive.lean"], ROOT, timeout=1200).split("\n")
    lean = [l for l in lean if l.strip()]
    cases = [(f, n) for f in FUNCS for n in INPUTS]
    assert len(lean) == len(native) == len(cases), (len(lean), len(native), lean[-5:])
    bad = [(c, w, g) for c, w, g in zip(cases, native, lean) if w != g]
    assert bad == [], bad
