"""Go `if` statements against the Go toolchain.

gosrc2cpg lowers `if [init;] cond { } else { }` into the ENCLOSING block as two
siblings, at the same source position: the init clause's own BLOCK -- empty for
every `if` written without an init, carrying the init's statements for
`if v := f(); cond` -- and then the CONTROL_STRUCTURE, whose children are the
condition, the then-block and the else-block. The frontend records no code on
that block, so `.code` reads back as Joern's `<empty>` placeholder, which the
exporter's "did the frontend drop statements?" check (`stmt:empty-ast-children`,
built for the C frontend, whose silent parse failures leave the REAL body text on
`.code`) took for dropped source: every Go `if` exported with that hole beside
it, so a function containing one was untranslatable (a `clamp` on the Go pr
fixture).

An empty init block now lowers to `Stmt.skip` (cartographer/compiler/
SourceCompiler.scala, `goIfInitOf`). A non-empty one is already sequenced ahead
of the `ifte`, so the init runs once and before the condition; it is flattened
into the enclosing scope, which is exact only when nothing else in the function
binds the init's names: gosrc2cpg resolves the `if`'s uses of a shadowing init
variable to the OUTER local, parameter or package variable, and the flattened
init would overwrite the outer one. Those stay the named hole `stmt:go-if-init`
(`goIfInitShadows`).

Exports the fixture, checks every plain form is hole-free and the shapes survived
(init before condition, else-if nested in the else branch), that every shadowing
form is the named hole, then compiles the same file with `go run` and compares
the Lean model with the real runtime on every case, including both sides of each
branch. Needs Joern (`AUTOFORM_TEST_JOERN=1`); the differential also needs `go`
and `lake`. Each missing piece is a named SKIP.
"""
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]

SOURCE = (Path(__file__).resolve().parent / "fixtures" / "go_if" / "gofuncs.go").read_text()

# (function, [x]); each function takes one int and returns one int.
CASES = (
    [("plain", [v]) for v in (5, 0, -3)] +
    [("ifelse", [v]) for v in (7, -7, 0)] +
    [("chain", [v]) for v in (20, 7, 1, 0, -5)] +
    [("withInit", [v]) for v in (6, 5, 0, -2)] +
    [("initElse", [v]) for v in (6, 3, 1, 0, -1)] +
    [("nested", [v]) for v in (9, 4, -1)] +
    [("twoInits", [v]) for v in (5, 2, 1, 0)]
)
LOWERED = sorted({f for f, _ in CASES} | {"double"})
SHADOWING = ("shadowLocal", "shadowParam", "shadowGlobal", "shadowInit", "laterVar")


def _joern():
    home = Path(os.environ.get("JOERN_HOME", Path.home() / "joern"))
    return home / "joern-cli" if (home / "joern-cli").is_dir() else home


def _run(args, cwd, env=None, timeout=900):
    r = subprocess.run([str(a) for a in args], cwd=str(cwd), env=env, capture_output=True,
                       text=True, timeout=timeout)
    assert r.returncode == 0, (r.stdout + r.stderr)[-3000:]
    return r.stdout


@pytest.fixture(scope="module")
def exported(tmp_path_factory):
    if os.environ.get("AUTOFORM_TEST_JOERN") != "1":
        pytest.skip("set AUTOFORM_TEST_JOERN=1 to export Go through Joern")
    joern = _joern()
    if not (joern / "joern").is_file():
        pytest.skip("Joern not found (JOERN_HOME)")
    tmp = tmp_path_factory.mktemp("goif")
    src = tmp / "src"
    src.mkdir()
    (src / "gofuncs.go").write_text(SOURCE)
    _run([joern / "joern-parse", src, "--output", tmp / "cpg.bin"], tmp)
    _run([joern / "joern", "--script", ROOT / "cartographer/export_ast.sc",
          "--param", "cpgPath=%s" % (tmp / "cpg.bin"), "--param", "out=%s" % (tmp / "ast.json"),
          "--param", "dataModel=lp64"], tmp)
    return tmp, json.loads((tmp / "ast.json").read_text())


def _func(funcs, short):
    hit = [f for f in funcs if f["name"].split(":")[0].split(".")[-1] == short]
    assert len(hit) == 1, (short, [f["name"] for f in funcs])
    return hit[0]


def _walk(body):
    """Every dict node in execution order: a `seq`'s `a` side before its `b` side."""
    out, stack = [], [body]
    while stack:
        v = stack.pop()
        if isinstance(v, dict):
            out.append(v)
            stack.extend(reversed([w for w in v.values() if isinstance(w, (dict, list))]))
        elif isinstance(v, list):
            stack.extend(reversed([w for w in v if isinstance(w, (dict, list))]))
    return out


def _holes(body):
    return [v["label"] for v in _walk(body) if v.get("k") in ("hole", "holeS")]


def _iftes(body):
    return [v for v in _walk(body) if v.get("k") == "ifte"]


def test_lowered_functions_are_hole_free(exported):
    _, funcs = exported
    holed = {f: _holes(_func(funcs, f)["body"]) for f in LOWERED}
    assert {f: h for f, h in holed.items() if h} == {}


def test_init_is_evaluated_once_and_before_the_condition(exported):
    """`if v := double(x); v > 10`: the call runs exactly once, ahead of the test.
    initElse exercises the `else if` arm, which reads the init's variable."""
    _, funcs = exported
    for short in ("withInit", "initElse"):
        kinds = [v.get("k") for v in _walk(_func(funcs, short)["body"])]
        assert kinds.count("call") == 1, (short, kinds)
        assert kinds.index("call") < kinds.index("ifte"), (short, kinds)


def test_else_if_is_an_if_in_the_else_branch(exported):
    """`if a {} else if b {} else {}`: the second `ifte` nests in the first's else."""
    _, funcs = exported
    iftes = _iftes(_func(funcs, "chain")["body"])
    assert len(iftes) == 2, iftes
    outer, inner = iftes
    assert _iftes(outer["e"]) == [inner]


def test_shadowing_init_is_a_named_hole(exported):
    """Flattening these would read or overwrite the wrong variable
    (`v := 1; if v := x; v > 0 { v = v + 10 }; return v` returns 1 in Go)."""
    _, funcs = exported
    for short in SHADOWING:
        assert "stmt:go-if-init" in _holes(_func(funcs, short)["body"]), short


def test_only_the_shadowing_inits_hole(exported):
    """No `if` leaves `stmt:empty-ast-children` behind, and `stmt:go-if-init` is
    confined to the shadowing forms (two same-named inits in sequence are not one)."""
    _, funcs = exported
    labels = {f["name"].split(".")[-1]: _holes(f["body"]) for f in funcs}
    assert {f: h for f, h in labels.items() if "stmt:empty-ast-children" in h} == {}
    assert sorted(f for f, h in labels.items() if "stmt:go-if-init" in h) == sorted(SHADOWING)


def test_lowering_agrees_with_go(exported):
    tmp, funcs = exported
    if shutil.which("go") is None:
        pytest.skip("no Go toolchain (go)")
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    if not Path(lake).exists():
        pytest.skip("lake not found")
    work = tmp / "native"
    work.mkdir(exist_ok=True)
    (work / "gofuncs.go").write_text(SOURCE)
    calls = "\n".join("    fmt.Println(%s(%s))" % (f, ", ".join(str(v) for v in args))
                      for f, args in CASES)
    (work / "main.go").write_text(
        'package main\n\nimport "fmt"\n\nfunc main() {\n%s\n}\n' % calls)
    # A private build cache: the suite may run several `go` tests at once.
    env = {k: os.environ[k] for k in ("PATH", "HOME", "LANG", "LC_ALL", "TMPDIR") if k in os.environ}
    env["GOCACHE"] = str(work / "gocache")
    native = _run(["go", "run", work / "gofuncs.go", work / "main.go"], work, env=env).splitlines()

    model = tmp / "GoIf.lean"
    _run([sys.executable, ROOT / "cartographer/render_lean.py", tmp / "ast.json", model,
          "GoIf"], ROOT)
    driver = model.read_text() + "\nopen Autoform.Core Autoform.Generated.GoIf\n"
    for f, args in CASES:
        driver += ('#eval IO.println (match runFunc program 4000 %s [%s] with '
                   '| .val (.int v) => toString v | .val (.str s) => s '
                   '| .val (.bool b) => toString b | .val .unit => "null" | .val (.fn n) => n '
                   '| .exn (.str n) => "exn:" ++ n | r => "unexpected " ++ reprStr r)\n'
                   % (json.dumps(_func(funcs, f)["name"]),
                      ", ".join(".int (%d)" % v for v in args)))
    (tmp / "Drive.lean").write_text(driver)
    lean = [l for l in _run([lake, "env", "lean", tmp / "Drive.lean"], ROOT,
                            timeout=1800).split("\n") if l.strip()]
    assert len(lean) == len(native) == len(CASES), (lean[-5:], native[-5:])
    bad = [(c, w, g) for c, w, g in zip(CASES, native, lean) if w != g]
    assert bad == [], bad
