"""The differential oracle end to end for Node, the JVM and Go, on in-repo fixtures.

`tests/test_runtime_backends.py` drives the runtime DRIVERS alone (does Node answer, does
`go test` build). These tests run the whole oracle -- runtime execution, `lake build` of
the rendered module, Lean evaluation of every case, the `same` comparison -- and read the
`conformance.json` the run writes. The subject is a hand-authored neutral AST for a
three-function fixture per language, NOT a Joern export: docs/languages.md names the real
corpora, whose sources are not in this repository. What these tests establish is that the
oracle for each runtime runs and agrees with Core on the fixture; what they do not
establish is anything about those corpora, and the support matrix says so in the same
words.

The end-to-end tests build a Lean module and evaluate it, so they are gated like the
Joern-backed suites: set `AUTOFORM_TEST_ORACLES=1` (or `AUTOFORM_TEST_JOERN=1`) to run
them. The `--language` tests below are cheap and always run.
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


def _name(v):
    return {"k": "name", "v": v}


def _ret(e):
    return {"k": "ret", "e": e}


def _binop(op, a, b):
    return {"k": "binop", "op": op, "a": a, "b": b}


def _int(n):
    return {"k": "int", "v": str(n)}


# language -> (source file, source text, functions, expected basis prefix, runtimes)
# The bodies use the operator spellings the exporter emits for each language
# (`js:+`, `num:java:i64:+`, `num:go:i64:+`), so the rendered module goes through the
# same Core paths a real export would.
FIXTURES = {
    "js": ("fixture.js",
           "function pick(a, b) { return a; }\n"
           "function add(a, b) { return a + b; }\n"
           "function forty() { return 40; }\n",
           [dict(name="fixture.js::program:pick", file="fixture.js", params=["this", "a", "b"],
                 body=_ret(_name("a"))),
            dict(name="fixture.js::program:add", file="fixture.js", params=["this", "a", "b"],
                 body=_ret(_binop("js:+", _name("a"), _name("b")))),
            dict(name="fixture.js::program:forty", file="fixture.js", params=["this"],
                 body=_ret(_int(40)))],
           "node-", ["node"]),
    "java": ("Numbers.java",
             "public class Numbers {\n"
             "  public static int pick(int a, int b) { return a; }\n"
             "  public static long add(long a, long b) { return a + b; }\n"
             "  public static int forty() { return 40; }\n"
             "}\n",
             [dict(name="Numbers.pick:int(int,int)", file="Numbers.java", params=["a", "b"],
                   body=_ret(_name("a"))),
              dict(name="Numbers.add:long(long,long)", file="Numbers.java", params=["a", "b"],
                   body=_ret(_binop("num:java:i64:+", _name("a"), _name("b")))),
              dict(name="Numbers.forty:int()", file="Numbers.java", params=[],
                   body=_ret(_int(40)))],
             "jvm-", ["javac", "java"]),
    "go": ("numbers.go",
           "package numbers\n"
           "func Pick(a int64, b int64) int64 { return a }\n"
           "func Add(a int64, b int64) int64 { return a + b }\n"
           "func Forty() int64 { return 40 }\n",
           [dict(name="numbers.Pick", file="numbers.go", params=["a", "b"],
                 body=_ret(_name("a"))),
            dict(name="numbers.Add", file="numbers.go", params=["a", "b"],
                 body=_ret(_binop("num:go:i64:+", _name("a"), _name("b")))),
            dict(name="numbers.Forty", file="numbers.go", params=[],
                 body=_ret(_int(40)))],
           "go-", ["go"]),
}


def _oracle_env():
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    env.pop("AUTOFORM_NO_REEXEC", None)
    return env


@pytest.fixture
def generated_module():
    """A throwaway `Autoform/Generated/<M>.lean`, removed with its build products."""
    made = []

    def make(module, ast_path):
        target = GENERATED / (module + ".lean")
        r = subprocess.run([sys.executable, str(ROOT / "cartographer/render_lean.py"),
                            str(ast_path), str(target), module],
                           capture_output=True, text=True, cwd=ROOT)
        assert r.returncode == 0, r.stderr
        made.append(target)
        return target

    yield make
    for target in made:
        target.unlink(missing_ok=True)
        lib = ROOT / ".lake/build/lib/lean/Autoform/Generated"
        for product in lib.glob(target.stem + ".*"):
            product.unlink(missing_ok=True)


def _skip_unless_runnable(runtimes):
    if not (os.environ.get("AUTOFORM_TEST_ORACLES") == "1"
            or os.environ.get("AUTOFORM_TEST_JOERN") == "1"):
        pytest.skip("set AUTOFORM_TEST_ORACLES=1 to run the runtime oracles end to end")
    missing = [r for r in runtimes if not shutil.which(r)]
    if missing:
        pytest.skip("runtime unavailable: " + ", ".join(missing))
    if not shutil.which("lake", path=_oracle_env()["PATH"]):
        pytest.skip("lake unavailable")


@pytest.mark.parametrize("lang", sorted(FIXTURES))
def test_oracle_agrees_with_core_on_the_fixture(lang, tmp_path, generated_module):
    filename, text, funcs, basis_prefix, runtimes = FIXTURES[lang]
    _skip_unless_runnable(runtimes)
    source = tmp_path / "source"
    source.mkdir()
    (source / filename).write_text(text)
    ast = tmp_path / "ast.json"
    ast.write_text(json.dumps(funcs))
    module = "DiffOracle" + lang.capitalize()
    generated_module(module, ast)
    work = tmp_path / "run"
    work.mkdir()
    r = subprocess.run([sys.executable, str(ROOT / "scripts/differential.py"), str(ast),
                        str(source), module, "3", "--language", lang],
                       capture_output=True, text=True, cwd=work, env=_oracle_env(),
                       timeout=900)
    report = json.loads((work / "conformance.json").read_text())
    assert r.returncode == 0, (r.stdout[-2000:], r.stderr[-2000:], report.get("status"))
    # The run says which runtime measured it, on what basis, and that the override was
    # used -- a Node rate must never read as a CPython one.
    assert report["language"] == lang and report["language_override"] == lang
    assert report["measurement_basis"].startswith(basis_prefix)
    assert report["backend_status"] == "available", report["backend_status"]
    assert report["runtime_version"] and not report["runtime_version"].startswith("unavailable")
    assert report["divergences"] == 0, report["divergence_detail"]
    names = {f["name"] for f in funcs}
    compared = {c["name"] for c in report["runtime_cases"]}
    assert compared == names, (compared, report["backend_skipped"], report["inconclusive_detail"])
    assert all(c["comparison"] == "agree" and c["runtime"] == report["runtime"]
               for c in report["runtime_cases"])
    assert report["agree"] >= len(funcs)
    # The fixture source was not modified: drivers work in a private copy.
    assert (source / filename).read_text() == text


def test_language_override_is_recorded_and_names_the_runtime_basis(tmp_path, differential,
                                                                    monkeypatch):
    ast = tmp_path / "ast.json"
    # An extension the table does not know: the vote alone would refuse.
    ast.write_text(json.dumps([dict(name="pkg.F", file="f.generated", params=[],
                                    body=dict(k="skip"))]))
    monkeypatch.setattr(differential, "go_backend", lambda *a: ([], {}, {}))
    monkeypatch.setattr(differential, "missing_tools", lambda *a: [])
    monkeypatch.setattr(differential.sys, "argv",
                        ["differential.py", str(ast), str(tmp_path), "Test", "3",
                         "--language", "go"])
    monkeypatch.chdir(tmp_path)
    assert differential.main() == 2          # no cases: not a pass
    report = json.loads((tmp_path / "conformance.json").read_text())
    assert report["language"] == "go" and report["language_override"] == "go"
    assert report["measurement_basis"] == "go-package-func-v1"
    assert "COUNTED" in report["measurement_basis_note"]


def test_unknown_language_override_is_refused(tmp_path, differential, monkeypatch):
    ast = tmp_path / "ast.json"
    ast.write_text(json.dumps([dict(name="f", file="f.go", params=[], body=dict(k="skip"))]))
    monkeypatch.setattr(differential.sys, "argv",
                        ["differential.py", str(ast), str(tmp_path), "Test", "3",
                         "--language", "cobol"])
    monkeypatch.chdir(tmp_path)
    assert differential.main() == 2


def test_every_runtime_has_its_own_measurement_basis(differential):
    """The basis strings are part of the evidence: a report must not describe a Node run
    in CPython's words."""
    src = (ROOT / "scripts/differential.py").read_text()
    for basis in ("node-numeric-pool-v1", "jvm-primitive-static-v1", "go-package-func-v1",
                  "python-exception-guards-v3", "python-deadlines-v4", "c-native-zero-boundary-v3"):
        assert basis in src, basis
