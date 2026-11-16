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
             "  public static final String GREETING = \"hi\";\n"
             "  public static int pick(int a, int b) { return a; }\n"
             "  public static long add(long a, long b) { return a + b; }\n"
             "  public static int forty() { return 40; }\n"
             "  public static String greet() { return GREETING; }\n"
             "}\n",
             [dict(name="Numbers.pick:int(int,int)", file="Numbers.java", params=["a", "b"],
                   body=_ret(_name("a"))),
              dict(name="Numbers.add:long(long,long)", file="Numbers.java", params=["a", "b"],
                   body=_ret(_binop("num:java:i64:+", _name("a"), _name("b")))),
              dict(name="Numbers.forty:int()", file="Numbers.java", params=[],
                   body=_ret(_int(40))),
              dict(name="Numbers.greet:java.lang.String()", file="Numbers.java", params=[],
                   body=_ret({"k": "field", "a": {"k": "fnref", "v": "Numbers"},
                              "f": "GREETING"}))],
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
    # The oracle re-executed itself under the sandbox (or says it was told not to): the
    # report carries the mechanism and whether it was enforced, never silence.
    assert report["sandbox"]["mechanism"] in ("seatbelt", "bwrap", "unshare", "off")
    assert report["sandbox"]["enforced"] is (os.environ.get("AUTOFORM_SANDBOX", "on") != "off")
    if report["sandbox"]["enforced"]:
        assert report["sandbox"]["network"] == "denied"
        assert report["backend_info"]["sandbox"]["inherited"] is True
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
    if lang == "java":
        # The agreeing observation carries the statics bindings its case ran with:
        # the holder cell lives in the recorded heap and the `javaStaticKey` frame
        # binding names it. synth_specs.py replays a case from the record alone, so
        # the bindings must travel with the observation or a static read holes there.
        greeted = [c for c in report["runtime_cases"]
                   if c["name"] == "Numbers.greet:java.lang.String()"]
        assert greeted, report["runtime_cases"]
        for c in greeted:
            assert c["comparison"] == "agree", c
            binding = dict(c["globals"]).get("<static>Numbers")
            assert binding and binding[0] == "ref", c.get("globals")
            assert c["heap"][binding[1]][0] == "<module>static:Numbers", c["heap"]
            assert dict(c["heap"][binding[1]][1])["GREETING"] == ["str", "hi"], c["heap"]


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
    for basis in ("node-numeric-pool-v2", "jvm-signatures-statics-v5", "go-package-func-v1",
                  "python-exception-guards-v3", "python-deadlines-v4", "c-native-typed-boundary-v4"):
        assert basis in src, basis


class _Refused:
    """A sandbox launch that records its command and reports a failed run."""
    record = {"mechanism": "test"}

    def __init__(self, command, launched):
        launched.append(list(command))

    def run(self, *args, **kwargs):
        return subprocess.CompletedProcess([], 1, "", "A.java:1: error: refused by the test\n1 error")


def _java_corpus(tmp_path, n):
    src = tmp_path / "src"
    src.mkdir()
    funcs = []
    for i in range(n):
        (src / ("C%d.java" % i)).write_text(
            "public class C%d { public static int f(int x) { return x; } }\n" % i)
        funcs.append(dict(name="C%d.f:int(int)" % i, file="C%d.java" % i, params=["x"],
                          body=_ret(_name("x"))))
    ast = tmp_path / "ast.json"
    ast.write_text(json.dumps(funcs))
    return ast, src, [f["name"] for f in funcs]


@pytest.mark.parametrize("focused", [False, True])
def test_focus_is_applied_before_the_jvm_backend_compiles_anything(tmp_path, differential,
                                                                   monkeypatch, focused):
    """`--focus` used to filter cases AFTER every candidate file had been compiled and
    driven, so a 7,349-function service paid for the whole corpus and timed out. Counted
    by the `javac` launches the backend makes: one per candidate file without focus, only
    the focused function's file with it."""
    ast, src, names = _java_corpus(tmp_path, 4)
    launched = []
    monkeypatch.setattr(differential.sandbox, "sandboxed",
                        lambda command, **kw: _Refused(command, launched))
    monkeypatch.setattr(differential, "missing_tools", lambda *a: [])
    monkeypatch.setattr(differential, "WORK", str(tmp_path / "work"))
    argv = ["differential.py", str(ast), str(src), "Test", "2", "--no-cache"]
    if focused:
        (tmp_path / "focus.json").write_text(json.dumps([names[2]]))
        argv += ["--focus", str(tmp_path / "focus.json")]
    monkeypatch.setattr(differential.sys, "argv", argv)
    monkeypatch.chdir(tmp_path)
    assert differential.main() == 2          # every compile refused: no cases, not a pass
    compiled = [c[-1] for c in launched if c[0] == "javac"]
    report = json.loads((tmp_path / "conformance.json").read_text())
    if focused:
        assert compiled == [str(src / "C2.java")]
        assert set(report["backend_skipped"]) == {names[2]}
        assert report["focus"]["backend_population"] == 1
        assert "among the --focus functions" in report["backend_status"]
    else:
        assert sorted(compiled) == sorted(str(src / ("C%d.java" % i)) for i in range(4))
        assert set(report["backend_skipped"]) == set(names) and report["focus"] is None
    # The hole-free population, and so the coverage denominator, is the whole AST either way.
    assert report["functions_hole_free"] == 4


@pytest.mark.parametrize("lang,ext,backend", [("go", "go", "go_backend"),
                                              ("js", "js", "node_backend")])
def test_focus_narrows_what_the_go_and_node_backends_are_given(tmp_path, differential,
                                                              monkeypatch, lang, ext, backend):
    funcs = [dict(name="f%d" % i, file="m." + ext, params=[], body=_ret(_name("x")))
             for i in range(3)]
    ast = tmp_path / "ast.json"
    ast.write_text(json.dumps(funcs))
    (tmp_path / "focus.json").write_text(json.dumps(["f1"]))
    given = []
    monkeypatch.setattr(differential, backend,
                        lambda root, fs, *a, **k: given.append([f["name"] for f in fs]) or ([], {}, {}))
    monkeypatch.setattr(differential, "missing_tools", lambda *a: [])
    monkeypatch.setattr(differential.sys, "argv",
                        ["differential.py", str(ast), str(tmp_path), "Test", "2", "--language",
                         lang, "--focus", str(tmp_path / "focus.json")])
    monkeypatch.chdir(tmp_path)
    assert differential.main() == 2
    assert given == [["f1"]]


def test_focus_keeps_same_named_c_definitions_so_ambiguity_is_still_refused(differential):
    """C refuses an entry point defined twice under one source name in one file. Cutting
    the population to the focused definition alone would hide the ambiguity."""
    funcs = [dict(name="a.c:f#1", sourceName="f", file="a.c"),
             dict(name="a.c:f#2", sourceName="f", file="a.c"),
             dict(name="a.c:g", file="a.c"), dict(name="b.c:f", sourceName="f", file="b.c")]
    kept = differential.focus_population(funcs, {"a.c:f#1"}, same_named=True)
    assert [f["name"] for f in kept] == ["a.c:f#1", "a.c:f#2"]
    assert [f["name"] for f in differential.focus_population(funcs, {"a.c:f#1"})] == ["a.c:f#1"]
    assert differential.focus_population(funcs, None) is funcs


def test_java_planner_attempts_static_void_and_charsequence_results(tmp_path, differential,
                                                                   monkeypatch):
    """A static `void` method (`Validate.isTrue(boolean)`'s shape) and a `CharSequence`
    result (`StringUtils.defaultIfBlank`'s) used to be skipped as signatures before any
    compile; now they are candidates and reach javac, which this test's sandbox refuses,
    so their skip reason is the compile and not the signature. A `StringBuilder` result
    still refuses by name."""
    src = tmp_path / "src"
    src.mkdir()
    (src / "V.java").write_text(
        "public class V {\n"
        "  public static void check(boolean b) { if (!b) throw new IllegalArgumentException(); }\n"
        "  public static CharSequence text(CharSequence s) { return s; }\n"
        "  public static StringBuilder built(int n) { return new StringBuilder(); }\n"
        "}\n")
    funcs = [dict(name="V.check:void(boolean)", file="V.java", params=["b"],
                  body=_ret({"k": "unit"})),
             dict(name="V.text:java.lang.CharSequence(java.lang.CharSequence)", file="V.java",
                  params=["s"], body=_ret(_name("s"))),
             dict(name="V.built:java.lang.StringBuilder(int)", file="V.java", params=["n"],
                  body=_ret(_name("n")))]
    launched = []
    monkeypatch.setattr(differential.sandbox, "sandboxed",
                        lambda command, **kw: _Refused(command, launched))
    monkeypatch.setattr(differential, "WORK", str(tmp_path / "work"))
    cases, info, skipped = differential.java_backend(str(src), funcs, 2)
    assert cases == []
    assert info["primitive_static_candidates"] == 2
    assert skipped["V.check:void(boolean)"].startswith("javac failed")
    assert skipped["V.text:java.lang.CharSequence(java.lang.CharSequence)"].startswith("javac failed")
    assert skipped["V.built:java.lang.StringBuilder(int)"].startswith("non-primitive signature")


def test_case_cap_keeps_every_function_and_is_deterministic(differential):
    """The cap used to be one random draw over every case: the CommonsLang3 run kept 600
    of 1087 and lost about 20 functions whole. Each function now keeps min(n, 2) of its
    cases before any function gets more, the total is exactly the cap, exact duplicates
    go first, and the same seed keeps the same cases."""
    import collections
    import random
    cases = []
    for i in range(300):                       # 300 functions with 1..5 cases each
        for j in range(1 + i % 5):
            cases.append({"name": "f%d" % i, "args": [["int", j]], "outcome": ["val", ["int", j]],
                          "origin": "random"})
    per = collections.Counter(c["name"] for c in cases)  # floors over UNIQUE cases:
    cases += [dict(cases[0]), dict(cases[1])]  # ... the two appended exact duplicates
    assert len(cases) > 600                    # are dropped before any seat is counted
    kept, duplicates = differential.cap_cases(cases, 600, random.Random(7))
    assert duplicates == 2 and len(kept) == 600
    got = collections.Counter(c["name"] for c in kept)
    assert all(got[name] >= min(n, differential.CAP_FLOOR) for name, n in per.items())
    again, _ = differential.cap_cases(cases, 600, random.Random(7))
    assert [repr(c) for c in again] == [repr(c) for c in kept]
    # Suite-traced cases still come first, and are never deduplicated.
    suite = [dict(c, origin="test-suite") for c in cases[:700]]
    kept, duplicates = differential.cap_cases(suite + cases, 600, random.Random(7))
    assert duplicates == 2 and all(c["origin"] == "test-suite" for c in kept)
    # Under the cap nothing is touched, duplicates included.
    assert differential.cap_cases(cases[:10] + cases[:1], 600) == (cases[:10] + cases[:1], 0)


def test_case_cap_limit_is_read_from_the_environment(monkeypatch):
    """The 600 default kept the CommonsLang3 domains at one or two cases each, and the
    mutation gate found 59 of 125 conformance theorems vacuous on them. `AUTOFORM_CASE_CAP`
    raises the cap for a run that wants every built case compared; unset, nothing changes."""
    from conftest import SCRIPTS, load
    monkeypatch.setenv("AUTOFORM_NO_REEXEC", "1")
    monkeypatch.setenv("AUTOFORM_CASE_CAP", "2405")
    capped = load(os.path.join(SCRIPTS, "differential.py"), "af_differential_capped")
    assert capped.MAX_TOTAL_CASES == 2405
    monkeypatch.delenv("AUTOFORM_CASE_CAP")
    default = load(os.path.join(SCRIPTS, "differential.py"), "af_differential_default_cap")
    assert default.MAX_TOTAL_CASES == 600


def test_skip_reasons_are_counted_over_every_skip_not_the_sample(differential):
    """conformance.json keeps 40 sampled skips; the reason counts evidence aggregated
    from that sample said 25/13/2 of a 232-skip run. `backend_skipped_by_reason` counts
    all of them, by the reason's head."""
    skipped = {}
    for i in range(150):
        skipped["A.a%d:int(int[])" % i] = "array signature: int[] -- the model has no ..."
    for i in range(80):
        skipped["A.n%d:java.util.Date()" % i] = ("non-primitive signature: java.util.Date is not "
                                                 "primitive, String, a cached box or a corpus enum")
    skipped["A.<init>:void()"] = "constructor: builds receivers, is not called as a method"
    skipped["A.focus:int()"] = "constructor: builds receivers, is not called as a method"
    record = differential.skip_record(skipped, {"A.focus:int()"})
    assert record["backend_skipped_total"] == 232
    assert len(record["backend_skipped"]) == 40 and record["backend_skipped_sampled"] is True
    assert "A.focus:int()" in record["backend_skipped"]
    assert record["backend_skipped_by_reason"] == {"array signature": 150,
                                                   "non-primitive signature": 80,
                                                   "constructor": 2}
    assert sum(record["backend_skipped_by_reason"].values()) == record["backend_skipped_total"]
    small = differential.skip_record({"A.x:int()": "javac failed: x"}, None)
    assert small["backend_skipped_sampled"] is False and small["backend_skipped_by_reason"] == {"javac failed": 1}
