"""Execute the shipped drivers, including failures the old harness silently skipped."""
import json
import math
import shutil
import struct
import subprocess

import pytest


def function(name, file, params, **extra):
    return dict(name=name, file=file, params=params, **extra)


def test_go_executes_package_with_local_dependency(tmp_path, differential):
    if not shutil.which("go"):
        pytest.skip("Go runtime unavailable")
    source = tmp_path / "source"
    source.mkdir()
    (source / "go.mod").write_text("module example.local/check\n\ngo 1.20\n")
    (source / "helper").mkdir()
    (source / "helper/h.go").write_text("package helper\nfunc One() int64 { return 1 }\n")
    (source / "numbers.go").write_text('''package numbers
import "example.local/check/helper"
func Add(a int64) int64 { return a + helper.One() }
func Wide() uint64 { return 18446744073709551615 }
func Quotient(a int64, b int64) int64 { return a / b }
''')
    funcs = [function("numbers.Add", "numbers.go", ["a"]),
             function("numbers.Wide", "numbers.go", []),
             function("numbers.Quotient", "numbers.go", ["a", "b"])]
    cases, info, skipped = differential.runtime_backends.go_backend(source, funcs, 5, tmp_path)
    assert not skipped, skipped
    assert info["cases_built"] == 15
    add = [c for c in cases if c["name"] == "numbers.Add"]
    assert add[3]["outcome"] == ("val", ("int", -9223372036854775808))
    assert [c for c in cases if c["name"] == "numbers.Wide"][0]["outcome"] == (
        "val", ("int", 18446744073709551615))
    assert not (source / "autoform_runtime_test.go").exists()


def test_a_go_package_runs_in_the_module_that_contains_it(tmp_path, differential):
    """The analysed root is a repository whose `go.mod` sits below it (`svc/go.mod`), as
    a `pr` run on the repository root sees it: the copy keeps `svc/go.mod`, so `go test`
    runs the package inside that module and its module-local import resolves."""
    if not shutil.which("go"):
        pytest.skip("Go runtime unavailable")
    rb = differential.runtime_backends
    source = tmp_path / "repo"
    (source / "svc/calc").mkdir(parents=True)
    (source / "svc/limits").mkdir(parents=True)
    (source / "svc/go.mod").write_text("module example.local/svc\n\ngo 1.20\n")
    (source / "svc/limits/limits.go").write_text("package limits\n\nconst Max = 100\n")
    (source / "svc/calc/calc.go").write_text(
        'package calc\n\nimport "example.local/svc/limits"\n\n'
        "func Cap(x int64) int64 {\n\tif x > limits.Max {\n\t\treturn limits.Max\n\t}\n\treturn x\n}\n")
    (source / "svc/calc/counter.go").write_text(
        "package calc\n\ntype Counter struct{ n int64 }\n\n"
        "func (c Counter) Offset(x int64) int64 { return c.n + x }\n")
    # The exporter's shape of a method: receiver first, typed by the package path.
    method = function("example.local/svc/calc.Counter.Offset", "svc/calc/counter.go", ["c", "x"],
                      sourceName="Offset", paramTypes=["example.local/svc/calc.Counter", "int64"])
    funcs = [function("calc.Cap", "svc/calc/calc.go", ["x"]), method]
    cases, info, skipped = rb.go_backend(source, funcs, 4, tmp_path / "work")
    # The method is refused by name; it is never called bare, so the package still builds.
    assert skipped == {method["name"]: "receiver fixture required"}
    assert info["cases_built"] == 4
    assert [c["outcome"] for c in cases][:2] == [("val", ("int", 0)), ("val", ("int", 1))]


@pytest.mark.parametrize("suffix", ["js", "cjs", "mjs", "ts"])
def test_node_executes_unexported_functions_and_implicit_this(tmp_path, differential, suffix):
    if not shutil.which("node"):
        pytest.skip("Node runtime unavailable")
    source = tmp_path / "source"
    source.mkdir()
    name = "numbers." + suffix
    original = "function add(a, b) { return a + b; }\nfunction constant() { return 7; }\n"
    (source / name).write_text(original)
    funcs = [function(name + "::program:add", name, ["this", "a", "b"]),
             function(name + "::program:constant", name, ["this"])]
    cases, info, skipped = differential.runtime_backends.node_backend(
        source, funcs, 5, "ts" if suffix == "ts" else "js", tmp_path)
    assert not skipped, skipped
    assert info["cases_built"] == 10
    assert cases[0]["args"][0] == ("unit",)
    assert cases[0]["outcome"] == ("val", ("int", 1))
    assert cases[-1]["outcome"] == ("val", ("int", 7))
    assert (source / name).read_text() == original


def node_run(tmp_path, differential, files, funcs, lang="ts", root="source", ncases=5):
    if not shutil.which("node"):
        pytest.skip("Node runtime unavailable")
    for rel, text in files.items():
        (tmp_path / rel).parent.mkdir(parents=True, exist_ok=True)
        (tmp_path / rel).write_text(text)
    work = tmp_path / "work"
    work.mkdir()
    return differential.runtime_backends.node_backend(tmp_path / root, funcs, ncases, lang, work)


def test_node_unencodable_result_is_refused_not_an_exception(tmp_path, differential):
    files = {"source/m.ts": "export class K { constructor() { this.a = 1; } }\n"
                            "export function inst(s: string): K { return new K(); }\n"
                            "export function boom(n: number): number { throw new RangeError('x'); }\n"}
    cases, info, skipped = node_run(tmp_path, differential, files, [
        function("m.ts::program:inst", "m.ts", ["s"], paramTypes=["__ecma.String"]),
        function("m.ts::program:boom", "m.ts", ["n"], paramTypes=["__ecma.Number"])])
    assert skipped == {"m.ts::program:inst": "unusable result: no encoding for a value of type object (K)"}
    assert [c["outcome"] for c in cases] == [("exn", "RangeError")] * 5
    assert all(c["name"].endswith("boom") for c in cases)


def test_node_arrays_and_plain_objects_encode_structurally(tmp_path, differential):
    """A dense Array / plain object result is a list / string-keyed dict on the wire, in
    the shape Core's harness reports a boxed JavaScript list / dict (`unboxDeep`).
    Everything whose structure Core's literals cannot reproduce is refused by name."""
    files = {"source/m.js": (
        'export function arns(s) { return s === "prod" ? ["p"] : ["d", s]; }\n'
        'export function tag(s) { return {key: s, n: 1, inner: {v: [s]}, u: undefined}; }\n'
        'export function bare(s) { return Object.create(null); }\n'
        'export function sparse(s) { return [1, , 3]; }\n'
        'export function extra(s) { const a = [1]; a.x = 2; return a; }\n'
        'export function cyc(s) { const a = []; a.push(a); return a; }\n'
        'export function intKey(s) { return {b: 1, 2: 0}; }\n'
        'export function getter(s) { return {get g() { return 1; }}; }\n'
        'export function sym(s) { return {[Symbol.iterator]: 1}; }\n')}
    names = ("arns", "tag", "bare", "sparse", "extra", "cyc", "intKey", "getter", "sym")
    cases, info, skipped = node_run(tmp_path, differential, files, [
        function("m.js::program:" + n, "m.js", ["s"], paramTypes=["__ecma.String"])
        for n in names], lang="js", ncases=2)
    by = {}
    for c in cases:
        by.setdefault(c["name"].split(":")[-1], []).append(c)
    assert [c["outcome"] for c in by["arns"]] == [
        ("val", ("list", [("str", "d"), ("str", "")])),
        ("val", ("list", [("str", "d"), ("str", "0")]))]
    assert by["tag"][0]["outcome"] == ("val", ("dict", [
        (("str", "key"), ("str", "")), (("str", "n"), ("int", 1)),
        (("str", "inner"), ("dict", [(("str", "v"), ("list", [("str", "")]))])),
        (("str", "u"), ("unit",))]))
    assert by["bare"][0]["outcome"] == ("val", ("dict", []))
    why = {k.split(":")[-1]: v for k, v in skipped.items()}
    assert why == {
        "sparse": "unusable result: no encoding for a sparse array or an array with extra properties",
        "extra": "unusable result: no encoding for a sparse array or an array with extra properties",
        "cyc": "unusable result: no encoding for a cyclic array",
        "intKey": "unusable result: no encoding for an object with an integer-like key",
        "getter": "unusable result: no encoding for an object with an accessor property",
        "sym": "unusable result: no encoding for an object with a symbol key"}


def test_node_string_params_draw_body_literals_and_string_pool(tmp_path, differential):
    files = {"source/m.ts": 'export function isProd(stage: string): number { return stage === "prod" ? 1 : 0; }\n'}
    body = {"k": "ret", "e": {"k": "cond", "c": {"k": "binop", "op": "==", "a": {"k": "name", "v": "stage"},
                                                 "b": {"k": "str", "v": "prod"}},
                              "t": {"k": "int", "v": 1}, "e": {"k": "int", "v": 0}}}
    cases, info, skipped = node_run(tmp_path, differential, files, [
        function("m.ts::program:isProd", "m.ts", ["stage"], paramTypes=["__ecma.String"], body=body)])
    assert not skipped, skipped
    assert [(c["args"], c["outcome"]) for c in cases[:3]] == [
        ([("str", "prod")], ("val", ("int", 1))),
        ([("str", "")], ("val", ("int", 0))),
        ([("str", "0")], ("val", ("int", 0)))]
    # Without aligned types the parameter is not guessed to be a string.
    cases, _, _ = node_run(tmp_path / "x", differential, files, [
        function("m.ts::program:isProd", "m.ts", ["stage"], body=body)])
    assert cases[0]["args"] == [("int", 0)]


def test_node_resolves_node_modules_above_the_subdir(tmp_path, differential):
    files = {"pkg/node_modules/dep/package.json": '{"name": "dep", "main": "index.js"}',
             "pkg/node_modules/dep/index.js": "module.exports = {one: () => 1};\n",
             "pkg/lib/uses.mjs": "import dep from 'dep';\nfunction one() { return dep.one(); }\n"}
    cases, info, skipped = node_run(tmp_path, differential, files,
                                    [function("uses.mjs::program:one", "uses.mjs", ["this"])],
                                    lang="js", root="pkg/lib", ncases=1)
    assert not skipped, skipped
    assert cases[0]["outcome"] == ("val", ("int", 1))
    assert not (tmp_path / "pkg/lib/node_modules").exists()


def test_node_static_methods_by_class_and_refusals(tmp_path, differential):
    files = {"source/c.ts": "export function twice(a: number): number { return -1; }\n"
                            "export class C {\n"
                            "  static twice(a: number): number { return a * 2; }\n"
                            "  static get g(): number { return 3; }\n"
                            "  inc(a: number): number { return a + 1; }\n}\n"}
    cases, info, skipped = node_run(tmp_path, differential, files, [
        function("c.ts::program:C:twice", "c.ts", ["a"], sourceName="twice"),
        function("c.ts::program:C:g", "c.ts", [], sourceName="g"),
        function("c.ts::program:C:inc", "c.ts", ["a"], sourceName="inc"),
        function("c.ts::program:C:<init>", "c.ts", [], sourceName="<init>"),
        function("c.ts::program:C:inc:<lambda>0", "c.ts", [], sourceName="<lambda>0")])
    pool = (0, 1, -1, 2147483647, 4294967296)
    assert [c["outcome"] for c in cases] == [("val", ("int", 2 * a)) for a in pool] \
        + [("val", ("int", a + 1)) for a in pool]
    assert info["instance_cases"] == 5
    # The instance method runs on a receiver the driver builds: a fresh `C` with no own
    # fields, its (empty) state reported before and after the call.
    inc = [c for c in cases if c["name"] == "c.ts::program:C:inc"]
    assert len(inc) == 5
    for c, a in zip(inc, pool):
        assert c["heap"] == [("C", [], None)] and c["self"] == ("ref", 0)
        assert c["args"] == [("int", a)] and c["origin"] == "constructed"
        assert c["post_heap"] == [("C", [], None)]
    assert all(c["name"] == "c.ts::program:C:twice"
               for c in cases if c["origin"] != "constructed")
    assert skipped == {
        "c.ts::program:C:g": "C.g is a static accessor or field, not a static method",
        "c.ts::program:C:<init>": "constructor: receiver fixture required",
        "c.ts::program:C:inc:<lambda>0": "not a module-scope callable or static method"}


def test_c_native_abi_is_not_assumed_int32(tmp_path, differential):
    if not shutil.which("cc"):
        pytest.skip("C compiler unavailable")
    (tmp_path / "numbers.c").write_text('''
long add(long a, long b) { return a + b; }
unsigned long long wide(void) { return 18446744073709551615ULL; }
int hang(int n) { for (;;) n++; }
''')
    get = differential.c_runtime(str(tmp_path))
    add = get(function("add", "numbers.c", ["a", "b"], paramIntegerTypes=["i64", "i64"], returnIntegerType="i64"))
    assert differential.call_in_child(add, [2147483647, 1]) == 2147483648
    wide = get(function("wide", "numbers.c", [], paramIntegerTypes=[], returnIntegerType="u64"))
    assert differential.call_in_child(wide, []) == 18446744073709551615
    assert get(function("add", "numbers.c", ["a", "b"])) is None
    hang = get(function("hang", "numbers.c", ["n"], paramIntegerTypes=["i32"], returnIntegerType="i32"))
    assert differential.call_in_child(hang, [0]) is None


@pytest.mark.parametrize("number", [0.0, -0.0, 3.75, float("inf"), float("nan")])
def test_float_wire_round_trip(number, differential):
    encoded = differential.Encoder().enc(number)
    assert differential.lean_val(encoded).startswith("Val.float (Fl.ofBits ")
    text = "Autoform.Core.EResult.val (Autoform.Core.Val.float { fmt := { prec := 53, emax := 1023, expBits := 11 }, bits := %d })" % encoded[1]
    decoded = differential.parse_result(text)
    assert differential.same(encoded, decoded[1], 0)
    if number == 0:
        opposite = ("float", encoded[1] ^ (1 << 63))
        assert not differential.same(encoded, opposite, 0)


def test_unknown_or_mixed_language_cannot_win_a_majority_vote(differential):
    for paths in (["a.py", "b.go"], ["a.py", "b.py", "c.unknown"]):
        assert differential.detect_language([dict(file=p) for p in paths])[0] is None


def test_python_module_name_cannot_resolve_to_standard_library(tmp_path, differential):
    source = tmp_path / "numbers.py"
    source.write_text("def add(a, b): return a + b\n")
    module = differential.load_module(str(source), str(tmp_path))
    assert module.add(2, 3) == 5
    assert module.__file__ == str(source)


def test_runtime_observations_reject_stale_sources(tmp_path, differential):
    rb = differential.runtime_backends
    source = tmp_path / "f.go"
    source.write_text("package sample\nfunc F() int { return 1 }\n")
    fs = [dict(name="sample.F", file="f.go", params=[])]
    ast = tmp_path / "ast.json"
    ast.write_text(json.dumps(fs))
    generated = tmp_path / "Model.lean"
    generated.write_text("def model := 1\n")
    report = tmp_path / "report.json"
    report.write_text(json.dumps(dict(module="Sample", build_stable=True, divergences=0,
        provenance=dict(ast_sha256=rb.sha256(ast), generated_sha256=rb.sha256(generated),
                        source_sha256=rb.source_fingerprints(tmp_path, fs),
                        semantics_sha256=rb.semantics_fingerprints()),
        runtime_cases=[dict(name="sample.F", comparison="agree")], runtime="go")))
    assert len(rb.load_observations(report, ast, tmp_path, "Sample", generated)[0]) == 1
    header = tmp_path / 'external.h'
    header.write_text('#define VALUE 1\n')
    evidence = json.loads(report.read_text())
    evidence['backend_info'] = {'dependencies_sha256': {str(header): rb.sha256(header)}}
    report.write_text(json.dumps(evidence))
    assert len(rb.load_observations(report, ast, tmp_path, "Sample", generated)[0]) == 1
    header.write_text('#define VALUE 2\n')
    with pytest.raises(ValueError, match='header dependency does not match'):
        rb.load_observations(report, ast, tmp_path, "Sample", generated)
    header.write_text('#define VALUE 1\n')
    source.write_text("package sample\nfunc F() int { return 2 }\n")
    with pytest.raises(ValueError, match="does not match"):
        rb.load_observations(report, ast, tmp_path, "Sample", generated)


def test_no_cases_is_nonzero_and_writes_report(tmp_path, differential, monkeypatch):
    ast = tmp_path / "ast.json"
    ast.write_text(json.dumps([dict(name="empty", file="f.go", params=[], body=dict(k="skip"))]))
    monkeypatch.setattr(differential, "go_backend", lambda *a: ([], {}, {}))
    monkeypatch.setattr(differential, "missing_tools", lambda *a: [])
    monkeypatch.setattr(differential.sys, "argv", ["differential.py", str(ast), str(tmp_path), "Test"])
    monkeypatch.chdir(tmp_path)
    assert differential.main() == 2
    assert json.loads((tmp_path / "conformance.json").read_text())["total"] == 0


# --------------------------------------------------------------------------- #
# JVM backend: a `CharSequence` parameter is a String slot (commons-lang3's
# `StringUtils` surface is almost entirely `CharSequence`-typed), and a corpus that is a
# SUBSET of a larger tree names the rest of that tree with AUTOFORM_JAVA_SOURCEPATH.
# --------------------------------------------------------------------------- #

def _java_funcs(*names):
    return [function(n, "Text.java", list("abcdefg"[:n.count(",") + (0 if n.endswith("()") else 1)]))
            for n in names]


@pytest.mark.skipif(not shutil.which("javac") or not shutil.which("java"), reason="JDK unavailable")
def test_jvm_backend_passes_strings_through_charsequence_parameters(tmp_path, differential):
    (tmp_path / "Text.java").write_text(
        "public class Text {\n"
        "  public static int len(CharSequence cs) { return cs == null ? -1 : cs.length(); }\n"
        "  public static boolean same(CharSequence a, String b) { return a.toString().equals(b); }\n"
        "  public static CharSequence echo(CharSequence cs) { return cs; }\n"
        "}\n")
    funcs = _java_funcs("Text.len:int(java.lang.CharSequence)",
                        "Text.same:boolean(java.lang.CharSequence,java.lang.String)",
                        "Text.echo:java.lang.CharSequence(java.lang.CharSequence)")
    cases, info, skipped = differential.java_backend(str(tmp_path), funcs, 4)
    # Since the v5 oracle (822af57) a CharSequence RESULT is comparable too: `echo` is a
    # candidate and its String results are compared. Only the call whose result is `null`
    # has no Core counterpart, and that is named per function, not hidden.
    assert list(skipped) == ["Text.echo:java.lang.CharSequence(java.lang.CharSequence)"]
    assert skipped["Text.echo:java.lang.CharSequence(java.lang.CharSequence)"].startswith(
        "returned null")
    assert info["primitive_static_candidates"] == 3 and info["cases_built"] == 11
    for c in cases:
        if c["name"].startswith("Text.echo"):
            arg, = c["args"]
            assert arg[0] == "str" and c["outcome"] == ("val", arg)
        elif c["name"].startswith("Text.len"):
            # `null` is an exceptional input for a Java reference parameter.
            arg, = c["args"]
            want = -1 if arg == ("unit",) else len(arg[1])
            assert arg[0] in ("str", "unit") and c["outcome"] == ("val", ("int", want))
        else:
            (ka, a), (kb, b) = c["args"]
            assert (ka, kb) == ("str", "str") and c["outcome"] == ("val", ("bool", a == b))


@pytest.mark.skipif(not shutil.which("javac") or not shutil.which("java"), reason="JDK unavailable")
def test_jvm_backend_resolves_a_subset_corpus_against_extra_source_roots(tmp_path, differential, monkeypatch):
    """A corpus exported as a subset of a tree: `A` (in the subset) uses `B` (outside it)."""
    subset = tmp_path / "subset" / "com" / "example"
    full = tmp_path / "full" / "com" / "example"
    subset.mkdir(parents=True); full.mkdir(parents=True)
    (subset / "A.java").write_text("package com.example;\npublic class A { public static int f(int x) { return B.v() + x; } }\n")
    (full / "B.java").write_text("package com.example;\npublic class B { static int v() { return 7; } }\n")
    funcs = [function("com.example.A.f:int(int)", "com/example/A.java", ["x"])]
    monkeypatch.delenv(differential.JAVA_SOURCEPATH_ENV, raising=False)
    cases, info, skipped = differential.java_backend(str(tmp_path / "subset"), funcs, 2)
    assert not cases and "extra_source_roots" not in info
    assert list(skipped.values())[0].startswith("javac failed"), skipped
    monkeypatch.setenv(differential.JAVA_SOURCEPATH_ENV, str(tmp_path / "full"))
    cases, info, skipped = differential.java_backend(str(tmp_path / "subset"), funcs, 2)
    assert not skipped, skipped
    assert info["extra_source_roots"] == [str(tmp_path / "full")] and info["cases_built"] == 2
    assert cases[0]["outcome"] == ("val", ("int", 7 + cases[0]["args"][0][1]))
    # A root that does not exist is a configuration error, reported, never ignored.
    monkeypatch.setenv(differential.JAVA_SOURCEPATH_ENV, str(tmp_path / "nowhere"))
    cases, info, _ = differential.java_backend(str(tmp_path / "subset"), funcs, 2)
    assert not cases and "missing directory" in info["driver"]


def test_kotlin_test_source_sets_are_recognised(differential):
    is_test = differential.runtime_backends.is_test_source
    for path in ("src/test/kotlin/p/A.kt", "src/testFixtures/kotlin/p/A.kt",
                 "src/integTest/kotlin/p/A.kt", "module/test/p/A.kt", "src/main/kotlin/p/ATest.kt",
                 "src/main/kotlin/p/ATests.kt"):
        assert is_test(path), path
    for path in ("src/main/kotlin/p/A.kt", "src/main/kotlin/testing/A.kt", "kotlin/p/Contest.kt",
                 "src/main/kotlin/p/Testable.kt"):
        assert not is_test(path), path


KOTLIN = pytest.mark.skipif(not shutil.which("kotlinc") or not shutil.which("javac")
                            or not shutil.which("java"), reason="kotlinc or JDK unavailable")


def _kotlin_tree(root, files):
    for rel, text in files.items():
        (root / rel).parent.mkdir(parents=True, exist_ok=True)
        (root / rel).write_text(text)


@KOTLIN
def test_kotlin_oracle_skips_tests_and_retries_candidates_alone(tmp_path, differential, monkeypatch):
    """A test source with an unresolvable test dependency is never compiled; a broken main
    file fails the whole-tree attempt, and the candidate file alone then compiles."""
    monkeypatch.setattr(differential, "WORK", str(tmp_path / "work"))
    monkeypatch.delenv(differential.JAVA_CLASSPATH_ENV, raising=False)
    src = tmp_path / "src"
    _kotlin_tree(src, {
        "src/main/kotlin/p/Util.kt": "package p\n\nfun add(a: Int, b: Int): Int = a + b\n"
                                     "fun twice(xs: List<Int>): List<Int> = xs.map { it * 2 }\n",
        "src/main/kotlin/p/Broken.kt": "package p\n\nfun broken(): Int = missingSymbol()\n",
        "src/test/kotlin/p/UtilTest.kt": "package p\n\nimport io.mockk.mockk\n"
                                         "class UtilTest { fun t() { mockk<Any>() } }\n"})
    util = "src/main/kotlin/p/Util.kt"
    funcs = [function("p.add:int(int,int)", util, ["a", "b"], sourceName="add"),
             function("p.twice.<lambda>0:int(int)", util, ["it"], sourceName="<lambda>0")]
    cases, info, skipped = differential.java_backend(str(src), funcs, 3, kotlin=True)
    # The lambda is a named refusal, not a static candidate that silently never runs.
    assert skipped == {"p.twice.<lambda>0:int(int)": "lambda: not callable by name"}
    assert info["primitive_static_candidates"] == 1
    whole, alone = info["kotlin_compile_attempts"]
    assert not whole["ok"] and whole["files"] == 2 and alone["ok"] and alone["files"] == 1
    assert whole["failing_files"] == ["src/main/kotlin/p/Broken.kt"]
    assert whole["first_errors"][0].startswith("src/main/kotlin/p/Broken.kt: unresolved reference")
    assert "UtilTest" not in json.dumps(info)
    assert info["files_candidate"] == info["files_compiled"] == 1
    assert "compile_failure_causes" not in info
    wrap = lambda v: (v + 2 ** 31) % 2 ** 32 - 2 ** 31  # Kotlin Int addition overflows
    assert len(cases) == 3 and all(
        c["outcome"] == ("val", ("int", wrap(c["args"][0][1] + c["args"][1][1]))) for c in cases)


@KOTLIN
def test_kotlin_oracle_names_the_failing_file_and_keeps_its_first_error(tmp_path, differential,
                                                                        monkeypatch):
    """Two candidate files, one broken: the good one is still called, and the broken one's
    skip reason and backend_info carry its FIRST error and its file name."""
    monkeypatch.setattr(differential, "WORK", str(tmp_path / "work"))
    monkeypatch.delenv(differential.JAVA_CLASSPATH_ENV, raising=False)
    src = tmp_path / "src"
    filler = "".join("fun filler%d(): Int = alsoMissing%d()\n" % (i, i) for i in range(60))
    _kotlin_tree(src, {
        "p/Good.kt": "package p\n\nfun inc(a: Int): Int = a + 1\n",
        "p/Bad.kt": "package p\n\nfun dec(a: Int): Int = firstMissing(a) - 1\n" + filler})
    funcs = [function("p.inc:int(int)", "p/Good.kt", ["a"], sourceName="inc"),
             function("p.dec:int(int)", "p/Bad.kt", ["a"], sourceName="dec")]
    cases, info, skipped = differential.java_backend(str(src), funcs, 2, kotlin=True)
    assert {c["name"] for c in cases} == {"p.inc:int(int)"}
    reason = skipped["p.dec:int(int)"]
    assert reason.startswith("kotlinc failed: p/Bad.kt: unresolved reference 'firstMissing'"), reason
    assert list(info["compile_failing_files"]) == ["p/Bad.kt"]
    assert "firstMissing" in info["compile_failing_files"]["p/Bad.kt"]
    assert info["compile_failure_causes"] == {"unresolved reference (missing classpath or source)": 1}
    assert info["files_candidate"] == 2 and info["files_compiled"] == 1 and info["files_failed"] == 1
    scopes = [a["scope"] for a in info["kotlin_compile_attempts"]]
    assert scopes == ["candidate files with the project's non-test sources",
                      "candidate file p/Good.kt", "candidate file p/Bad.kt"], scopes


def test_kotlin_reference_closure_resolves_by_package_and_simple_name(tmp_path, differential):
    """Imports (explicit, nested, star), same-package use and fully qualified names pull
    in the declaring files, transitively; a same-named declaration of another package, a
    word inside a comment and an unreferenced file do not."""
    _kotlin_tree(tmp_path, {
        "a/Use.kt": "package p.a\n\nimport p.b.Mode\nimport p.c.*\n// Unrelated is only mentioned here\n"
                    "fun use(m: Mode): Int = helper() + Holder.Inner.X + p.d.far()\n",
        "a/Help.kt": "package p.a\n\ninternal fun helper(): Int = Deep.v\n",
        "a/Deep.kt": "package p.a\n\nobject Deep { val v = 1 }\n",
        "a/Unrelated.kt": "package p.a\n\nclass Unrelated\n",
        "b/Mode.kt": "package p.b\n\nenum class Mode { ON }\n",
        "b/Other.kt": "package p.b\n\nfun helper(): Int = 2\n",
        "c/Holder.kt": "package p.c\n\nclass Holder { object Inner { const val X = 3 } }\n",
        "c/Star.kt": "package p.c\n\nfun String.ext(): Int = length\n",
        "d/Far.kt": "package p.d\n\nfun far(): Int = 4\n",
        "e/Mode.kt": "package p.e\n\nclass Mode\n"})
    seed = tmp_path / "a/Use.kt"
    pool = sorted(p for p in tmp_path.rglob("*.kt") if p != seed)
    got = differential.runtime_backends.kotlin_reference_closure([seed], pool)
    assert got[0] == seed
    assert sorted(str(p.relative_to(tmp_path)) for p in got) == [
        "a/Deep.kt", "a/Help.kt", "a/Use.kt", "b/Mode.kt", "c/Holder.kt", "c/Star.kt", "d/Far.kt"]


@KOTLIN
def test_kotlin_oracle_compiles_a_candidate_with_the_files_it_references(tmp_path, differential,
                                                                          monkeypatch):
    """The whole tree fails (an unrelated broken file) and the candidate alone fails (it
    uses a same-package class): the attempt with the files it references compiles."""
    monkeypatch.setattr(differential, "WORK", str(tmp_path / "work"))
    monkeypatch.delenv(differential.JAVA_CLASSPATH_ENV, raising=False)
    src = tmp_path / "src"
    _kotlin_tree(src, {
        "p/Use.kt": "package p\n\nfun scaled(a: Int): Int = a * Factor.K\n",
        "p/Factor.kt": "package p\n\nobject Factor { const val K = 3 }\n",
        "p/Broken.kt": "package p\n\nfun broken(): Int = missingSymbol()\n"})
    funcs = [function("p.scaled:int(int)", "p/Use.kt", ["a"], sourceName="scaled")]
    cases, info, skipped = differential.java_backend(str(src), funcs, 3, kotlin=True)
    assert skipped == {}
    scopes = [(a["scope"], a["files"], a["ok"]) for a in info["kotlin_compile_attempts"]]
    assert scopes == [("candidate files with the project's non-test sources", 3, False),
                      ("candidate files with the 1 same-repo file(s) they reference", 2, True)], scopes
    wrap = lambda v: (v + 2 ** 31) % 2 ** 32 - 2 ** 31  # Kotlin Int multiplication overflows
    assert len(cases) == 3 and all(c["outcome"] == ("val", ("int", wrap(c["args"][0][1] * 3))) for c in cases)
