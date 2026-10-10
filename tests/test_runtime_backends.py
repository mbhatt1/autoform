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
    # The CharSequence RETURN is still refused: `enc` has no faithful encoding for it.
    assert skipped == {"Text.echo:java.lang.CharSequence(java.lang.CharSequence)": "non-primitive signature"}
    assert info["primitive_static_candidates"] == 2 and info["cases_built"] == 8
    for c in cases:
        if c["name"].startswith("Text.len"):
            (kind, text), = c["args"]
            assert kind == "str" and c["outcome"] == ("val", ("int", len(text)))
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
