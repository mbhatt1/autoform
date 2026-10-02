"""Kotlin conformance test: width-typed integer arithmetic (item S), against a Kotlin compiler.

1. `tests/fixtures/kotlinintwidth/cases.kt` is the source; `ast.json` is what
   `cartographer/export_ast.sc` produced from it (kotlin2cpg 4.0.606, from Maven Central --
   see `provenance.json`, which pins the digests).
2. `Autoform/KotlinIntWidthProgram.lean` is `render_lean.py` of that AST (checked byte for
   byte).
3. `Autoform/KotlinIntWidth.lean` pins, with `#guard_msgs`, what Core computes for every
   `case_*` function; THIS file compiles `cases.kt` with `Main.kt` (the driver, not
   exported), runs it on the JVM, and checks each pin against the program's output.

The oracle is a real Kotlin compiler: `kotlinc` on PATH, or -- when `AUTOFORM_KOTLIN_JARS`
names a directory holding kotlin-compiler-embeddable and kotlin-stdlib jars (the runtime
dependencies of `io.joern:kotlin2cpg_3:4.0.606`) -- that compiler's `K2JVMCompiler`.
Skipped, not passed, when neither exists or there is no JDK.
"""
import glob
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys

import pytest


ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FIX = os.path.join(ROOT, "tests", "fixtures", "kotlinintwidth")
SRC = os.path.join(FIX, "cases.kt")
DRIVER = os.path.join(FIX, "Main.kt")
AST = os.path.join(FIX, "ast.json")
PROV = os.path.join(FIX, "provenance.json")
PINS = os.path.join(ROOT, "Autoform", "KotlinIntWidth.lean")
PROGRAM = os.path.join(ROOT, "Autoform", "KotlinIntWidthProgram.lean")
RENDER = os.path.join(ROOT, "cartographer", "render_lean.py")


def pinned_results() -> dict:
    text = open(PINS).read()
    pat = re.compile(r'/-- info: "([^"]*)" -/\s*\n#guard_msgs in #eval gRun "(case_\w+)"')
    return {m.group(2): m.group(1) for m in pat.finditer(text)}


def as_kotlin(core: str) -> str:
    if core.startswith("bool "):
        return core[5:]
    m = re.fullmatch(r"<exception (.*)>", core)
    if m:
        return "exception " + m.group(1)
    return core


def build_and_run(tmp_path) -> str:
    """Compile cases.kt + Main.kt and return the program's stdout; skip if no compiler."""
    if shutil.which("java") is None:
        pytest.skip("no JDK on PATH")
    out = tmp_path / "ktout"
    jars = os.environ.get("AUTOFORM_KOTLIN_JARS")
    if shutil.which("kotlinc"):
        jar = tmp_path / "k.jar"
        subprocess.run(["kotlinc", SRC, DRIVER, "-include-runtime", "-d", str(jar)],
                       check=True, capture_output=True, text=True)
        cmd = ["java", "-jar", str(jar)]
    elif jars and glob.glob(os.path.join(jars, "kotlin-compiler-embeddable-*.jar")):
        def jar(prefix):
            return sorted(glob.glob(os.path.join(jars, prefix + "-[0-9]*.jar")))[-1]
        stdlib = jar("kotlin-stdlib")
        cp = os.pathsep.join([jar("kotlin-compiler-embeddable"), stdlib, jar("kotlin-script-runtime"),
                              jar("kotlin-reflect"), jar("kotlinx-coroutines-core-jvm"),
                              jar("annotations"), jar("kotlin-daemon-embeddable")])
        subprocess.run(["java", "-cp", cp, "org.jetbrains.kotlin.cli.jvm.K2JVMCompiler",
                        "-no-stdlib", "-no-reflect", "-cp", stdlib, "-d", str(out), SRC, DRIVER],
                       check=True, capture_output=True, text=True)
        cmd = ["java", "-cp", os.pathsep.join([str(out), stdlib]), "MainKt"]
    else:
        pytest.skip("no Kotlin compiler (kotlinc on PATH, or AUTOFORM_KOTLIN_JARS)")
    return subprocess.run(cmd, check=True, capture_output=True, text=True).stdout


def test_every_case_is_pinned_and_agrees_with_kotlin(tmp_path):
    stdout = build_and_run(tmp_path)
    got = dict(line.split(" ", 1) for line in stdout.splitlines() if line.startswith("case_"))
    declared = set(re.findall(r"^fun (case_\w+)\(\)", open(SRC).read(), re.M))
    assert declared and set(got) == declared, "Main.kt must print every case_* function"
    pins = pinned_results()
    assert set(pins) == declared, (
        f"cases without a pin: {sorted(declared - set(pins))}; "
        f"pins without a case: {sorted(set(pins) - declared)}")
    for case, expected in got.items():
        assert as_kotlin(pins[case]) == expected, (
            f"{case}: Core pinned {pins[case]!r}, Kotlin gives {expected!r}")


def test_no_case_is_a_hole():
    assert not [c for c, p in pinned_results().items() if p.startswith("hole ")]


def test_ast_was_exported_from_this_source():
    prov = json.load(open(PROV))
    assert prov["source_sha256"] == hashlib.sha256(open(SRC, "rb").read()).hexdigest(), (
        "cases.kt changed since ast.json was exported; re-run the command in "
        "tests/fixtures/kotlinintwidth/provenance.json")
    assert prov["ast_sha256"] == hashlib.sha256(open(AST, "rb").read()).hexdigest()


def test_case_functions_are_hole_free():
    # The file's `<global>` module initializer lists its functions as `stmt:METHOD`
    # holes (a pre-existing Kotlin gap, unrelated to arithmetic); the cases are clean.
    for fn in json.load(open(AST)):
        if fn["name"].startswith("case_"):
            assert '"hole' not in json.dumps(fn), fn["name"]


def test_ast_uses_typed_operators():
    ops = set(re.findall(r'"op":\s*"([^"]+)"', open(AST).read()))
    for op in ("*:k64", "*:k32", "-:q32", "*:q64", "<<:k32", ">>>:k64", ">>:q32", "~:q32",
               "cast:i8", "cast:u8", "cast:i64", "/:k32"):
        assert op in ops, op
    for op in ("+", "-", "*", "/", "%", "<<", ">>", ">>>"):
        assert op not in ops, f"untyped {op!r} survived in the Kotlin export"


def test_program_is_the_render_of_the_ast(tmp_path):
    out = tmp_path / "KotlinIntWidthProgram.lean"
    r = subprocess.run([sys.executable, RENDER, AST, str(out), "KotlinIntWidth"],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    assert out.read_text() == open(PROGRAM).read(), (
        "Autoform/KotlinIntWidthProgram.lean is not the render of "
        "tests/fixtures/kotlinintwidth/ast.json")
