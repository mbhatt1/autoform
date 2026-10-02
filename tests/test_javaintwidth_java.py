"""Java conformance test: width-typed integer arithmetic (item O), against `java`.

1. `tests/fixtures/javaintwidth/JavaIntWidth.java` is the source; `ast.json` is what
   `cartographer/export_ast.sc` produced from it (javasrc2cpg 4.0.606, assembled from
   Maven Central -- see `provenance.json`, which pins both digests).
2. `Autoform/JavaIntWidthProgram.lean` is `render_lean.py` of that AST (checked byte for
   byte).
3. `Autoform/JavaIntWidth.lean` pins, with `#guard_msgs`, what Core computes for every
   `case_*` method; THIS file compiles the Java with `javac`, runs its `main` (which
   prints `name value` per case) and checks each pin against it.

Skipped, not passed, when no JDK is on PATH.
"""
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys

import pytest


ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FIX = os.path.join(ROOT, "tests", "fixtures", "javaintwidth")
SRC = os.path.join(FIX, "JavaIntWidth.java")
AST = os.path.join(FIX, "ast.json")
PROV = os.path.join(FIX, "provenance.json")
PINS = os.path.join(ROOT, "Autoform", "JavaIntWidth.lean")
PROGRAM = os.path.join(ROOT, "Autoform", "JavaIntWidthProgram.lean")
RENDER = os.path.join(ROOT, "cartographer", "render_lean.py")


def pinned_results() -> dict:
    text = open(PINS).read()
    pat = re.compile(r'/-- info: "([^"]*)" -/\s*\n#guard_msgs in #eval jRun "(case_\w+)"')
    return {m.group(2): m.group(1) for m in pat.finditer(text)}


@pytest.mark.skipif(shutil.which("javac") is None or shutil.which("java") is None,
                    reason="no JDK on PATH")
def test_every_case_is_pinned_and_agrees_with_java(tmp_path):
    subprocess.run(["javac", "-d", str(tmp_path), SRC], check=True,
                   capture_output=True, text=True)
    r = subprocess.run(["java", "-cp", str(tmp_path), "JavaIntWidth"], check=True,
                       capture_output=True, text=True)
    got = dict(line.split() for line in r.stdout.splitlines() if line.startswith("case_"))
    declared = set(re.findall(r"static long (case_\w+)\(\)", open(SRC).read()))
    assert declared and set(got) == declared, "main() must print every case_* method"
    pins = pinned_results()
    assert set(pins) == declared, (
        f"cases without a pin: {sorted(declared - set(pins))}; "
        f"pins without a case: {sorted(set(pins) - declared)}")
    for case, expected in got.items():
        assert pins[case] == expected, f"{case}: Core pinned {pins[case]!r}, java gives {expected}"


def test_ast_was_exported_from_this_source():
    prov = json.load(open(PROV))
    assert prov["source_sha256"] == hashlib.sha256(open(SRC, "rb").read()).hexdigest(), (
        "JavaIntWidth.java changed since ast.json was exported; re-run the command in "
        "tests/fixtures/javaintwidth/provenance.json")
    assert prov["ast_sha256"] == hashlib.sha256(open(AST, "rb").read()).hexdigest()


def test_ast_is_hole_free():
    assert '"hole' not in open(AST).read()


def test_ast_uses_typed_operators():
    ops = set(re.findall(r'"op":\s*"([^"]+)"', open(AST).read()))
    for op in ("*:j64", "*:j32", ">>:j32", ">>>:j32", ">>>:j64", "<<:j64", "cast:i8", "cast:u16"):
        assert op in ops, op


def test_program_is_the_render_of_the_ast(tmp_path):
    out = tmp_path / "JavaIntWidthProgram.lean"
    r = subprocess.run([sys.executable, RENDER, AST, str(out), "JavaIntWidth"],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    assert out.read_text() == open(PROGRAM).read(), (
        "Autoform/JavaIntWidthProgram.lean is not the render of "
        "tests/fixtures/javaintwidth/ast.json")
