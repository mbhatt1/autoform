"""Go conformance test: width-typed integer arithmetic (item S), against the `go` toolchain.

1. `tests/fixtures/gointwidth/cases.go` is the source; `ast.json` is what
   `cartographer/export_ast.sc` produced from it (gosrc2cpg 4.0.606, assembled from Maven
   Central, with goastgen 0.1.0 -- see `provenance.json`, which pins the digests).
2. `Autoform/GoIntWidthProgram.lean` is `render_lean.py` of that AST (checked byte for
   byte).
3. `Autoform/GoIntWidth.lean` pins, with `#guard_msgs`, what Core computes for every
   `case_*` function; THIS file builds `cases.go` together with `main.go` (the driver,
   which is not exported), runs it, and checks each pin against Go's own output.

Skipped, not passed, when no `go` is on PATH.
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
FIX = os.path.join(ROOT, "tests", "fixtures", "gointwidth")
SRC = os.path.join(FIX, "cases.go")
DRIVER = os.path.join(FIX, "main.go")
AST = os.path.join(FIX, "ast.json")
PROV = os.path.join(FIX, "provenance.json")
PINS = os.path.join(ROOT, "Autoform", "GoIntWidth.lean")
PROGRAM = os.path.join(ROOT, "Autoform", "GoIntWidthProgram.lean")
RENDER = os.path.join(ROOT, "cartographer", "render_lean.py")

# The one case Core refuses: `1 << n` with an untyped constant left operand takes its
# type from the context (here `int64`), which the exporter cannot see. Go: 1099511627776.
HOLES = {"case_untyped_const_shift": "hole op:int:untyped-constant-shift"}


def pinned_results() -> dict:
    text = open(PINS).read()
    pat = re.compile(r'/-- info: "([^"]*)" -/\s*\n#guard_msgs in #eval gRun "(case_\w+)"')
    return {m.group(2): m.group(1) for m in pat.finditer(text)}


def as_go(core: str) -> str:
    """A Core pin spelled as the Go program prints the same result."""
    if core.startswith("bool "):
        return core[5:]
    m = re.fullmatch(r"<exception panic: (.*)>", core)
    if m:
        return "panic: runtime error: " + m.group(1)
    return core


@pytest.mark.skipif(shutil.which("go") is None, reason="no go toolchain on PATH")
def test_every_case_is_pinned_and_agrees_with_go(tmp_path):
    exe = tmp_path / "gointwidth"
    subprocess.run(["go", "build", "-o", str(exe), SRC, DRIVER], check=True,
                   capture_output=True, text=True, cwd=tmp_path)
    r = subprocess.run([str(exe)], check=True, capture_output=True, text=True)
    got = dict(line.split(" ", 1) for line in r.stdout.splitlines() if line.startswith("case_"))
    declared = set(re.findall(r"^func (case_\w+)\(\)", open(SRC).read(), re.M))
    assert declared and set(got) == declared, "main.go must print every case_* function"
    pins = pinned_results()
    assert set(pins) == declared, (
        f"cases without a pin: {sorted(declared - set(pins))}; "
        f"pins without a case: {sorted(set(pins) - declared)}")
    for case, expected in got.items():
        if case in HOLES:
            assert pins[case] == HOLES[case]
        else:
            assert as_go(pins[case]) == expected, (
                f"{case}: Core pinned {pins[case]!r}, go gives {expected!r}")


def test_only_the_declared_cases_are_holes():
    assert {c for c, p in pinned_results().items() if p.startswith("hole ")} == set(HOLES)


def test_ast_was_exported_from_this_source():
    prov = json.load(open(PROV))
    assert prov["source_sha256"] == hashlib.sha256(open(SRC, "rb").read()).hexdigest(), (
        "cases.go changed since ast.json was exported; re-run the command in "
        "tests/fixtures/gointwidth/provenance.json")
    assert prov["ast_sha256"] == hashlib.sha256(open(AST, "rb").read()).hexdigest()


def test_ast_holes_are_exactly_the_declared_ones():
    labels = re.findall(r'"label":\s*"([^"]+)"', open(AST).read())
    assert labels == ["op:int:untyped-constant-shift"]


def test_ast_uses_typed_operators():
    ops = set(re.findall(r'"op":\s*"([^"]+)"', open(AST).read()))
    for op in ("*:g64", "*:g32", "+:g08", "-:w08", "-:w64", "<<:g32", ">>:g32", "&^:w08",
               "~:w08", "cast:i32", "cast:u8", "/:g64"):
        assert op in ops, op
    # No untyped integer arithmetic is left in the integer cases.
    for op in ("+", "-", "*", "/", "%", "<<", ">>"):
        assert op not in ops, f"untyped {op!r} survived in the Go export"


def test_program_is_the_render_of_the_ast(tmp_path):
    out = tmp_path / "GoIntWidthProgram.lean"
    r = subprocess.run([sys.executable, RENDER, AST, str(out), "GoIntWidth"],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    assert out.read_text() == open(PROGRAM).read(), (
        "Autoform/GoIntWidthProgram.lean is not the render of "
        "tests/fixtures/gointwidth/ast.json")
