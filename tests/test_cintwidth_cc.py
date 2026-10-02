"""C conformance test: width-typed integer arithmetic (item O), against `cc`.

The three-link chain of `test_cboolint_cc.py`:

1. `tests/fixtures/cintwidth/cintwidth_cases.c` is the source; `ast.json` is what
   `cartographer/export_ast.sc` produced from it (Joern 4.0.606 `c2cpg`, data model
   `lp64`), and `provenance.json` pins both digests.
2. `Autoform/CIntWidthProgram.lean` is `render_lean.py` of that AST (checked byte for byte).
3. `Autoform/CIntWidth.lean` pins, with `#guard_msgs`, what Core computes for every
   `case_*` function; THIS file compiles the C with `cc -O0 -fwrapv`, calls every case
   through ctypes at its declared 64-bit return type, and checks each pin against it.

`-fwrapv` because `case_int_mul_wraps` overflows a signed `int`, which ISO C leaves
undefined; wrapping is the policy Core is configured with (`Dialect.toNumConfig .cLike`).
Every pin must be the exact integer; a hole is a failure.
"""
import ctypes
import hashlib
import json
import os
import re
import subprocess
import sys

import pytest


ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FIX = os.path.join(ROOT, "tests", "fixtures", "cintwidth")
SRC = os.path.join(FIX, "cintwidth_cases.c")
AST = os.path.join(FIX, "ast.json")
PROV = os.path.join(FIX, "provenance.json")
PINS = os.path.join(ROOT, "Autoform", "CIntWidth.lean")
PROGRAM = os.path.join(ROOT, "Autoform", "CIntWidthProgram.lean")
RENDER = os.path.join(ROOT, "cartographer", "render_lean.py")

SIG = re.compile(r"^(long long|unsigned long long) (case_\w+)\(void\)", re.M)


def cc_results(tmp_path) -> dict:
    lib = os.path.join(str(tmp_path), "libcintwidth.so")
    subprocess.run(["cc", "-shared", "-fPIC", "-O0", "-fwrapv", "-o", lib, SRC], check=True)
    dll = ctypes.CDLL(lib)
    sigs = SIG.findall(open(SRC).read())
    assert sigs, "no case_* functions found in the fixture"
    out = {}
    for ret, name in sigs:
        fn = getattr(dll, name)
        fn.restype = ctypes.c_ulonglong if ret.startswith("unsigned") else ctypes.c_longlong
        fn.argtypes = []
        out[name] = fn()
    return out


def pinned_results() -> dict:
    text = open(PINS).read()
    pat = re.compile(r'/-- info: "([^"]*)" -/\s*\n#guard_msgs in #eval cRun "(case_\w+)"')
    return {m.group(2): m.group(1) for m in pat.finditer(text)}


def test_every_case_is_pinned_and_agrees_with_cc(tmp_path):
    cc = cc_results(tmp_path)
    pins = pinned_results()
    assert set(cc) == set(pins), (
        f"cases without a pin: {sorted(set(cc) - set(pins))}; "
        f"pins without a case: {sorted(set(pins) - set(cc))}")
    for case, expected in cc.items():
        assert re.fullmatch(r"-?\d+", pins[case]), f"{case}: Core pinned {pins[case]!r}"
        assert int(pins[case]) == expected, f"{case}: Core pinned {pins[case]!r}, cc gives {expected}"


def test_ast_was_exported_from_this_source():
    prov = json.load(open(PROV))
    assert prov["source_sha256"] == hashlib.sha256(open(SRC, "rb").read()).hexdigest(), (
        "cintwidth_cases.c changed since ast.json was exported; re-run the command in "
        "tests/fixtures/cintwidth/provenance.json")
    assert prov["ast_sha256"] == hashlib.sha256(open(AST, "rb").read()).hexdigest()


def test_ast_is_hole_free():
    assert '"hole' not in open(AST).read()


def test_ast_uses_typed_operators():
    # The point of the fixture: 64-bit and unsigned operations are named as such. An
    # export that fell back to the untyped (32-bit) operators would make the pins above
    # agree with nothing.
    ops = set(re.findall(r'"op":\s*"([^"]+)"', open(AST).read()))
    for op in ("*:i64", "<<:i64", ">>:u64", "<:u32", "/:u32", "*:u64", "cast:u8"):
        assert op in ops, op


def test_program_is_the_render_of_the_ast(tmp_path):
    out = tmp_path / "CIntWidthProgram.lean"
    r = subprocess.run([sys.executable, RENDER, AST, str(out), "CIntWidth"],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    assert out.read_text() == open(PROGRAM).read(), (
        "Autoform/CIntWidthProgram.lean is not the render of tests/fixtures/cintwidth/ast.json")
