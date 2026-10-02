"""C conformance test: comparison/logical results used as integers, against `cc`.

Same three-link chain as `test_pyscoping_cpython.py`:

1. `tests/fixtures/cboolint/cboolint_cases.c` is the source; `ast.json` is what
   `cartographer/export_ast.sc` produced from it (Joern 4.0.606 `c2cpg`), and
   `provenance.json` pins both digests.
2. `Autoform/CBoolIntProgram.lean` is `render_lean.py` of that AST (checked byte for byte).
3. `Autoform/CBoolInt.lean` pins, with `#guard_msgs`, what Core computes for every
   `case_*` function; THIS file compiles the C with `cc`, calls every case through
   ctypes and checks each pin against it.

A pin may be `bool true`/`bool false` where `cc` returns 1/0 only through the return
conversion `scripts/differential.py` applies (`c_return_conversion`): Core keeps
comparison results as `Val.bool` under `.cLike` and promotes them to 0/1 in every integer
context (Semantics.lean, `Dialect.promotesBool`); the conversion of the returned value to
the function's `int` return type is the one such context Core does not see. Every other
pin must be the exact integer, and a hole is a failure: none of these cases needs one.
"""
import ctypes
import hashlib
import json
import os
import re
import subprocess
import sys


ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FIX = os.path.join(ROOT, "tests", "fixtures", "cboolint")
SRC = os.path.join(FIX, "cboolint_cases.c")
AST = os.path.join(FIX, "ast.json")
PROV = os.path.join(FIX, "provenance.json")
PINS = os.path.join(ROOT, "Autoform", "CBoolInt.lean")
PROGRAM = os.path.join(ROOT, "Autoform", "CBoolIntProgram.lean")
RENDER = os.path.join(ROOT, "cartographer", "render_lean.py")


def cc_results(tmp_path) -> dict:
    lib = os.path.join(str(tmp_path), "libcboolint.so")
    subprocess.run(["cc", "-shared", "-fPIC", "-O0", "-o", lib, SRC], check=True)
    dll = ctypes.CDLL(lib)
    names = re.findall(r"^int (case_\w+)\(void\)", open(SRC).read(), re.M)
    assert names, "no case_* functions found in the fixture"
    out = {}
    for n in names:
        fn = getattr(dll, n)
        fn.restype, fn.argtypes = ctypes.c_int, []
        out[n] = fn()
    return out


def pinned_results() -> dict:
    text = open(PINS).read()
    pat = re.compile(r'/-- info: "([^"]*)" -/\s*\n#guard_msgs in #eval cRun "(case_\w+)"')
    return {m.group(2): m.group(1) for m in pat.finditer(text)}


def as_c_int(pin: str):
    """The integer a pinned Core result stands for under C's return conversion."""
    if pin == "bool true":
        return 1
    if pin == "bool false":
        return 0
    if re.fullmatch(r"-?\d+", pin):
        return int(pin)
    return None                      # a hole, an exception, anything else: no integer


def test_every_case_is_pinned_and_agrees_with_cc(tmp_path):
    cc = cc_results(tmp_path)
    pins = pinned_results()
    assert set(cc) == set(pins), (
        f"cases without a pin: {sorted(set(cc) - set(pins))}; "
        f"pins without a case: {sorted(set(pins) - set(cc))}")
    for case, expected in cc.items():
        got = as_c_int(pins[case])
        assert got == expected, f"{case}: Core pinned {pins[case]!r}, cc gives {expected}"


def test_return_conversion_is_the_only_bool_mapping(differential):
    # The harness and this test apply the same rule, and it is exactly 0/1: a Core
    # `bool` never matches any other integer.
    conv = differential.c_return_conversion
    assert conv(("val", ("bool", True))) == ("val", ("int", 1))
    assert conv(("val", ("bool", False))) == ("val", ("int", 0))
    assert conv(("val", ("int", 5))) == ("val", ("int", 5))
    assert conv(("hole", "x")) == ("hole", "x")


def test_ast_was_exported_from_this_source():
    prov = json.load(open(PROV))
    assert prov["source_sha256"] == hashlib.sha256(open(SRC, "rb").read()).hexdigest(), (
        "cboolint_cases.c changed since ast.json was exported; re-run the command in "
        "tests/fixtures/cboolint/provenance.json")
    assert prov["ast_sha256"] == hashlib.sha256(open(AST, "rb").read()).hexdigest()


def test_ast_is_hole_free():
    # A hole in the export would make the comparison above vacuous for that case.
    assert '"hole' not in open(AST).read()


def test_program_is_the_render_of_the_ast(tmp_path):
    out = tmp_path / "CBoolIntProgram.lean"
    r = subprocess.run([sys.executable, RENDER, AST, str(out), "CBoolInt"],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    assert out.read_text() == open(PROGRAM).read(), (
        "Autoform/CBoolIntProgram.lean is not the render of tests/fixtures/cboolint/ast.json")


def test_typed_arg_stays_in_range(differential):
    # The typed C leg must never hand a C function a value its parameter type cannot
    # hold: that would be a conversion on the C side the Lean side never sees.
    import random
    random.seed(1)
    for t in ({"bits": 8, "signed": False}, {"bits": 16, "signed": True},
              {"bits": 32, "signed": False}, {"bits": 64, "signed": True},
              {"bits": 64, "signed": False}, {"bits": 8, "signed": False, "bool": True}):
        lo, hi = differential.c_type_range(t)
        vals = [differential.c_typed_arg(t) for _ in range(2000)]
        assert all(lo <= v <= hi for v in vals), t
        if not t.get("bool"):
            assert hi in vals and lo in vals, t     # the boundaries are actually drawn
