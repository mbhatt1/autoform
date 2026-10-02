"""CPython differential test for Python calling convention and scoping (STRATEGY.md §57).

Three links of one chain, each checked here or by the Lean build:

1. `tests/fixtures/pyscoping/pyscoping_cases.py` is the source. Its `ast.json` is what
   `cartographer/export_ast.sc` produced from it (Joern 4.0.606 `pysrc2cpg`), and
   `provenance.json` records the source digest the export was made from -- checked below,
   so editing the fixture without re-exporting fails here.
2. `Autoform/PyScopingProgram.lean` is `render_lean.py` of that AST -- re-rendered and
   compared byte-for-byte below.
3. `Autoform/PyScoping.lean` pins, with `#guard_msgs`, what Core computes for every
   `case_*` function of that program; `lake build Autoform.PyScoping` fails if Core
   disagrees with a pin. THIS file runs every case under CPython and checks each pin
   against what CPython returned.

A pin may differ from CPython only by being a HOLE named in `EXPECTED_HOLES`, with the
reason. A pin that is a different VALUE fails, always: that is a wrong translation, which
this project ranks below a hole (CONTRIBUTING.md rule 1).
"""
import hashlib
import importlib.util
import json
import os
import re
import struct
import subprocess
import sys

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FIX = os.path.join(ROOT, "tests", "fixtures", "pyscoping")
SRC = os.path.join(FIX, "pyscoping_cases.py")
AST = os.path.join(FIX, "ast.json")
PROV = os.path.join(FIX, "provenance.json")
PINS = os.path.join(ROOT, "Autoform", "PyScoping.lean")
PROGRAM = os.path.join(ROOT, "Autoform", "PyScopingProgram.lean")
RENDER = os.path.join(ROOT, "cartographer", "render_lean.py")

# Cases where Core holes and CPython computes a value. Each is a documented boundary,
# not a bug: the default is not a literal, Joern does not lower the default expression,
# and evaluating it per call instead of once at `def` time would be the wrong answer
# (for `acc=[]`, the classic aliasing bug in reverse).
EXPECTED_HOLES = {
    "case_mutable_default_needed": "param:default-nonliteral",
    "case_global_default_needed": "param:default-nonliteral",
}


def show(v) -> str:
    """CPython value -> the canonical text `PyScoping.showV` prints for the Core value."""
    if v is None:
        return "None"
    if v is True:
        return "True"
    if v is False:
        return "False"
    if isinstance(v, int):
        return str(v)
    if isinstance(v, float):
        return "float(bits=%d)" % struct.unpack("<Q", struct.pack("<d", v))[0]
    if isinstance(v, str):
        assert "'" not in v and "\\" not in v, "fixture strings must not need escaping"
        return "'" + v + "'"
    if isinstance(v, tuple):
        inner = ", ".join(show(x) for x in v)
        return "(" + inner + ("," if len(v) == 1 else "") + ")"
    if isinstance(v, list):
        return "[" + ", ".join(show(x) for x in v) + "]"
    if isinstance(v, dict):
        return "{" + ", ".join(show(k) + ": " + show(x) for k, x in v.items()) + "}"
    raise AssertionError(f"no canonical form for {type(v).__name__}")


def cpython_results() -> dict:
    spec = importlib.util.spec_from_file_location("pyscoping_cases", SRC)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    out = {}
    for name in sorted(n for n in dir(mod) if n.startswith("case_")):
        try:
            out[name] = show(getattr(mod, name)())
        except Exception as e:  # noqa: BLE001 -- the exception TYPE is the result
            out[name] = "raise " + type(e).__name__
    return out


def pinned_results() -> dict:
    text = open(PINS).read()
    pat = re.compile(r'/-- info: "((?:[^"\\]|\\.)*)" -/\s*\n#guard_msgs in #eval pyRun "(case_\w+)"')
    return {m.group(2): m.group(1).replace('\\"', '"').replace("\\\\", "\\")
            for m in pat.finditer(text)}


def test_every_case_is_pinned_and_agrees_with_cpython():
    py = cpython_results()
    pins = pinned_results()
    assert set(py) == set(pins), (
        f"cases without a pin: {sorted(set(py) - set(pins))}; "
        f"pins without a case: {sorted(set(pins) - set(py))}")
    for case, expected in py.items():
        got = pins[case]
        if case in EXPECTED_HOLES:
            assert got == "hole " + EXPECTED_HOLES[case], (case, got, expected)
        else:
            assert got == expected, f"{case}: Core pinned {got!r}, CPython gives {expected!r}"


def test_expected_holes_are_real_divergences():
    # An entry that CPython ALSO fails on, or that names a case that no longer exists, is
    # an excuse with nothing behind it.
    py = cpython_results()
    for case in EXPECTED_HOLES:
        assert case in py and not py[case].startswith("raise "), case


def test_ast_was_exported_from_this_source():
    prov = json.load(open(PROV))
    digest = hashlib.sha256(open(SRC, "rb").read()).hexdigest()
    assert prov["source_sha256"] == digest, (
        "pyscoping_cases.py changed since ast.json was exported; re-run the command in "
        "tests/fixtures/pyscoping/provenance.json")
    assert prov["ast_sha256"] == hashlib.sha256(open(AST, "rb").read()).hexdigest()


def test_program_is_the_render_of_the_ast(tmp_path):
    out = tmp_path / "PyScopingProgram.lean"
    r = subprocess.run([sys.executable, RENDER, AST, str(out), "PyScoping"],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    assert out.read_text() == open(PROGRAM).read(), (
        "Autoform/PyScopingProgram.lean is not the render of tests/fixtures/pyscoping/ast.json")


@pytest.mark.parametrize("label", sorted(set(EXPECTED_HOLES.values())))
def test_hole_labels_are_in_the_ast(label):
    # The runtime hole has to be a hole the ledger can count statically, or the gap is
    # invisible until someone happens to call the function.
    assert label in open(AST).read()
