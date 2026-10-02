"""CPython differential test for Python method resolution and name scoping (STRATEGY.md §59).

The same three-link chain as `tests/test_pyscoping_cpython.py`:

1. `tests/fixtures/pymro/pymro_cases.py` is the source; `ast.json` is what
   `cartographer/export_ast.sc` produced from it, and `provenance.json` records the digests
   -- checked below, so editing the fixture without re-exporting fails here.
2. `Autoform/PyMroProgram.lean` is `render_lean.py` of that AST, re-rendered and compared
   byte-for-byte below. It carries the class table (`pyClasses := some [...]`), which is
   what switches Core to Python's lookup rules.
3. `Autoform/PyMro.lean` pins, with `#guard_msgs`, what Core computes for every `case_*`
   function; `lake build Autoform.PyMro` fails if Core disagrees with a pin. THIS file runs
   every case under CPython and checks each pin against what CPython returned.

A pin may differ from CPython only by being a HOLE named in `EXPECTED_HOLES`, with the
reason. A pin that is a different VALUE fails, always (CONTRIBUTING.md rule 1).

Unlike the `pyscoping` holes, these are RUNTIME holes: whether a lookup reaches an external
base or an unknown class depends on the receiver's class, which the static ledger cannot
see. `test_hole_labels_are_runtime_mro_labels` pins that they are exactly the labels
`Ctx.lookupMethod`, `Ctx.unboundName` and `Expr.call` produce, so a new label cannot slip in
unexamined.
"""
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tests"))
from test_pyscoping_cpython import show  # noqa: E402  -- one canonical printer for both

FIX = os.path.join(ROOT, "tests", "fixtures", "pymro")
SRC = os.path.join(FIX, "pymro_cases.py")
AST = os.path.join(FIX, "ast.json")
PROV = os.path.join(FIX, "provenance.json")
PINS = os.path.join(ROOT, "Autoform", "PyMro.lean")
PROGRAM = os.path.join(ROOT, "Autoform", "PyMroProgram.lean")
RENDER = os.path.join(ROOT, "cartographer", "render_lean.py")

# Cases where Core holes. Each is a documented boundary of the class table, not a bug.
EXPECTED_HOLES = {
    # `fetch = get` in the class body: a class attribute, not a `def`. The function table
    # does not say what it holds, so lookup stops there.
    "case_class_attribute_alias": "mro:class-attribute:Shelf.fetch",
    # `Bag.get` is inherited from `collections.abc.Mapping`, outside the corpus.
    "case_external_base_method": "mro:external-base:collections.abc.Mapping.get",
    # `class Dynamic(make_base())`: a base the exporter cannot resolve statically.
    "case_unresolvable_base": "mro:unknown-class:Dynamic",
    # CPython raises AttributeError (caught, so the case returns a string); Core has no
    # model of `object`'s attributes and of `__getattr__`, so an absent method is a hole.
    "case_absent_method": "mcall:Store.nonexistent",
    # CPython raises NameError (caught). Core cannot tell an unbound name from a binding its
    # globals frame did not receive, so the honest answer is a hole -- where suffix
    # resolution used to call `Holder.orphan_fn`.
    "case_unbound_name_is_not_a_method": "call:orphan_fn",
}


def cpython_results() -> dict:
    spec = importlib.util.spec_from_file_location("pymro_cases", SRC)
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


def test_expected_holes_name_existing_cases():
    py = cpython_results()
    for case in EXPECTED_HOLES:
        assert case in py, case


def test_most_cases_are_values():
    # The point of the fixture is that the MRO rules COMPUTE: holes are the exception.
    pins = pinned_results()
    values = [c for c, v in pins.items() if not v.startswith("hole ")]
    assert len(values) >= 15, values


def test_hole_labels_are_runtime_mro_labels():
    for label in EXPECTED_HOLES.values():
        assert re.match(r"^(mro:(class-attribute|external-base|unknown-class):|"
                        r"mcall:[A-Za-z_]\w*\.|call:[A-Za-z_]\w*$)", label), label


def test_ast_was_exported_from_this_source():
    prov = json.load(open(PROV))
    digest = hashlib.sha256(open(SRC, "rb").read()).hexdigest()
    assert prov["source_sha256"] == digest, (
        "pymro_cases.py changed since ast.json was exported; re-run the command in "
        "tests/fixtures/pymro/provenance.json")
    assert prov["ast_sha256"] == hashlib.sha256(open(AST, "rb").read()).hexdigest()


def test_ast_records_the_class_table():
    funcs = json.load(open(AST))
    tables = [f["pyClasses"] for f in funcs if "pyClasses" in f]
    assert tables, "the export has no class table, so Core would use the legacy rules"
    table = {k: v for t in tables for k, v in t.items()}
    assert table["Bottom"]["bases"] == ["Left", "Right"]          # source order
    assert table["Bag"]["bases"] == ["<ext>collections.abc.Mapping"]
    assert table["Shelf"]["attrs"] == ["fetch"]                     # `make` is a staticmethod
    assert "Dynamic" not in table                                   # unresolvable base


def test_program_is_the_render_of_the_ast(tmp_path):
    out = tmp_path / "PyMroProgram.lean"
    r = subprocess.run([sys.executable, RENDER, AST, str(out), "PyMro"],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    assert out.read_text() == open(PROGRAM).read(), (
        "Autoform/PyMroProgram.lean is not the render of tests/fixtures/pymro/ast.json")


@pytest.mark.parametrize("cls,base", [("DefaultStore", "Store"), ("StepCounter", "Counter")])
def test_render_carries_bases(cls, base):
    text = open(PROGRAM).read()
    assert '{ name := "%s", bases := ["%s"]' % (cls, base) in text
