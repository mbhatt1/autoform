"""`scripts/lang_matrix.py` keeps its own copy of the extension -> dialect table (it
measures the pipeline, so it must not import from it). A copy that is not checked drifts:
it did, silently, until this test. Likewise `scripts/core_oracle.py` writes Lean source
that must open the generated module's own namespace, or `program` does not resolve and
every probe fails to elaborate."""
import importlib.util
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _load(rel, name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def test_lang_matrix_dialects_match_the_renderer():
    renderer = _load("cartographer/render_lean.py", "render_lean_for_matrix_test")
    matrix = _load("scripts/lang_matrix.py", "lang_matrix_under_test")
    expected = {ext: d.lstrip(".") for ext, d in renderer.DIALECT.items()}
    assert matrix.DIALECT == expected, (
        "scripts/lang_matrix.py DIALECT drifted from cartographer/render_lean.py DIALECT: "
        "differing keys %s" % sorted(
            k for k in set(expected) | set(matrix.DIALECT)
            if expected.get(k) != matrix.DIALECT.get(k)))


def test_core_oracle_lean_probes_open_the_generated_namespace():
    src = open(os.path.join(ROOT, "scripts", "core_oracle.py")).read()
    opens = [l for l in src.splitlines()
             if l.startswith("open Autoform.Core Autoform.Generated")]
    imports = [l for l in src.splitlines()
               if "import Autoform.Generated.{mod}" in l]
    assert len(opens) >= 2 and len(imports) >= 2, (
        "expected the CORE_PROBE and HEADER Lean templates, each importing and "
        "opening the generated module")
    for l in opens:
        assert l == "open Autoform.Core Autoform.Generated.{mod}", (
            "a Lean probe must open Autoform.Generated.{mod}, where `program` lives; "
            "opening only `Autoform.Generated` leaves `program` unresolved: %r" % l)
