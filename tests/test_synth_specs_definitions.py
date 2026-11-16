"""The identifier a synthesized theorem is about must be the one the renderer declared.

`render_lean.ident` cuts identifiers at 120 characters and the renderer resolves the
collisions that cut produces with a trailing prime. `synth_specs.py` used to re-derive the
identifier from the function name alone, which cannot see the prime: on CommonsLang3 the
4-argument `StringUtils.replaceIgnoreCase` and the 3-argument overload collide at 120
characters, the 4-argument candidate was bound to the 3-argument definition, and the law
was refuted on the function's own agreeing JVM observations (2026-10-22, the first oracle
run wide enough to compare that overload). `rendered_definitions` reads the module.
"""
import os

from conftest import SCRIPTS, load


def _synth(monkeypatch):
    # synth_specs imports differential, which re-executes the process under
    # PYTHONHASHSEED=0 at import unless told not to (see the `differential` fixture).
    monkeypatch.setenv("AUTOFORM_NO_REEXEC", "1")
    return load(os.path.join(SCRIPTS, "synth_specs.py"), "af_synth_specs_defs")


LONG = "org.example.StringUtils.replaceIgnoreCase:java.lang.String(" + ",".join(
    ["java.lang.String"] * 6) + "%s)"


def test_rendered_definitions_follow_the_renderer_not_the_name(tmp_path, monkeypatch):
    synth = _synth(monkeypatch)
    three, four = LONG % "", LONG % ",int"
    base = synth.lean_ident(three)
    assert synth.lean_ident(four) == base, "the fixture must collide at the 120-char cut"
    module = tmp_path / "Autoform" / "Generated" / "Fixture.lean"
    module.parent.mkdir(parents=True)
    module.write_text(
        "namespace Autoform.Generated.Fixture\n"
        f"def {base} : Func :=\n  {{ name := \"{three}\"\n    , params := [] }}\n\n"
        f"def {base}' : Func :=\n  {{ name := \"{four}\"\n    , params := [] }}\n\n"
        "def f_short : Func :=\n  { name := \"org.example.Short.f:int()\" }\n"
        "end Autoform.Generated.Fixture\n", encoding="utf-8")
    defs = synth.rendered_definitions(str(module))
    assert defs[three] == base
    assert defs[four] == base + "'", "the later definition carries the renderer's prime"
    assert defs["org.example.Short.f:int()"] == "f_short"
    # The call site falls back to the re-derived identifier only for an undeclared name.
    assert (defs.get("org.example.Missing.g:int()") or synth.lean_ident("org.example.Missing.g:int()")) == "f_org_example_Missing_g_int__"


def test_candidates_are_bound_to_the_declared_identifier(monkeypatch):
    synth = _synth(monkeypatch)
    three, four = LONG % "", LONG % ",int"
    base = synth.lean_ident(three)
    byname = {four: {"name": four, "body": {"k": "ret", "e": {"k": "lit", "v": ["int", 0]}}}}
    rec = {"name": four, "heap": [], "self": None, "args": [["str", ""]] * 7,
           "outcome": ["val", ["str", ""]], "globals": [], "origin": "random"}
    cands = synth.gen_candidates([four], byname, [rec], None, conformance_only=True,
                                 definitions={four: base + "'"})
    conform = [c for c in cands if c.family == "conform"]
    assert conform and conform[0].fdef == base + "'"
    assert ("lawConform C FUEL %s'" % base) == conform[0].law
    # Without the map the old behaviour -- and the defect -- is what you get.
    cands = synth.gen_candidates([four], byname, [rec], None, conformance_only=True)
    assert [c for c in cands if c.family == "conform"][0].fdef == base
