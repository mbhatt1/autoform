"""The documentation is the claim, and a claim needs evidence that exists.

`scripts/check_docs.py` binds documented *numbers* to artifact fields. This file binds
documented *statements* to the theorem, `#guard` or test that backs them, so that a
"done" in README cannot outlive the thing that made it true, and a status line cannot
say "landed" about code that has been reverted.

Everything here is a read of the repository. Nothing is built or run.
"""
from __future__ import annotations

import re
from pathlib import Path

import pytest
from conftest import exporter_source

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    if rel == "cartographer/export_ast.sc":
        return exporter_source()
    return (ROOT / rel).read_text(encoding="utf-8")


def present(identifier: str, *rels: str) -> bool:
    """Does `identifier` occur verbatim in any of the named files?"""
    return any(identifier in read(r) for r in rels)


SEMANTICS = "Autoform/Lang/Core/Semantics.lean"
SYNTAX = "Autoform/Lang/Core/Syntax.lean"
STDLIB = "Autoform/Lang/Core/Stdlib.lean"
NUMERIC = "Autoform/Lang/Core/Numeric.lean"
EXPORTER = "cartographer/export_ast.sc"
T_SIGNATURES = "tests/test_python_signatures.py"
T_GAPS = "tests/test_production_gaps.py"
T_NUMERIC = "tests/test_source_numeric.py"


def not_yet_built_bullets() -> list[str]:
    """The four bullets of README's 'Not yet built' section, one string each."""
    text = read("README.md")
    section = text.split("## Not yet built", 1)[1].split("## Dependencies", 1)[0]
    bullets = re.findall(r"^\* \*\*(.+?)\*\*(.*?)(?=^\* \*\*|^\S|\Z)", section,
                         re.S | re.M)
    assert len(bullets) == 4, f"expected the four named gaps, found {len(bullets)}"
    return [head + body for head, body in bullets]


# Each README bullet, the phrase that marks it as a claim rather than a plan, and the
# evidence that must exist for the claim to be allowed to stand. A bullet that says
# "done" with none of its evidence present is the drift this file exists to catch.
CLAIMS = {
    "Mutable containers": [
        ("THE SWITCHOVER", [SEMANTICS]),           # the allocation site is marked
        ("aliasProg", [SEMANTICS]),                # aliasing checked against CPython
        ("execForRef", [SEMANTICS]),               # live iteration exists
        ("inductive Payload", [SYNTAX]),
    ],
    "Cross-scope writes": [
        ("cellProg", [SEMANTICS]),                 # Core can express a closure cell
        ("capturedBoxes", [EXPORTER]),             # the no-prologue set
        ("nonlocalDeclNames", [EXPORTER]),         # its own parser, not `global`'s
        ("TestNonlocalBoxing", [T_SIGNATURES]),    # the safety boundary is tested
    ],
    "Calling conventions": [
        ("inductive DefaultValue", [SYNTAX]),
        ("TestLiteralParameterDefaults", [T_GAPS]),
        ("TestFunctionReferenceDefaults", [T_SIGNATURES]),
        ("TestModuleAttributeDefaults", [T_SIGNATURES]),
        ("TestStaticMethodBinding", [T_SIGNATURES]),
    ],
    "Language-specific numeric behavior": [
        ("test_joern_native_numeric", [T_NUMERIC]),
        ("python_shiftCount_trap", [NUMERIC]),
        ("test_python_negative_shift_raises_valueerror_by_name", [T_NUMERIC]),
    ],
}

DONE_MARKERS = ("done", "no open divergence")


class TestReadmeNotYetBuilt:
    def test_every_named_gap_is_stated_as_a_measurement(self):
        for bullet in not_yet_built_bullets():
            head = bullet.split("—", 1)[0].split(" - ", 1)[0]
            assert any(m in bullet.lower() for m in DONE_MARKERS) or "remain" in bullet.lower(), (
                f"README bullet {head!r} neither claims a result nor says what remains")

    @pytest.mark.parametrize("item", sorted(CLAIMS))
    def test_a_done_claim_has_its_evidence(self, item):
        bullet = next(b for b in not_yet_built_bullets() if b.startswith(item))
        if not any(m in bullet.lower() for m in DONE_MARKERS):
            pytest.skip(f"{item} is not claimed as done")
        missing = [ident for ident, files in CLAIMS[item] if not present(ident, *files)]
        assert not missing, (
            f"README says {item!r} is done, but its evidence is gone: {missing}. "
            f"Either the code was reverted and the claim must go, or the identifier was "
            f"renamed and this table must follow it.")

    def test_the_hole_table_is_marked_as_a_snapshot_to_re_measure(self):
        """Other passes close labels concurrently; a count in prose is stale the day it
        is written. The table must say so and give the command, not pose as current."""
        section = read("README.md").split("## Not yet built", 1)[1]
        assert "re-measure" in section.lower(), (
            "README's hole table must be marked as a snapshot to re-measure")
        assert "lang_matrix.py" in section, (
            "README's hole table must name the command that reproduces it")


class TestStatusLinesMatchTheCode:
    def test_boxed_containers_status_agrees_with_semantics(self):
        """The design doc's status line and the interpreter must not disagree about
        whether container literals allocate. Both directions: a reverted switchover with
        a doc still saying 'landed' is the worse one."""
        status = read("docs/boxed-containers.md").split("\n\n", 2)[1].lower()
        landed_in_code = "THE SWITCHOVER" in read(SEMANTICS)
        landed_in_doc = "switchover" in status and "landed" in status
        assert landed_in_code == landed_in_doc, (
            f"boxed-containers status says landed={landed_in_doc}, "
            f"Semantics.lean says {landed_in_code}")

    def test_exception_producers_named_in_docs_exist(self):
        """docs/languages.md says every exception producer is pinned by a theorem and
        names them. If a name disappears the sentence becomes false."""
        doc = read("docs/languages.md")
        for thm, rel in [("makeException_excSafe", STDLIB), ("raiseValue_excSafe", STDLIB),
                         ("python_shiftCount_trap", NUMERIC)]:
            if thm in doc:
                assert present(thm, rel), f"docs name `{thm}` but {rel} no longer has it"

    def test_trust_chain_hole_row_is_bound_by_check_docs(self):
        """`scripts/check_docs.py` binds README's `N holes, all named` cell to the tracked
        AST. The row must keep the exact shape the regex expects, or the check goes quiet
        -- which is the failure mode check_docs itself warns about."""
        readme = read("README.md")
        assert re.search(r"\|\s*\d+ holes, all named\s*\|", readme), (
            "README trust-chain hole row changed shape; check_docs would stop checking it")
        checker = read("scripts/check_docs.py")
        assert "holes, all named" in checker
