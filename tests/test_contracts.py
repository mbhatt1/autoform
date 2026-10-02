"""Contracts at holes: the assurance case must keep conditional results apart.

`docs/contracts.md`. A function with holes can be proved correct *relative to* named
contracts on those holes. The failure this file guards against is the quiet one: a
conditional result read as an unconditional one, either because the assurance case
folds it into the verifiable core, drops the assumption it rests on, or counts a theorem
about a different (historical) program as evidence about this module.
"""
from __future__ import annotations

import json
import os
import re

import pytest

from conftest import ROOT, load

MOD = "Toy"
PROG = f"Autoform.Generated.{MOD}.program"
F_OK = "toy.py:<module>.C.delete"        # holed, call-closed, has a proved contract
F_COND = "toy.py:<module>.C.pop"         # holed, call-closed, nothing proved
F_PURE = "toy.py:<module>.C.size"        # hole-free


def _ast():
    hole_s = {"k": "holeS", "label": "op:delete-index"}
    return [
        {"name": F_OK, "body": {"k": "seq", "a": hole_s, "b": {"k": "skip"}}},
        {"name": F_COND, "body": {"k": "seq", "a": dict(hole_s), "b": {"k": "skip"}}},
        {"name": F_PURE, "body": {"k": "skip"}},
    ]


def _ledger():
    return {
        "module": MOD, "dialect": "python", "functions": 3, "nodes": 7, "holes": 2,
        "holeFree": 1, "verifiableCore": 1, "dynamicHoleRisk": 0,
        "conditionallyVerifiable": 2, "conditionalAssumptions": 2,
        "holeAssumptions": [
            {"id": f"H:{F_OK}#0:op:delete-index", "function": F_OK,
             "label": "op:delete-index", "kind": "stmt", "conditionallyVerifiable": True},
            {"id": f"H:{F_COND}#0:op:delete-index", "function": F_COND,
             "label": "op:delete-index", "kind": "stmt", "conditionallyVerifiable": True},
        ],
        "holesByLabel": [{"label": "op:delete-index", "count": 2}],
    }


def _rel(site):
    return [{"label": "op:delete-index", "site": site, "kind": "stmt",
             "statement": "completes or raises; no attribute writes", "fuelBound": 1}]


def _contracts(extra=()):
    ths = [
        {"theorem": "T.delete_under", "relativeTo": _rel(F_OK), "satisfiable": True,
         "satisfiabilityProof": "T.sat", "program": PROG, "function": F_OK},
        # About a historical slice, not this module: must not count.
        {"theorem": "T.historical", "relativeTo": _rel(F_OK), "satisfiable": True,
         "satisfiabilityProof": "T.sat", "program": "T.someSlice", "function": F_OK},
    ]
    ths.extend(extra)
    return {"module": MOD, "theorems": ths}


@pytest.fixture(scope="module")
def sacm():
    return load(os.path.join(ROOT, "scripts", "sacm.py"), "af_sacm_contracts")


def _case(sacm, tmp_path, contracts):
    (tmp_path / f"ast-{MOD}.json").write_text(json.dumps(_ast()))
    (tmp_path / f"ledger-{MOD}.json").write_text(json.dumps(_ledger()))
    (tmp_path / f"contracts-{MOD}.json").write_text(json.dumps(contracts))
    c, meta, _, _ = sacm.build_case(MOD, str(tmp_path))
    return c, meta


def test_conditional_numbers_are_separate_from_the_core(sacm, tmp_path):
    c, meta = _case(sacm, tmp_path, _contracts())
    cnt = meta["counts"]
    # The unconditional figures are untouched by the conditional ones.
    assert cnt["holeFree"] == 1
    core = next(n for n in c.claims if n["id"] == "G3.1")
    assert core["scope"]["functions"] == 1
    # The conditional ones are present, labelled, and distinct.
    assert cnt["conditionallyVerifiable"] == 2
    assert cnt["conditionalAssumptions"] == 2
    g33 = next(n for n in c.claims if n["id"] == "G3.3")
    assert "CONDITIONAL" in g33["description"]
    # G3.3 never SUPPORTS the top claim or the coverage claim.
    sup = {(l["source"], l["target"]) for l in c.links if l["type"] == "SUPPORTS"}
    assert ("G3.3", "G1") not in sup and ("G3.3", "G3") not in sup
    md = sacm.render_markdown(c, meta)
    assert "**Conditionally** verifiable" in md
    assert "**Conditionally verified**" in md


def test_conditionally_verified_counts_only_on_subject_satisfiable(sacm, tmp_path):
    unsat = {"theorem": "T.vacuous", "relativeTo": _rel(F_COND), "satisfiable": False,
             "satisfiabilityProof": None, "program": PROG, "function": F_COND}
    c, meta = _case(sacm, tmp_path, _contracts([unsat]))
    # Only T.delete_under counts: T.historical is about another program and
    # T.vacuous has no satisfiability proof (refinesUnder_of_unsatisfiable).
    assert meta["counts"]["conditionallyVerified"] == 1
    assert meta["counts"]["conditionallyVerifiedFunctions"] == [F_OK]
    vac = next(n for n in c.claims if n["id"] == "G.CONTRACT.vacuous")
    assert vac["status"] == sacm.DEFEATED
    hist = next(n for n in c.claims if n["id"] == "G.CONTRACT.historical")
    assert "NOT about the current" in hist["description"]


def test_every_hole_occurrence_is_a_named_assumption(sacm, tmp_path):
    c, _ = _case(sacm, tmp_path, _contracts())
    ids = {a["id"] for a in c.assumptions}
    for ha in _ledger()["holeAssumptions"]:
        assert ha["id"] in ids, f"hole occurrence {ha['id']} silently trusted"


def test_contract_assumption_names_the_occurrence_it_assumes(sacm, tmp_path):
    c, _ = _case(sacm, tmp_path, _contracts())
    node = next(a for a in c.assumptions if a.get("contractOf") == "T.delete_under")
    assert node["holeAssumptions"] == [f"H:{F_OK}#0:op:delete-index"]
    # Attached to the theorem's own claim, never to the top goal.
    targets = {l["target"] for l in c.links if l["source"] == node["id"]}
    assert targets == {"G.CONTRACT.delete_under"}
    # The other occurrence of the same label is NOT named by this theorem.
    assert f"H:{F_COND}#0:op:delete-index" not in node["holeAssumptions"]


@pytest.mark.parametrize("path", ["Autoform/Contracts.lean", "Autoform/HoleContracts.lean"])
def test_no_hole_contract_is_an_axiom(path):
    """Contracts are hypotheses (`UnderS`, `RefinesUnder`), never axioms: an axiom would
    make a conditional result indistinguishable from an unconditional one in the audit."""
    src = open(os.path.join(ROOT, path)).read()
    code = re.sub(r"/-.*?-/", "", src, flags=re.S)
    code = re.sub(r"--[^\n]*", "", code)
    assert not re.search(r"^\s*(private\s+|noncomputable\s+)*axiom\s", code, re.M), path
    assert not re.search(r"\bsorry\b", code), path
    assert not re.search(r"\bnative_decide\b", code), path


def test_ledger_names_every_hole_when_present():
    """`Func.holeSites_labels` proves the inventory equals `Func.holes`; this checks the
    emitted artifact agrees (it once missed the holes in parameter defaults)."""
    path = os.path.join(ROOT, "ledger-Cachetools.json")
    if not os.path.exists(path):
        pytest.skip("ledger-Cachetools.json not generated (scripts/ledger.lean.tmpl)")
    led = json.load(open(path))
    if "holeAssumptions" not in led:
        pytest.skip("ledger predates per-hole assumptions")
    assert len(led["holeAssumptions"]) == led["holes"]
    ids = [h["id"] for h in led["holeAssumptions"]]
    assert len(set(ids)) == len(ids), "hole assumption names must be unique"


def test_emitter_reads_the_combined_registry():
    """`emit_contracts.py` must render the registry that includes statement-hole
    records; rendering only `Contracts.Demo.contractRecords` would silently drop them."""
    src = open(os.path.join(ROOT, "scripts", "emit_contracts.py")).read()
    assert "Autoform.HoleContracts.Demo.allContractRecordsJson" in src
