"""`scripts/sacm.py` consumes the ledger's `closedByContract` / `contractsUsed`
(docs/ledger-schema.md, "Closure by contract in E6").

A function whose only open callees are contracted standard-library calls is closed only
relative to an assumption about each callee. The case must say so: a narrowed claim G3.3
with one Assumption node per callee attached to it, never folded into G3.1 or the top goal.
"""
import json
from pathlib import Path

from conftest import SCRIPTS, load

AST = [
    dict(name="f", body=dict(k="ret", e=dict(k="lit", v=1))),
    dict(name="g", body=dict(k="ret", e=dict(k="call", f="strlen", args=[dict(k="lit", v="x")]))),
]
LEDGER = dict(module="Check", dialect="c-like", functions=2, nodes=4, holes=0, holeFree=2,
              verifiableCore=1, closedByTranslation=1, dynamicHoleRisk=0, holesByLabel=[])


def build(root: Path, ledger_extra: dict):
    root.mkdir(parents=True, exist_ok=True)
    (root / "ast-Check.json").write_text(json.dumps(AST))
    (root / "ledger-Check.json").write_text(json.dumps(dict(LEDGER, **ledger_extra)))
    sacm = load(str(Path(SCRIPTS) / "sacm.py"), "af_sacm_contracts")
    case, meta, _, _ = sacm.build_case("Check", str(root))
    return sacm, case, meta


CONTRACTS = dict(closedByContract=1,
                 contractsUsed=[dict(callee="strlen", sites=1), dict(callee="Math.max", sites=3)])


def test_contracted_callees_become_assumptions_of_a_narrowed_claim(tmp_path):
    _, case, meta = build(tmp_path, CONTRACTS)
    claims = {c["id"]: c for c in case.claims}
    g33 = claims["G3.3"]
    assert g33["status"] == "SUPPORTED" and g33["evidenceKind"] == "STATIC"
    assert g33["scope"]["functions"] == 1
    assert g33["scope"]["contractedCallees"] == ["strlen", "Math.max"]
    assert "CONDITIONAL" in g33["notes"]
    assumptions = {a["id"]: a for a in case.assumptions}
    assert assumptions["A.contract:strlen"]["occurrences"] == 1
    assert assumptions["A.contract:Math.max"]["occurrences"] == 3
    assert assumptions["A.contract:strlen"]["status"] == "ASSUMED"
    links = {(l["source"], l["target"], l["type"]) for l in case.links}
    assert ("A.contract:strlen", "G3.3", "SUPPORTS") in links
    assert ("A.contract:Math.max", "G3.3", "SUPPORTS") in links
    assert ("G3.3", "G3", "SUPPORTS") in links
    assert ("E6", "G3.3", "SUPPORTS") in links


def test_contract_assumptions_never_reach_the_core_claim_or_the_top_goal(tmp_path):
    _, case, meta = build(tmp_path, CONTRACTS)
    for link in case.links:
        if link["source"].startswith("A.contract:"):
            assert link["target"] == "G3.3", link
    claims = {c["id"]: c for c in case.claims}
    # The two closure counts sit side by side and are never summed.
    assert claims["G3.1"]["scope"]["functions"] == 1
    assert "1-function core" in claims["G3.1"]["description"]
    assert meta["counts"]["closedByContract"] == 1
    assert meta["counts"]["contractAssumptions"] == 2


def test_e6_carries_the_ledger_fields_verbatim(tmp_path):
    _, case, _ = build(tmp_path, CONTRACTS)
    e6 = next(e for e in case.evidence if e["id"] == "E6")
    assert e6["value"]["closedByContract"] == 1
    assert e6["value"]["contractsUsed"] == CONTRACTS["contractsUsed"]
    assert e6["value"]["verifiableCore"] == 1


def test_consuming_contracts_changes_no_other_status(tmp_path):
    _, plain, plain_meta = build(tmp_path / "plain", {})
    _, with_c, with_meta = build(tmp_path / "contracts", CONTRACTS)
    before = {c["id"]: c["status"] for c in plain.claims}
    after = {c["id"]: c["status"] for c in with_c.claims}
    assert set(after) - set(before) == {"G3.3"}
    assert all(after[k] == before[k] for k in before)
    assert plain_meta["topStatus"] == with_meta["topStatus"]
    assert plain_meta["subClaimStatus"] == with_meta["subClaimStatus"]


def test_ledger_without_contract_fields_is_unchanged(tmp_path):
    _, case, meta = build(tmp_path, {})
    assert "G3.3" not in {c["id"] for c in case.claims}
    assert not any(a["id"].startswith("A.contract:") for a in case.assumptions)
    assert meta["counts"]["closedByContract"] == 0
    assert meta["counts"]["contractAssumptions"] == 0
    e6 = next(e for e in case.evidence if e["id"] == "E6")
    assert e6["value"]["closedByContract"] is None


def test_used_contracts_that_close_nothing_emit_no_claim(tmp_path):
    _, case, meta = build(tmp_path, dict(closedByContract=0,
                                         contractsUsed=[dict(callee="strlen", sites=2)]))
    assert "G3.3" not in {c["id"] for c in case.claims}
    assert not any(a["id"].startswith("A.contract:") for a in case.assumptions)
    assert meta["counts"]["contractAssumptions"] == 0


def test_closure_by_contract_without_named_callees_is_not_earned(tmp_path):
    _, case, _ = build(tmp_path, dict(closedByContract=2, contractsUsed=[]))
    claims = {c["id"]: c for c in case.claims}
    assert claims["G3.3"]["status"] == "UNSUPPORTED"
    assert not any(a["id"].startswith("A.contract:") for a in case.assumptions)
    links = {(l["source"], l["target"], l["type"]) for l in case.links}
    assert ("E6", "G3.3", "COUNTERS") in links


def test_off_subject_ledger_contributes_no_contract_assumptions(tmp_path):
    _, case, meta = build(tmp_path, dict(CONTRACTS, module="Other"))
    assert "G3.3" not in {c["id"] for c in case.claims}
    assert meta["counts"]["contractAssumptions"] == 0


def test_markdown_and_sacm_json_list_the_contract_nodes(tmp_path):
    sacm, case, meta = build(tmp_path, CONTRACTS)
    md = sacm.render_markdown(case, meta)
    assert "G3.3" in md and "`A.contract:strlen`" in md and "Closed by contract: **1**" in md
    doc = sacm.to_sacm(case, meta)
    ids = {a["id"] for a in doc["argumentPackage"]["assumptions"]}
    assert {"A.contract:strlen", "A.contract:Math.max"} <= ids
    assert doc["summary"]["counts"]["closedByContract"] == 1
