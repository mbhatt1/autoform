"""scripts/mutate.py --rank-survivors / --rank-existing: ranking survivors by difference rate.

The Lean side is stubbed (a fake `run_lean` answering in the harness's output format); the
harness text, the parsing, the ranking, the never-silent handling and the report fields are
what is under test. A real run is recorded in docs/trust-model.md.
"""
from __future__ import annotations

import json
import sys

import pytest

TINY = """\
import Autoform.Lang.Core.Observation
namespace Autoform.Generated.Tiny

/-- first -/
def f_one : Func :=
  { name := "m:one"
  , params := ["x"]
  , body := (.seq
            (.expr (.lit (.str "doc")))
            (.ret (.name "x"))) }

/-- second -/
def f_two : Func :=
  { name := "m:two"
  , params := ["x"]
  , body := (.ret (.name "x")) }

end Autoform.Generated.Tiny
"""


@pytest.fixture()
def vr(mutate):
    return sys.modules["vacuity_rank"]


def case(x):
    return {"name": "m:one", "heap": [], "self": None, "args": [["int", x]]}


def test_domain_loading_dedupes_and_accepts_conformance_shape(tmp_path, vr):
    f = tmp_path / "c.json"
    f.write_text(json.dumps({"runtime_cases": [case(1), case(1), case(2),
                                               dict(case(3), name="m:two")]}))
    domains, sources = vr.load_domains([str(f)])
    assert [len(domains[n]) for n in ("m:one", "m:two")] == [2, 1]
    assert sources == [{"file": "c.json", "cases": 4}]
    bad = tmp_path / "b.json"
    bad.write_text(json.dumps({"nothing": []}))
    with pytest.raises(ValueError):
        vr.load_domains([str(bad)])


def test_decl_text_drops_next_doc_comment_and_renames(tmp_path, mutate, vr):
    lines = TINY.splitlines(keepends=True)
    decls = mutate.parse_decls(lines)
    one = next(d for d in decls if d.name == "f_one")
    text = vr.decl_text(lines, one)
    assert "second" not in text and text.rstrip().endswith("}")
    ln = next(i for i, l in enumerate(lines, 1) if '"doc"' in l)
    mut = vr.rename_def(vr.decl_text(lines, one, ln, "            .skip\n"), "f_one")
    assert "private def mutantUnderTest" in mut and ".skip" in mut and "doc" not in mut
    assert vr.func_name(text) == "m:one"


def test_harness_runs_both_sides_on_the_same_cases(vr):
    src = vr.harness("Autoform.Generated.Tiny", 77, False, "f_one", "private def mutantUnderTest : Func := x",
                     [case(5), dict(case(0), self=["ref", 0], heap=[["C", [["a", ["int", 1]]]]])])
    assert src.count("runWith f_one c") == 1 and "runWith mutantUnderTest c" in src
    assert "Val.int (5)" in src and "some (Val.ref (base + 0))" in src and '"a", Val.int (1)' in src
    assert "applyFunc dctx 77" in src and "([] : List Func)" in src


def test_parse_output_marks_holes_and_missing_answers(vr):
    out = "@@vac@@0@@VV@@same\n@@vac@@1@@VV@@diff\n@@vac@@2@@HV@@same\nnoise\n"
    assert vr.parse_output(out, 4) == {0: "same", 1: "diff", 2: "hole"}


def fake(answers):
    def run(root, source, timeout, env):
        n = source.count("{ slf :=")
        return "\n".join(f"@@vac@@{i}@@VV@@{answers(i)}" for i in range(n)), None
    return run


def test_estimate_rate_cap_and_unestimable_reasons(vr):
    pool = {"m:one": [case(i) for i in range(10)]}
    r = vr.estimate("/", "Autoform.Generated.Tiny", 5, False, "f_one", "x", "m:one", pool, "D",
                    4, 9, {}, 1, runner=fake(lambda i: "diff" if i == 0 else "same"))
    assert r["sample"]["run"] == 4 and r["sample"]["available"] == 10 and r["sample"]["cap"] == 4
    assert r["difference_rate"] == pytest.approx(0.25) and r["vacuity"] == "estimated"
    z = vr.estimate("/", "M", 5, False, "f_one", "x", "m:one", pool, "D", 4, 9, {}, 1,
                    runner=fake(lambda i: "same"))
    assert z["difference_rate"] == 0 and z["vacuity"] == "equivalent-looking"
    none = vr.estimate("/", "M", 5, False, "f_one", "x", "m:absent", pool, "D", 4, 9, {}, 1)
    assert none["difference_rate"] is None and "no case" in none["reason"]
    to = vr.estimate("/", "M", 5, False, "f_one", "x", "m:one", pool, "D", 4, 9, {}, 1,
                     runner=lambda *a: (None, "timeout after 9s"))
    assert to["difference_rate"] is None and "timeout" in to["reason"]
    unans = vr.estimate("/", "M", 5, False, "f_one", "x", "m:one", pool, "D", 4, 9, {}, 1,
                        runner=lambda *a: ("error: boom", None))
    assert unans["difference_rate"] is None and "boom" in unans["reason"]


def test_rank_orders_lowest_first_with_ties_and_unestimable_last(vr):
    items = [{"difference_rate": 0.5}, {"difference_rate": None}, {"difference_rate": 0.0},
             {"difference_rate": 0.0}]
    ordered = vr.rank(items)
    assert [i["difference_rate"] for i in ordered] == [0.0, 0.0, 0.5, None]
    assert [i["rank"] for i in ordered] == [1, 1, 3, None]


def test_rank_existing_adds_fields_and_changes_no_verdict(tmp_path, monkeypatch, mutate, vr):
    (tmp_path / "lakefile.toml").write_text("")
    gen = tmp_path / "Autoform" / "Generated"
    gen.mkdir(parents=True)
    src = gen / "Tiny.lean"
    src.write_text(TINY)
    doc_line = next(i for i, l in enumerate(TINY.splitlines(), 1) if '"doc"' in l)
    two_line = next(i for i, l in enumerate(TINY.splitlines(), 1) if "body := (.ret" in l)
    sv_one = {"op": "ast-seq-delete", "line": doc_line, "decl": "f_one",
              "before": '            (.expr (.lit (.str "doc")))', "after": "            .skip"}
    sv_two = {"op": "x", "line": two_line, "decl": "f_two", "before": "  , body := (.ret (.name \"x\")) }",
              "after": "  , body := (.ret (.lit .unit)) }"}
    stale = {"op": "x", "line": 5, "decl": "f_one", "before": "not the line", "after": "y"}
    verdict = {"T1": "survived"}
    report = {"theorems": {
        "T1": {"survivors": [sv_one, sv_two, stale], "verdict": "WEAK", "score": 0.5},
        "T2": {"survivors": [sv_one], "verdict": "WEAK", "score": 0.5},
        "T3": {"survivors": [], "verdict": "UNTESTED", "score": 0.0}},
        "mutants": [dict(sv_one, verdict=verdict), dict(sv_two, verdict={"T1": "killed"})]}
    prior = tmp_path / "mutation.json"
    prior.write_text(json.dumps(report))
    before = json.loads(prior.read_text())
    dom = tmp_path / "d.json"
    # m:one differs on 1 of 4 cases; m:two has no case at all
    dom.write_text(json.dumps({"cases": [case(i) for i in range(4)]}))
    monkeypatch.setattr(vr, "run_lean", fake(lambda i: "diff" if i == 0 else "same"))
    monkeypatch.setattr(mutate, "lake_env", lambda: {})
    out = tmp_path / "ranked.json"
    argv = ["mutate.py", str(src), "Autoform.Generated.Tiny", "--rank-existing", str(prior),
            "--rank-domain", str(dom), "--json", str(out), "--rank-max-samples", "8"]
    monkeypatch.setattr(sys, "argv", argv)
    assert mutate.main() == 0
    got = json.loads(out.read_text())
    assert json.loads(prior.read_text()) == before          # the finished report is untouched
    sv = got["theorems"]["T1"]["survivors"][0]
    assert sv["difference_rate"] == pytest.approx(0.25) and sv["rank"] == 1
    assert sv["sample"]["cap"] == 8 and "d.json" in sv["domain"]
    assert got["theorems"]["T2"]["survivors"][0]["difference_rate"] == pytest.approx(0.25)
    assert got["mutants"][0]["difference_rate"] == pytest.approx(0.25)
    assert "difference_rate" not in got["mutants"][1]       # killed: not a survivor
    ranking = got["survivor_ranking"]
    names = {s["decl"]: s for s in ranking["survivors"] if s["line"] != 5}
    assert names["f_one"]["theorems"] == ["T1", "T2"]
    assert names["f_two"]["difference_rate"] is None and "no case" in names["f_two"]["reason"]
    stale_item = [s for s in ranking["survivors"] if s["line"] == 5][0]
    assert "stale" in stale_item["reason"]
    assert ranking["untested_theorems"][0]["theorem"] == "T3"
    for t in got["theorems"]:                               # no verdict or score moved
        for k in ("verdict", "score"):
            assert got["theorems"][t][k] == before["theorems"][t][k]


def test_rank_existing_refuses_to_overwrite_and_needs_a_domain(tmp_path, monkeypatch, mutate):
    f = tmp_path / "mutation.json"
    f.write_text("{}")
    (tmp_path / "x.lean").write_text("def a := 1\n")
    base = ["mutate.py", str(tmp_path / "x.lean"), "M", "--rank-existing", str(f)]
    monkeypatch.setattr(sys, "argv", base)
    with pytest.raises(SystemExit):
        mutate.main()
    dom = tmp_path / "d.json"
    dom.write_text("[]")
    monkeypatch.setattr(sys, "argv", base + ["--rank-domain", str(dom), "--json", str(f)])
    with pytest.raises(SystemExit):
        mutate.main()
