"""`scripts/scale_table.py` prints the coverage table in docs/scale.md from the ledgers.

The table it replaces was typed in from one run and three of its rows drifted 3-4x from
the `ledger-<M>.json` on disk without anything noticing, because only the cachetools row
was pinned. Two things must therefore hold of the generator, and this file holds them:

* a row is a pure function of its ledger -- counts, floored percentages, `closedByContract`
  beside the core and never summed into it, and the GOAL bar (>= 85 % hole-free, >= 60 %
  core) with the top `holesByLabel` entry named when the bar is missed;
* the rows have exactly the cell shape `scripts/check_docs.py` pins, so regenerating the
  table can never make a pin stop matching silently -- every scale.md pattern in
  `check_docs.CHECKS`/`OPTIONAL` is run against the printed table here and must capture
  the value it is bound to.

A corpus whose ledger is absent prints the words "ledger not on disk", not a number.
Nothing here runs Lean or any pipeline stage.
"""
from __future__ import annotations

import json
import os
import re

import pytest
from conftest import ROOT, SCRIPTS, load, run_script

SCRIPT = os.path.join(SCRIPTS, "scale_table.py")


@pytest.fixture(scope="module")
def st():
    return load(SCRIPT, "af_scale_table")


@pytest.fixture(scope="module")
def check_docs():
    return load(os.path.join(SCRIPTS, "check_docs.py"), "af_check_docs_for_scale_table")


HOLDS = {  # cachetools-shaped: 90 % hole-free, 70 % core -> the bar holds
    "module": "Cachetools", "functions": 100, "holeFree": 90, "verifiableCore": 70,
    "closedByTranslation": 70, "closedByContract": 3, "holes": 12, "nodes": 1000,
    "dynamicHoleRisk": 40,
    "holesByLabel": [{"label": "op:starredUnpack", "count": 7},
                     {"label": "control:TRY-finally-escaping", "count": 5}],
}
MISSES = {  # requests-shaped: 80 % hole-free, 45 % core -> misses both legs
    "module": "Requests", "functions": 200, "holeFree": 160, "verifiableCore": 90,
    "closedByTranslation": 90, "closedByContract": 1, "holes": 50, "nodes": 5000,
    "dynamicHoleRisk": 300,
    "holesByLabel": [{"label": "control:TRY-handler-type", "count": 13},
                     {"label": "op:raise-cause", "count": 9}],
}


def _repo(tmp_path, with_provenance=True):
    """A root holding two of the eight ledgers; the other six are absent on purpose."""
    d = str(tmp_path)
    json.dump(HOLDS, open(os.path.join(d, "ledger-Cachetools.json"), "w"))
    json.dump(MISSES, open(os.path.join(d, "ledger-Requests.json"), "w"))
    if with_provenance:
        os.makedirs(os.path.join(d, "provenance"))
        json.dump({"command": "scripts/reland_corpus.sh /tmp/c/requests-2.32.5-sdist Requests"},
                  open(os.path.join(d, "provenance", "ast-Requests.json.prov.json"), "w"))
    return d


EXPECTED_HOLDS = ("| `cachetools` (published) | 100 | 90 (90%) | 70 (70%) | 3 | 12 | holds |")
EXPECTED_MISSES = ("| `requests` 2.32.5 | 200 | 160 (80%) | 90 (45%) | 1 | 50 | "
                   "misses: hole-free 80% < 85%; core 45% < 60%; "
                   "top hole `control:TRY-handler-type` 13 |")


class TestRows:
    def test_two_ledgers_give_the_expected_rows_and_verdicts(self, st, tmp_path):
        out = st.render(_repo(tmp_path))
        lines = out.splitlines()
        assert lines[0].startswith("| repo | functions | hole-free |")
        assert lines[1].startswith("|---|")
        assert EXPECTED_HOLDS in lines
        assert EXPECTED_MISSES in lines

    def test_absent_ledgers_print_words_not_numbers(self, st, tmp_path):
        out = st.render(_repo(tmp_path))
        body = out.splitlines()[2:]
        assert len(body) == 8, "one row per GOAL corpus, present or not"
        absent = [l for l in body if "ledger not on disk" in l]
        assert len(absent) == 6
        for name in ("`sqlparse`", "`flask`", "`click`", "`rich`", "`django/`"):
            assert any(l.startswith(f"| {name} |") for l in absent), name
        # "jinja2" is the GOAL's "jinja": the ledger module is Jinja2 and README says jinja2.
        assert any(l.startswith("| `jinja2` |") for l in absent)
        for l in absent:
            assert not re.search(r"\|\s*\d+\s*\|", l), f"an absent ledger produced a figure: {l}"

    def test_rows_follow_the_goal_order(self, st, tmp_path):
        names = [l.split("|")[1].strip().split(" ")[0]
                 for l in st.render(_repo(tmp_path)).splitlines()[2:]]
        assert names == ["`cachetools`", "`sqlparse`", "`requests`", "`flask`", "`jinja2`",
                         "`click`", "`rich`", "`django/`"]

    def test_version_comes_from_provenance_or_is_omitted(self, st, tmp_path):
        out = st.render(_repo(tmp_path, with_provenance=False))
        assert "| `requests` | 200 |" in out, "no provenance record -> bare label"
        assert "2.32.5" not in out

    def test_percentages_are_floored_like_the_published_row(self, st):
        # 204/209 = 97.6 %: the published cachetools row has always said 97 %, and
        # check_docs' `(\d+%)` only reads integers.
        assert st.pct(204, 209) == 97
        assert st.pct(150, 209) == 71
        assert st.pct(0, 0) == 0


class TestBar:
    def test_holds_only_when_both_legs_hold(self, st):
        assert st.bar_verdict(HOLDS) == "holds"
        assert st.bar_verdict(dict(HOLDS, holeFree=84)).startswith("misses: hole-free 84% < 85%")
        assert st.bar_verdict(dict(HOLDS, closedByTranslation=59, verifiableCore=59)) \
            .startswith("misses: core 59% < 60%")

    def test_bar_uses_exact_fractions_not_floored_percent(self, st):
        # 85/100 is exactly the bar; 169/200 = 84.5 % floors to 84 and must miss.
        assert st.bar_verdict(dict(HOLDS, holeFree=85)) == "holds"
        assert st.bar_verdict(dict(MISSES, holeFree=169, closedByTranslation=120,
                                   verifiableCore=120)).startswith("misses: hole-free 84%")

    def test_a_miss_names_the_top_hole_label_and_count(self, st):
        v = st.bar_verdict(MISSES)
        assert v.endswith("top hole `control:TRY-handler-type` 13")

    def test_a_miss_without_labels_says_so(self, st):
        v = st.bar_verdict(dict(MISSES, holesByLabel=[]))
        assert v.endswith("no holes listed")
        v = st.bar_verdict({k: v for k, v in MISSES.items() if k != "holesByLabel"})
        assert v.endswith("no holes listed")

    def test_core_falls_back_to_verifiableCore_on_an_old_ledger(self, st):
        old = {k: v for k, v in HOLDS.items() if k != "closedByTranslation"}
        assert st.row("x", old) == "| x | 100 | 90 (90%) | 70 (70%) | 3 | 12 | holds |"

    def test_an_empty_population_misses_without_dividing_by_zero(self, st):
        assert st.bar_verdict({"functions": 0, "holeFree": 0, "closedByTranslation": 0}) \
            .startswith("misses: hole-free 0% < 85%; core 0% < 60%")


class TestCheckDocsShape:
    """The printed cells must be the cells check_docs.py pins, or a regenerated table could
    silently stop being checked (the failure check_docs itself warns about)."""

    def _scale_md_patterns(self, check_docs):
        rows = [(rx, art, key) for doc, rx, art, key, _ in check_docs.CHECKS
                if doc == "docs/scale.md"]
        rows += [(rx, art, derive) for doc, rx, art, derive, _ in check_docs.OPTIONAL
                 if doc == "docs/scale.md"]
        assert rows, "check_docs no longer pins docs/scale.md at all"
        return rows

    def test_every_scale_md_pin_matches_the_generated_table(self, st, check_docs, tmp_path):
        out = st.render(_repo(tmp_path))
        ledgers = {"ledger-Cachetools.json": HOLDS, "ledger-Requests.json": MISSES}
        checked = 0
        for rx, art, key in self._scale_md_patterns(check_docs):
            if art not in ledgers:
                # click/jinja2 pins: their rows print "ledger not on disk" here, so the
                # numeric pattern must NOT match -- an absent ledger must never bind.
                assert re.search(rx, out, re.S) is None, (rx, art)
                continue
            m = re.search(rx, out, re.S)
            assert m, f"check_docs pattern no longer matches the generated table: {rx}"
            want = key(ledgers[art]) if callable(key) else check_docs.dig(ledgers[art], key)
            assert int(m.group(1).replace(",", "")) == want, (rx, art)
            checked += 1
        assert checked >= 7, "functions, holeFree, core for cachetools and the four requests pins"

    def test_the_cachetools_label_is_the_pinned_one(self, st):
        assert st.label_for("cachetools", "7.1.7") == "`cachetools` (published)"


class TestCli:
    def test_prints_the_table_and_exits_zero(self, tmp_path):
        rc, out = run_script(SCRIPT, "--root", _repo(tmp_path))
        assert rc == 0, out
        assert EXPECTED_HOLDS in out and EXPECTED_MISSES in out
        assert out.count("ledger not on disk") == 6

    def test_an_empty_root_still_prints_eight_rows(self, tmp_path):
        rc, out = run_script(SCRIPT, "--root", str(tmp_path))
        assert rc == 0, out
        assert out.count("ledger not on disk") == 8

    def test_the_committed_table_is_the_generator_output_shape(self):
        """docs/scale.md's generated table must carry the generator's header verbatim: the
        rows are a snapshot (dated in the doc) but the shape is the script's."""
        doc = open(os.path.join(ROOT, "docs", "scale.md"), encoding="utf-8").read()
        st_mod = load(SCRIPT, "af_scale_table_doc")
        assert st_mod.HEADER in doc
        assert "scripts/scale_table.py" in doc
        assert "scripts/ledger_corpus.sh" in doc
