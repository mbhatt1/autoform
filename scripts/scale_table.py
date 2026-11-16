#!/usr/bin/env python3
"""scale_table.py — the coverage table in docs/scale.md, printed from the ledgers.

docs/GOAL-arbitrary-codebases.md (milestone 7) asks for the eight-row scale table to be
"regenerated from the ledgers only". It was not: the table in docs/scale.md was typed in
from a 2026-10 run and three of its rows (requests, click, jinja) disagreed with the
`ledger-<M>.json` on disk by 3-4x in every column, with only the cachetools row pinned by
`scripts/check_docs.py`. This script is the generator, so the table has one source.

For each of the eight scale corpora it reads `ledger-<Module>.json` from the repository
root — a gitignored run product written by `scripts/ledger_corpus.sh <src> <Module>` (or
by `scripts/reland_corpus.sh`) — and prints one markdown row: functions, hole-free
(count and %), verifiable core (`closedByTranslation`, count and %), `closedByContract`,
holes, and the GOAL bar (>= 85 % hole-free, >= 60 % in the core). A row that misses the
bar names the top hole label and its count from `holesByLabel`, as the milestone's exit
criterion requires. A corpus whose ledger is absent prints "ledger not on disk" rather
than a stale number.

The cells are shaped exactly as `check_docs.py` pins them (`| <label> | N | N (P%) |
N (P%) |`); percentages are floored, as the published cachetools row always was. Nothing
here is timestamped: the caller dates the snapshot in the document.

Usage:  scripts/scale_table.py [--root .]
Exit:   0 (the table is printed even when every ledger is absent; absence is a cell).
"""
from __future__ import annotations
import argparse, json, os, re, sys

HOLE_FREE_BAR = 0.85     # docs/GOAL-arbitrary-codebases.md, "The bar"
CORE_BAR = 0.60

# (name in the table, ledger module). Order is the GOAL's. The cachetools label keeps the
# "(published)" tag because check_docs.py has pinned that exact row since before this
# script existed, and the README quotes it.
CORPORA = [
    ("cachetools", "Cachetools"),
    ("sqlparse", "Sqlparse"),
    ("requests", "Requests"),
    ("flask", "Flask"),
    ("jinja2", "Jinja2"),
    ("click", "Click"),
    ("rich", "Rich"),
    ("django", "Django"),
]

HEADER = ("| repo | functions | hole-free | verifiable core (closed by translation) "
          "| closed by contract | holes | bar (>= 85 % hole-free, >= 60 % core) |\n"
          "|---|--:|--:|--:|--:|--:|---|")


def pct(n, d):
    """Floored percentage, the shape `(\\d+%)` in check_docs.py expects."""
    return 0 if not d else 100 * n // d


def corpus_version(root, module):
    """The corpus version, read from the tracked provenance record's `command`
    (`.../requests-2.32.5-sdist Requests`) so the label says which re-land the row is;
    None when no record names one."""
    path = os.path.join(root, "provenance", f"ast-{module}.json.prov.json")
    if not os.path.exists(path):
        return None
    cmd = json.load(open(path)).get("command") or ""
    m = re.search(r"[/ ]([A-Za-z0-9_]+)-(\d+(?:\.\d+)+)(?:-sdist)?\b", cmd)
    return m.group(2) if m else None


def label_for(name, version):
    if name == "cachetools":
        return "`cachetools` (published)"
    if name == "django":
        return "`django/`"
    return f"`{name}` {version}" if version else f"`{name}`"


def bar_verdict(ledger):
    """'holds', or 'misses: <which> ...; top hole `label` N'."""
    fn = ledger.get("functions") or 0
    hf = ledger.get("holeFree") or 0
    core = ledger.get("closedByTranslation", ledger.get("verifiableCore")) or 0
    misses = []
    if fn == 0 or hf / fn < HOLE_FREE_BAR:
        misses.append(f"hole-free {pct(hf, fn)}% < 85%")
    if fn == 0 or core / fn < CORE_BAR:
        misses.append(f"core {pct(core, fn)}% < 60%")
    if not misses:
        return "holds"
    top = (ledger.get("holesByLabel") or [{}])[0]
    if top.get("label") is not None:
        return (f"misses: {'; '.join(misses)}; top hole `{top['label']}` "
                f"{top.get('count', 0)}")
    return f"misses: {'; '.join(misses)}; no holes listed"


def row(label, ledger):
    """One markdown row. `ledger` is the parsed ledger-<M>.json, or None if absent."""
    if ledger is None:
        return f"| {label} | ledger not on disk | — | — | — | — | — |"
    fn = ledger.get("functions") or 0
    hf = ledger.get("holeFree") or 0
    core = ledger.get("closedByTranslation", ledger.get("verifiableCore")) or 0
    cbc = ledger.get("closedByContract", 0)
    holes = ledger.get("holes", 0)
    return (f"| {label} | {fn} | {hf} ({pct(hf, fn)}%) | {core} ({pct(core, fn)}%) "
            f"| {cbc} | {holes} | {bar_verdict(ledger)} |")


def render(root="."):
    lines = [HEADER]
    for name, module in CORPORA:
        path = os.path.join(root, f"ledger-{module}.json")
        ledger = json.load(open(path)) if os.path.exists(path) else None
        lines.append(row(label_for(name, corpus_version(root, module)), ledger))
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--root", default=".")
    a = ap.parse_args()
    sys.stdout.write(render(a.root))
    return 0


if __name__ == "__main__":
    sys.exit(main())
