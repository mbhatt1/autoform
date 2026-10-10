"""`scripts/ledger.py` is a mirror of `Autoform/Ledger.lean`, and a mirror is only evidence
while it agrees with the original.

Three guards:

* the name lists the script copies from the Lean sources (`Stdlib.freeNames`,
  `Stdlib.excNames`, `Stdlib.methodNames`, `Iteration.freeNames`, `contractedCallees`) are
  re-read from those sources here, so an edit on either side fails this file;
* the script's ledger equals the ledger Lean wrote, field for field, on every corpus
  pinned under `tests/fixtures/ledger-lean/` (produced by `scripts/ledger.lean.tmpl`,
  pinned to the AST's sha256 by `scripts/ledger_fixture.py`), and on the live
  `ledger-Cachetools.json` CI regenerates from the built module before running pytest;
* on Django, which no one elaborates whole, the script's ledger of part 1 of the sharded
  render equals the ledger Lean computed on that one part (`scripts/ledger.py
  --emit-lean-check`); the AST is a local product, so that check names its skip when the
  AST is absent instead of passing.

Equality is on every field `Program.ledgerJson` writes. `holesByLabel` and
`contractsUsed` are compared as maps: Lean orders equal counts in hash-map order.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCRIPT = os.path.join(ROOT, "scripts", "ledger.py")
FIXTURES = os.path.join(ROOT, "tests", "fixtures", "ledger-lean")
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import ledger as L  # noqa: E402


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def run_ledger(ast, module, out, *extra):
    r = subprocess.run([sys.executable, SCRIPT, ast, module, "--out", out, "--quiet", *extra],
                       capture_output=True, text=True, timeout=600, cwd=ROOT)
    assert r.returncode == 0, r.stderr
    with open(out) as fh:
        return json.load(fh)


def diff_ledgers(lean, py):
    """Every field Lean wrote, compared with the script's; the differences, if any."""
    bad = {}
    for k in lean:
        if k in ("holesByLabel", "contractsUsed"):
            key, val = ("label", "count") if k == "holesByLabel" else ("callee", "sites")
            a = {r[key]: r[val] for r in lean[k]}
            b = {r[key]: r[val] for r in py.get(k, [])}
            if a != b:
                bad[k] = {x: (a.get(x), b.get(x)) for x in set(a) | set(b) if a.get(x) != b.get(x)}
        elif lean[k] != py.get(k):
            bad[k] = (lean[k], py.get(k))
    return bad


# ---------------------------------------------------------------------------
# The copied name lists
# ---------------------------------------------------------------------------

def _lean(path):
    with open(os.path.join(ROOT, "Autoform", "Lang", "Core", path)
              if not path.startswith("Autoform") else os.path.join(ROOT, path)) as fh:
        return fh.read()


def _strip_comments(text):
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def _strings(text):
    return [m.group(1) for m in re.finditer(r'"((?:[^"\\]|\\.)*)"', text)]


def _list_def(source, name):
    """The string literals of `def <name> : List String := ...`, up to the next `def`."""
    m = re.search(rf"^def {re.escape(name)} : List String :=\n(.*?)(?=^\S)", source,
                  flags=re.S | re.M)
    assert m, f"{name} not found"
    return _strings(_strip_comments(m.group(1)))


def test_stdlib_name_lists_match_lean():
    stdlib = _lean("Stdlib.lean")
    assert _list_def(stdlib, "excNames") == L.STDLIB_EXC_NAMES
    # `freeNames := excNames ++ [...]`
    assert L.STDLIB_EXC_NAMES + _list_def(stdlib, "freeNames") == L.STDLIB_FREE_NAMES
    assert _list_def(stdlib, "methodNames") == L.STDLIB_METHOD_NAMES
    assert _list_def(_lean("Iteration.lean"), "freeNames") == L.ITERATION_FREE_NAMES


def test_contracted_callees_match_lean():
    src = _lean("Autoform/Ledger.lean")
    m = re.search(r"^def contractedCallees : Dialect → List String\n(.*?)(?=^\S)", src,
                  flags=re.S | re.M)
    assert m
    arms = re.split(r"^\s*\| \.(\w+) =>", _strip_comments(m.group(1)), flags=re.M)
    assert arms[0].strip() == ""
    seen = {}
    for dialect, body in zip(arms[1::2], arms[2::2]):
        seen["." + dialect] = _strings(body)
    assert set(seen) == set(L.CONTRACTED_CALLEES)
    # python: `Stdlib.methodNames.map ("." ++ ·) ++ [ ... ]`
    assert "Stdlib.methodNames.map" in m.group(1)
    assert seen[".python"] == ["."] + [c for c in L.CONTRACTED_CALLEES[".python"]
                                       if not c.startswith(".")]
    for dialect in (".cLike", ".java", ".go", ".javascript"):
        assert seen[dialect] == L.CONTRACTED_CALLEES[dialect], dialect


def test_knows_free_is_python_only():
    assert L.knows_free(".python", "len") and L.knows_free(".python", "iter")
    assert not L.knows_free(".cLike", "len") and not L.knows_free(".python", "print")


# ---------------------------------------------------------------------------
# The ledger itself, against what Lean wrote
# ---------------------------------------------------------------------------

def _fixtures():
    return sorted(f for f in os.listdir(FIXTURES) if f.endswith(".json")) if os.path.isdir(FIXTURES) else []


@pytest.mark.parametrize("name", [f for f in _fixtures() if "-Part" not in f])
def test_matches_pinned_lean_ledger(name, tmp_path):
    with open(os.path.join(FIXTURES, name)) as fh:
        pin = json.load(fh)
    ast = os.path.join(ROOT, pin["ast"])
    assert os.path.exists(ast), f"{pin['ast']} is tracked and must exist"
    assert sha256_file(ast) == pin["astSha256"], (
        f"{pin['ast']} is not the AST this fixture was pinned to. The fixture is the LEAN "
        f"ledger of the old AST; regenerate it: render + `lake build Autoform.Generated."
        f"{pin['module']}`, `lake env lean` on scripts/ledger.lean.tmpl, then "
        f"`scripts/ledger_fixture.py {pin['module']}`.")
    py = run_ledger(ast, pin["module"], str(tmp_path / "py.json"))
    assert diff_ledgers(pin["ledger"], py) == {}
    assert py["producer"] == "scripts/ledger.py" and py["astSha256"] == pin["astSha256"]


def test_matches_live_lean_ledger_cachetools(tmp_path):
    """CI regenerates ledger-Cachetools.json from the built module before pytest, so there
    the comparison is against a ledger Lean wrote minutes earlier, not a pin."""
    live = os.path.join(ROOT, "ledger-Cachetools.json")
    ast = os.path.join(ROOT, "ast-Cachetools.json")
    if not os.path.exists(live):
        pytest.skip("ledger-Cachetools.json absent (a build product): CI regenerates it with "
                    "scripts/ledger.lean.tmpl before pytest; locally run that first. The "
                    "pinned fixture above still checks cachetools.")
    with open(live) as fh:
        lean = json.load(fh)
    if lean.get("producer") == "scripts/ledger.py":
        pytest.skip("ledger-Cachetools.json was written by scripts/ledger.py itself; "
                    "regenerate it with scripts/ledger.lean.tmpl to compare against Lean.")
    py = run_ledger(ast, "Cachetools", str(tmp_path / "py.json"))
    assert lean["functions"] == py["functions"], (
        "ledger-Cachetools.json and ast-Cachetools.json disagree on the population: the "
        "ledger is stale; re-run scripts/ledger.lean.tmpl before trusting either.")
    assert diff_ledgers(lean, py) == {}


def test_part_ledger_is_the_parts_own_program(tmp_path):
    """`--part K --shard-functions N` is the slice a part defines: on a corpus smaller than
    one shard it is the whole module minus the auxiliary functions."""
    ast = os.path.join(ROOT, "ast-Cachetools.json")
    whole = run_ledger(ast, "Cachetools", str(tmp_path / "w.json"))
    part = run_ledger(ast, "Cachetools", str(tmp_path / "p.json"),
                      "--part", "1", "--shard-functions", "100000")
    assert part["part"] == 1 and part["shardFunctions"] == 100000
    assert part["functions"] == whole["functions"] and part["holes"] == whole["holes"]
    # Dropping the auxiliary functions from the table can only shrink the core.
    assert part["verifiableCore"] <= whole["verifiableCore"]
    r = subprocess.run([sys.executable, SCRIPT, ast, "Cachetools", "--part", "9",
                        "--shard-functions", "1000", "--out", str(tmp_path / "x.json")],
                       capture_output=True, text=True, cwd=ROOT)
    assert r.returncode != 0 and "beyond" in r.stderr


DJANGO_PART = "Django-Part0001.json"


def test_django_part_matches_lean(tmp_path):
    """The milestone-5 cross-check: Django is never elaborated whole, so the Lean side of
    this comparison is one part of the sharded render, and the fixture carries what Lean
    wrote for it. Both sides are pinned to the same AST digest."""
    pin_path = os.path.join(FIXTURES, DJANGO_PART)
    assert os.path.exists(pin_path), (
        "tests/fixtures/ledger-lean/Django-Part0001.json is missing: the Django cross-check "
        "has no Lean side. Produce it with scripts/ledger_corpus.sh (see its --lean-part).")
    with open(pin_path) as fh:
        pin = json.load(fh)
    ast = os.environ.get("AUTOFORM_DJANGO_AST") or os.path.join(ROOT, pin["ast"])
    if not os.path.exists(ast):
        pytest.skip(f"{pin['ast']} absent: the Django AST is a local product of "
                    f"scripts/ledger_corpus.sh (Joern, ~4 min, 6.6 GB) and CI does not export "
                    f"it. The Django half of the cross-check did NOT run here.")
    assert sha256_file(ast) == pin["astSha256"], (
        f"{ast} is a different Django export from the one the fixture's Lean ledger was "
        f"computed on. Re-run scripts/ledger_corpus.sh ... --lean-part 1 and re-pin.")
    py = run_ledger(ast, pin["module"], str(tmp_path / "py.json"),
                    "--part", str(pin["part"]), "--shard-functions", str(pin["shardFunctions"]))
    assert diff_ledgers(pin["ledger"], py) == {}
