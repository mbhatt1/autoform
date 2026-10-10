#!/usr/bin/env python3
"""ledger_fixture.py — pin a Lean-produced ledger to its AST, for tests/test_ledger_py.py.

    scripts/ledger_fixture.py <Module> [--ledger ledger-<Module>.json] [--ast ast-<Module>.json]
                              [--name <fixture name>] [--part K --shard-functions N]

Reads a ledger that `scripts/ledger.lean.tmpl` (or the part check `scripts/ledger.py
--emit-lean-check` writes) produced with Lean, and writes
`tests/fixtures/ledger-lean/<name>.json` carrying that ledger together with the sha256
of the AST it was computed from. The test re-derives the ledger from the same AST with
`scripts/ledger.py` and compares; if the AST on disk no longer has the pinned digest the
test fails and names this command, because a fixture that outlived its AST pins nothing.

This script never computes a ledger. It copies one that Lean wrote.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FIXTURES = os.path.join(ROOT, "tests", "fixtures", "ledger-lean")
LEAN_KEYS = ("module", "dialect", "functions", "nodes", "holes", "holeFree", "verifiableCore",
             "closedByTranslation", "closedByContract", "contractsUsed", "dynamicHoleRisk",
             "holesByLabel")


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("module")
    ap.add_argument("--ledger", default=None)
    ap.add_argument("--ast", default=None)
    ap.add_argument("--name", default=None)
    ap.add_argument("--part", type=int, default=None)
    ap.add_argument("--shard-functions", type=int, default=0)
    ap.add_argument("--command", default=None,
                    help="how the ledger was produced (recorded verbatim)")
    a = ap.parse_args(argv)
    ledger_path = a.ledger or os.path.join(ROOT, f"ledger-{a.module}.json")
    ast_path = a.ast or os.path.join(ROOT, f"ast-{a.module}.json")
    with open(ledger_path) as fh:
        ledger = json.load(fh)
    if ledger.get("producer") == "scripts/ledger.py":
        raise SystemExit(f"{ledger_path} was written by scripts/ledger.py; a fixture must be "
                         f"the LEAN ledger (scripts/ledger.lean.tmpl), or the test checks "
                         f"the script against itself.")
    missing = [k for k in LEAN_KEYS if k not in ledger]
    if missing:
        raise SystemExit(f"{ledger_path} lacks ledger fields {missing}")
    if ledger["module"] != a.module:
        raise SystemExit(f"{ledger_path} is tagged module={ledger['module']!r}, not {a.module!r}")
    name = a.name or (a.module if a.part is None else f"{a.module}-Part{a.part:04d}")
    record = {
        "module": a.module,
        "ast": os.path.relpath(ast_path, ROOT),
        "astSha256": sha256_file(ast_path),
        "producedBy": a.command or "scripts/ledger.lean.tmpl via `lake env lean` (Program.ledgerJson)",
        "ledger": {k: ledger[k] for k in LEAN_KEYS},
    }
    if a.part is not None:
        if a.shard_functions <= 0:
            raise SystemExit("--part needs --shard-functions N > 0")
        record["part"] = a.part
        record["shardFunctions"] = a.shard_functions
    os.makedirs(FIXTURES, exist_ok=True)
    dst = os.path.join(FIXTURES, name + ".json")
    with open(dst, "w") as fh:
        json.dump(record, fh, indent=1, sort_keys=True)
        fh.write("\n")
    print(f"pinned {os.path.relpath(ledger_path, ROOT)} to {record['ast']} "
          f"({record['astSha256'][:12]}) -> {os.path.relpath(dst, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
