#!/usr/bin/env python3
"""emit_contracts.py — render `Autoform.Contracts.Demo.contractRecords` to JSON.

A contract-relative theorem is not the same claim as an unconditional one, and the
difference is invisible unless the assurance case is told. This writes the registry that
`scripts/sacm.py` reads to attach `Assumption` nodes to *the theorem's own goal*.

Usage: scripts/emit_contracts.py [Module] [--out PATH]
"""
from __future__ import annotations
import json, os, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

DRIVER = '''import Autoform.Contracts
def main : IO Unit :=
  IO.println (Autoform.Contracts.Demo.contractRecordsJson %s).compress
'''


def emit(module: str) -> dict:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT, delete=False) as fh:
        fh.write(DRIVER % json.dumps(module))
        path = fh.name
    try:
        r = subprocess.run(["lake", "env", "lean", "--run", path],
                           cwd=ROOT, capture_output=True, text=True, timeout=1800)
    finally:
        os.unlink(path)
    if r.returncode != 0:
        sys.exit("emit_contracts: lean failed\n" + (r.stderr or r.stdout)[-3000:])
    line = [l for l in r.stdout.splitlines() if l.startswith("{")]
    if not line:
        sys.exit("emit_contracts: no JSON on stdout\n" + r.stdout[-2000:])
    return json.loads(line[-1])


def main():
    argv = sys.argv[1:]
    out = None
    if "--out" in argv:
        i = argv.index("--out"); out = argv[i + 1]; del argv[i:i + 2]
    module = argv[0] if argv else "Cachetools"
    doc = emit(module)
    out = out or os.path.join(ROOT, f"contracts-{module}.json")
    with open(out, "w") as fh:
        json.dump(doc, fh, indent=1)
    ths = doc.get("theorems", [])
    unsat = [t["theorem"] for t in ths if not t.get("satisfiable")]
    print(f"contracts-{module}: {len(ths)} contract-relative theorems, "
          f"{len(unsat)} with no satisfiability proof -> {out}")
    for t in unsat:
        print(f"  DISQUALIFIED (no Satisfiable proof): {t}")


if __name__ == "__main__":
    main()
