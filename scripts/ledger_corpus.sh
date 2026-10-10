#!/usr/bin/env bash
# ledger_corpus.sh — export, render and ledger a corpus, each stage timed, no `lake build`.
#
#   scripts/ledger_corpus.sh <source-dir> <Module> [--lean-part K]
#
# The ledger stage is `scripts/ledger.py` on the exported AST (docs/GOAL-arbitrary-codebases.md
# milestone 5: "Django's ledger runs under 60 s"). The Lean ledger (`scripts/ledger.lean.tmpl`)
# needs the whole generated module elaborated first, which for Django is minutes and
# gigabytes per part; this script never elaborates the module. With `--lean-part K` it
# builds ONE part of the sharded render and runs Lean's `Program.ledgerJson` on that part
# alone, so the Python ledger of the same part can be compared with it
# (`tests/test_ledger_py.py::test_django_part_matches_lean`, pinned with
# `scripts/ledger_fixture.py`). That is one `lean` process of a few GB, the most this
# script will ever hold.
#
# Writes into the repository root: ast-<M>.json, Autoform/Generated/<M>.lean (+ parts),
# ledger-<M>.json and, with --lean-part, ledger-<M>-PartNNNN.lean.json. All are build
# products (.gitignore); nothing is committed. Timings go to stdout and to
# .autoform-work/ledger/<M>/timings.json.
set -euo pipefail

if [ $# -lt 2 ]; then
  echo "usage: $0 <source-dir> <Module> [--lean-part K]" >&2
  exit 2
fi
SRC="$(cd "$1" && pwd -P)"
MOD="$2"
shift 2
LEAN_PART=""
while [ $# -gt 0 ]; do
  case "$1" in
    --lean-part) LEAN_PART="$2"; shift 2 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done
ROOT="$(cd "$(dirname "$0")/.." && pwd -P)"
cd "$ROOT"

PYTHON="${AUTOFORM_PYTHON:-python3}"
if [ -z "${AUTOFORM_PYTHON:-}" ] && [ -x "$ROOT/.venv/bin/python" ]; then
  PYTHON="$ROOT/.venv/bin/python"
fi
JOERN="${JOERN_HOME:-$HOME/joern}"
if [ -d "$JOERN/joern-cli" ]; then JOERN="$JOERN/joern-cli"; fi
if [ ! -x "$JOERN/joern" ]; then
  echo "ledger_corpus: joern not found under $JOERN (set JOERN_HOME)" >&2
  exit 1
fi
export PATH="$HOME/.elan/bin:$PATH"
SHARD="${AUTOFORM_SHARD_FUNCTIONS:-1000}"

WORK="$(mktemp -d "${TMPDIR:-/tmp}/ledger-$MOD.XXXXXX")"
REPORT="$ROOT/.autoform-work/ledger/$MOD"
mkdir -p "$REPORT"
echo "==> work: $WORK"
echo "==> report: $REPORT"

now() { "$PYTHON" -c 'import time; print(time.time())'; }
TIMINGS=()
stage() {  # stage <name> <command...>: run, time, record
  local name="$1"; shift
  local t0 t1
  t0="$(now)"
  "$@"
  t1="$(now)"
  local secs
  secs="$("$PYTHON" -c "print(round($t1 - $t0, 1))")"
  echo "    [$name] ${secs} s"
  TIMINGS+=("\"$name\": $secs")
}

echo "==> [1/4] parse (joern-parse)"
stage parse bash -c "cd '$WORK' && '$JOERN/joern-parse' '$SRC' --output '$WORK/cpg.bin' > '$REPORT/parse.log' 2>&1"

echo "==> [2/4] export (cartographer/export_ast.sc)"
stage export bash -c "cd '$WORK' && '$JOERN/joern' --script '$ROOT/cartographer/export_ast.sc' \
  --param cpgPath='$WORK/cpg.bin' --param out='$WORK/ast.json' \
  --param dataModel='${AUTOFORM_DATA_MODEL:-lp64}' > '$REPORT/export.log' 2>&1"
grep -E "^exported" "$REPORT/export.log" || { cat "$REPORT/export.log" >&2; exit 1; }
cp "$WORK/ast.json" "$ROOT/ast-$MOD.json"
echo "    ast-$MOD.json: $(shasum -a 256 "ast-$MOD.json" | cut -d' ' -f1)"

echo "==> [3/4] render, $SHARD functions per part (cartographer/render_lean.py)"
stage render "$PYTHON" cartographer/render_lean.py "ast-$MOD.json" "Autoform/Generated/$MOD.lean" "$MOD" \
  --shard-functions "$SHARD"

echo "==> [4/4] ledger (scripts/ledger.py, from the AST; no Lean)"
stage ledger "$PYTHON" scripts/ledger.py "ast-$MOD.json" "$MOD"
cp "ledger-$MOD.json" "$REPORT/ledger-$MOD.json"

if [ -n "$LEAN_PART" ]; then
  PART="$(printf 'Part%04d' "$LEAN_PART")"
  echo "==> [+] Lean ledger of $PART alone (lake build one part, then Program.ledgerJson)"
  stage "lake build $PART" lake build "Autoform.Generated.$MOD.$PART"
  "$PYTHON" scripts/ledger.py "ast-$MOD.json" "$MOD" --part "$LEAN_PART" --shard-functions "$SHARD" \
    --emit-lean-check "$REPORT/LedgerPart.lean" --out "ledger-$MOD-$PART.lean.json"
  stage "lean ledger $PART" lake env lean "$REPORT/LedgerPart.lean"
  stage "python ledger $PART" "$PYTHON" scripts/ledger.py "ast-$MOD.json" "$MOD" \
    --part "$LEAN_PART" --shard-functions "$SHARD" --out "$REPORT/ledger-$MOD-$PART.py.json" --quiet
  "$PYTHON" - "ledger-$MOD-$PART.lean.json" "$REPORT/ledger-$MOD-$PART.py.json" <<'PYEOF'
import json, sys
lean, py = (json.load(open(p)) for p in sys.argv[1:3])
bad = {}
for k in lean:
    if k in ("holesByLabel", "contractsUsed"):
        key, val = ("label", "count") if k == "holesByLabel" else ("callee", "sites")
        a = {r[key]: r[val] for r in lean[k]}; b = {r[key]: r[val] for r in py.get(k, [])}
        if a != b: bad[k] = (a, b)
    elif lean[k] != py.get(k): bad[k] = (lean[k], py.get(k))
if bad:
    print("CROSS-CHECK FAILED: scripts/ledger.py disagrees with Program.ledgerJson:", file=sys.stderr)
    for k, v in bad.items(): print(f"  {k}: lean={v[0]} py={v[1]}", file=sys.stderr)
    sys.exit(1)
print(f"    cross-check OK: Lean and Python agree on every ledger field of this part "
      f"({lean['functions']} functions, core {lean['verifiableCore']})")
PYEOF
  echo "    pin it: scripts/ledger_fixture.py $MOD --ledger ledger-$MOD-$PART.lean.json --part $LEAN_PART --shard-functions $SHARD"
fi

{
  echo "{"
  echo " \"module\": \"$MOD\", \"source\": \"$SRC\", \"shardFunctions\": $SHARD,"
  echo " \"astSha256\": \"$(shasum -a 256 "ast-$MOD.json" | cut -d' ' -f1)\","
  echo " \"seconds\": {$(IFS=,; echo "${TIMINGS[*]}")}"
  echo "}"
} > "$REPORT/timings.json"
echo "==> timings: $REPORT/timings.json"
cat "$REPORT/timings.json"
