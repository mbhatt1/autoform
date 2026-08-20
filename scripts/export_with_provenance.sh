#!/usr/bin/env bash
# export_with_provenance.sh — produce a neutral AST that can be traced back to what made it.
#
#   scripts/export_with_provenance.sh <source-dir> <ModuleName>
#
# Same three steps as `autoform.sh`'s stages 1 and 3, plus the two that make the result
# reproducible:
#
#   0. refuse to run at all unless the installed Joern matches `joern-version`.  The
#      neutral AST is a function of the CPG front end; exporting with an unpinned Joern
#      produces an artifact whose differences from its neighbours mean nothing.
#   1. joern-parse <source-dir> -> cpg.bin
#   2. export_ast.sc              -> ast-<Module>.json
#   3. provenance.py record       -> provenance/ast-<Module>.json.prov.json
#
# Step 3 is the point.  The .cpg is thrown away here exactly as it is everywhere else --
# it is hundreds of megabytes and tracking it is not on the table -- but the record names
# the source tree, its revision, the Joern version and the exact command, so the CPG can
# be REBUILT.  `scripts/reproduce_ast.py` does the rebuild; `scripts/check_provenance.py`
# checks, without any of that, that the record still describes the artifact and that the
# exporter has not moved underneath it.
#
# This does not render Lean or run the differential; use ./autoform.sh for the full run.
# Until autoform.sh calls provenance.py itself (see docs/architecture.md, "Merge-phase
# changes this asks for elsewhere"), an AST produced by autoform.sh is unattributed and
# scripts/check_provenance.py will say so by name.
set -euo pipefail

SRC="${1:?usage: export_with_provenance.sh <source-dir> <ModuleName>}"
MOD="${2:?usage: export_with_provenance.sh <source-dir> <ModuleName>}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
JOERN="${JOERN_HOME:-$HOME/joern}/joern-cli"
OUT="$ROOT/ast-$MOD.json"

python3 "$ROOT/scripts/provenance.py" joern-version --check

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK" "$ROOT/workspace"' EXIT

PARSE_CMD="$JOERN/joern-parse $SRC --output <cpg>"
EXPORT_CMD="$JOERN/joern --script cartographer/export_ast.sc --param cpgPath=<cpg> --param out=ast-$MOD.json"

echo "==> [1/3] joern-parse $SRC"
"$JOERN/joern-parse" "$SRC" --output "$WORK/cpg.bin" >/dev/null

echo "==> [2/3] export_ast.sc -> ast-$MOD.json"
( cd "$ROOT" && "$JOERN/joern" --script cartographer/export_ast.sc \
    --param cpgPath="$WORK/cpg.bin" --param out="$OUT" ) 2>&1 | grep -E "^exported"

echo "==> [3/3] recording provenance"
python3 "$ROOT/scripts/provenance.py" record \
  --artifact "$OUT" \
  --source "$SRC" \
  --exporter cartographer/export_ast.sc \
  --command "$PARSE_CMD && $EXPORT_CMD"

echo
echo "ast-$MOD.json is attributed. Re-render the Lean module from it before trusting any"
echo "figure derived from either:  python3 cartographer/render_lean.py ast-$MOD.json \\"
echo "    Autoform/Generated/$MOD.lean $MOD"
