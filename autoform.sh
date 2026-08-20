#!/usr/bin/env bash
# autoform — point at any codebase Joern can parse, get Lean.
#
#   ./autoform.sh <source-dir> [ModuleName]
#
#   source ──Joern──▶ CPG ──▶ neutral JSON AST ──▶ Lean Core program ──▶ ledger
#                      │                                    │
#                      └─▶ formalization graph              └─▶ differential vs runtime
#
# The CPG is the universal front end: C/C++/Java/JavaScript/Python/Kotlin/binaries all
# normalize to one node vocabulary, so one semantics and one exporter cover all of them.
set -euo pipefail

SRC="${1:?usage: autoform.sh <source-dir> [ModuleName]}"
MOD="${2:-Translated}"
ROOT="$(cd "$(dirname "$0")" && pwd)"
JOERN="${JOERN_HOME:-$HOME/joern}/joern-cli"
WORK="$(mktemp -d)"
export PATH="$HOME/.elan/bin:$PATH"
cd "$ROOT"

echo "==> [1/6] parsing $SRC"
"$JOERN/joern-parse" "$SRC" --output "$WORK/cpg.bin" >/dev/null 2>&1

echo "==> [2/6] cartographer: formalization graph"
"$JOERN/joern" --script "$ROOT/cartographer/formalization_graph.sc" \
  --param cpgPath="$WORK/cpg.bin" --param out="$ROOT/formalization-graph.json" 2>&1 \
  | grep -E "^wrote|^pure" || true

echo "==> [3/6] transpiler: CPG -> neutral AST"
"$JOERN/joern" --script "$ROOT/cartographer/export_ast.sc" \
  --param cpgPath="$WORK/cpg.bin" --param out="$WORK/ast.json" 2>&1 | grep -E "^exported"
cp "$WORK/ast.json" "$ROOT/ast-$MOD.json"

echo "==> [4/6] rendering Lean"
python3 "$ROOT/cartographer/render_lean.py" "$WORK/ast.json" \
  "$ROOT/Autoform/Generated/$MOD.lean" "$MOD"

echo "==> [5/6] type-checking generated Lean"
lake build "Autoform.Generated.$MOD"

echo "==> [6/6] differential conformance vs the real runtime"
python3 "$ROOT/scripts/differential.py" "$WORK/ast.json" "$SRC" "$MOD" 5 || true

sed "s/@MODULE@/$MOD/g" "$ROOT/scripts/ledger.lean.tmpl" > "$WORK/Ledger.lean"
lake env lean "$WORK/Ledger.lean"
rm -rf "$ROOT/workspace"
