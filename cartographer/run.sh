#!/usr/bin/env bash
# Cartographer driver: source tree -> code property graph -> formalization graph.
#
# Usage: cartographer/run.sh <source-dir> [output.json]
set -euo pipefail

SRC="${1:?usage: run.sh <source-dir> [out.json]}"
OUT="${2:-formalization-graph.json}"
JOERN="${JOERN_HOME:-$HOME/joern}/joern-cli"
WORK="$(mktemp -d)"

"$JOERN/joern-parse" "$SRC" --output "$WORK/cpg.bin"
"$JOERN/joern" --script "$(dirname "$0")/formalization_graph.sc" \
  --param cpgPath="$WORK/cpg.bin" --param out="$OUT"

echo "formalization graph -> $OUT"
