#!/usr/bin/env bash
# reland_corpus.sh — re-land a tracked corpus from its identified source revision.
#
#   scripts/reland_corpus.sh <source-dir> <Module>
#
# A tracked `ast-<Module>.json` is evidence about the exporter that produced it, not about
# the exporter in the tree (docs/integrity.md). Re-exporting it is NOT a local change: the
# AST, its render, the manifest hashes, the provenance record, the conformance evidence,
# the generated specs and the ledger all have to move together, or every gate stays green
# while agreeing on a mixture of old and new. This script performs that cascade in the
# documented order and stops at the first failure. It does NOT commit; review the diff.
#
# Prerequisites: a clean tree (checked), the pinned Joern on JOERN_HOME or ~/joern,
# elan on PATH, and the source runtime for the corpus (CPython for a Python corpus).
# Optional: AUTOFORM_TESTS=<dir> (the corpus test suite), AUTOFORM_CASES, AUTOFORM_SPEC_EXCLUDE.
set -euo pipefail

if [ $# -ne 2 ]; then
  echo "usage: $0 <source-dir> <Module>" >&2
  exit 2
fi
SRC="$(cd "$1" && pwd -P)"
MOD="$2"
ROOT="$(cd "$(dirname "$0")/.." && pwd -P)"
cd "$ROOT"

# A re-land on a dirty tree cannot be reviewed: the diff would mix this cascade with
# whatever was already uncommitted, and `synth_specs.py` itself refuses a dirty subject.
if [ -n "$(git status --porcelain)" ]; then
  echo "reland: working tree is dirty; commit or stash first." >&2
  git status --short >&2
  exit 1
fi

PYTHON="${AUTOFORM_PYTHON:-python3}"
if [ -z "${AUTOFORM_PYTHON:-}" ] && [ -x "$ROOT/.venv/bin/python" ]; then
  PYTHON="$ROOT/.venv/bin/python"
fi
JOERN="${JOERN_HOME:-$HOME/joern}"
if [ -d "$JOERN/joern-cli" ]; then JOERN="$JOERN/joern-cli"; fi
if [ ! -x "$JOERN/joern" ]; then
  echo "reland: joern not found under $JOERN (set JOERN_HOME)" >&2
  exit 1
fi
export PATH="$HOME/.elan/bin:$PATH"

WORK="$(mktemp -d "${TMPDIR:-/tmp}/reland-$MOD.XXXXXX")"
REPORT="$ROOT/.autoform-work/reland/$MOD"
mkdir -p "$REPORT"
echo "==> work: $WORK"
echo "==> report: $REPORT"

# Record what is being replaced, so the review has both digests in front of it.
OLD_SHA="$(shasum -a 256 "ast-$MOD.json" 2>/dev/null | cut -d' ' -f1 || true)"
echo "==> replacing ast-$MOD.json (${OLD_SHA:-not tracked})"

echo "==> [1/9] parse"
LANGUAGE_ARGS=()
if [ -n "${AUTOFORM_FRONTEND:-}" ]; then LANGUAGE_ARGS=(--language "$AUTOFORM_FRONTEND"); fi
(cd "$WORK" && "$JOERN/joern-parse" "$SRC" --output "$WORK/cpg.bin" \
   ${LANGUAGE_ARGS[@]+"${LANGUAGE_ARGS[@]}"}) >"$REPORT/parse.log" 2>&1 || { cat "$REPORT/parse.log" >&2; exit 1; }

echo "==> [2/9] export"
EXPORT_OUT="$(cd "$WORK" && "$JOERN/joern" --script "$ROOT/cartographer/export_ast.sc" \
  --param cpgPath="$WORK/cpg.bin" --param out="$WORK/ast.json" \
  --param dataModel="${AUTOFORM_DATA_MODEL:-lp64}" 2>&1)" || { echo "$EXPORT_OUT" >&2; exit 1; }
printf '%s\n' "$EXPORT_OUT" > "$REPORT/export.log"
grep -E "^exported" <<<"$EXPORT_OUT" || { echo "$EXPORT_OUT" >&2; exit 1; }
cp "$WORK/ast.json" "$ROOT/ast-$MOD.json"
NEW_SHA="$(shasum -a 256 "ast-$MOD.json" | cut -d' ' -f1)"
echo "    ast-$MOD.json: ${OLD_SHA:-none} -> $NEW_SHA"

echo "==> [3/9] provenance: record, and retire the backlog entry"
"$PYTHON" scripts/provenance.py record \
  --artifact "ast-$MOD.json" --source "$SRC" \
  --exporter cartographer/export_ast.sc \
  --command "scripts/reland_corpus.sh $SRC $MOD" | tee "$REPORT/provenance.log"
# A real record supersedes the backlog line. Leaving both makes check_provenance report
# a digest change against a baseline that no longer applies.
"$PYTHON" - "$MOD" <<'PYEOF'
import json, sys, collections
mod = sys.argv[1]
path = "provenance/unattributed.json"
d = json.load(open(path), object_pairs_hook=collections.OrderedDict)
removed = d["artifacts"].pop(f"ast-{mod}.json", None)
json.dump(d, open(path, "w"), indent=1); open(path, "a").write("\n")
print("    backlog entry", "removed" if removed else "absent", f"for ast-{mod}.json")
PYEOF
# Other corpora can still carry the previous exporter pin while this one is being
# regenerated. Validate this artifact fully now; the repository-wide gate below is
# still required before claiming the whole re-land complete.
"$PYTHON" scripts/check_provenance.py --strict --artifact "ast-$MOD.json"

echo "==> [4/9] render"
# Tracked corpora are pinned as single-module renders (artifact-manifest.json).
"$PYTHON" cartographer/render_lean.py "ast-$MOD.json" "Autoform/Generated/$MOD.lean" "$MOD" \
  --shard-functions 0

echo "==> [5/9] manifest: re-record the AST/render pins"
"$PYTHON" scripts/check_render.py --record "$MOD"

echo "==> [6/9] type-check the render and everything that imports it"
lake build "Autoform.Generated.$MOD" 2>&1 | tail -3
echo "    (a failure in Contracts/Specs here is a theorem whose truth depended on the old AST;"
echo "     see the RELAND annotations in Autoform/Specs/${MOD}Spec.lean)"
lake build 2>&1 | tail -3

echo "==> [7/9] conformance vs the real runtime"
# AUTOFORM_TESTS names the corpus's own test suite when it lives outside <source-dir>
# (an sdist package exported without its tests); differential.py records it.
TEST_ARGS=()
if [ -n "${AUTOFORM_TESTS:-}" ]; then TEST_ARGS=(--tests "$(cd "$AUTOFORM_TESTS" && pwd -P)"); fi
(cd "$REPORT" && "$PYTHON" "$ROOT/scripts/differential.py" "$ROOT/ast-$MOD.json" "$SRC" "$MOD" "${AUTOFORM_CASES:-5}" \
   ${TEST_ARGS[@]+"${TEST_ARGS[@]}"}) \
  | tee "$REPORT/conformance.log" | tail -4
[ -f "$REPORT/conformance.json" ] && cp "$REPORT/conformance.json" "$ROOT/conformance.json"

echo "==> [8/9] regenerate specs against the new corpus"
# AUTOFORM_SPEC_EXCLUDE names subjects whose by-computation proofs do not terminate in the
# emission budget (`;`-separated); the report records them as excluded, not as proved.
# The render was regenerated by step 4 and is deliberately uncommitted (this script does
# not commit), so `synth_specs.py`'s pristine-subject check -- which exists to catch a
# mutation run in flight -- would refuse it. The cascade IS the legitimate regeneration.
"$PYTHON" -u scripts/synth_specs.py "ast-$MOD.json" "$SRC" "$MOD" \
  --conformance "$REPORT/conformance.json" --conformance-only \
  --domain "${AUTOFORM_CASES:-5}" --sample-subjects 0 --json "$REPORT/specs.json" \
  --allow-dirty-subject \
  ${AUTOFORM_SPEC_EXCLUDE:+--exclude-subjects "$AUTOFORM_SPEC_EXCLUDE"} \
  | tee "$REPORT/specs.log" | tail -5
lake build "Autoform.SpecsGen.$MOD" 2>&1 | tail -2
# check_specs_fresh binds each spec module to the AST digest it was generated from. The
# generated module was just regenerated against the new AST and the hand-written
# `Specs/<M>Spec.lean` was just rebuilt against it (step 6), so re-pinning here IS the
# documented case for --record; it prints the digest it overwrites.
"$PYTHON" scripts/check_specs_fresh.py --record --corpus "$MOD"

echo "==> [9/9] ledger"
sed "s/@MODULE@/$MOD/g" scripts/ledger.lean.tmpl > "$WORK/Ledger.lean"
lake env lean "$WORK/Ledger.lean"
cp "ledger-$MOD.json" "$REPORT/ledger-$MOD.json"

cat <<EOT

==> re-land of $MOD staged in the working tree. Before committing, still run:
      scripts/check_docs.py          # documented figures now quote the new ledger/conformance
      scripts/check_render.py        # 0 mismatched, and $MOD verified
      scripts/check_provenance.py    # repository-wide; other corpora may need re-landing
      scripts/audit_all.py --strict  # axiom sweep + leanchecker --fresh
      scripts/mutate.py Autoform/Generated/$MOD.lean Autoform.Generated.$MOD \\
        --spec-file Autoform/Specs/${MOD}Spec.lean --spec-module Autoform.Specs.${MOD}Spec
    and review, in the diff: which RELAND-annotated theorems broke and why, the hole-count
    delta (scripts/lang_matrix.py ast-$MOD.json), and the provenance record.
EOT
