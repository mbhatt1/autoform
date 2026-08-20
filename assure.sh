#!/usr/bin/env bash
# assure.sh — the full assurance pipeline over an arbitrary codebase.
#
#   ./assure.sh <source-dir> <ModuleName>
#
# autoform.sh gets you Lean. This gets you an *argued, evidenced claim* about that Lean,
# with the trust boundary stated explicitly. The distinction matters: the deliverable was
# never "your codebase is verified".
#
#   1. translate            source -> CPG -> Core -> Lean            (autoform.sh)
#   2. conformance          Lean interpreter vs the real runtime     (differential.py)
#   3. axiom + escape audit every declaration, every escape hatch    (audit_all.py)
#   4. specification teeth  mutation gate over the Lean theorems     (mutate.py)
#   5. contract registry    which theorems are conditional          (emit_contracts.py)
#   6. assurance case       SACM argument + in-toto attestation      (sacm.py)
#
# Steps 2-4 may legitimately FAIL — a divergence, a leaked axiom, a surviving mutant are
# all real findings. The pipeline records them and continues, because a suppressed finding
# is worse than a red build. Only step 5 decides whether the top claim is assertable.
set -uo pipefail

SRC="${1:?usage: assure.sh <source-dir> <ModuleName>}"
MOD="${2:?usage: assure.sh <source-dir> <ModuleName>}"
ROOT="$(cd "$(dirname "$0")" && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
cd "$ROOT"

hdr() { printf '\n\033[1m=== %s ===\033[0m\n' "$1"; }

hdr "1/5 translate"
JOERN_HOME="${JOERN_HOME:-$HOME/joern}" ./autoform.sh "$SRC" "$MOD" || echo "  translate: FAILED"

hdr "2/5 conformance vs real runtime"
python3 scripts/differential.py "ast-$MOD.json" "$SRC" "$MOD" 5 || echo "  conformance: divergences found (recorded)"

hdr "3/5 axiom + escape-hatch audit"
# The audit sweeps every declaration in the built library, so the WHOLE library must be
# built first. autoform.sh only builds the generated module; without this the sweep aborts
# on a missing .olean and reports FAIL for a reason that has nothing to do with soundness.
lake build >/dev/null 2>&1 || echo "  (library build failed; audit will report it)"
python3 scripts/audit_all.py || echo "  audit: findings recorded"

hdr "4/5 specification teeth (mutation gate)"
# Mutate the module under assurance, not the toy reference semantics. This step used to
# hardcode Autoform/Lang/Imp/Semantics.lean, so every assure.sh run produced G4 evidence
# about Imp regardless of the module named on the command line. sacm.py correctly capped
# that as off-subject, which meant the pipeline could never support G4 on its own.
if [ -f "$ROOT/Autoform/Specs/${MOD}Spec.lean" ]; then
  python3 scripts/mutate.py "Autoform/Generated/$MOD.lean" "Autoform.Generated.$MOD" \
    --max-mutants 8 || echo "  mutation: survivors recorded"
else
  echo "  no Autoform/Specs/${MOD}Spec.lean — G4 will be UNDEVELOPED for $MOD (correct)"
fi

hdr "5/5 assurance case"
# Contract-relative theorems must be emitted BEFORE the assurance case is built: if
# contracts-$MOD.json is absent, sacm.py simply omits the G.CONTRACT branch, and a
# conditional theorem that never reaches the case reads exactly like an unconditional
# one. A failure here is therefore not "|| true" -- it is a missing argument branch.
# The docs are part of the claim. A figure that was true when written and is false now
# is the same defect class as a metric computed from the artifact it describes -- and
# this repo had three documents quoting three different verifiable-core numbers, none
# current, because nothing checked.
python3 scripts/check_docs.py || true

python3 scripts/emit_contracts.py "$MOD"

python3 scripts/sacm.py --module "$MOD"
STATUS=$?

hdr "artifacts"
ls -1 formalization-graph.json "ast-$MOD.json" "ledger-$MOD.json" conformance.json \
       audit.json mutation.json "sacm-$MOD.json" 2>/dev/null

exit $STATUS
