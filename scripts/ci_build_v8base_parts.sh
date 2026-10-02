#!/usr/bin/env bash
# Build SpecsGen/V8Base/Part<FROM>..Part<TO> one at a time, in order.
#
#   scripts/ci_build_v8base_parts.sh 1 15
#
# Why not just `lake build`: each heavy V8Base part is an `rfl`-by-computation file that
# holds about 4 GB while it elaborates (measured: see STRATEGY.md section 67), and Lake 5.0
# has no job-limit flag, so it starts as many parts at once as there are free workers. On a
# hosted runner that exhausted memory partway through the heavy parts and the runner was
# shut down (exit 143) -- twice, at 108 minutes (run 115) and at 20 minutes into a run that
# had restored 427 modules from the cache (run 117). Locally, three heavy parts at once
# killed 18 of 73 parts with exit 137 on a 15 GB box; all 18 built when run one at a time.
# One part at a time is the only setting that fits the smallest runner.
set -euo pipefail

from=${1:?usage: ci_build_v8base_parts.sh FROM TO}
to=${2:?usage: ci_build_v8base_parts.sh FROM TO}

for n in $(seq "$from" "$to"); do
  start=$(date +%s)
  echo "::group::SpecsGen.V8Base.Part$n"
  lake build "Autoform.SpecsGen.V8Base.Part$n"
  echo "::endgroup::"
  echo "Part$n: $(( $(date +%s) - start )) s"
done
