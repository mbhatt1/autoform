#!/usr/bin/env bash
# Build SpecsGen/V8Base/Part<FROM>..Part<TO> one at a time, in order.
#
#   scripts/ci_build_v8base_parts.sh 1 15
#
# Why not just `lake build`: each heavy V8Base part is an `rfl`-by-computation file with a
# large memory peak. Measured with one `lean` process alone (peak resident set, includes the
# mapped .olean pages): Part60 8.7 GB in 575 s, Part33 6.6 GB in 325 s (STRATEGY.md section
# 67). Lake 5.0 has no job-limit flag, so it starts as many parts at once as there are
# workers, and a hosted runner's memory runs out partway through the heavy parts: the runner
# was shut down (exit 143) in runs 115 and 117. Locally, three heavy parts at once killed 18
# of 73 parts with exit 137 on a 15 GB box; all 18 built when run one at a time. One part at
# a time is the only setting that fits a 16 GB runner, and the peaks above are why it would
# not fit a 7 GB one: the "Runner resources" step in ci.yml prints what the runner has.
set -euo pipefail

from=${1:?usage: ci_build_v8base_parts.sh FROM TO}
to=${2:?usage: ci_build_v8base_parts.sh FROM TO}

for n in $(seq "$from" "$to"); do
  start=$(date +%s)
  echo "::group::SpecsGen.V8Base.Part$n"
  awk '/MemAvailable/ {printf "MemAvailable before Part'"$n"': %d MB\n", $2/1024}' /proc/meminfo
  lake build "Autoform.SpecsGen.V8Base.Part$n"
  echo "::endgroup::"
  echo "Part$n: $(( $(date +%s) - start )) s"
done
