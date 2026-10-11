#!/usr/bin/env bash
# rust_setup.sh AENEAS_HOME DIR -- create the scratch Lake project the Rust path needs.
#
# The Aeneas Lean library pins its own Lean (rust-pins.json: lean_toolchain) and mathlib,
# which differ from Autoform's, so it lives in a SEPARATE Lake project; Autoform's
# lean-toolchain and lakefile are never touched. DIR is a copy of the release's
# backends/lean with its lake-manifest.json as shipped (no `lake update`: the manifest is
# the pin). The mathlib cache is downloaded, then the Aeneas library is built (Lake fetches
# the release's prebuilt archive when one matches the platform).
#
# Afterwards: export AUTOFORM_RUST_LEAN_PROJECT=DIR (docs/rust.md).
set -euo pipefail
if [ $# -ne 2 ]; then
  echo "usage: $0 AENEAS_HOME DIR" >&2
  exit 2
fi
home=$1
dir=$2
if [ ! -f "$home/backends/lean/lakefile.lean" ]; then
  echo "rust_setup: $home/backends/lean/lakefile.lean not found; AENEAS_HOME must be the unpacked Aeneas release" >&2
  exit 2
fi
if [ -e "$dir" ] && [ ! -f "$dir/lakefile.lean" ]; then
  echo "rust_setup: $dir exists and is not a Lake project; choose another directory" >&2
  exit 2
fi
if [ ! -e "$dir" ]; then
  mkdir -p "$(dirname "$dir")"
  cp -R "$home/backends/lean" "$dir"
fi
if ! cmp -s "$home/backends/lean/lake-manifest.json" "$dir/lake-manifest.json"; then
  echo "rust_setup: $dir/lake-manifest.json differs from the release's; refusing to mix pins" >&2
  exit 2
fi
cd "$dir"
echo "rust_setup: lean toolchain $(cat lean-toolchain)"
lake exe cache get
lake build Aeneas
echo "rust_setup: ready. export AUTOFORM_RUST_LEAN_PROJECT=$(pwd)"
