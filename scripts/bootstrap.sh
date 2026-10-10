#!/usr/bin/env bash
# scripts/bootstrap.sh — a fresh clone to `VERDICT: PASS` in one command.
#
#   git clone <this repository> autoform && cd autoform && scripts/bootstrap.sh
#
# What it does, in order, each step announced and each failure fatal (roadmap 0.2):
#
#   1. host     : names the OS/arch and every prerequisite it will NOT install for you
#   2. elan     : installs elan if absent and the toolchain pinned in `lean-toolchain`
#   3. python   : a `.venv` on the first interpreter >= 3.10 it finds, with requirements.txt
#   4. joern    : the release pinned in `joern-version`, verified by sha512 before unzip,
#                 then checked against the jars on disk (scripts/provenance.py)
#   5. build    : the CI closure, with the memory sequencing ci.yml uses — the two ~13 GB
#                 cachetools modules one at a time, then `Autoform.CI`
#   6. corpus   : the cachetools sources at the commit ast-Cachetools.json was exported from
#   7. oracle   : the conformance oracle must COMPARE something (CI: "oracle is alive")
#   8. audit    : `scripts/audit_all.py --strict` must print `VERDICT: PASS`
#   9. tree     : `git status` is reported; a clean tree is the roadmap 0.3 exit
#
# Idempotent: a second run re-checks every step and rebuilds only what changed.
# Nothing is skipped silently. Anything this host cannot do is named in the output
# (for example `taskset` does not exist on macOS, so the three builds run one after
# another instead of pinned to a core; a JDK is never installed).
#
# Tested: macOS 26 arm64, 2026-10-10 (log attached to the roadmap item).
# NOT tested: Ubuntu. The Linux branches are transcribed from .github/workflows/ci.yml,
# which is what runs on ubuntu-latest, but this script itself has not been run there.
#
# Environment (all optional):
#   AUTOFORM_PYTHON             interpreter for the venv (default: python3.12, 3.11, 3.13, python3)
#   JOERN_HOME                  where Joern lives / is installed (default: ~/joern)
#   AUTOFORM_CACHETOOLS_DIR     where the corpus is cloned (default: /tmp/cachetools, as CI)
#   AUTOFORM_BOOTSTRAP_ROOT     Autoform.CI (default, what CI proves) or Autoform (the whole
#                               project incl. SpecsGen.V8Base: ~25 GB peak, release checklist)
#
# Exit status: 0 only when every step ran and the audit printed VERDICT: PASS.
set -Eeuo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

STEP=start
T0=$(date +%s)
NOTES=()        # things this host could not do the CI way; printed in the summary

say()  { printf '\n==> [%s] %s\n' "$STEP" "$*"; }
note() { NOTES+=("$*"); printf 'bootstrap: NOTE: %s\n' "$*"; }
die()  { printf 'bootstrap: FAILED at step %s: %s\n' "$STEP" "$*" >&2; exit 1; }
on_err() {
  local code=$?
  printf '\nbootstrap: FAILED at step %s (exit %d) after %ds\n' "$STEP" "$code" "$(( $(date +%s) - T0 ))" >&2
  exit "$code"
}
trap on_err ERR

# --------------------------------------------------------------------------- #
STEP=1/9-host
say "host"
OS="$(uname -s)"; ARCH="$(uname -m)"
case "$OS" in
  Darwin) OS_NAME=macos ;;
  Linux)  OS_NAME=linux ;;
  *) die "unsupported OS '$OS' (macOS and Linux only; see docs/running.md)" ;;
esac
case "$ARCH" in
  arm64|aarch64) JOERN_ARCH=arm64 ;;
  x86_64|amd64)  JOERN_ARCH=x86_64 ;;
  *) die "unsupported architecture '$ARCH' (Joern ships linux/macos x86_64 and arm64 only)" ;;
esac
echo "os=$OS_NAME arch=$ARCH root=$ROOT"
for tool in git curl unzip; do
  command -v "$tool" >/dev/null || die "'$tool' is required and not on PATH"
done
if command -v sha512sum >/dev/null; then
  SHA512_CHECK=(sha512sum -c)
elif command -v shasum >/dev/null; then
  SHA512_CHECK=(shasum -a 512 -c)
else
  die "neither sha512sum nor shasum is available; the Joern download cannot be verified"
fi
# Joern needs a JDK (CI installs temurin 21). This script never installs one: say so.
if command -v java >/dev/null; then
  echo "java: $(java -version 2>&1 | head -1)"
else
  die "no 'java' on PATH. Joern needs a JDK (CI uses temurin 21); install one and re-run. This script does not install a JDK."
fi
if [ "$OS_NAME" = linux ]; then
  command -v taskset >/dev/null || die "'taskset' (util-linux) is required on Linux: it is how CI keeps the build under the memory ceiling"
else
  note "taskset does not exist on $OS_NAME: the three builds run one after another instead of pinned to one core"
fi
ROOT_MODULE="${AUTOFORM_BOOTSTRAP_ROOT:-Autoform.CI}"
case "$ROOT_MODULE" in
  Autoform.CI|Autoform) ;;
  *) die "AUTOFORM_BOOTSTRAP_ROOT must be Autoform.CI or Autoform, not '$ROOT_MODULE'" ;;
esac
echo "root module: $ROOT_MODULE"

# --------------------------------------------------------------------------- #
STEP=2/9-elan
PIN="$(cat lean-toolchain)"
say "Lean toolchain $PIN via elan"
export PATH="$HOME/.elan/bin:$PATH"
if command -v elan >/dev/null; then
  echo "elan already installed: $(elan --version)"
else
  echo "installing elan into $HOME/.elan (PATH is not modified; this script exports it)"
  tmp_elan="$(mktemp -d)"
  curl -sSfL --retry 5 --retry-all-errors https://elan.lean-lang.org/elan-init.sh -o "$tmp_elan/elan-init.sh"
  sh "$tmp_elan/elan-init.sh" -y --no-modify-path --default-toolchain "$PIN"
  rm -rf "$tmp_elan"
  command -v elan >/dev/null || die "elan-init.sh exited 0 but $HOME/.elan/bin/elan is not there"
fi
# elan defers the toolchain download to the first `lean` call (ci.yml); fetch it here
# and retry, so a transient TLS failure is retried instead of killing the build later.
for attempt in 1 2 3 4 5; do
  if elan run "$PIN" lean --version; then break; fi
  [ "$attempt" = 5 ] && die "toolchain $PIN could not be fetched after 5 attempts"
  sleep $((attempt * 30))
done
# `lake`/`lean` in this directory must resolve to the pin (elan reads lean-toolchain).
lean_ver="$(lean --version)"
PIN_VER="${PIN#*:}"; PIN_VER="${PIN_VER#v}"     # leanprover/lean4:v4.30.0-rc1 -> 4.30.0-rc1
case "$lean_ver" in
  *"$PIN_VER"*) echo "lean: $lean_ver" ;;
  *) die "'lean --version' in $ROOT reports '$lean_ver', not the pinned $PIN_VER" ;;
esac
lake --version
# The independent kernel replay ships with the toolchain (v4.28.0+). If it is missing the
# audit below would report UNVERIFIED and --strict would fail; better to know here.
command -v leanchecker >/dev/null || die "'leanchecker' is not on PATH; it ships with toolchain $PIN"

# --------------------------------------------------------------------------- #
STEP=3/9-python
say "Python environment (.venv)"
py_ok() { "$1" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 10) else 1)' 2>/dev/null; }
# A venv is only usable if its interpreter starts and has pip. A uv-managed CPython
# reached through ~/.local/bin makes a venv whose python cannot even find `encodings`,
# so the only honest probe is to make one and run it.
make_venv() {  # interpreter -> 0 when .venv works
  rm -rf .venv
  "$1" -m venv .venv >/dev/null 2>&1 || return 1
  .venv/bin/python -c 'import sys, encodings' >/dev/null 2>&1 || return 1
  .venv/bin/python -m pip --version >/dev/null 2>&1 || return 1
}
if [ -x .venv/bin/python ] && py_ok .venv/bin/python && .venv/bin/python -m pip --version >/dev/null 2>&1; then
  echo ".venv already present: $(.venv/bin/python --version)"
elif [ -n "${AUTOFORM_PYTHON:-}" ]; then
  py_ok "$AUTOFORM_PYTHON" || die "AUTOFORM_PYTHON=$AUTOFORM_PYTHON is not a Python >= 3.10"
  make_venv "$AUTOFORM_PYTHON" || die "AUTOFORM_PYTHON=$AUTOFORM_PYTHON cannot create a working venv (python or pip does not start inside it)"
  echo "created .venv from AUTOFORM_PYTHON=$AUTOFORM_PYTHON ($(.venv/bin/python --version))"
else
  chosen=
  for cand in python3.12 python3.11 python3.13 python3; do
    path="$(command -v "$cand" 2>/dev/null)" || { echo "  $cand: not on PATH"; continue; }
    py_ok "$path" || { echo "  $path: older than 3.10, skipped"; continue; }
    if make_venv "$path"; then chosen="$path"; break; fi
    echo "  $path: cannot create a working venv (python or pip does not start inside it), skipped"
  done
  [ -n "$chosen" ] || die "no Python >= 3.10 on PATH can create a working venv (tried python3.12, python3.11, python3.13, python3). Install one (python.org, Homebrew, apt) or set AUTOFORM_PYTHON."
  echo "created .venv from $chosen ($(.venv/bin/python --version))"
fi
PY="$ROOT/.venv/bin/python"
"$PY" -m pip install --quiet --upgrade pip
"$PY" -m pip install --quiet pytest -r requirements.txt
"$PY" -c 'import hypothesis, pytest' || die "requirements did not import after install"
echo "python: $("$PY" --version) at $PY"

# --------------------------------------------------------------------------- #
STEP=4/9-joern
JOERN_PIN="$(cat joern-version)"
export JOERN_HOME="${JOERN_HOME:-$HOME/joern}"
say "Joern $JOERN_PIN in $JOERN_HOME"
if "$PY" scripts/provenance.py joern-version --check; then
  echo "Joern already installed and matches the pin"
elif [ -d "$JOERN_HOME/joern-cli" ]; then
  die "$JOERN_HOME/joern-cli exists but does not match the pin ($JOERN_PIN). Not overwriting someone's install: remove it, or point JOERN_HOME at an empty directory, and re-run."
else
  ASSET="joern-cli-${OS_NAME}-${JOERN_ARCH}.zip"
  URL="https://github.com/joernio/joern/releases/download/v${JOERN_PIN}"
  dl="$(mktemp -d)"
  # The .sha512 manifest names the zip as target/<asset>, so it is fetched there (ci.yml).
  mkdir -p "$dl/target" "$JOERN_HOME"
  echo "downloading $URL/$ASSET (about 1.7 GB)"
  # -sS: no progress meter (a logged run is otherwise 60 KB of carriage returns), errors still shown.
  curl -sSfL --retry 5 --retry-all-errors "$URL/$ASSET" -o "$dl/target/$ASSET"
  curl -sSfL --retry 5 --retry-all-errors "$URL/$ASSET.sha512" -o "$dl/$ASSET.sha512"
  (cd "$dl" && "${SHA512_CHECK[@]}" "$ASSET.sha512") || die "sha512 of $ASSET does not match the release manifest"
  unzip -q "$dl/target/$ASSET" -d "$JOERN_HOME"
  rm -rf "$dl"
  # Reads the version out of the jar names on disk: catches an unzip that "worked"
  # but left no distribution behind.
  "$PY" scripts/provenance.py joern-version --check || die "installed Joern does not match the pin after install"
fi
[ -x "$JOERN_HOME/joern-cli/joern-parse" ] || die "$JOERN_HOME/joern-cli/joern-parse is missing or not executable"

# --------------------------------------------------------------------------- #
STEP=5/9-build
say "lake build ($ROOT_MODULE closure, CI memory sequencing)"
# ci.yml: `Autoform.SpecsGen.Cachetools` and `Autoform.Specs.CachetoolsSpec` elaborate at
# ~13 GB each and are independent, so Lake would schedule them together; one at a time
# each fits. On Linux CI additionally pins the whole process tree to one core with
# `taskset -c 0` (Lake has no jobs flag in this version); there is no taskset on macOS.
build() {
  if [ "$OS_NAME" = linux ]; then taskset -c 0 lake build "$@"; else lake build "$@"; fi
}
if [ "$ROOT_MODULE" = Autoform ]; then
  # `Autoform.lean` imports `Autoform.SpecsGen.V8Base`, which needs the gitignored render
  # of the tracked AST (docs/integrity.md, "Build and replay scope"); CI regenerates it.
  "$PY" cartographer/render_lean.py ast-V8Base.json Autoform/Generated/V8Base.lean V8Base
  test -s Autoform/Generated/V8Base.lean || die "render of ast-V8Base.json is empty"
  note "AUTOFORM_BOOTSTRAP_ROOT=Autoform builds the V8Base parts too; CI does not (they exceed its runner), and this path was not exercised when the script was written"
fi
echo "--- lake build Autoform.SpecsGen.Cachetools"
build Autoform.SpecsGen.Cachetools
echo "--- lake build Autoform.Specs.CachetoolsSpec"
build Autoform.Specs.CachetoolsSpec
echo "--- lake build $ROOT_MODULE"
build "$ROOT_MODULE"
olean=".lake/build/lib/lean/${ROOT_MODULE//.//}.olean"
test -s "$olean" || die "lake build exited 0 but $olean does not exist"

# --------------------------------------------------------------------------- #
STEP=6/9-corpus
CORPUS="${AUTOFORM_CACHETOOLS_DIR:-/tmp/cachetools}"
CORPUS_REV=01af8e5
say "cachetools corpus at $CORPUS_REV in $CORPUS"
# PINNED (ci.yml): ast-Cachetools.json was exported from this commit; the coverage
# denominator comes from tracing this commit's own tests. Re-pin and re-export together.
have_corpus=0
if [ -d "$CORPUS/.git" ] \
   && [ "$(git -C "$CORPUS" rev-parse --short=7 HEAD 2>/dev/null)" = "$CORPUS_REV" ] \
   && [ -z "$(git -C "$CORPUS" status --porcelain 2>/dev/null)" ]; then
  have_corpus=1
  echo "corpus already present at $CORPUS_REV and clean; reusing it"
fi
if [ "$have_corpus" = 0 ]; then
  rm -rf "$CORPUS"
  git clone --no-checkout https://github.com/tkem/cachetools "$CORPUS"
  git -C "$CORPUS" checkout -q "$CORPUS_REV"
fi
test -d "$CORPUS/src" || die "$CORPUS/src is missing; the clone did not produce the corpus"
# Bundled Cachetools notice matches the pinned upstream revision (ci.yml).
"$PY" - "$CORPUS" <<'PY'
from pathlib import Path
import subprocess, sys
corpus = sys.argv[1]
upstream = Path(corpus, 'LICENSE').read_text()
bundled = Path('licenses/cachetools-MIT.txt').read_text()
if upstream.split() != bundled.split():
    raise SystemExit('Bundled Cachetools notice differs from pinned upstream; review the original license before release.')
print('License matched at', subprocess.check_output(['git', '-C', corpus, 'rev-parse', 'HEAD'], text=True).strip())
PY

# --------------------------------------------------------------------------- #
STEP=7/9-oracle
say "conformance oracle is alive (compared > 0)"
# The only check that compares the semantics to a real runtime. It once reported every
# case INCONCLUSIVE for weeks while every gate stayed green (ci.yml); so the test is not
# the agreement rate but that it decided anything at all.
conf_log="$(mktemp)"
PYTHONHASHSEED=0 AUTOFORM_NO_REEXEC=1 "$PY" scripts/differential.py \
  ast-Cachetools.json "$CORPUS" Cachetools 5 | tee "$conf_log"
compared=$(sed -n 's/.*, \([0-9]*\) COMPARED .*/\1/p' "$conf_log" | head -1)
rm -f "$conf_log"
echo "compared=${compared:-0}"
if [ "${compared:-0}" -eq 0 ]; then
  die "the conformance oracle compared 0 cases: it is not deciding anything, which is indistinguishable from agreeing about everything"
fi

# --------------------------------------------------------------------------- #
STEP=8/9-audit
say "trust audit: scripts/audit_all.py --strict --module $ROOT_MODULE"
audit_log="$(mktemp)"
"$PY" scripts/audit_all.py --strict --module "$ROOT_MODULE" | tee "$audit_log"
grep -q '^VERDICT: PASS' "$audit_log" || { rm -f "$audit_log"; die "audit did not print VERDICT: PASS (see audit.json)"; }
rm -f "$audit_log"

# --------------------------------------------------------------------------- #
STEP=9/9-tree
say "working tree after the run"
dirty="$(git status --porcelain)"
if [ -z "$dirty" ]; then
  echo "git status: clean"
else
  # Not a bootstrap failure on a developer's checkout, but never silent: on a fresh clone
  # anything listed here is a product that escaped .gitignore (roadmap 0.3).
  echo "git status: NOT clean. Files a run left behind or that you changed:"
  printf '  %s\n' "$dirty"
  note "git status is not clean after the run (listed above)"
fi

# --------------------------------------------------------------------------- #
STEP=done
elapsed=$(( $(date +%s) - T0 ))
printf '\n==> bootstrap: PASS in %dm%02ds (root module %s, os %s/%s)\n' $((elapsed / 60)) $((elapsed % 60)) "$ROOT_MODULE" "$OS_NAME" "$ARCH"
echo "toolchain $PIN, joern $JOERN_PIN at $JOERN_HOME, python $("$PY" --version 2>&1) at .venv, corpus $CORPUS"
if [ "${#NOTES[@]}" -gt 0 ]; then
  echo "what this host did differently from CI, or could not do:"
  printf '  - %s\n' "${NOTES[@]}"
fi
echo 'add to your shell: export PATH="$HOME/.elan/bin:$PATH"'
