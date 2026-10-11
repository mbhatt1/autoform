#!/usr/bin/env bash
# release_check.sh -- the preconditions for cutting a release, checked, then the exact
# commands printed. It never tags, releases or uploads anything.
#
# Fails (exit 1) unless ALL of these hold:
#   1. the working tree is clean (no modified, staged or untracked files);
#   2. pyproject.toml, src/autoform/__init__.py and the top CHANGELOG.md section agree
#      on one version, and the tag v<version> does not exist locally or on origin;
#   3. every required workflow has a SUCCESSFUL run on exactly this HEAD (`gh run list`);
#   4. that version is not already on PyPI (a published version can never be replaced).
# Exit 2: a tool the check needs (git, gh, curl, python3) is missing or a lookup failed
# in a way that does not answer the question (network error is not "not on PyPI").
#
# Usage: scripts/release_check.sh [--repo OWNER/REPO]   (default: the origin remote's repo)
set -uo pipefail

cd "$(git rev-parse --show-toplevel)" || exit 2
REQUIRED_WORKFLOWS=("ci.yml" "package.yml" "source.yml" "machine.yml")
PKG="autoform-lean"
REPO=""
while [ $# -gt 0 ]; do
  case "$1" in
    --repo) REPO="${2:-}"; shift 2 ;;
    *) echo "usage: $0 [--repo OWNER/REPO]" >&2; exit 2 ;;
  esac
done

fail=0
bad() { echo "FAIL: $*" >&2; fail=1; }
ok()  { echo "ok:   $*"; }
need() { command -v "$1" >/dev/null 2>&1 || { echo "ERROR: $1 is required" >&2; exit 2; }; }
for tool in git gh curl python3; do need "$tool"; done

# 1. clean tree
dirty="$(git status --porcelain)"
if [ -n "$dirty" ]; then bad "working tree is not clean:"; echo "$dirty" | sed 's/^/        /' >&2; else ok "working tree clean"; fi

# 2. one version everywhere
version="$(python3 - <<'PY'
import re, pathlib
t = pathlib.Path("pyproject.toml").read_text()
m = re.search(r'(?m)^version\s*=\s*"([^"]+)"', t)
print(m.group(1) if m else "")
PY
)"
init_version="$(sed -n 's/^__version__ *= *"\([^"]*\)".*/\1/p' src/autoform/__init__.py | head -1)"
changelog_version="$(sed -n 's/^## \[\([^]]*\)\].*/\1/p' CHANGELOG.md | head -1)"
if [ -z "$version" ]; then bad "no version in pyproject.toml"; fi
[ "$version" = "$init_version" ] && ok "pyproject.toml == src/autoform/__init__.py ($version)" \
  || bad "pyproject.toml says '$version' but src/autoform/__init__.py says '$init_version'"
[ "$version" = "$changelog_version" ] && ok "top CHANGELOG.md section is [$version]" \
  || bad "top CHANGELOG.md section is [$changelog_version], not [$version]"
tag="v$version"
if git rev-parse -q --verify "refs/tags/$tag" >/dev/null; then bad "tag $tag already exists locally"; fi
if remote_tag="$(git ls-remote --tags origin "refs/tags/$tag" 2>&1)"; then
  [ -n "$remote_tag" ] && bad "tag $tag already exists on origin"
else
  echo "ERROR: could not query origin for tags: $remote_tag" >&2; exit 2
fi

# 3. CI green on HEAD
head_sha="$(git rev-parse HEAD)"
repo_args=()
[ -n "$REPO" ] && repo_args=(--repo "$REPO")
for wf in "${REQUIRED_WORKFLOWS[@]}"; do
  if ! out="$(gh run list ${repo_args[@]+"${repo_args[@]}"} --workflow "$wf" --commit "$head_sha" --limit 20 \
                --json conclusion,status,headSha --jq \
                '[.[] | select(.status=="completed")] | if length==0 then "none" else (.[0].conclusion) end' 2>&1)"; then
    echo "ERROR: gh run list failed for $wf: $out" >&2; exit 2
  fi
  case "$out" in
    success) ok "$wf: latest completed run on ${head_sha:0:10} succeeded" ;;
    none)    bad "$wf: no completed run on HEAD ${head_sha:0:10} (push it and wait, or the run is still in progress)" ;;
    *)       bad "$wf: latest completed run on HEAD ${head_sha:0:10} concluded '$out'" ;;
  esac
done

# 4. not on PyPI
if [ -n "$version" ]; then
  code="$(curl -s -o /dev/null -w '%{http_code}' --max-time 30 "https://pypi.org/pypi/$PKG/$version/json" || true)"
  case "$code" in
    404) ok "$PKG $version is not on PyPI" ;;
    200) bad "$PKG $version is already on PyPI; a version cannot be re-uploaded -- bump it" ;;
    *)   echo "ERROR: PyPI lookup returned '$code'; cannot tell whether $version is published" >&2; exit 2 ;;
  esac
fi

if [ "$fail" != 0 ]; then
  echo "release_check: NOT READY" >&2
  exit 1
fi

cat <<EOT

release_check: READY. Nothing was tagged, released or uploaded.
The commands below are printed, not run. Running them publishes $PKG $version to PyPI
through the package workflow's trusted-publisher job, and cannot be undone.

  git tag -a $tag -m "autoform $version" $head_sha
  git push origin $tag
  gh release create $tag --verify-tag --title "autoform $version" \
      --notes "See the [$version] section of CHANGELOG.md."

Publishing happens when the release is published: .github/workflows/package.yml re-runs
every gate, then attaches the CycloneDX SBOM, attests the build provenance, and uploads to PyPI.
EOT
