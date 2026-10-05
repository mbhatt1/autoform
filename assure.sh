#!/usr/bin/env bash
# Compatibility entry point. The Python CLI owns assurance orchestration.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
GLOBAL=()
POSITIONAL=()
while [ "$#" -gt 0 ]; do
  case "$1" in
    --json|--dry-run|--keep-work)
      GLOBAL+=("$1"); shift ;;
    --config|--repo-root|--joern-home|--cpp-defines|--run-id|--artifact-dir)
      GLOBAL+=("$1" "${2:?$1 requires a value}"); shift 2 ;;
    --version|-h|--help)
      GLOBAL+=("$1"); shift ;;
    *)
      POSITIONAL+=("$1"); shift ;;
  esac
done
CMD=(python3 -m autoform_cli)
if [ "${#GLOBAL[@]}" -gt 0 ]; then
  CMD+=("${GLOBAL[@]}")
fi
CMD+=(assure)
if [ "${#POSITIONAL[@]}" -gt 0 ]; then
  CMD+=("${POSITIONAL[@]}")
fi
exec "${CMD[@]}"
