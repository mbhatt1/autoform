#!/usr/bin/env bash
# Complete evidence collection, including a report when a stage cannot run.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
PYTHON="${AUTOFORM_PYTHON:-python3}"
if [ -z "${AUTOFORM_PYTHON:-}" ] && [ -x "$ROOT/.venv/bin/python" ]; then
  PYTHON="$ROOT/.venv/bin/python"
fi
exec "$PYTHON" "$ROOT/scripts/assure.py" "$@"
