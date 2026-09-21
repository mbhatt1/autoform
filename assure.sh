#!/usr/bin/env bash
# Complete evidence collection, including a report when a stage cannot run.
#
#   ./assure.sh <source-dir> <ModuleName> [--properties FILE] [--stage-timeout SECONDS]
#
# Exit status (docs/running.md §7): 0 every required check completed; 1 the workflow
# finished with unresolved verification gaps (`completed_with_gaps` in run.json --
# read it beside guarantee.json, a scoped certificate can coexist with this); 2 an
# invocation, setup or orchestration failure, or a refused run (see below); 128+N
# interrupted by signal N.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
if [ "${1:-}" = "--help" ] || [ "${1:-}" = "-h" ]; then
  sed -n '2,10p' "$0" | sed 's/^# \{0,1\}//'
  exit 0
fi
PYTHON="${AUTOFORM_PYTHON:-python3}"
if [ -z "${AUTOFORM_PYTHON:-}" ] && [ -x "$ROOT/.venv/bin/python" ]; then
  PYTHON="$ROOT/.venv/bin/python"
fi
# Same refusal as autoform.sh: never collect evidence over a live mutant or a
# modified tracked artifact (docs/integrity.md, "Concurrency"). The module is the
# second positional argument; `assure.py` validates it properly afterwards.
# shellcheck source=scripts/integrity_guard.sh
. "$ROOT/scripts/integrity_guard.sh"
autoform_integrity_guard "$ROOT" "${2:-}" || exit $?
exec "$PYTHON" "$ROOT/scripts/assure.py" "$@"
