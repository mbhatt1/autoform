#!/usr/bin/env bash
# autoform — point at any codebase Joern can parse, get Lean.
#
#   ./autoform.sh <source-dir> [ModuleName]
#
#   source ──Joern──▶ CPG ──▶ neutral JSON AST ──▶ Lean Core program ──▶ ledger
#                      │                                    │
#                      └─▶ formalization graph              └─▶ differential vs runtime
#
# Source frontends normalize syntax through Joern; dialect-specific coverage is limited.
# --machine uses a separate p-code interpreter for binary and assembly input.
set -euo pipefail

if [ "${1:-}" = "--help" ] || [ "${1:-}" = "-h" ]; then
  cat <<'USAGE'
Usage:
  ./autoform.sh <source-dir> [ModuleName]
  ./autoform.sh --machine <binary-or-assembly> [ModuleName] [options]
  ./autoform.sh --machine --list-languages

Source mode requires Joern and Lean. Machine mode uses requirements-machine.txt
and Lean. See docs/machine-code.md or ./autoform.sh --machine --help.
AUTOFORM_DATA_MODEL selects lp64 (default), llp64, ilp32, or unknown for source integers.
USAGE
  exit 0
fi

# Binary and assembly models use machine semantics rather than a guessed source dialect.
if [ "${1:-}" = "--machine" ]; then
  shift
  ROOT="$(cd "$(dirname "$0")" && pwd)"
  PYTHON="${AUTOFORM_PYTHON:-python3}"
  if [ -z "${AUTOFORM_PYTHON:-}" ] && [ -x "$ROOT/.venv/bin/python" ]; then
    PYTHON="$ROOT/.venv/bin/python"
  fi
  exec "$PYTHON" "$ROOT/scripts/formalize_machine.py" "$@"
fi

SRC="${1:?usage: autoform.sh <source-dir> [ModuleName]}"
MOD="${2:-Translated}"
ROOT="$(cd "$(dirname "$0")" && pwd)"
if [[ ! "$MOD" =~ ^[A-Z][A-Za-z0-9_]*$ ]]; then
  echo "ModuleName must be a Lean identifier beginning with an uppercase letter" >&2
  exit 2
fi
SRC="$(cd "$SRC" && pwd)"
JOERN="${JOERN_HOME:-$HOME/joern}"
if [ -d "$JOERN/joern-cli" ]; then JOERN="$JOERN/joern-cli"; fi
# Joern is a ~1.7 GB external prerequisite and by far the most likely thing to be
# missing on a first run. Without this check the pipeline gets as far as clone +
# inventory and then dies on a bare "No such file or directory" from the shell,
# which names a path the user never typed and suggests no remedy.
if [ ! -x "$JOERN/joern-parse" ]; then
  echo "autoform: no Joern frontend at $JOERN/joern-parse" >&2
  echo "  Joern is required to translate source code and is installed separately." >&2
  echo "  Set JOERN_HOME to an existing install, or see docs/running.md to install it." >&2
  echo "  Run 'autoform doctor' to check every prerequisite at once." >&2
  exit 2
fi
PYTHON="${AUTOFORM_PYTHON:-python3}"
if [ -z "${AUTOFORM_PYTHON:-}" ] && [ -x "$ROOT/.venv/bin/python" ]; then
  PYTHON="$ROOT/.venv/bin/python"
fi
if [[ "$PYTHON" == */* ]]; then
  PYTHON="$(cd "$(dirname "$PYTHON")" && pwd)/$(basename "$PYTHON")"
fi
REPORT="$ROOT/artifacts/pipeline/$MOD"
mkdir -p "$REPORT"
WORK="$(mktemp -d)"
STAGE=setup
export PYTHONUNBUFFERED=1
# Unconditional cleanup: `set -e` means any failing stage below (a `lake build`
# hitting a heartbeat/recDepth limit, an unresolved codebase, ...) exits the
# script immediately, and a plain trailing `rm -rf` at the bottom of the file is
# never reached on that path. Every failed run used to leak `$WORK`'s full CPG
# binary + exported AST JSON (measured on a real SQLite attempt: ~100-200 MB per
# leaked run) and Joern's own project cache under `$ROOT/workspace` forever.
finish() {
  local status=$?
  "$PYTHON" - "$REPORT" "$MOD" "$SRC" "$STAGE" "$status" <<'PY'
import datetime, json, pathlib, sys
report, module, source, stage, code = sys.argv[1:]
path = pathlib.Path(report) / "pipeline.json"
data = dict(module=module, source=source, stage=stage, exit_code=int(code),
            status="passed" if int(code) == 0 else "failed",
            finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
path.write_text(json.dumps(data, indent=2) + "\n")
PY
  rm -rf "$WORK"
}
trap finish EXIT
# Clear only reports produced by this pipeline, so an aborted run cannot leave
# yesterday's passing evidence under today's output paths.
"$PYTHON" - "$REPORT" "$MOD" "$SRC" <<'PY'
import json, pathlib, sys
report = pathlib.Path(sys.argv[1])
for name in ("conformance.json", "specs.json", "ledger.json", "audit.json",
             "core-oracle.json", "mutation.json", "assurance.md", "sacm.json",
             "native-build.json", "context.json", "frontend.json", "export.log",
             "ast-" + sys.argv[2] + ".json", "ledger-" + sys.argv[2] + ".json",
             "sacm-" + sys.argv[2] + ".json", "contracts-" + sys.argv[2] + ".json"):
    (report / name).unlink(missing_ok=True)
(report / "pipeline.json").write_text(json.dumps(dict(
    module=sys.argv[2], source=sys.argv[3], status="running", stage="setup")))
PY
export PATH="$HOME/.elan/bin:$PATH"
# `export_ast.sc`'s own comments are full of real prose punctuation (em-dashes,
# curly quotes). Joern's C frontend does not need a locale to run correctly,
# but the JVM's OWN source-file reads (compiling the script itself, and a
# separate "scan every .sc file for `using` directives" classpath step) fall
# back to the PLATFORM DEFAULT charset when none is set -- which is plain
# ASCII/POSIX on a bare container with no locale configured, Colab's own
# default runtime included. Reading any non-ASCII byte under that charset
# throws mid-file, corrupting the compiler's own view of everything after it
# and surfacing as a cascade of unrelated "Not found" errors from that point
# to the end of the file -- not a hint that anything in the source itself is
# wrong. Confirmed live: identical failure, same two line numbers, across
# four completely unrelated fixtures, on a Colab runtime that reproduced it
# after this session's own local sandbox (once it hit the identical failure
# earlier) could not, purely because the sandbox's own commands had been
# carrying `LANG=C.UTF-8` explicitly ever since -- a workaround on the
# CALLER's side, never fixed here, where every actual invocation needs it.
export LANG="${LANG:-C.UTF-8}"
export LC_ALL="${LC_ALL:-C.UTF-8}"
export JAVA_TOOL_OPTIONS="${JAVA_TOOL_OPTIONS:-} -Dfile.encoding=UTF-8"
cd "$ROOT"

# `009-reduce-remaining-holes-4`: `cartographer/run.sh`'s own `CPP_DEFINES`
# mechanism, ported here so `autoform.sh` (the pipeline this whole feature's
# own local sandbox testing runs, and what `notebooks/*.ipynb`'s
# `run_one_background` calls for the FULL corpus) has the SAME capability
# `run_one_chunked_background`'s own separate, inline joern-parse call
# already had -- this script had simply never been given it. For a C/C++
# tree, set CPP_DEFINES to a comma-separated list of names Joern's C frontend
# (which does not run the real preprocessor) should treat as defined --
# either bare (`SQLITE_TEST`, an `#ifdef`-guarded feature flag: without it,
# guarded code parses with its raw `.code` kept but ZERO ast children,
# reported honestly as `stmt:empty-ast-children`) or `NAME=VALUE` (a plain
# macro TOKEN substitution: `ALIGN128=`, `SQLITE_API=`, `SQLITE_EXTERN=extern`
# -- SQLite's own attribute/linkage macros, which the frontend cannot resolve
# at all without preprocessing and gives up on entirely, reported as
# `stmt:UNKNOWN:CASTProblemDeclaration`; a DIFFERENT failure mode from the
# `#ifdef` case, needing a value substitution rather than a bare presence
# flag). Empty by default: no behavior change for a codebase this does not
# apply to, or when the caller does not set it.
FRONTEND_ARGS=()
"$PYTHON" "$ROOT/scripts/source_context.py" "$SRC" "$REPORT/context.json" \
  --args-file "$WORK/frontend-args"
while IFS= read -r -d '' option; do FRONTEND_ARGS+=("$option"); done < "$WORK/frontend-args"
LANGUAGE_ARGS=()
if [ -n "${AUTOFORM_FRONTEND:-}" ]; then
  LANGUAGE_ARGS=(--language "$AUTOFORM_FRONTEND")
fi

STAGE=parse
echo "==> [1/8] parsing $SRC"
# Bash 3.2 (macOS) treats an empty array as unset under `set -u`. Expand it only
# when populated, without passing an empty argument to the frontend.
if ! (cd "$WORK" && "$JOERN/joern-parse" "$SRC" --output "$WORK/cpg.bin" ${LANGUAGE_ARGS[@]+"${LANGUAGE_ARGS[@]}"} ${FRONTEND_ARGS[@]+"${FRONTEND_ARGS[@]}"}) >"$REPORT/parse.log" 2>&1; then
  cat "$REPORT/parse.log" >&2
  exit 1
fi

STAGE=graph
echo "==> [2/8] cartographer: formalization graph"
if ! (cd "$WORK" && "$JOERN/joern" --script "$ROOT/cartographer/formalization_graph.sc" \
  --param cpgPath="$WORK/cpg.bin" --param out="$REPORT/formalization-graph.json") >"$REPORT/graph.log" 2>&1; then
  cat "$REPORT/graph.log" >&2
  exit 1
fi
cp "$REPORT/formalization-graph.json" "$ROOT/formalization-graph.json"

STAGE=export
echo "==> [3/8] transpiler: CPG -> neutral AST"
EXPORT_OUT="$(cd "$WORK" && "$JOERN/joern" --script "$ROOT/cartographer/export_ast.sc" \
  --param cpgPath="$WORK/cpg.bin" --param out="$WORK/ast.json" \
  --param dataModel="${AUTOFORM_DATA_MODEL:-lp64}" 2>&1)" && EXPORT_STATUS=0 || EXPORT_STATUS=$?
printf '%s\n' "$EXPORT_OUT" > "$REPORT/export.log"
if [ "$EXPORT_STATUS" -ne 0 ] || ! grep -qE "^exported" <<<"$EXPORT_OUT"; then
  echo "$EXPORT_OUT" >&2
  echo "==> [3/8] FAILED: export_ast.sc did not report success (see output above)" >&2
  exit 1
fi
grep -E "^exported" <<<"$EXPORT_OUT"
if [ -n "${AUTOFORM_LANGUAGE:-}" ]; then
  "$PYTHON" "$ROOT/scripts/repository_scope.py" "$WORK/ast.json" "$SRC" \
    "$AUTOFORM_LANGUAGE" "$REPORT/selection.json"
fi
cp "$WORK/ast.json" "$ROOT/ast-$MOD.json"
cp "$WORK/ast.json" "$REPORT/ast-$MOD.json"
if [ -f "$WORK/ast.json.meta.json" ]; then cp "$WORK/ast.json.meta.json" "$REPORT/frontend.json"; fi

# Attribute the AST to the frontend and exporter that produced it. Until this ran,
# every AST this pipeline emitted was unattributed -- `provenance/` held a single
# `unattributed.json` -- even though `provenance.py record` already captured exactly
# the two fields that matter: `joern_version` (the neutral AST is a function of the
# frontend build) and `exporter_sha256` (an exporter change silently alters the AST
# for reasons unrelated to the source; the `'0'`-is-48 fix is a live example).
# docs/architecture.md has prescribed this call since the provenance work landed.
#
# Deliberately NOT fatal, and deliberately not `joern-version --check`: an analysis
# run must not be refused because the installed Joern differs from the pin. The pin
# is enforced where a user asks for a verdict -- `autoform doctor` returns 1 on a
# mismatch -- while here a mismatch is recorded and announced, so the artifact still
# says which frontend made it.
if ! "$PYTHON" "$ROOT/scripts/provenance.py" record \
      --artifact "$ROOT/ast-$MOD.json" --source "$SRC" \
      --exporter cartographer/export_ast.sc \
      --command "autoform.sh $MOD" >"$REPORT/provenance.log" 2>&1; then
  echo "==> [3/8] WARNING: AST is unattributed (see $REPORT/provenance.log)" >&2
  sed -n '1,3p' "$REPORT/provenance.log" >&2 || true
fi

STAGE=render
echo "==> [4/8] rendering Lean"
"$PYTHON" "$ROOT/cartographer/render_lean.py" "$WORK/ast.json" \
  "$ROOT/Autoform/Generated/$MOD.lean" "$MOD"

STAGE=build
echo "==> [5/8] type-checking generated Lean"
lake build Autoform.Runtime "Autoform.Generated.$MOD"

STAGE=runtime
echo "==> [6/8] differential conformance vs the real runtime"
CONFORMANCE_STATUS=0
(cd "$REPORT" && "$PYTHON" "$ROOT/scripts/differential.py" "$ROOT/ast-$MOD.json" "$SRC" "$MOD" "${AUTOFORM_CASES:-5}") \
  >"$REPORT/conformance.log" 2>&1 || CONFORMANCE_STATUS=$?
cat "$REPORT/conformance.log"
if [ -f "$REPORT/conformance.json" ]; then
  cp "$REPORT/conformance.json" "$ROOT/conformance.json"
fi

STAGE=ledger
echo "==> [7/8] coverage ledger"
sed "s/@MODULE@/$MOD/g" "$ROOT/scripts/ledger.lean.tmpl" > "$WORK/Ledger.lean"
lake env lean "$WORK/Ledger.lean"
cp "$ROOT/ledger-$MOD.json" "$REPORT/ledger.json"
cp "$ROOT/ledger-$MOD.json" "$REPORT/ledger-$MOD.json"
if [ "$CONFORMANCE_STATUS" -eq 0 ]; then
  STAGE=proofs
  echo "==> [8/8] proving native runtime observations"
  "$PYTHON" -u "$ROOT/scripts/synth_specs.py" "$ROOT/ast-$MOD.json" "$SRC" "$MOD" \
    --conformance "$REPORT/conformance.json" --conformance-only \
    --domain "${AUTOFORM_CASES:-5}" --sample-subjects 0 --json "$REPORT/specs.json" \
    >"$REPORT/specs.log" 2>&1 || { cat "$REPORT/specs.log" >&2; exit 1; }
  cat "$REPORT/specs.log"
  lake build "Autoform.SpecsGen.$MOD"
fi
if [ "$CONFORMANCE_STATUS" -eq 0 ]; then STAGE=complete; else STAGE=runtime; fi
echo "==> evidence: $REPORT"
exit "$CONFORMANCE_STATUS"
