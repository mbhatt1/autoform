#!/usr/bin/env bash
# sqlite_corpus.sh — reproducible parse setup for the full SQLite source tree.
#
#   scripts/sqlite_corpus.sh <sqlite-src> <outdir> [gen|parse|export|all]
#
# The SQLite checkout (github.com/sqlite/sqlite) does not contain `sqlite3.h`: the build
# generates it from `src/sqlite.h.in` with `tool/mksqlite3h.tcl`. Every `sqliteInt.h`
# translation unit includes it, so without it Joern sees `sqlite3_int64`, `sqlite3_value`
# and friends as unknown types, and the exporter (correctly) holes the casts and `sizeof`s
# that mention them. This script produces the header the real build would, and parses the
# tree with it:
#
#   gen     copy <sqlite-src> to <outdir>/tree (minus .git) and generate
#           <outdir>/tree/src/sqlite3.h exactly as `make sqlite3.h` does: with SQLite's
#           own `tool/mksqlite3h.tcl`, run by the Tcl interpreter SQLite ships for builds
#           without a system tclsh (`autosetup/jimsh0.c`, compiled with main.mk's
#           CFLAGS.jimsh), and `tool/mksourceid` built from `tool/mksourceid.c`. No
#           handwritten or version-mismatched header is used. Helper binaries go to
#           <outdir>/bin, outside the parsed tree.
#   parse   c2cpg <outdir>/tree -> <outdir>/cpg.bin with $DEFINES (below).
#   export  cartographer/export_ast.sc on a copy of that CPG -> <outdir>/ast.json, with
#           `cppDefines` set to the same list (the exporter's struct-layout logic needs to
#           know which names the parse defined), then /opt/corpus/metrics.py if present.
#
# DEFINES: the configuration the published full-tree census used (`SQLITE_OS_UNIX`,
# `SQLITE_TEST`) plus SQLite's linkage/calling-convention macros, each defined to what
# sqlite3.h/sqliteInt.h/tcl.h default them to on gcc/Linux, minus attributes that have
# no effect on the value semantics (`SQLITE_NOINLINE`). Note the trailing space in
# `NAME= `: c2cpg crashes on an empty `NAME=`, and a bare `NAME` is defined EMPTY (so
# `#if NAME` is false -- checked on a two-branch fixture; `NAME=1` takes the true branch).
#
# Joern runs take the machine-wide lock /opt/corpus/joern.lock when it exists; JOERN_XMX
# defaults to 13g (the full tree needs it).
set -euo pipefail

SRC="$(realpath "${1:?usage: sqlite_corpus.sh <sqlite-src> <outdir> [gen|parse|export|all]}")"
OUT="$(realpath -m "${2:?usage: sqlite_corpus.sh <sqlite-src> <outdir> [gen|parse|export|all]}")"
STEP="${3:-all}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
JOERN="${JOERN_CLI:-/opt/joern/joern-cli}"
CC="${CC:-cc}"
export JOERN_XMX="${JOERN_XMX:-13g}"
export LANG=C.UTF-8 LC_ALL=C.UTF-8 JAVA_TOOL_OPTIONS="${JAVA_TOOL_OPTIONS:-} -Dfile.encoding=UTF-8"

DEFINES="${DEFINES:-SQLITE_OS_UNIX,SQLITE_TEST,SQLITE_API= ,SQLITE_CDECL= ,SQLITE_APICALL= ,SQLITE_STDCALL= ,SQLITE_CALLBACK= ,SQLITE_SYSAPI= ,SQLITE_EXTERN=extern,SQLITE_TCLAPI= ,SQLITE_NOINLINE= ,CONST=const,JNIEXPORT= ,JNICALL= }"

LOCK=()
if [ -e /opt/corpus/joern.lock ]; then LOCK=(flock /opt/corpus/joern.lock); fi

gen() {
  rm -rf "$OUT/tree" "$OUT/bin"; mkdir -p "$OUT/tree" "$OUT/bin"
  tar -C "$SRC" --exclude=.git -cf - . | tar -C "$OUT/tree" -xf -
  # main.mk: `$(B.cc) -o $@ $(CFLAGS.jimsh) $(TOP)/autosetup/jimsh0.c`, CFLAGS.jimsh ?= -DHAVE_REALPATH
  "$CC" -O1 -DHAVE_REALPATH -o "$OUT/bin/jimsh" "$SRC/autosetup/jimsh0.c"
  "$CC" -O1 -o "$OUT/bin/mksourceid" "$SRC/tool/mksourceid.c"
  # mksqlite3h.tcl runs `$PWD/mksourceid`, so it must run from bin/.
  (cd "$OUT/bin" && ./jimsh "$SRC/tool/mksqlite3h.tcl" "$SRC" -o "$OUT/tree/src/sqlite3.h")
  grep -m2 -E '^#define SQLITE_(VERSION|SOURCE_ID) ' "$OUT/tree/src/sqlite3.h"
  echo "VERSION file: $(cat "$SRC/VERSION")  manifest.uuid: $(cat "$SRC/manifest.uuid" 2>/dev/null || echo none)"
}

frontend_args() {
  local IFS=','; local d
  for d in $DEFINES; do printf '%s\0' --define "$d"; done
}

parse() {
  local args=(); while IFS= read -r -d '' a; do args+=("$a"); done < <(frontend_args)
  printf 'c2cpg %s' "$OUT/tree"; printf ' %q' "${args[@]}"; echo
  "${LOCK[@]}" "$JOERN/c2cpg.sh" "$OUT/tree" "${args[@]}" --output "$OUT/cpg.bin" \
    > "$OUT/parse.log" 2>&1 || { tail -30 "$OUT/parse.log"; exit 1; }
  ls -la "$OUT/cpg.bin"
}

export_ast() {
  rm -rf "$OUT/workspace"; cp "$OUT/cpg.bin" "$OUT/cpg.work.bin"
  (cd "$OUT" && "${LOCK[@]}" "$JOERN/joern" --script "$ROOT/cartographer/export_ast.sc" \
     --param cpgPath="$OUT/cpg.work.bin" --param out="$OUT/ast.json" \
     --param "cppDefines=$DEFINES" > "$OUT/export.log" 2>&1) \
    || { grep -v 'JAVA_TOOL\|SLF4J' "$OUT/export.log" | grep -v '^\s*at ' | tail -30; exit 1; }
  rm -rf "$OUT/workspace" "$OUT/cpg.work.bin"
  grep '^exported' "$OUT/export.log"
  if [ -f /opt/corpus/metrics.py ]; then
    python3 /opt/corpus/metrics.py "$OUT/ast.json" 30 | tee "$OUT/metrics.txt"
  fi
}

case "$STEP" in
  gen) gen ;;
  parse) parse ;;
  export) export_ast ;;
  all) gen; parse; export_ast ;;
  *) echo "unknown step $STEP" >&2; exit 2 ;;
esac
