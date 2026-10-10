# Sourced by autoform.sh and assure.sh before a run touches any artifact.
#
# Two hazards, both documented in docs/integrity.md under "Concurrency", and both of
# which have actually happened in this repository:
#
#   * `scripts/mutate.py` rewrites `Autoform/Generated/<M>.lean` IN PLACE and leaves a
#     `<M>.lean.mutate-backup` beside it while a mutant is live. A pipeline run taken
#     during that window builds and compares a MUTANT and reports its divergences as
#     if they were the program's. One such mutant survived four commits.
#   * A tracked generated module or AST that is modified in the working tree is, by
#     definition, not the artifact the manifest and the proofs describe. Building the
#     runtime with it in the import graph compares the wrong program.
#
# Refusing is the honest response: neither situation can be repaired from inside a
# run, and continuing produces evidence about something other than the source. Exit 2
# puts this in the "invocation/setup" class of docs/running.md §7.
#
# AUTOFORM_ALLOW_DIRTY=1 disables the tracked-file check for development on a module
# whose render you are deliberately iterating on. It never disables the
# `.mutate-backup` check: there is no legitimate reason to run a pipeline over a live
# mutant.
#
# Usage:  . "$ROOT/scripts/integrity_guard.sh"; autoform_integrity_guard "$ROOT" "$MOD"

autoform_integrity_guard() {
  local root="$1" module="${2:-}"
  local backups=""
  if [ -d "$root/Autoform" ]; then
    backups="$(find "$root/Autoform" -name '*.mutate-backup' -print 2>/dev/null || true)"
  fi
  if [ -n "$backups" ]; then
    {
      echo "autoform: refusing to run: a mutation gate is live or was interrupted in this tree."
      echo "  These files mean a translated module is currently a MUTANT, not the program:"
      printf '    %s\n' $backups
      echo "  Any conformance or proof taken now would describe the mutant (docs/integrity.md)."
      echo "  Let scripts/mutate.py finish, or restore each <M>.lean from its .mutate-backup"
      echo "  and delete the backup, then re-run."
    } >&2
    return 2
  fi
  if [ "${AUTOFORM_ALLOW_DIRTY:-0}" = "1" ]; then
    return 0
  fi
  # An installed workspace (`autoform init`) is not a git checkout; there is nothing
  # tracked to be dirty, and the render for the requested module is this run's own
  # output. Only a repository checkout has tracked artifacts to protect.
  if ! git -C "$root" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    return 0
  fi
  local dirty
  dirty="$(git -C "$root" status --porcelain --untracked-files=no -- \
             'Autoform/Generated' 'Autoform/SpecsGen' 'ast-*.json' 2>/dev/null || true)"
  if [ -n "$module" ] && [ -n "$dirty" ]; then
    # This run legitimately rewrites its OWN module's render, spec module and AST.
    dirty="$(printf '%s\n' "$dirty" | grep -v -F \
               -e "Autoform/Generated/$module.lean" \
               -e "Autoform/SpecsGen/$module.lean" \
               -e "ast-$module.json" || true)"
  fi
  if [ -n "$dirty" ]; then
    {
      echo "autoform: refusing to run: tracked generated artifacts are modified in this checkout:"
      printf '%s\n' "$dirty" | sed 's/^/    /'
      echo "  A modified render or AST is not the artifact the manifest and proofs describe, so a"
      echo "  run now would compare the wrong program (docs/integrity.md). Commit or restore them,"
      echo "  run scripts/check_render.py, or set AUTOFORM_ALLOW_DIRTY=1 if you are deliberately"
      echo "  iterating on one of these and understand that the result is not evidence."
    } >&2
    return 2
  fi
  return 0
}
