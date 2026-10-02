import Autoform.Lang.Core.Semantics

-- Lean's default `maxRecDepth` (512) is a guard against runaway elaboration, not
-- a statement about reasonable programs. A deep-embedded function body is one
-- term, so the elaborator's recursion depth tracks the *source's* nesting depth:
-- Linux `lib/` hit the limit at two declarations and the whole module failed to
-- type-check. Raising it costs nothing for shallow modules and is the difference
-- between compiling a real codebase and not.
--
-- 8000 was not enough either. The binding constraint is not the nesting depth of
-- any one body (Ansible's deepest is 297) but the `funcs := [...]` list literal,
-- which elaborates as nested cons cells -- one frame or more per function, and
-- Ansible has 5,546. So the limit has to scale with the module's function count,
-- not with how deep its code happens to be.
set_option maxRecDepth 8056

-- Lean's default `maxHeartbeats` (200000) budgets ONE declaration's own
-- elaboration cost, separately from `maxRecDepth` above (which bounds nesting
-- depth, not total work). A single source file whose top-level declarations
-- carry a large static table -- SQLite's `test_vdbecov.c`, whose `<global>`
-- initializer alone is ~5.3M characters of generated Lean -- blows through the
-- default budget on that ONE declaration and fails with a `(deterministic)
-- timeout at isDefEq` error, unrelated to whether the translation is correct.
-- Unlike `maxRecDepth`, this does not scale with function COUNT (Ansible-style
-- corpora with thousands of small functions never hit it); it is one
-- pathologically large declaration, which no per-function-count formula would
-- predict, so this disables the budget outright rather than guessing a bigger
-- number that the next large static table would just exceed again. Scoped to
-- THIS generated file only (`set_option` here does not touch hand-written proof
-- files elsewhere in the project, which keep the default as a real safety net
-- against a genuine runaway elaboration bug while someone is editing them).
set_option maxHeartbeats 0

/-!
# LinuxLibSample — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.LinuxLibSample
open Autoform.Core

/-- `alloc_mod_tags_mem`  (from `alloc_tag.c`) -/
def f_alloc_mod_tags_mem : Func :=
  { name := "alloc_mod_tags_mem"
  , params := [""]
  , body := (.ret (.lit (.int 0))) }

/-- `bad_io_access`  (from `iomap.c`) -/
def f_bad_io_access : Func :=
  { name := "bad_io_access"
  , params := ["port", "access"]
  , body := (.seq
            .skip
            (.seq
              (.assign "count" (.lit (.int 10)))
              (.ifte
                (.binop "!=" (.name "count") (.lit (.int 0)))
                (.assign "count" (.binop "-" (.name "count") (.lit (.int 1))))
                .skip))) }

/-- `debugfs_errno_set`  (from `notifier-error-inject.c`) -/
def f_debugfs_errno_set : Func :=
  { name := "debugfs_errno_set"
  , params := ["data", "val"]
  , body := (.ret (.lit (.int 0))) }

/-- `percpu_counter_cpu_dead`  (from `percpu_counter.c`) -/
def f_percpu_counter_cpu_dead : Func :=
  { name := "percpu_counter_cpu_dead"
  , params := ["cpu"]
  , body := (.ret (.lit (.int 0))) }

/-- `radix_tree_tagged`  (from `radix-tree.c`) -/
def f_radix_tree_tagged : Func :=
  { name := "radix_tree_tagged"
  , params := ["root", "tag"]
  , body := (.ret (.call "root_tag_get" [(.name "root"), (.name "tag")])) }

/-- `root_tag_get`  (from `radix-tree.c`) -/
def f_root_tag_get : Func :=
  { name := "root_tag_get"
  , params := ["root", "tag"]
  , body := .skip }

/-- `span_iteration_check<duplicate>0`  (from `interval_tree_test.c`) -/
def f_span_iteration_check_duplicate_0 : Func :=
  { name := "span_iteration_check<duplicate>0"
  , params := [""]
  , body := (.ret (.lit (.int 0))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_alloc_mod_tags_mem,
  f_bad_io_access,
  f_debugfs_errno_set,
  f_percpu_counter_cpu_dead,
  f_radix_tree_tagged,
  f_root_tag_get,
  f_span_iteration_check_duplicate_0
] }

end Autoform.Generated.LinuxLibSample