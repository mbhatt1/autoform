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
set_option maxRecDepth 8032

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
# PipelineKotlin — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.PipelineKotlin
open Autoform.Core

/-- `numbers.add:long(long,long)`  (from `Numbers.kt`) -/
def f_numbers_add_long_long_long_ : Func :=
  { name := "numbers.add:long(long,long)"
  , params := ["a", "b"]
  , body := (.ret (.binop "num:java:i64:+" (.name "a") (.name "b"))) }

/-- `numbers.word:int(int,int)`  (from `Numbers.kt`) -/
def f_numbers_word_int_int_int_ : Func :=
  { name := "numbers.word:int(int,int)"
  , params := ["a", "b"]
  , body := (.ret (.binop "num:java:i32:+" (.name "a") (.name "b"))) }

/-- `numbers.shift:long(long,int)`  (from `Numbers.kt`) -/
def f_numbers_shift_long_long_int_ : Func :=
  { name := "numbers.shift:long(long,int)"
  , params := ["a", "n"]
  , body := (.ret (.binop "num:java:i64:<<" (.name "a") (.name "n"))) }

/-- `Numbers.kt:Numbers.kt:numbers.global`  (from `Numbers.kt`) -/
def f_Numbers_kt_Numbers_kt_numbers_global : Func :=
  { name := "Numbers.kt:Numbers.kt:numbers.global"
  , params := []
  , body := (.seq .skip (.seq .skip .skip)) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.java` (integer division/modulo convention). -/
def program : Program := { dialect := .java, funcs := [
  f_numbers_add_long_long_long_,
  f_numbers_word_int_int_int_,
  f_numbers_shift_long_long_int_,
  f_Numbers_kt_Numbers_kt_numbers_global
] }

end Autoform.Generated.PipelineKotlin