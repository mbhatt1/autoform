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
set_option maxRecDepth 8072

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
# PipelineGo — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.PipelineGo
open Autoform.Core

/-- `numbers.Add`  (from `numbers.go`) -/
def f_numbers_Add : Func :=
  { name := "numbers.Add"
  , params := ["a", "b"]
  , body := (.ret (.binop "num:go:i64:+" (.name "a") (.name "b"))) }

/-- `numbers.Div`  (from `numbers.go`) -/
def f_numbers_Div : Func :=
  { name := "numbers.Div"
  , params := ["a", "b"]
  , body := (.ret (.binop "num:go:i64:/" (.name "a") (.name "b"))) }

/-- `numbers.Shift`  (from `numbers.go`) -/
def f_numbers_Shift : Func :=
  { name := "numbers.Shift"
  , params := ["a", "b"]
  , body := (.ret (.binop "num:go:u64:<<" (.name "a") (.name "b"))) }

/-- `numbers.Right`  (from `numbers.go`) -/
def f_numbers_Right : Func :=
  { name := "numbers.Right"
  , params := ["a", "b"]
  , body := (.ret (.binop "num:go:i64:>>" (.name "a") (.name "b"))) }

/-- `numbers.Inc`  (from `numbers.go`) -/
def f_numbers_Inc : Func :=
  { name := "numbers.Inc"
  , params := ["a"]
  , body := (.seq
            (.assign "a" (.unop "cast:i64" (.binop "num:go:i64:+" (.name "a") (.lit (.int 1)))))
            (.ret (.name "a"))) }

/-- `numbers.Bump`  (from `numbers.go`) -/
def f_numbers_Bump : Func :=
  { name := "numbers.Bump"
  , params := ["a"]
  , body := (.seq
            (.assign "a" (.unop "cast:i8" (.binop "num:go:i8:+" (.name "a") (.lit (.int 1)))))
            (.ret (.name "a"))) }

/-- `numbers.Word`  (from `numbers.go`) -/
def f_numbers_Word : Func :=
  { name := "numbers.Word"
  , params := ["a", "b"]
  , body := (.ret (.binop "num:go:i64:+" (.name "a") (.name "b"))) }

/-- `numbers.ContextShift`  (from `numbers.go`) -/
def f_numbers_ContextShift : Func :=
  { name := "numbers.ContextShift"
  , params := ["n"]
  , body := (.ret (.binop "num:go:u32:<<" (.lit (.int 1)) (.name "n"))) }

/-- `numbers.Constant`  (from `numbers.go`) -/
def f_numbers_Constant : Func :=
  { name := "numbers.Constant"
  , params := []
  , body := (.ret (.lit (.int 9223372036854775808))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.go` (integer division/modulo convention). -/
def program : Program := { dialect := .go, funcs := [
  f_numbers_Add,
  f_numbers_Div,
  f_numbers_Shift,
  f_numbers_Right,
  f_numbers_Inc,
  f_numbers_Bump,
  f_numbers_Word,
  f_numbers_ContextShift,
  f_numbers_Constant
] }

end Autoform.Generated.PipelineGo