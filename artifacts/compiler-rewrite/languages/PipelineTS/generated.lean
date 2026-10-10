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
# PipelineTS — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.PipelineTS
open Autoform.Core

/-- `numbers.ts::program:shift`  (from `numbers.ts`) -/
def f_numbers_ts__program_shift : Func :=
  { name := "numbers.ts::program:shift"
  , params := ["a", "b"]
  , body := (.ret (.binop "num:js:i32:<<" (.name "a") (.name "b"))) }

/-- `numbers.ts::program`  (from `numbers.ts`) -/
def f_numbers_ts__program : Func :=
  { name := "numbers.ts::program"
  , params := []
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.assign "shift" (.fnref "numbers.ts::program:shift"))
                  (.seq
                    (.assign "unsigned" (.fnref "numbers.ts::program:unsigned"))
                    (.assign "constant" (.fnref "numbers.ts::program:constant"))))))) }

/-- `numbers.ts::program:unsigned`  (from `numbers.ts`) -/
def f_numbers_ts__program_unsigned : Func :=
  { name := "numbers.ts::program:unsigned"
  , params := ["a", "b"]
  , body := (.ret (.binop "num:js:i32:>>>" (.name "a") (.name "b"))) }

/-- `numbers.ts::program:constant`  (from `numbers.ts`) -/
def f_numbers_ts__program_constant : Func :=
  { name := "numbers.ts::program:constant"
  , params := []
  , body := (.ret (.lit (.int 7))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.javascript` (integer division/modulo convention). -/
def program : Program := { dialect := .javascript, funcs := [
  f_numbers_ts__program_shift,
  f_numbers_ts__program,
  f_numbers_ts__program_unsigned,
  f_numbers_ts__program_constant
] }

end Autoform.Generated.PipelineTS