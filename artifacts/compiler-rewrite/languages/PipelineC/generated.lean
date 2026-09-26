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
set_option maxRecDepth 8104

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
# PipelineC — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.PipelineC
open Autoform.Core

/-- `add`  (from `numbers.c`) -/
def f_add : Func :=
  { name := "add"
  , params := ["a", "b"]
  , body := (.ret (.unop "cast:i64" (.binop "num:c:i64:+" (.name "a") (.name "b")))) }

/-- `wrap`  (from `numbers.c`) -/
def f_wrap : Func :=
  { name := "wrap"
  , params := ["a", "b"]
  , body := (.ret (.unop "cast:u32" (.binop "num:c:u32:+" (.name "a") (.name "b")))) }

/-- `mixed`  (from `numbers.c`) -/
def f_mixed : Func :=
  { name := "mixed"
  , params := ["a", "b"]
  , body := (.ret (.unop "cast:i32" (.binop "num:c:u32:<" (.name "a") (.name "b")))) }

/-- `right`  (from `numbers.c`) -/
def f_right : Func :=
  { name := "right"
  , params := ["a", "b"]
  , body := (.ret (.unop "cast:u32" (.binop "num:c:u32:>>>" (.name "a") (.name "b")))) }

/-- `bump`  (from `numbers.c`) -/
def f_bump : Func :=
  { name := "bump"
  , params := ["a"]
  , body := (.seq
            (.assign "a" (.unop "cast:u8" (.binop "num:c:i32:+" (.name "a") (.lit (.int 1)))))
            (.ret (.unop "cast:u8" (.name "a")))) }

/-- `nested`  (from `numbers.c`) -/
def f_nested : Func :=
  { name := "nested"
  , params := ["a", "b"]
  , body := (.ret
            (.unop
              "cast:i64"
              (.binop "num:c:i64:*" (.binop "num:c:i64:+" (.name "a") (.name "b")) (.name "b")))) }

/-- `literal`  (from `numbers.c`) -/
def f_literal : Func :=
  { name := "literal"
  , params := []
  , body := (.ret (.unop "cast:i64" (.binop "num:c:i64:+" (.lit (.int 2147483648)) (.lit (.int 1))))) }

/-- `mixedwidth`  (from `numbers.c`) -/
def f_mixedwidth : Func :=
  { name := "mixedwidth"
  , params := ["a", "b"]
  , body := (.ret (.unop "cast:i64" (.binop "num:c:i64:+" (.name "a") (.name "b")))) }

/-- `promote`  (from `numbers.c`) -/
def f_promote : Func :=
  { name := "promote"
  , params := ["a", "b"]
  , body := (.ret (.unop "cast:i32" (.binop "num:c:i32:+" (.name "a") (.name "b")))) }

/-- `hexliteral`  (from `numbers.c`) -/
def f_hexliteral : Func :=
  { name := "hexliteral"
  , params := []
  , body := (.ret (.unop "cast:u32" (.binop "num:c:u32:|" (.lit (.int 4294967295)) (.lit (.int 0))))) }

/-- `wideshift`  (from `numbers.c`) -/
def f_wideshift : Func :=
  { name := "wideshift"
  , params := []
  , body := (.ret (.unop "cast:u64" (.binop "num:c:u64:<<" (.lit (.int 1)) (.lit (.int 40))))) }

/-- `octalcompare`  (from `numbers.c`) -/
def f_octalcompare : Func :=
  { name := "octalcompare"
  , params := []
  , body := (.ret (.unop "cast:i32" (.binop "num:c:u32:<" (.lit (.int 4294967295)) (.lit (.int 0))))) }

/-- `numbers.c:<global>`  (from `numbers.c`) -/
def f_numbers_c__global_ : Func :=
  { name := "numbers.c:<global>"
  , params := []
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := [f_numbers_c__global_]

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_add,
  f_wrap,
  f_mixed,
  f_right,
  f_bump,
  f_nested,
  f_literal,
  f_mixedwidth,
  f_promote,
  f_hexliteral,
  f_wideshift,
  f_octalcompare,
  f_numbers_c__global_
] }

end Autoform.Generated.PipelineC