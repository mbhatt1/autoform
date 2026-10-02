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
set_option maxRecDepth 8048

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
# CMath — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.CMath
open Autoform.Core

/-- `clamp`  (from `math.c`) -/
def f_clamp : Func :=
  { name := "clamp"
  , params := ["x", "lo", "hi"]
  , body := (.seq
            (.ifte (.binop "<" (.name "x") (.name "lo")) (.ret (.name "lo")) .skip)
            (.seq
              (.ifte (.binop ">" (.name "x") (.name "hi")) (.ret (.name "hi")) .skip)
              (.ret (.name "x")))) }

/-- `poly`  (from `math.c`) -/
def f_poly : Func :=
  { name := "poly"
  , params := ["a", "b", "c"]
  , body := (.ret
            (.binop "-" (.binop "+" (.binop "*" (.name "a") (.name "b")) (.name "c")) (.name "a"))) }

/-- `sumto`  (from `math.c`) -/
def f_sumto : Func :=
  { name := "sumto"
  , params := ["n"]
  , body := (.seq
            .skip
            (.seq
              (.assign "acc" (.lit (.int 0)))
              (.seq
                .skip
                (.seq
                  (.assign "i" (.lit (.int 0)))
                  (.seq
                    (.loop
                      (.binop "<=" (.name "i") (.name "n"))
                      (.seq
                        (.assign "acc" (.binop "+" (.name "acc") (.name "i")))
                        (.assign "i" (.binop "+" (.name "i") (.lit (.int 1))))))
                    (.ret (.name "acc"))))))) }

/-- `cdiv`  (from `math.c`) -/
def f_cdiv : Func :=
  { name := "cdiv"
  , params := ["a", "b"]
  , body := (.seq
            (.ifte (.binop "==" (.name "b") (.lit (.int 0))) (.ret (.lit (.int 0))) .skip)
            (.ret (.binop "/" (.name "a") (.name "b")))) }

/-- `cmod`  (from `math.c`) -/
def f_cmod : Func :=
  { name := "cmod"
  , params := ["a", "b"]
  , body := (.seq
            (.ifte (.binop "==" (.name "b") (.lit (.int 0))) (.ret (.lit (.int 0))) .skip)
            (.ret (.binop "%" (.name "a") (.name "b")))) }

/-- `math.c:<global>`  (from `math.c`) -/
def f_math_c__global_ : Func :=
  { name := "math.c:<global>"
  , params := []
  , body := (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := [f_math_c__global_]

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_clamp,
  f_poly,
  f_sumto,
  f_cdiv,
  f_cmod,
  f_math_c__global_
] }

end Autoform.Generated.CMath