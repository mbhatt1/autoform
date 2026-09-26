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
set_option maxRecDepth 8080

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
# PipelineJS — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.PipelineJS
open Autoform.Core

/-- `numbers.js::program:shift`  (from `numbers.js`) -/
def f_numbers_js__program_shift : Func :=
  { name := "numbers.js::program:shift"
  , params := ["a", "b"]
  , body := (.ret (.binop "num:js:i32:<<" (.name "a") (.name "b"))) }

/-- `numbers.js::program`  (from `numbers.js`) -/
def f_numbers_js__program : Func :=
  { name := "numbers.js::program"
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
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              (.assign "shift" (.fnref "numbers.js::program:shift"))
                              (.seq
                                (.assign "unsigned" (.fnref "numbers.js::program:unsigned"))
                                (.seq
                                  (.assign "signed" (.fnref "numbers.js::program:signed"))
                                  (.seq
                                    (.assign "bits" (.fnref "numbers.js::program:bits"))
                                    (.seq
                                      (.assign
                                        "complement"
                                        (.fnref "numbers.js::program:complement"))
                                      (.seq
                                        (.assign
                                        "signedAssign"
                                        (.fnref "numbers.js::program:signedAssign"))
                                        (.seq
                                        (.assign
                                        "unsignedAssign"
                                        (.fnref "numbers.js::program:unsignedAssign"))
                                        (.seq
                                        (.assign
                                        "unsignedValue"
                                        (.fnref "numbers.js::program:unsignedValue"))
                                        (.assign "add" (.fnref "numbers.js::program:add"))))))))))))))))))) }

/-- `numbers.js::program:unsigned`  (from `numbers.js`) -/
def f_numbers_js__program_unsigned : Func :=
  { name := "numbers.js::program:unsigned"
  , params := ["a", "b"]
  , body := (.ret (.binop "num:js:i32:>>>" (.name "a") (.name "b"))) }

/-- `numbers.js::program:signed`  (from `numbers.js`) -/
def f_numbers_js__program_signed : Func :=
  { name := "numbers.js::program:signed"
  , params := ["a", "b"]
  , body := (.ret (.binop "num:js:i32:>>" (.name "a") (.name "b"))) }

/-- `numbers.js::program:bits`  (from `numbers.js`) -/
def f_numbers_js__program_bits : Func :=
  { name := "numbers.js::program:bits"
  , params := ["a", "b"]
  , body := (.ret (.binop "num:js:i32:|" (.name "a") (.name "b"))) }

/-- `numbers.js::program:complement`  (from `numbers.js`) -/
def f_numbers_js__program_complement : Func :=
  { name := "numbers.js::program:complement"
  , params := ["a"]
  , body := (.ret (.unop "num:js:i32:~" (.name "a"))) }

/-- `numbers.js::program:signedAssign`  (from `numbers.js`) -/
def f_numbers_js__program_signedAssign : Func :=
  { name := "numbers.js::program:signedAssign"
  , params := ["a", "b"]
  , body := (.seq (.assign "a" (.binop "num:js:i32:>>" (.name "a") (.name "b"))) (.ret (.name "a"))) }

/-- `numbers.js::program:unsignedAssign`  (from `numbers.js`) -/
def f_numbers_js__program_unsignedAssign : Func :=
  { name := "numbers.js::program:unsignedAssign"
  , params := ["a", "b"]
  , body := (.seq (.assign "a" (.binop "num:js:i32:>>>" (.name "a") (.name "b"))) (.ret (.name "a"))) }

/-- `numbers.js::program:unsignedValue`  (from `numbers.js`) -/
def f_numbers_js__program_unsignedValue : Func :=
  { name := "numbers.js::program:unsignedValue"
  , params := ["a", "b"]
  , body := (.seq (.assign "a" (.binop "num:js:i32:>>>" (.name "a") (.name "b"))) (.ret (.name "a"))) }

/-- `numbers.js::program:add`  (from `numbers.js`) -/
def f_numbers_js__program_add : Func :=
  { name := "numbers.js::program:add"
  , params := ["a", "b"]
  , body := (.ret (.binop "js:+" (.name "a") (.name "b"))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.javascript` (integer division/modulo convention). -/
def program : Program := { dialect := .javascript, funcs := [
  f_numbers_js__program_shift,
  f_numbers_js__program,
  f_numbers_js__program_unsigned,
  f_numbers_js__program_signed,
  f_numbers_js__program_bits,
  f_numbers_js__program_complement,
  f_numbers_js__program_signedAssign,
  f_numbers_js__program_unsignedAssign,
  f_numbers_js__program_unsignedValue,
  f_numbers_js__program_add
] }

end Autoform.Generated.PipelineJS