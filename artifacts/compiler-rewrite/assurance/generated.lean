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
set_option maxRecDepth 8040

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
# CompilerRewrite — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.CompilerRewrite
open Autoform.Core

/-- `numbers.py:<module>.add`  (from `numbers.py`) -/
def f_numbers_py__module__add : Func :=
  { name := "numbers.py:<module>.add"
  , params := ["a", "b"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["a", "b"], isMethod := some false }
  , body := (.ret (.binop "+" (.name "a") (.name "b"))) }

/-- `numbers.py:<module>.quotient`  (from `numbers.py`) -/
def f_numbers_py__module__quotient : Func :=
  { name := "numbers.py:<module>.quotient"
  , params := ["a", "b"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["a", "b"], isMethod := some false }
  , body := (.ret (.binop "//" (.name "a") (.name "b"))) }

/-- `numbers.py:<module>.fraction`  (from `numbers.py`) -/
def f_numbers_py__module__fraction : Func :=
  { name := "numbers.py:<module>.fraction"
  , params := ["a", "b"]
  , pythonSignature := some { positionalOnly := [], keywordOnly := [], required := ["a", "b"], isMethod := some false }
  , body := (.ret (.binop "py:/" (.name "a") (.name "b"))) }

/-- `<module-objects>:<module>`  (from ``) -/
def f__module_objects___module_ : Func :=
  { name := "<module-objects>:<module>"
  , params := []
  , body := (.seq
            (.setGlobal "<module>numbers.py" (.alloc "<module>numbers.py" []))
            (.seq
              (.setField (.name "<module>numbers.py") "add" (.fnref "numbers.py:<module>.add"))
              (.seq
                (.setField
                  (.name "<module>numbers.py")
                  "fraction"
                  (.fnref "numbers.py:<module>.fraction"))
                (.seq
                  (.setField
                    (.name "<module>numbers.py")
                    "quotient"
                    (.fnref "numbers.py:<module>.quotient"))
                  .skip)))) }

/-- `numbers.py:<module>`  (from `numbers.py`) -/
def f_numbers_py__module_ : Func :=
  { name := "numbers.py:<module>"
  , params := []
  , body := (.seq
            (.setField (.name "<module>numbers.py") "add" (.fnref "numbers.py:<module>.add"))
            (.seq
              (.setField
                (.name "<module>numbers.py")
                "quotient"
                (.fnref "numbers.py:<module>.quotient"))
              (.seq
                (.setField
                  (.name "<module>numbers.py")
                  "fraction"
                  (.fnref "numbers.py:<module>.fraction"))
                (.seq .skip (.seq .skip .skip))))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := [f__module_objects___module_, f_numbers_py__module_]

/-- Source dialect: `.python` (integer division/modulo convention). -/
def program : Program := { dialect := .python, funcs := [
  f_numbers_py__module__add,
  f_numbers_py__module__quotient,
  f_numbers_py__module__fraction,
  f__module_objects___module_,
  f_numbers_py__module_
] }

end Autoform.Generated.CompilerRewrite