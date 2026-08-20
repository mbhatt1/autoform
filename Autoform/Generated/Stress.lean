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

/-!
# Stress — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated
open Autoform.Core

/-- `ops.py:<module>.fdiv`  (from `ops.py`) -/
def f_ops_py__module__fdiv : Func :=
  { name := "ops.py:<module>.fdiv"
  , params := ["a", "b"]
  , body := (.seq
            (.ifte (.binop "==" (.name "b") (.lit (.int 0))) (.ret (.lit (.int 0))) .skip)
            (.ret (.binop "/" (.name "a") (.name "b")))) }

/-- `ops.py:<module>.fmod`  (from `ops.py`) -/
def f_ops_py__module__fmod : Func :=
  { name := "ops.py:<module>.fmod"
  , params := ["a", "b"]
  , body := (.seq
            (.ifte (.binop "==" (.name "b") (.lit (.int 0))) (.ret (.lit (.int 0))) .skip)
            (.ret (.binop "%" (.name "a") (.name "b")))) }

/-- `ops.py:<module>.poly`  (from `ops.py`) -/
def f_ops_py__module__poly : Func :=
  { name := "ops.py:<module>.poly"
  , params := ["a", "b", "c"]
  , body := (.ret
            (.binop "-" (.binop "+" (.binop "*" (.name "a") (.name "b")) (.name "c")) (.name "a"))) }

/-- `ops.py:<module>.cmpchain`  (from `ops.py`) -/
def f_ops_py__module__cmpchain : Func :=
  { name := "ops.py:<module>.cmpchain"
  , params := ["x", "y"]
  , body := (.seq
            (.ifte (.binop "<" (.name "x") (.name "y")) (.ret (.unop "-" (.lit (.int 1)))) .skip)
            (.seq
              (.ifte (.binop ">" (.name "x") (.name "y")) (.ret (.lit (.int 1))) .skip)
              (.ret (.lit (.int 0))))) }

/-- `ops.py:<module>.absval`  (from `ops.py`) -/
def f_ops_py__module__absval : Func :=
  { name := "ops.py:<module>.absval"
  , params := ["x"]
  , body := (.seq
            (.ifte (.binop "<" (.name "x") (.lit (.int 0))) (.ret (.unop "-" (.name "x"))) .skip)
            (.ret (.name "x"))) }

/-- `ops.py:<module>.gcdish`  (from `ops.py`) -/
def f_ops_py__module__gcdish : Func :=
  { name := "ops.py:<module>.gcdish"
  , params := ["a", "b"]
  , body := (.seq
            (.loop
              (.binop "!=" (.name "b") (.lit (.int 0)))
              (.seq
                (.assign "t" (.name "b"))
                (.seq (.assign "b" (.binop "%" (.name "a") (.name "b"))) (.assign "a" (.name "t")))))
            (.seq .skip (.ret (.name "a")))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.python` (integer division/modulo convention). -/
def program : Program := { dialect := .python, funcs := [
  f_ops_py__module__fdiv,
  f_ops_py__module__fmod,
  f_ops_py__module__poly,
  f_ops_py__module__cmpchain,
  f_ops_py__module__absval,
  f_ops_py__module__gcdish
] }

end Autoform.Generated