import Autoform.Lang.Core.Semantics

/-!
# SC — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated
open Autoform.Core

/-- `sc.py:<module>.safemod`  (from `sc.py`) -/
def f_sc_py__module__safemod : Func :=
  { name := "sc.py:<module>.safemod"
  , params := ["a", "b"]
  , body := (.seq
            (.ifte
              (.binop
                "&&"
                (.binop "!=" (.name "b") (.lit (.int 0)))
                (.binop "==" (.binop "%" (.name "a") (.name "b")) (.lit (.int 0))))
              (.ret (.lit (.int 1)))
              .skip)
            (.ret (.lit (.int 0)))) }

/-- Source dialect: `.python` (integer division/modulo convention). -/
def program : Program := { dialect := .python, funcs := [
  f_sc_py__module__safemod
] }

end Autoform.Generated