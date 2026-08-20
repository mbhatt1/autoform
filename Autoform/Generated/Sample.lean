import Autoform.Lang.Core.Semantics

/-!
# Sample — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated
open Autoform.Core

/-- `lib.py:<module>.add`  (from `lib.py`) -/
def f_lib_py__module__add : Func :=
  { name := "lib.py:<module>.add"
  , params := ["a", "b"]
  , body := (.ret (.binop "+" (.name "a") (.name "b"))) }

/-- `lib.py:<module>.clamp`  (from `lib.py`) -/
def f_lib_py__module__clamp : Func :=
  { name := "lib.py:<module>.clamp"
  , params := ["x", "lo", "hi"]
  , body := (.seq (.ifte (.binop "<" (.name "x") (.name "lo")) (.ret (.name "lo")) .skip) (.seq (.ifte (.binop ">" (.name "x") (.name "hi")) (.ret (.name "hi")) .skip) (.ret (.name "x")))) }

/-- `lib.py:<module>.encode`  (from `lib.py`) -/
def f_lib_py__module__encode : Func :=
  { name := "lib.py:<module>.encode"
  , params := ["xs"]
  , body := (.seq (.assign "out" (.hole "op:listLiteral")) (.seq .skip (.seq (.seq (.assign "tmp0" (.call "__iter__" [(.hole "op:fieldAccess"), (.name "xs")])) (.loop (.hole "expr:UNKNOWN") (.seq (.assign "x" (.call "__next__" [(.hole "op:fieldAccess"), (.name "tmp0")])) (.expr (.call "append" [(.hole "op:fieldAccess"), (.name "out"), (.call "add" [(.name "add"), (.name "x"), (.lit (.int 1))])]))))) (.seq .skip (.seq (.ret (.name "out")) (.seq .skip .skip)))))) }

/-- `lib.py:<module>.save`  (from `lib.py`) -/
def f_lib_py__module__save : Func :=
  { name := "lib.py:<module>.save"
  , params := ["path", "xs"]
  , body := (.seq (.seq (.assign "manager_tmp0" (.call "open" [(.name "open"), (.name "path"), (.lit (.str "w"))])) (.seq (.assign "enter_tmp0" (.hole "op:fieldAccess")) (.seq (.assign "exit_tmp0" (.hole "op:fieldAccess")) (.seq (.assign "value_tmp0" (.call "" [(.name "enter_tmp0"), (.name "manager_tmp0")])) (.hole "control:TRY"))))) (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `lib.py:<module>.sample_id`  (from `lib.py`) -/
def f_lib_py__module__sample_id : Func :=
  { name := "lib.py:<module>.sample_id"
  , params := []
  , body := (.seq (.assign "random" (.call "import" [(.name "import"), (.lit (.str "")), (.lit (.str "random"))])) (.seq .skip (.seq (.ret (.call "random" [(.hole "op:fieldAccess"), (.name "random")])) .skip))) }

/-- Source dialect: `.python` (integer division/modulo convention). -/
def program : Program := { dialect := .python, funcs := [
  f_lib_py__module__add,
  f_lib_py__module__clamp,
  f_lib_py__module__encode,
  f_lib_py__module__save,
  f_lib_py__module__sample_id
] }

end Autoform.Generated