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
  , body := (.seq
            (.ifte (.binop "<" (.name "x") (.name "lo")) (.ret (.name "lo")) .skip)
            (.seq
              (.ifte (.binop ">" (.name "x") (.name "hi")) (.ret (.name "hi")) .skip)
              (.ret (.name "x")))) }

/-- `lib.py:<module>.encode`  (from `lib.py`) -/
def f_lib_py__module__encode : Func :=
  { name := "lib.py:<module>.encode"
  , params := ["xs"]
  , body := (.seq
            (.assign "out" (.listE []))
            (.seq
              .skip
              (.seq
                (.forIn
                  "x"
                  (.name "xs")
                  (.expr
                    (.mcall (.name "out") "append" [(.call "add" [(.name "x"), (.lit (.int 1))])])))
                (.seq .skip (.seq (.ret (.name "out")) (.seq .skip .skip)))))) }

/-- `lib.py:<module>.save`  (from `lib.py`) -/
def f_lib_py__module__save : Func :=
  { name := "lib.py:<module>.save"
  , params := ["path", "xs"]
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.call "open" [(.name "path"), (.lit (.str "w"))]))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.call "" []))
                    (.seq
                      (.tryCatch
                        (.seq
                          (.assign "f" (.name "value_tmp0"))
                          (.expr
                            (.mcall
                              (.name "f")
                              "write"
                              [(.call "str" [(.call "encode" [(.name "xs")])])])))
                        "__exc"
                        (.seq (.expr (.call "" [])) (.raise (.name "__exc"))))
                      (.expr (.call "" [])))))))
            (.seq
              .skip
              (.seq
                .skip
                (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `lib.py:<module>.sample_id`  (from `lib.py`) -/
def f_lib_py__module__sample_id : Func :=
  { name := "lib.py:<module>.sample_id"
  , params := []
  , body := (.seq
            (.assign "random" (.call "import" [(.lit .unit), (.hole "lit:unquoted")]))
            (.seq .skip (.seq (.ret (.mcall (.name "random") "random" [])) .skip))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.python` (integer division/modulo convention). -/
def program : Program := { dialect := .python, funcs := [
  f_lib_py__module__add,
  f_lib_py__module__clamp,
  f_lib_py__module__encode,
  f_lib_py__module__save,
  f_lib_py__module__sample_id
] }

end Autoform.Generated