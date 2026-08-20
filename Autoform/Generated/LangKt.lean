import Autoform.Lang.Core.Semantics

-- Lean's default `maxRecDepth` (512) is a guard against runaway elaboration, not
-- a statement about reasonable programs. A deep-embedded function body is one
-- term, so the elaborator's recursion depth tracks the *source's* nesting depth:
-- Linux `lib/` hit the limit at two declarations and the whole module failed to
-- type-check. Raising it costs nothing for shallow modules and is the difference
-- between compiling a real codebase and not.
set_option maxRecDepth 8000

/-!
# LangKt — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated
open Autoform.Core

/-- `gcd:int(int,int)`  (from `T.kt`) -/
def f_gcd_int_int_int_ : Func :=
  { name := "gcd:int(int,int)"
  , params := ["a", "b"]
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.name "a"))
              (.seq
                .skip
                (.seq
                  (.assign "y" (.name "b"))
                  (.seq
                    (.loop
                      (.binop "!=" (.name "y") (.lit (.int 0)))
                      (.seq
                        .skip
                        (.seq
                          (.assign "t" (.binop "%" (.name "x") (.name "y")))
                          (.seq (.assign "x" (.name "y")) (.assign "y" (.name "t"))))))
                    (.ret (.name "x"))))))) }

/-- `addAll:int(int)`  (from `T.kt`) -/
def f_addAll_int_int_ : Func :=
  { name := "addAll:int(int)"
  , params := ["n"]
  , body := (.seq
            .skip
            (.seq
              (.assign "s" (.lit (.int 0)))
              (.seq
                .skip
                (.seq
                  (.assign "i" (.lit (.int 0)))
                  (.seq
                    (.loop
                      (.binop "<" (.name "i") (.name "n"))
                      (.seq
                        (.assign "s" (.binop "+" (.name "s") (.name "i")))
                        (.assign "i" (.binop "+" (.name "i") (.lit (.int 1))))))
                    (.ret (.name "s"))))))) }

/-- `T.kt:<global>.global`  (from `T.kt`) -/
def f_T_kt__global__global : Func :=
  { name := "T.kt:<global>.global"
  , params := []
  , body := (.seq (.hole "stmt:METHOD") (.hole "stmt:METHOD")) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_gcd_int_int_int_,
  f_addAll_int_int_,
  f_T_kt__global__global
] }

end Autoform.Generated