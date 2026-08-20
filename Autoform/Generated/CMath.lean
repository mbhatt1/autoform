import Autoform.Lang.Core.Semantics

/-!
# CMath — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated
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

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_clamp,
  f_poly,
  f_sumto,
  f_cdiv,
  f_cmod
] }

end Autoform.Generated