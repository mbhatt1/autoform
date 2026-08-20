import Autoform.Lang.Core.Semantics

/-!
# Ov — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated
open Autoform.Core

/-- `mulbig`  (from `ov.c`) -/
def f_mulbig : Func :=
  { name := "mulbig"
  , params := ["a", "b"]
  , body := (.ret (.binop "*" (.name "a") (.name "b"))) }

/-- `ov.c:<global>`  (from `ov.c`) -/
def f_ov_c__global_ : Func :=
  { name := "ov.c:<global>"
  , params := []
  , body := (.seq (.hole "stmt:METHOD_REF") (.hole "stmt:METHOD_REF")) }

/-- `addbig`  (from `ov.c`) -/
def f_addbig : Func :=
  { name := "addbig"
  , params := ["a", "b"]
  , body := (.ret (.binop "+" (.name "a") (.name "b"))) }

/-- `<includes>:<global>`  (from `<includes>`) -/
def f__includes___global_ : Func :=
  { name := "<includes>:<global>"
  , params := []
  , body := .skip }

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_mulbig,
  f_ov_c__global_,
  f_addbig,
  f__includes___global_
] }

end Autoform.Generated