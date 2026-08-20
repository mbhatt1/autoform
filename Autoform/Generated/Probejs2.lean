import Autoform.Lang.Core.Semantics

/-!
# Probejs2 — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated
open Autoform.Core

/-- `q.js::program:looseEq`  (from `q.js`) -/
def f_q_js__program_looseEq : Func :=
  { name := "q.js::program:looseEq"
  , params := ["this", "a", "b"]
  , body := (.ret (.binop "==" (.name "a") (.name "b"))) }

/-- `q.js::program`  (from `q.js`) -/
def f_q_js__program : Func :=
  { name := "q.js::program"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "looseEq" (.fnref "q.js::program:looseEq"))
                (.assign "strictEq" (.fnref "q.js::program:strictEq"))))) }

/-- `q.js::program:strictEq`  (from `q.js`) -/
def f_q_js__program_strictEq : Func :=
  { name := "q.js::program:strictEq"
  , params := ["this", "a", "b"]
  , body := (.ret (.binop "==" (.name "a") (.name "b"))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_q_js__program_looseEq,
  f_q_js__program,
  f_q_js__program_strictEq
] }

end Autoform.Generated