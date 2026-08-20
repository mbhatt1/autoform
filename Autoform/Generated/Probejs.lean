import Autoform.Lang.Core.Semantics

/-!
# Probejs — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated
open Autoform.Core

/-- `probe.js::program:addOverflow`  (from `probe.js`) -/
def f_probe_js__program_addOverflow : Func :=
  { name := "probe.js::program:addOverflow"
  , params := ["this", "a", "b"]
  , body := (.ret (.binop "+" (.name "a") (.name "b"))) }

/-- `probe.js::program`  (from `probe.js`) -/
def f_probe_js__program : Func :=
  { name := "probe.js::program"
  , params := ["this"]
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
                      (.assign "addOverflow" (.fnref "probe.js::program:addOverflow"))
                      (.seq
                        (.assign "halve" (.fnref "probe.js::program:halve"))
                        (.seq
                          (.assign "looseEq" (.fnref "probe.js::program:looseEq"))
                          (.seq
                            (.assign "modneg" (.fnref "probe.js::program:modneg"))
                            (.assign "shiftBig" (.fnref "probe.js::program:shiftBig"))))))))))) }

/-- `probe.js::program:halve`  (from `probe.js`) -/
def f_probe_js__program_halve : Func :=
  { name := "probe.js::program:halve"
  , params := ["this", "a", "b"]
  , body := (.ret (.binop "/" (.name "a") (.name "b"))) }

/-- `probe.js::program:looseEq`  (from `probe.js`) -/
def f_probe_js__program_looseEq : Func :=
  { name := "probe.js::program:looseEq"
  , params := ["this", "a", "b"]
  , body := (.ret (.binop "==" (.name "a") (.name "b"))) }

/-- `probe.js::program:modneg`  (from `probe.js`) -/
def f_probe_js__program_modneg : Func :=
  { name := "probe.js::program:modneg"
  , params := ["this", "a", "b"]
  , body := (.ret (.binop "%" (.name "a") (.name "b"))) }

/-- `probe.js::program:shiftBig`  (from `probe.js`) -/
def f_probe_js__program_shiftBig : Func :=
  { name := "probe.js::program:shiftBig"
  , params := ["this", "a", "k"]
  , body := (.ret (.hole "op:shiftLeft")) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_probe_js__program_addOverflow,
  f_probe_js__program,
  f_probe_js__program_halve,
  f_probe_js__program_looseEq,
  f_probe_js__program_modneg,
  f_probe_js__program_shiftBig
] }

end Autoform.Generated