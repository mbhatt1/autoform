import Autoform.Lang.Core.Semantics

/-!
# Probego — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated
open Autoform.Core

/-- `probe.AddInt`  (from `probe.go`) -/
def f_probe_AddInt : Func :=
  { name := "probe.AddInt"
  , params := ["a", "b"]
  , body := (.ret (.binop "+" (.name "a") (.name "b"))) }

/-- `probe.MulInt`  (from `probe.go`) -/
def f_probe_MulInt : Func :=
  { name := "probe.MulInt"
  , params := ["a", "b"]
  , body := (.ret (.binop "*" (.name "a") (.name "b"))) }

/-- `probe.DivInt`  (from `probe.go`) -/
def f_probe_DivInt : Func :=
  { name := "probe.DivInt"
  , params := ["a", "b"]
  , body := (.ret (.binop "/" (.name "a") (.name "b"))) }

/-- `probe.ShiftInt`  (from `probe.go`) -/
def f_probe_ShiftInt : Func :=
  { name := "probe.ShiftInt"
  , params := ["a", "k"]
  , body := (.ret (.hole "op:shiftLeft")) }

/-- `probe.go:probe.probe.go`  (from `probe.go`) -/
def f_probe_go_probe_probe_go : Func :=
  { name := "probe.go:probe.probe.go"
  , params := []
  , body := .skip }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_probe_AddInt,
  f_probe_MulInt,
  f_probe_DivInt,
  f_probe_ShiftInt,
  f_probe_go_probe_probe_go
] }

end Autoform.Generated