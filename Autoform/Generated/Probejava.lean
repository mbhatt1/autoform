import Autoform.Lang.Core.Semantics

/-!
# Probejava — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated
open Autoform.Core

/-- `Probe.addLong:long(long,long)`  (from `Probe.java`) -/
def f_Probe_addLong_long_long_long_ : Func :=
  { name := "Probe.addLong:long(long,long)"
  , params := ["a", "b"]
  , body := (.ret (.binop "+" (.name "a") (.name "b"))) }

/-- `Probe.shiftBig:int(int,int)`  (from `Probe.java`) -/
def f_Probe_shiftBig_int_int_int_ : Func :=
  { name := "Probe.shiftBig:int(int,int)"
  , params := ["a", "k"]
  , body := (.ret (.hole "op:shiftLeft")) }

/-- `Probe.divZero:int(int,int)`  (from `Probe.java`) -/
def f_Probe_divZero_int_int_int_ : Func :=
  { name := "Probe.divZero:int(int,int)"
  , params := ["a", "b"]
  , body := (.ret (.binop "/" (.name "a") (.name "b"))) }

/-- `Probe.ushift:int(int,int)`  (from `Probe.java`) -/
def f_Probe_ushift_int_int_int_ : Func :=
  { name := "Probe.ushift:int(int,int)"
  , params := ["a", "k"]
  , body := (.ret (.hole "op:arithmeticShiftRight")) }

/-- `Probe.mulLong:long(long,long)`  (from `Probe.java`) -/
def f_Probe_mulLong_long_long_long_ : Func :=
  { name := "Probe.mulLong:long(long,long)"
  , params := ["a", "b"]
  , body := (.ret (.binop "*" (.name "a") (.name "b"))) }

/-- `Probe.<init>:void()`  (from `Probe.java`) -/
def f_Probe__init__void__ : Func :=
  { name := "Probe.<init>:void()"
  , params := ["this"]
  , body := .skip }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_Probe_addLong_long_long_long_,
  f_Probe_shiftBig_int_int_int_,
  f_Probe_divZero_int_int_int_,
  f_Probe_ushift_int_int_int_,
  f_Probe_mulLong_long_long_long_,
  f_Probe__init__void__
] }

end Autoform.Generated