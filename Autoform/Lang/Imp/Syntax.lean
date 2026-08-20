import Specimen

/-!
# Imp — deep-embedded syntax

Layer 3 of the autoform pipeline lowers a real source AST into terms of these types.
Nothing here is LLM-generated at run time: the transpiler is a deterministic program.

`Stmt.opaqueHole` is the effect boundary. Anything the transpiler cannot faithfully
embed (I/O, FFI, reflection, concurrency) becomes a hole carrying a name, and the
trust ledger counts holes rather than silently dropping the construct.
-/

namespace Autoform.Imp

/-- Variable names. `Nat` rather than `String` so generators stay small. -/
abbrev Var := Nat

/-- Arithmetic expressions. -/
inductive Expr where
  | lit   : Int → Expr
  | var   : Var → Expr
  | add   : Expr → Expr → Expr
  | sub   : Expr → Expr → Expr
  | mul   : Expr → Expr → Expr
  deriving Repr, DecidableEq, Inhabited

/-- Boolean expressions. -/
inductive BExpr where
  | tt    : BExpr
  | ff    : BExpr
  | le    : Expr → Expr → BExpr
  | eq    : Expr → Expr → BExpr
  | not   : BExpr → BExpr
  | and   : BExpr → BExpr → BExpr
  deriving Repr, DecidableEq, Inhabited

/-- Statements. -/
inductive Stmt where
  | skip   : Stmt
  | assign : Var → Expr → Stmt
  | seq    : Stmt → Stmt → Stmt
  | ite    : BExpr → Stmt → Stmt → Stmt
  | loop   : BExpr → Stmt → Stmt
  /-- Effect boundary: an untranslated construct, tracked by name in the ledger. -/
  | opaqueHole : Nat → Stmt
  deriving Repr, DecidableEq, Inhabited

/-- Program state: a finite store indexed by `Var`, defaulting to `0` out of range.

    Deliberately a concrete `List`, not a function `Var → Int`: Specimen/Plausible must
    be able to *generate* states, and function types are not generable. -/
abbrev State := List Int

namespace State

/-- The empty store. Every variable reads as `0`. -/
def empty : State := []

/-- Read a variable; out-of-range reads are `0`. -/
def get (s : State) (x : Var) : Int := s.getD x 0

/-- Write a variable, growing the store with zeros as needed. -/
def set (s : State) (x : Var) (v : Int) : State :=
  let s' := if x < s.length then s else s ++ List.replicate (x + 1 - s.length) 0
  List.set s' x v

end State

end Autoform.Imp
