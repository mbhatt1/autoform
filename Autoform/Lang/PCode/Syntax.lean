import Std

/-!
# Raw p-code: a machine-level target independent of source language and ISA

The input is SLEIGH's raw instruction semantics, not decompiler output. Sizes and
offsets are in bytes; values are little or big endian unsigned bit patterns. The
lifter and its processor descriptions remain outside Lean's trusted kernel.
-/

namespace Autoform.PCode

structure Varnode where
  space : String
  offset : Nat
  size : Nat
  deriving Repr, Inhabited, DecidableEq

structure Op where
  code : String
  output : Option Varnode := none
  inputs : List Varnode := []
  /-- LOAD/STORE's space ID is resolved by the lifter, not read as an operand. -/
  space : String := "ram"
  /-- Addressable units in the LOAD/STORE space, explicitly supplied by the loader. -/
  wordSize : Nat := 1
  /-- A decoder-mode output must retain the mode used for static translation. -/
  guardValue : Option Nat := none
  deriving Repr, Inhabited, DecidableEq

structure Instruction where
  address : Nat
  /-- Includes delay-slot bytes consumed by this instruction's translation. -/
  length : Nat
  ops : List Op
  deriving Repr, Inhabited, DecidableEq

structure Program where
  language : String
  bigEndian : Bool := false
  codeSpace : String := "ram"
  instructions : List Instruction
  deriving Repr, Inhabited

/-- A partial byte store. Uninitialized reads are holes, never invented zeros.
Registers share this store, so overlapping register names really alias. -/
abbrev Memory := List ((String × Nat) × Nat)

structure State where
  pc : Nat
  micro : Nat := 0
  memory : Memory := []
  deriving Repr, Inhabited, DecidableEq

inductive Outcome where
  /-- Reached an explicitly requested observation address, before executing it. -/
  | stopped : State → Outcome
  | outOfFuel : State → Outcome
  | hole : String → State → Outcome
  deriving Repr, Inhabited, DecidableEq

end Autoform.PCode
