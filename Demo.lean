import Autoform

/-!
Phase-0 end-to-end demo. Run with:  lake env lean Demo.lean
-/
open Autoform.Imp Plausible

section RefutationGate
-- Candidates are fuzzed BEFORE any prover time is spent.
-- Survives -> send to the proof portfolio.
#eval Testable.check
  (∀ (s : State) (c : Stmt) (n : Nat),
      evalStmt n s c ≠ .outOfFuel → evalStmt (n + 1) s c = evalStmt n s c)
  { numInst := 25, maxSize := 6 }

-- Refuted -> discard before any prover time is spent.
#eval Testable.check
  (∀ (s : State) (c : Stmt), evalStmt 5 s c = .ok s)
  { numInst := 25, maxSize := 6 }
end RefutationGate

section AxiomAudit
-- The real theorem stands on the ordinary Lean axioms.
#audit_axioms Autoform.Imp.evalStmt_sound
end AxiomAudit

section VacuityDetection
-- A theorem that is true, provable, and says nothing about the implementation.
-- This is the single most common failure mode of generated specifications.
theorem vacuous_spec (s : State) : evalStmt 0 s .skip = .outOfFuel := rfl

#audit_depends Autoform.Imp.evalStmt_sound on Autoform.Imp.evalStmt Autoform.Imp.BigStep
#audit_depends vacuous_spec on Autoform.Imp.BigStep   -- expected: VACUOUS

-- A theorem admitted with `sorry` is caught by the axiom audit, not by inspection.
theorem not_actually_proved (s : State) (c : Stmt) : evalStmt 99 s c ≠ .outOfFuel := by
  sorry

#audit_axioms not_actually_proved   -- expected: TRUSTED-CODE LEAK
end VacuityDetection

section Ledger
#audit_ledger Autoform.Imp.evalStmt_sound vacuous_spec not_actually_proved
end Ledger
