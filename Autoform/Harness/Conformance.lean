import Autoform.Lang.Imp.Semantics
import Specimen
import Plausible

/-!
# Conformance harness

The semantics of a language must be *testable before it is proved*, or an
LLM-assisted (or human-assisted) semantics is unfalsifiable.

Specimen derives producers and checkers directly from the `BigStep` **inductive
relation** — so the thing being fuzzed is the specification itself, not a hand-written
paraphrase of it. That is what removes the usual drift between "the property we tested"
and "the theorem we proved".

Three uses here:

1. `Arbitrary`/`Enum` on the syntax — random programs, for differential testing
   `evalStmt` against a real runtime (Layer 2's conformance oracle).
2. A derived **checker** for `BigStep` — decides the relation without a hand-written
   decision procedure, so `evalStmt` can be diffed against the relation directly.
3. `plausible` as the **refutation gate**: every candidate specification is attacked
   before a prover is allowed to spend time on it.
-/

namespace Autoform.Imp

open Plausible

deriving instance Arbitrary, Shrinkable, Enum for Expr
deriving instance Arbitrary, Shrinkable, Enum for BExpr
deriving instance Arbitrary, Shrinkable, Enum for Stmt

-- Sample random programs: the corpus for differential testing against a real runtime.
-- #eval runArbitrary (α := Stmt) 5
-- #eval runEnum (α := Stmt) 3

/-!
## The refutation gate

Candidate specifications are fuzzed *first*. Survivors go to the proof portfolio;
refuted candidates are discarded before any prover time is spent.
-/

/-!
## The refutation gate

Candidate specifications are stated as `abbrev`s and fuzzed with `Testable.check`
(see `Demo.lean`), **not** with the `plausible` tactic: the tactic closes the goal with
`sorry`, which would pollute the axiom audit with exactly the thing the audit exists to
catch. A gate must never manufacture evidence of its own success.
-/

/-- Candidate 1: the interpreter is monotone in fuel. Survives the gate, so it is worth
sending to the proof portfolio. -/
abbrev candidateFuelMonotone : Prop :=
  ∀ (s : State) (c : Stmt) (n : Nat),
    evalStmt n s c ≠ .outOfFuel → evalStmt (n + 1) s c = evalStmt n s c

/-- Candidate 2: false, and of exactly the shape LLM spec synthesis produces. Refuted by
the gate, so no prover time is spent on it. -/
abbrev candidateBogus : Prop :=
  ∀ (s : State) (c : Stmt), evalStmt 5 s c = .ok s

end Autoform.Imp
