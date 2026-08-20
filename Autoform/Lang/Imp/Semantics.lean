import Autoform.Lang.Imp.Syntax

/-!
# Imp — semantics

Two presentations, deliberately kept apart:

* `BigStep` — an **inductive relation**. This is the specification of the language.
  Specimen derives generators/enumerators/checkers for it, which is what makes the
  semantics testable before anything is proved.
* `eval` — a **computable, fuel-indexed** interpreter. This is what the differential
  harness runs against a real runtime.

`evalStmt_sound` is the bridge. In the full pipeline the same shape recurs one level up:
the deep-embedded program is proved equivalent to a clean shallow Lean function.
-/

namespace Autoform.Imp

/-- Arithmetic evaluation. Total, so no fuel needed. -/
def evalExpr (s : State) : Expr → Int
  | .lit n     => n
  | .var x     => s.get x
  | .add a b   => evalExpr s a + evalExpr s b
  | .sub a b   => evalExpr s a - evalExpr s b
  | .mul a b   => evalExpr s a * evalExpr s b

/-- Boolean evaluation. Total. -/
def evalBExpr (s : State) : BExpr → Bool
  | .tt        => true
  | .ff        => false
  | .le a b    => evalExpr s a ≤ evalExpr s b
  | .eq a b    => evalExpr s a == evalExpr s b
  | .not b     => !evalBExpr s b
  | .and a b   => evalBExpr s a && evalBExpr s b

/-- Big-step operational semantics: `BigStep s c s'` means running `c` in `s` terminates
in `s'`. Note there is **no rule for `opaqueHole`** — an untranslated construct has no
semantics, so any theorem about a program containing one is vacuous unless the hole is
discharged by an explicit assumption. That is the point. -/
inductive BigStep : State → Stmt → State → Prop where
  | skip (s) :
      BigStep s .skip s
  | assign (s x e) :
      BigStep s (.assign x e) (s.set x (evalExpr s e))
  | seq {s₁ s₂ s₃ c₁ c₂} :
      BigStep s₁ c₁ s₂ → BigStep s₂ c₂ s₃ → BigStep s₁ (.seq c₁ c₂) s₃
  | iteTrue {s s' b c₁ c₂} :
      evalBExpr s b = true  → BigStep s c₁ s' → BigStep s (.ite b c₁ c₂) s'
  | iteFalse {s s' b c₁ c₂} :
      evalBExpr s b = false → BigStep s c₂ s' → BigStep s (.ite b c₁ c₂) s'
  | loopFalse {s b c} :
      evalBExpr s b = false → BigStep s (.loop b c) s
  | loopTrue {s s' s'' b c} :
      evalBExpr s b = true → BigStep s c s' → BigStep s' (.loop b c) s'' →
      BigStep s (.loop b c) s''

/-- Why a run produced no result. Distinguishing these matters for the ledger: running
out of fuel is ignorance, hitting a hole is a tracked assumption. -/
inductive Outcome where
  | ok        : State → Outcome
  | outOfFuel : Outcome
  | hitHole   : Nat → Outcome
  deriving Repr, DecidableEq, Inhabited

/-- Fuel-indexed interpreter. Structurally recursive on fuel, hence total. -/
def evalStmt : Nat → State → Stmt → Outcome
  | 0,     _, _              => .outOfFuel
  | _+1,   s, .skip          => .ok s
  | _+1,   s, .assign x e    => .ok (s.set x (evalExpr s e))
  | _+1,   _, .opaqueHole h  => .hitHole h
  | n+1,   s, .seq c₁ c₂     =>
      match evalStmt n s c₁ with
      | .ok s'     => evalStmt n s' c₂
      | .outOfFuel => .outOfFuel
      | .hitHole h => .hitHole h
  | n+1,   s, .ite b c₁ c₂   =>
      if evalBExpr s b then evalStmt n s c₁ else evalStmt n s c₂
  | n+1,   s, .loop b c     =>
      if evalBExpr s b then
        match evalStmt n s c with
        | .ok s'     => evalStmt n s' (.loop b c)
        | .outOfFuel => .outOfFuel
        | .hitHole h => .hitHole h
      else .ok s

/-- **Soundness of the interpreter against the relation.** Anything the executable
evaluator claims, the specification agrees with. -/
theorem evalStmt_sound :
    ∀ (n : Nat) (s s' : State) (c : Stmt), evalStmt n s c = .ok s' → BigStep s c s' := by
  intro n
  induction n with
  | zero => intro s s' c h; simp [evalStmt] at h
  | succ n ih =>
    intro s s' c h
    cases c with
    | skip => simp [evalStmt] at h; subst h; exact .skip _
    | assign x e => simp [evalStmt] at h; subst h; exact .assign _ _ _
    | opaqueHole i => simp [evalStmt] at h
    | seq c₁ c₂ =>
      simp only [evalStmt] at h
      split at h
      · next s₂ h₁ => exact .seq (ih _ _ _ h₁) (ih _ _ _ h)
      · next => cases h
      · next => cases h
    | ite b c₁ c₂ =>
      simp only [evalStmt] at h
      split at h
      · next hb => exact .iteTrue hb (ih _ _ _ h)
      · next hb => exact .iteFalse (by simpa using hb) (ih _ _ _ h)
    | loop b c =>
      simp only [evalStmt] at h
      split at h
      · next hb =>
        split at h
        · next s₂ h₁ => exact .loopTrue hb (ih _ _ _ h₁) (ih _ _ _ h)
        · next => cases h
        · next => cases h
      · next hb => simp at h; subst h; exact .loopFalse (by simpa using hb)

/-!
## Independent characterization of the boolean evaluator

`scripts/mutate.py` found that `evalStmt_sound` is structurally incapable of detecting
any bug in `evalBExpr`: `BigStep`'s `iteTrue`/`iteFalse`/`loopTrue`/`loopFalse` side
conditions are themselves stated in terms of `evalBExpr`, so mutating `evalBExpr` mutates
*both sides* of the equation and the proof goes through unchanged. Measured mutation
score: 2 killed / 6 survived (25%, WEAK) — and every survivor was in `evalBExpr`.

This is precisely the vacuity class that `#audit_depends` cannot see: `evalStmt_sound`
*does* transitively depend on `evalBExpr`, it just says nothing about it. It is the
argument for keeping the mutation gate separate from the dependency check.

The fix is to pin `evalBExpr` against something not defined in terms of itself — the
integer order and equality on `evalExpr`'s results. These lemmas are `rfl`, but they are
not vacuous: each one dies under the corresponding mutation.
-/

section Characterization

variable (s : State) (a b : Expr) (p q : BExpr)

@[simp] theorem evalBExpr_tt  : evalBExpr s .tt = true := rfl
@[simp] theorem evalBExpr_ff  : evalBExpr s .ff = false := rfl

/-- `le` really is the integer order on the operands, not merely whatever `evalBExpr`
happens to compute. -/
@[simp] theorem evalBExpr_le  :
    evalBExpr s (.le a b) = decide (evalExpr s a ≤ evalExpr s b) := rfl

/-- `eq` really is equality on the operands. -/
@[simp] theorem evalBExpr_eq  :
    evalBExpr s (.eq a b) = (evalExpr s a == evalExpr s b) := rfl

/-- `not` really is boolean negation. -/
@[simp] theorem evalBExpr_not : evalBExpr s (.not p) = !evalBExpr s p := rfl

/-- `and` really is boolean conjunction, and in particular is not `or`. -/
@[simp] theorem evalBExpr_and :
    evalBExpr s (.and p q) = (evalBExpr s p && evalBExpr s q) := rfl

/-- Conjunction is not disjunction. Stated explicitly because the `&&`→`||` mutant
survived until these lemmas existed. -/
theorem evalBExpr_and_ne_or :
    ∃ (s : State) (p q : BExpr),
      evalBExpr s (.and p q) ≠ (evalBExpr s p || evalBExpr s q) := by
  exact ⟨[], .tt, .ff, by simp⟩

/-- `tt` and `ff` are distinguishable — kills the `.tt => false` mutant. -/
theorem evalBExpr_tt_ne_ff (s : State) : evalBExpr s .tt ≠ evalBExpr s .ff := by
  simp

/-- `le` is not `ge` — kills the `≤`→`≥` mutant. -/
theorem evalBExpr_le_ne_ge :
    ∃ (s : State) (a b : Expr),
      evalBExpr s (.le a b) ≠ decide (evalExpr s b ≤ evalExpr s a) := by
  exact ⟨[], .lit 0, .lit 1, by simp [evalBExpr, evalExpr]⟩

end Characterization

end Autoform.Imp
