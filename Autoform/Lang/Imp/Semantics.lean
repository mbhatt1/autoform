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
survived until these lemmas existed.

Proved by `decide` — by evaluating `evalBExpr` itself — and deliberately *not* via the
`@[simp]` lemmas above. Through `simp` it was hostage to `evalBExpr_and`: under the
mutant that lemma fails, Lean's error recovery keeps it (with a `sorry` proof) in the
simp set, and this theorem then "proved" the false statement through it. The
per-theorem mutation gate recorded it as killing nothing. -/
theorem evalBExpr_and_ne_or :
    ∃ (s : State) (p q : BExpr),
      evalBExpr s (.and p q) ≠ (evalBExpr s p || evalBExpr s q) :=
  ⟨[], .tt, .ff, by decide⟩

/-- `tt` and `ff` are distinguishable — kills the `.tt => false` and `.ff => true`
mutants. Unfolds `evalBExpr` directly for the same reason as `evalBExpr_and_ne_or`. -/
theorem evalBExpr_tt_ne_ff (s : State) : evalBExpr s .tt ≠ evalBExpr s .ff := by
  intro h; simp only [evalBExpr] at h; exact Bool.noConfusion h

/-- `le` is not `ge` — kills the `≤`→`≥` mutant. -/
theorem evalBExpr_le_ne_ge :
    ∃ (s : State) (a b : Expr),
      evalBExpr s (.le a b) ≠ decide (evalExpr s b ≤ evalExpr s a) :=
  ⟨[], .lit 0, .lit 1, by decide⟩

/-!
## Independent characterization of the arithmetic evaluator

The same vacuity, one level down: `BigStep.assign` and the `le`/`eq` lemmas above are
all stated in terms of `evalExpr`, so `+`→`-`, `-`→`+` and `*`→`/` in `evalExpr`
survived *every* theorem in this file when the gate was re-run with per-theorem
attribution (see `mutation-Imp.json`). Pinned against `Int`'s own operations here.
-/

/-- `add` is integer addition. -/
@[simp] theorem evalExpr_add : evalExpr s (.add a b) = evalExpr s a + evalExpr s b := rfl
/-- `sub` is integer subtraction. -/
@[simp] theorem evalExpr_sub : evalExpr s (.sub a b) = evalExpr s a - evalExpr s b := rfl
/-- `mul` is integer multiplication. -/
@[simp] theorem evalExpr_mul : evalExpr s (.mul a b) = evalExpr s a * evalExpr s b := rfl

end Characterization

/-!
## The store

`State.get`/`State.set` (in `Syntax.lean`) are used by `BigStep.assign` and by `evalExpr`
alike, so no theorem above can see a bug in them: every one of the nine mutants of
`State.set`/`State.get` survived the whole file. These are the read-over-write laws a
store must satisfy, plus the documented default.
-/

theorem State.get_empty (x : Var) : State.empty.get x = 0 := by
  simp [State.empty, State.get]

theorem State.get_set_self (s : State) (x : Var) (v : Int) : (s.set x v).get x = v := by
  -- Kept free of the padding arithmetic's exact shape (`omega` decides the length side
  -- condition), so the mutation gate grades this statement, not the proof script.
  unfold State.set State.get
  split
  · simp [*]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_self]
    · rfl
    · simp only [List.length_append, List.length_replicate]
      omega

theorem State.get_set_ne (s : State) (x y : Var) (v : Int) (h : y ≠ x) :
    (s.set x v).get y = s.get y := by
  unfold State.set State.get
  split
  · simp [Ne.symm h]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm h, if_false,
      List.getElem?_append, List.getElem?_replicate]
    by_cases hy : y < s.length
    · simp [hy]
    · have : s[y]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hy)
      simp only [hy, if_false, this]
      split <;> simp

/-!
## Completeness, and the hole/fuel distinction

`evalStmt_sound` only constrains runs that end in `.ok`. The `Outcome` type exists to keep
"ran out of fuel" (ignorance) apart from "hit an untranslated construct" (a tracked
assumption), but nothing stated that: the three mutants that report a hole as
`.outOfFuel` survived every theorem. `HitsHole` says, independently of `evalStmt`, when a
run reaches a hole; `evalStmt_hole_complete` says the interpreter reports it as such.
`evalStmt_complete` (the converse of `evalStmt_sound`) and fuel monotonicity are needed
to prove it.
-/

theorem evalStmt_mono :
    ∀ (n : Nat) (s : State) (c : Stmt) (r : Outcome),
      evalStmt n s c = r → r ≠ .outOfFuel → evalStmt (n + 1) s c = r := by
  intro n
  induction n with
  | zero => intro s c r h hr; simp [evalStmt] at h; exact absurd h.symm hr
  | succ n ih =>
    intro s c r h hr
    cases c with
    | skip => simpa [evalStmt] using h
    | assign x e => simpa [evalStmt] using h
    | opaqueHole i => simpa [evalStmt] using h
    | seq c₁ c₂ =>
      simp only [evalStmt] at h ⊢
      cases h₁ : evalStmt n s c₁ with
      | ok s₂ =>
        rw [h₁] at h
        rw [ih _ _ _ h₁ (by simp)]
        exact ih _ _ _ h hr
      | outOfFuel => rw [h₁] at h; exact absurd h.symm hr
      | hitHole i =>
        rw [h₁] at h
        rw [ih _ _ _ h₁ (by simp)]
        exact h
    | ite b c₁ c₂ =>
      simp only [evalStmt] at h ⊢
      split at h
      · next hb => simp [hb]; exact ih _ _ _ h hr
      · next hb => simp [hb]; exact ih _ _ _ h hr
    | loop b c =>
      simp only [evalStmt] at h ⊢
      split at h
      · next hb =>
        simp only [hb, if_true]
        cases h₁ : evalStmt n s c with
        | ok s₂ =>
          rw [h₁] at h
          rw [ih _ _ _ h₁ (by simp)]
          exact ih _ _ _ h hr
        | outOfFuel => rw [h₁] at h; exact absurd h.symm hr
        | hitHole i =>
          rw [h₁] at h
          rw [ih _ _ _ h₁ (by simp)]
          exact h
      · next hb => simp [hb]; exact h

theorem evalStmt_mono_le {n m : Nat} {s : State} {c : Stmt} {r : Outcome}
    (h : evalStmt n s c = r) (hr : r ≠ .outOfFuel) (hle : n ≤ m) : evalStmt m s c = r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact evalStmt_mono _ _ _ _ ih hr

theorem evalStmt_complete {s c s'} (h : BigStep s c s') : ∃ n, evalStmt n s c = .ok s' := by
  induction h with
  | skip s => exact ⟨1, rfl⟩
  | assign s x e => exact ⟨1, rfl⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨n₁, e₁⟩ := ih₁; obtain ⟨n₂, e₂⟩ := ih₂
    refine ⟨max n₁ n₂ + 1, ?_⟩
    simp only [evalStmt, evalStmt_mono_le e₁ (by simp) (Nat.le_max_left _ _),
      evalStmt_mono_le e₂ (by simp) (Nat.le_max_right _ _)]
  | iteTrue hb _ ih => obtain ⟨n, e⟩ := ih; exact ⟨n + 1, by simp [evalStmt, hb, e]⟩
  | iteFalse hb _ ih => obtain ⟨n, e⟩ := ih; exact ⟨n + 1, by simp [evalStmt, hb, e]⟩
  | loopFalse hb => exact ⟨1, by simp [evalStmt, hb]⟩
  | loopTrue hb _ _ ih₁ ih₂ =>
    obtain ⟨n₁, e₁⟩ := ih₁; obtain ⟨n₂, e₂⟩ := ih₂
    refine ⟨max n₁ n₂ + 1, ?_⟩
    simp only [evalStmt, hb, if_true, evalStmt_mono_le e₁ (by simp) (Nat.le_max_left _ _),
      evalStmt_mono_le e₂ (by simp) (Nat.le_max_right _ _)]

/-- `HitsHole s c h`: running `c` from `s` reaches the hole `h` before terminating.
Defined over `BigStep` and `evalBExpr`, not over `evalStmt`. -/
inductive HitsHole : State → Stmt → Nat → Prop where
  | hole (s h) : HitsHole s (.opaqueHole h) h
  | seqL {s c₁ c₂ h} : HitsHole s c₁ h → HitsHole s (.seq c₁ c₂) h
  | seqR {s s' c₁ c₂ h} : BigStep s c₁ s' → HitsHole s' c₂ h → HitsHole s (.seq c₁ c₂) h
  | iteTrue {s b c₁ c₂ h} : evalBExpr s b = true → HitsHole s c₁ h → HitsHole s (.ite b c₁ c₂) h
  | iteFalse {s b c₁ c₂ h} : evalBExpr s b = false → HitsHole s c₂ h → HitsHole s (.ite b c₁ c₂) h
  | loopBody {s b c h} : evalBExpr s b = true → HitsHole s c h → HitsHole s (.loop b c) h
  | loopNext {s s' b c h} : evalBExpr s b = true → BigStep s c s' → HitsHole s' (.loop b c) h →
      HitsHole s (.loop b c) h

theorem evalStmt_hole_complete {s c h} (hh : HitsHole s c h) :
    ∃ n, evalStmt n s c = .hitHole h := by
  induction hh with
  | hole s h => exact ⟨1, rfl⟩
  | seqL _ ih => obtain ⟨n, e⟩ := ih; exact ⟨n + 1, by simp [evalStmt, e]⟩
  | seqR hs _ ih =>
    obtain ⟨n₁, e₁⟩ := evalStmt_complete hs; obtain ⟨n₂, e₂⟩ := ih
    refine ⟨max n₁ n₂ + 1, ?_⟩
    simp only [evalStmt, evalStmt_mono_le e₁ (by simp) (Nat.le_max_left _ _),
      evalStmt_mono_le e₂ (by simp) (Nat.le_max_right _ _)]
  | iteTrue hb _ ih => obtain ⟨n, e⟩ := ih; exact ⟨n + 1, by simp [evalStmt, hb, e]⟩
  | iteFalse hb _ ih => obtain ⟨n, e⟩ := ih; exact ⟨n + 1, by simp [evalStmt, hb, e]⟩
  | loopBody hb _ ih => obtain ⟨n, e⟩ := ih; exact ⟨n + 1, by simp [evalStmt, hb, e]⟩
  | loopNext hb hs _ ih =>
    obtain ⟨n₁, e₁⟩ := evalStmt_complete hs; obtain ⟨n₂, e₂⟩ := ih
    refine ⟨max n₁ n₂ + 1, ?_⟩
    simp only [evalStmt, hb, if_true, evalStmt_mono_le e₁ (by simp) (Nat.le_max_left _ _),
      evalStmt_mono_le e₂ (by simp) (Nat.le_max_right _ _)]

end Autoform.Imp
