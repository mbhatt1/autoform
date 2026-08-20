import Lean
import Autoform.Refine
import Autoform.Generated.Cachetools

/-!
# Contracts at holes

`STRATEGY.md` §5: *"Proof burden grows superlinearly with program size. Hence: verified
core + contracts, never whole-repo."* `Refine.lean` built the verified-core half. This
file builds the contracts half.

## The problem

`Expr.hole l` evaluates to `EResult.hole l`, `Stmt.hole l` to `Ctl.hole l`, and
`Refine.Outcome` deliberately has no `hole` constructor — so `refines_not_hole` says a
refined function provably never reaches an untranslated construct. That is the right
default and it is not being weakened here. Its cost is that **one** hole anywhere in a
function puts the entire function outside anything we can state: on `cachetools`, 165 of
238 functions are hole-free and 74 are call-closed, so roughly 70% of the code is
currently unspeakable.

## The mechanism

A contract is an *opt-in assumption about one hole*. Given a hole labelled
`op:starredUnpack`, a contract says: "every implementation of this construct, run with at
least `fuel` budget, satisfies `post`". Then

    RefinesUnder Γ p name N dom spec

says: **for every** way of filling the contracted holes that satisfies Γ, the resulting
program refines `spec`. It is a universally quantified statement over implementations,
not a re-definition of the semantics. Three consequences follow, and each is a theorem
below rather than a comment:

* With `Γ = []` there is nothing to fill, and `RefinesUnder` is *literally* `Refines`
  (`refinesUnder_nil_iff`). The two are therefore not confusable: a contract-relative
  theorem carries its `Γ` in its statement.
* If Γ is **unsatisfiable** — no implementation at all meets it — then `RefinesUnder Γ`
  holds for *every* spec (`refinesUnder_of_unsatisfiable`). This is the failure mode of
  every contract system stated as a theorem: an inconsistent assumption set is a machine
  for assuming your conclusion. Hence `Satisfiable` is a proof obligation, not a comment.
* If Γ **is** satisfiable, contracts still cannot prove two different things
  (`refinesUnder_unique`), which is the `refines_unique` guarantee recovered relative to Γ.

And the honest default has teeth: a contract that assumes *nothing* about a hole
(`topContract`) proves nothing at all — `methodkey_not_refinable_under_top` shows a real
`cachetools` function is provably unrefinable under it, because leaving the hole in place
is itself a legal implementation.

## What a contract-relative theorem is worth

Exactly the truth of its contracts. Nothing here discharges them; `ContractEnv.assumptions`
exists to hand them to `scripts/sacm.py` as named `Assumption` nodes **of that theorem**.
See `docs/contracts.md` for what a reader must check.
-/

namespace Autoform.Contracts

open Autoform.Core Autoform.Refine

/-! ## 1. Contracts -/

/-- A contract on one hole label.

* `post` is the load-bearing part: a predicate on the pre-heap, the environment at the
  hole site, and the pair the interpreter is assumed to produce. It ranges over the whole
  `Heap × EResult`, so an implementation is free to mutate the heap, raise, or return —
  and an *unconstrained* hole is exactly `post := fun _ _ _ => True`, which is the honest
  default and provably useless (`methodkey_not_refinable_under_top`).
* `fuel` is the budget the implementation is assumed to need. Without it the fuel bound
  `N` of a `RefinesUnder` theorem would be a lie: the cost of the untranslated construct
  has to appear somewhere, so it appears here.
* `stmt` is **unchecked prose** for the assurance case. It is never used in any proof;
  a wrong `stmt` misleads a human reader and cannot mislead the kernel. `docs/contracts.md`
  lists checking `stmt` against `post` as a reader obligation.
-/
structure Contract where
  /-- The CPG hole label this contract is about, e.g. `op:starredUnpack`. -/
  label : String
  /-- Human-readable rendering of `post`, for SACM. Unchecked. -/
  stmt  : String
  /-- Fuel budget the hole's implementation is assumed to need. -/
  fuel  : Nat
  /-- The assumed behaviour: `post h ρ (h', r)` for the hole evaluated in heap `h`,
  environment `ρ`, yielding heap `h'` and result `r`. -/
  post  : Heap → Env → Heap × EResult → Prop

/-- A contract environment: the assumptions a theorem is relative to. -/
abbrev ContractEnv := List Contract

/-- The hole labels a contract environment speaks about. -/
def ContractEnv.labels (Γ : ContractEnv) : List String := Γ.map (·.label)

/-! ## 2. Implementations

A contract constrains; an *implementation* is a witness. Filling a hole means replacing
`Expr.hole l` by an ordinary `Expr`, so implementations stay inside the language and the
semantics is untouched — there is no second interpreter to trust. -/

/-- A way of filling holes: hole label ↦ replacement expression. -/
abbrev Impl := List (String × Expr)

/-- The labels an implementation fills. -/
def Impl.labels (σ : Impl) : List String := σ.map (·.1)

mutual
/-- Substitute implementations for holes in an expression. -/
def substE (σ : Impl) : Expr → Expr
  | .hole l        => match σ.lookup l with
                      | some e => e
                      | none   => .hole l
  | .binop o a b   => .binop o (substE σ a) (substE σ b)
  | .unop o a      => .unop o (substE σ a)
  | .index a b     => .index (substE σ a) (substE σ b)
  | .field a f     => .field (substE σ a) f
  | .call f as     => .call f (substEL σ as)
  | .mcall r m as  => .mcall (substE σ r) m (substEL σ as)
  | .alloc c as    => .alloc c (substEL σ as)
  | .listE as      => .listE (substEL σ as)
  | .tupleE as     => .tupleE (substEL σ as)
  | .dictE kvs     => .dictE (substEP σ kvs)
  | .cond c a b    => .cond (substE σ c) (substE σ a) (substE σ b)
  | .isOp n a b    => .isOp n (substE σ a) (substE σ b)
  | .inOp n a b    => .inOp n (substE σ a) (substE σ b)
  | .lit l         => .lit l
  | .name x        => .name x
  | .fnref f       => .fnref f
  | .closure f     => .closure f
  | .classClosure c => .classClosure c

/-- Substitution across a list of expressions. -/
def substEL (σ : Impl) : List Expr → List Expr
  | []      => []
  | e :: es => substE σ e :: substEL σ es

/-- Substitution across key/value expression pairs. -/
def substEP (σ : Impl) : List (Expr × Expr) → List (Expr × Expr)
  | []           => []
  | (k, v) :: ps => (substE σ k, substE σ v) :: substEP σ ps
end

/-- Substitute implementations for holes in a statement.

`Stmt.hole` is **not** filled: a statement-level hole is an untranslated *effect*, and
filling it with an expression would be a category error. Statement holes therefore remain
outside the mechanism, which is the conservative direction — see `docs/contracts.md`. -/
def substS (σ : Impl) : Stmt → Stmt
  | .expr e          => .expr (substE σ e)
  | .assign x e      => .assign x (substE σ e)
  | .setField r f v  => .setField (substE σ r) f (substE σ v)
  | .setIndex r i v  => .setIndex (substE σ r) (substE σ i) (substE σ v)
  | .seq a b         => .seq (substS σ a) (substS σ b)
  | .ifte c a b      => .ifte (substE σ c) (substS σ a) (substS σ b)
  | .loop c a        => .loop (substE σ c) (substS σ a)
  | .forIn x e b     => .forIn x (substE σ e) (substS σ b)
  | .ret e           => .ret (substE σ e)
  | .tryCatch b x hd => .tryCatch (substS σ b) x (substS σ hd)
  | .tryFinally b f  => .tryFinally (substS σ b) (substS σ f)
  | .raise e         => .raise (substE σ e)
  | .setGlobal x e   => .setGlobal x (substE σ e)
  | .skip            => .skip
  | .brk             => .brk
  | .cont            => .cont
  | .del x           => .del x
  | .declGlobal x    => .declGlobal x
  | .hole l          => .hole l

/-- Apply an implementation to a function. Name and parameters are untouched, so name
resolution in the instantiated program is the same as in the original. -/
def Impl.onFunc (σ : Impl) (f : Func) : Func := { f with body := substS σ f.body }

/-- Apply an implementation to a whole program. -/
def Impl.onProgram (σ : Impl) (p : Program) : Program :=
  { p with funcs := p.funcs.map σ.onFunc }

/-! ### The empty implementation changes nothing

Needed for `refinesUnder_nil_iff`, and worth having independently: it says substitution
is not quietly rewriting the program. -/

mutual
theorem substE_nil : ∀ e : Expr, substE [] e = e
  | .hole _        => rfl
  | .lit _         => rfl
  | .name _        => rfl
  | .fnref _       => rfl
  | .closure _     => rfl
  | .classClosure _ => rfl
  | .binop o a b   => by rw [substE, substE_nil a, substE_nil b]
  | .unop o a      => by rw [substE, substE_nil a]
  | .index a b     => by rw [substE, substE_nil a, substE_nil b]
  | .field a f     => by rw [substE, substE_nil a]
  | .call f as     => by rw [substE, substEL_nil as]
  | .mcall r m as  => by rw [substE, substE_nil r, substEL_nil as]
  | .alloc c as    => by rw [substE, substEL_nil as]
  | .listE as      => by rw [substE, substEL_nil as]
  | .tupleE as     => by rw [substE, substEL_nil as]
  | .dictE kvs     => by rw [substE, substEP_nil kvs]
  | .cond c a b    => by rw [substE, substE_nil c, substE_nil a, substE_nil b]
  | .isOp n a b    => by rw [substE, substE_nil a, substE_nil b]
  | .inOp n a b    => by rw [substE, substE_nil a, substE_nil b]

theorem substEL_nil : ∀ es : List Expr, substEL [] es = es
  | []      => rfl
  | e :: es => by rw [substEL, substE_nil e, substEL_nil es]

theorem substEP_nil : ∀ ps : List (Expr × Expr), substEP [] ps = ps
  | []           => rfl
  | (k, v) :: ps => by rw [substEP, substE_nil k, substE_nil v, substEP_nil ps]
end

theorem substS_nil : ∀ s : Stmt, substS [] s = s
  | .skip | .brk | .cont | .del _ | .declGlobal _ | .hole _ => rfl
  | .expr e          => by rw [substS, substE_nil e]
  | .assign x e      => by rw [substS, substE_nil e]
  | .setField r f v  => by rw [substS, substE_nil r, substE_nil v]
  | .setIndex r i v  => by rw [substS, substE_nil r, substE_nil i, substE_nil v]
  | .seq a b         => by rw [substS, substS_nil a, substS_nil b]
  | .ifte c a b      => by rw [substS, substE_nil c, substS_nil a, substS_nil b]
  | .loop c a        => by rw [substS, substE_nil c, substS_nil a]
  | .forIn x e b     => by rw [substS, substE_nil e, substS_nil b]
  | .ret e           => by rw [substS, substE_nil e]
  | .tryCatch b x hd => by rw [substS, substS_nil b, substS_nil hd]
  | .tryFinally b f  => by rw [substS, substS_nil b, substS_nil f]
  | .raise e         => by rw [substS, substE_nil e]
  | .setGlobal x e   => by rw [substS, substE_nil e]

@[simp] theorem onFunc_nil (f : Func) : Impl.onFunc [] f = f := by
  simp [Impl.onFunc, substS_nil]

@[simp] theorem onProgram_nil (p : Program) : Impl.onProgram [] p = p := by
  simp [Impl.onProgram, List.map_id'']

/-! ## 3. Consistency, satisfiability, and `RefinesUnder` -/

/-- `Consistent Γ p σ`: the implementation `σ` is a legal witness for the contracts `Γ`
in program `p`.

Two clauses, both load-bearing:

* **`σ` may only fill labels `Γ` speaks about.** Without this clause a "contract-relative"
  theorem could silently repair holes nobody declared, and `refinesUnder_nil_iff` would be
  false. The contract environment is therefore an exact inventory of what was assumed.
* **Every filled hole really behaves as its contract says**, at every fuel budget at or
  above the contract's declared `fuel`, in every heap and every environment. Universal
  quantification over `h` and `ρ` is what makes a contract a statement about the
  *construct* rather than about one call site. -/
def Consistent (Γ : ContractEnv) (p : Program) (σ : Impl) : Prop :=
  (∀ l ∈ σ.labels, l ∈ Γ.labels) ∧
  (∀ c ∈ Γ, ∀ e, σ.lookup c.label = some e →
     ∀ k, c.fuel ≤ k → ∀ h ρ, c.post h ρ (evalExpr (ctxOf (σ.onProgram p)) k h ρ e))

/-- `σ` fills every hole `Γ` speaks about. A partial witness would leave a contracted
hole in place and the "refinement" would be about a program that still holes. -/
def Total (Γ : ContractEnv) (σ : Impl) : Prop :=
  ∀ c ∈ Γ, (σ.lookup c.label).isSome

/-- **The contracts are satisfiable**: some implementation actually meets them.

This is the anti-vacuity obligation, and it is not decorative — see
`refinesUnder_of_unsatisfiable`. §4's discipline is that a specification must be shown to
constrain something; for an assumption the corresponding obligation is that it can be
met. -/
def Satisfiable (Γ : ContractEnv) (p : Program) : Prop :=
  ∃ σ, Consistent Γ p σ ∧ Total Γ σ

/-- **Refinement relative to a contract environment.**

`RefinesUnder Γ p name N dom spec`: for *every* implementation of the contracted holes
that satisfies `Γ`, the instantiated program refines `spec` in the ordinary
`Refine.Refines` sense — same `Outcome` type with no `hole` and no `outOfFuel`, same
universally quantified fuel above the concrete bound `N`, same explicit domain.

Nothing about `Refines` is weakened. What is weakened is *which program* the claim is
about: not `p`, but every instantiation of `p` consistent with `Γ`. That is strictly less
than a claim about `p` itself, and the difference is exactly `Γ`. -/
def RefinesUnder (Γ : ContractEnv) (p : Program) (name : String) (N : Nat)
    (dom : List Val → Prop) (spec : List Val → Outcome) : Prop :=
  ∀ σ, Consistent Γ p σ → Total Γ σ → Refines (σ.onProgram p) name N dom spec

/-! ### Relationship to `Refines` -/

/-- **No contracts, no difference.** With an empty contract environment `RefinesUnder`
*is* `Refines`, in both directions.

The `←` direction is the one that needs the "only contracted labels" clause of
`Consistent`: it forces `σ = []`, so the instantiated program is `p` itself. Together
with the fact that `Γ` appears in the statement of every contract-relative theorem, this
is what keeps the two claims unconfusable — a theorem is unconditional iff its `Γ` is
literally `[]`. -/
theorem refinesUnder_nil_iff (p : Program) (name : String) (N : Nat)
    (dom : List Val → Prop) (spec : List Val → Outcome) :
    RefinesUnder [] p name N dom spec ↔ Refines p name N dom spec := by
  constructor
  · intro h
    have hcons : Consistent [] p [] := by
      refine ⟨?_, ?_⟩
      · intro l hl; cases hl
      · intro c hc; cases hc
    have htot : Total [] [] := by intro c hc; cases hc
    simpa using h [] hcons htot
  · intro h σ hc _
    have hσ : σ = [] := by
      cases σ with
      | nil => rfl
      | cons a as =>
        exact absurd (hc.1 a.1 (by simp [Impl.labels])) (by simp [ContractEnv.labels])
    subst hσ; simpa using h

/-- A contract-relative theorem becomes an ordinary one exactly when the contracts are
**discharged**: exhibit an implementation, prove it consistent, and the refinement holds
of the instantiated program. This is the only route from `RefinesUnder` to `Refines`, and
it terminates in `Refines (σ.onProgram p)` — a claim about the *repaired* program, never
silently about `p`. -/
theorem RefinesUnder.discharge {Γ p name N dom spec} (h : RefinesUnder Γ p name N dom spec)
    {σ : Impl} (hc : Consistent Γ p σ) (ht : Total Γ σ) :
    Refines (σ.onProgram p) name N dom spec := h σ hc ht

/-- Under contracts, the instantiated program still never reaches an untranslated hole
and still terminates. `Refine`'s non-vacuity theorems survive relativisation — what a
contract buys is a *different program*, not a laxer notion of refinement. -/
theorem refinesUnder_not_hole {Γ p name N dom spec} (h : RefinesUnder Γ p name N dom spec)
    {σ : Impl} (hc : Consistent Γ p σ) (ht : Total Γ σ)
    (args : List Val) (hd : dom args) (fuel : Nat) (hf : N ≤ fuel) (l : String) :
    runFunc (σ.onProgram p) fuel name args ≠ .hole l :=
  refines_not_hole (h σ hc ht) args hd fuel hf l

/-! ### The failure mode, stated as theorems

A contract mechanism is a machine for assuming your conclusion. The two theorems below
are what make that visible rather than latent. -/

/-- **An unsatisfiable contract environment proves everything.**

If no implementation meets `Γ`, then `RefinesUnder Γ` holds for every entry point, every
fuel bound, every domain and every specification — including contradictory ones. This is
not a defect to be patched; it is the definition of assuming a falsehood, and the useful
thing is to have it in the open. Its immediate corollary is the reader obligation in
`docs/contracts.md`: **a contract-relative theorem is worthless until `Satisfiable Γ p`
is proved.** -/
theorem refinesUnder_of_unsatisfiable {Γ p} (h : ¬ Satisfiable Γ p)
    (name : String) (N : Nat) (dom : List Val → Prop) (spec : List Val → Outcome) :
    RefinesUnder Γ p name N dom spec := by
  intro σ hc ht
  exact absurd ⟨σ, hc, ht⟩ h

/-- Contradiction is *detectable*: a contract whose `post` is unsatisfiable makes the
whole environment unsatisfiable, in any program. Nothing about the hole's implementation
is needed — the contract cannot be met by anything, which is precisely why it would
otherwise prove anything. -/
theorem unsatisfiable_of_false_post {Γ : ContractEnv} {p : Program} {c : Contract}
    (hmem : c ∈ Γ) (hfalse : ∀ h ρ st, ¬ c.post h ρ st) : ¬ Satisfiable Γ p := by
  rintro ⟨σ, hc, ht⟩
  have hs := ht c hmem
  match hlk : σ.lookup c.label with
  | none   => rw [hlk] at hs; exact absurd hs (by simp)
  | some e =>
    exact hfalse [] [] _ (hc.2 c hmem e hlk c.fuel (Nat.le_refl _) [] [])

/-- **Satisfiable contracts still cannot prove two different things.**

`Refine.refines_unique` says a program determines its shallow model. The relative form:
if `Γ` can be met at all, then two specs proved under the *same* `Γ` agree on the domain.
So a satisfiable contract environment is not a licence to conclude anything — it is
exactly as constraining as the program plus `Γ`.

Note what this does **not** say: two specs proved under *different* contract environments
need not agree, and must not be expected to. `methodkey_refinesUnder_value` and
`methodkey_refinesUnder_raise` below are a concrete pair. -/
theorem refinesUnder_unique {Γ p name N₁ N₂ dom s₁ s₂}
    (hsat : Satisfiable Γ p)
    (h₁ : RefinesUnder Γ p name N₁ dom s₁) (h₂ : RefinesUnder Γ p name N₂ dom s₂)
    (args : List Val) (hd : dom args) : (s₁ args).toEResult = (s₂ args).toEResult := by
  obtain ⟨σ, hc, ht⟩ := hsat
  exact refines_unique (h₁ σ hc ht) (h₂ σ hc ht) args hd

/-- Contracts compose in the safe direction: assuming *more* labels can only weaken the
claim, never strengthen it. Formally, an environment that constrains a superset of labels
admits at least the implementations of the smaller one, so a theorem proved under `Γ`
survives under any `Γ'` whose consistent, total implementations are among `Γ`'s. -/
theorem refinesUnder_weaken {Γ Γ' p name N dom spec}
    (hsub : ∀ σ, Consistent Γ' p σ → Total Γ' σ → Consistent Γ p σ ∧ Total Γ σ)
    (h : RefinesUnder Γ p name N dom spec) : RefinesUnder Γ' p name N dom spec := by
  intro σ hc ht
  obtain ⟨hc', ht'⟩ := hsub σ hc ht
  exact h σ hc' ht'

/-! ## 4. Standard contracts

Three, spanning the useful range. `topContract` is the honest default for a hole nobody
has looked at; the other two are what a human asserts after looking. -/

/-- **Assume nothing.** The hole may do anything at all: mutate the heap, raise, return,
or remain a hole. Always satisfiable, and provably useless — see
`methodkey_not_refinable_under_top`. This is what an undeclared hole *means*, made
explicit. -/
def topContract (l : String) : Contract :=
  { label := l, fuel := 0
  , stmt  := s!"the construct `{l}` may do anything (no assumption)"
  , post  := fun _ _ _ => True }

/-- **Assume the hole is a pure value producer**: it terminates, returns some value, does
not raise, and does not touch the heap. This is the weakest contract that lets a proof
walk *through* a hole, and it is a real assumption: `op:starredUnpack` in CPython can
raise `TypeError` on a non-iterable, so a theorem using this contract is conditional on
the unpacked argument being iterable. -/
def pureValueContract (l : String) : Contract :=
  { label := l, fuel := 1
  , stmt  := s!"`{l}` terminates, returns a value, raises nothing, and does not mutate the heap"
  , post  := fun h _ st => st.1 = h ∧ ∃ v, st.2 = .val v }

/-- **Assume the hole raises**, with a named payload and no heap effect. Exceptions are
behaviour, not ignorance (`Refine`'s `Outcome.raise`), so this is a genuine specification
of a hole rather than a way of hiding it. -/
def raisesContract (l : String) (payload : Val) : Contract :=
  { label := l, fuel := 1
  , stmt  := s!"`{l}` raises, with no heap effect"
  , post  := fun h _ st => st = (h, .exn payload) }

/-- Any contract whose `post` is `True` is met by leaving the hole exactly where it is:
the identity implementation. So `topContract` environments are always satisfiable — which
is the point. They are consistent *and* worthless, the two properties that together show
satisfiability is necessary but not sufficient. -/
theorem satisfiable_top (l : String) (p : Program) :
    Satisfiable [topContract l] p :=
  ⟨[(l, .hole l)],
   ⟨by intro l' hl'; simp [Impl.labels] at hl'; simp [ContractEnv.labels, topContract, hl'],
    by intro c hc e _ k _ h ρ; simp at hc; subst hc; trivial⟩,
   by intro c hc; simp at hc; subst hc; simp [topContract]⟩

/-! ## 5. Extracting the assumptions

`Ledger.lean` and `scripts/sacm.py` turn every hole label into a named SACM `Assumption`
node of the *module*. A contract-relative theorem needs finer granularity: these are
assumptions of **that theorem**, and the assurance case should say so, because discharging
them is a different piece of work from discharging the module's other holes. -/

/-- One SACM `Assumption` node, derived from one contract. -/
structure Assumption where
  /-- The CPG hole label. Matches the labels `Ledger.tally` already counts. -/
  label : String
  /-- Unchecked prose from `Contract.stmt`. -/
  statement : String
  /-- The fuel budget assumed for the construct. -/
  fuelBound : Nat
  deriving Repr, DecidableEq

/-- The assumptions a contract environment represents. -/
def ContractEnv.assumptions (Γ : ContractEnv) : List Assumption :=
  Γ.map fun c => { label := c.label, statement := c.stmt, fuelBound := c.fuel }

/-- Machine-readable assumption record for one contract-relative theorem.

`theoremName` is the Lean declaration the assumptions belong to; `satisfiable` records
whether a `Satisfiable Γ p` proof exists and names it. A `false` there is not a warning,
it is a disqualification: by `refinesUnder_of_unsatisfiable` the theorem carries no
information until it is `true`. `scripts/sacm.py` should cap any claim supported by such
a theorem at the same level it caps unattributed evidence. -/
def assumptionsJson (theoremName : String) (Γ : ContractEnv)
    (satisfiabilityProof : Option String) : Lean.Json :=
  Lean.Json.mkObj
    [ ("theorem", .str theoremName)
    , ("relativeTo", .arr (Γ.assumptions.map (fun a =>
        Lean.Json.mkObj
          [ ("label", .str a.label)
          , ("statement", .str a.statement)
          , ("fuelBound", .num a.fuelBound) ])).toArray)
    , ("satisfiable", .bool satisfiabilityProof.isSome)
    , ("satisfiabilityProof",
        match satisfiabilityProof with | some n => .str n | none => .null) ]

end Autoform.Contracts
