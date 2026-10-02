import Lean
import Autoform.Contracts
import Autoform.Generated.Cachetools

/-!
# Contracts at *statement* holes, scoped to a site

`Autoform/Contracts.lean` gives contracts to **expression** holes and, deliberately, stops
there: `substS` leaves `Stmt.hole` alone, because a statement hole is an untranslated
*effect* and its contract has to be a relation on control outcomes, not on values. This
file supplies that relation, so that a function whose only gaps are statements like
`del self.__data[key]` (`op:delete-index`, 6 occurrences in `cachetools`) can be reasoned
about **under a stated assumption** rather than discarded.

Three design decisions, each forced by something that would otherwise be unsound or
misleading:

* **Contracts are per site, not per label.** A statement contract is keyed by
  `(function, label)`. The same label means different things at different sites:
  `del self.__data[key]` in `Cache.__delitem__` deletes from a plain `dict` and touches no
  attribute, while `del self[key]` in `Cache.pop` dispatches to `Cache.__delitem__` and
  *does* write `_Cache__currsize`. One label-wide contract would have to be false at one of
  them. Keying by site makes the assumption exactly as wide as the place it is used.
* **The contract is a relation `post : Heap → Env → Heap × Ctl → Prop`.** That is where an
  *effect footprint* lives (`AttrFrame`: which parts of the heap the hole may change) and
  where the *result relation* lives (normal completion, a raise, or anything else). It is
  universally quantified over heaps, environments and every fuel budget above a declared
  bound, so it is a claim about the construct at that site, not about one execution.
* **A contract is never an axiom.** Everything below is a *hypothesis* of a definition
  (`UnderS`): a contract-relative result is `∀ τ, ConsistentS Γ p τ → TotalS Γ τ → Q
  (τ.onProgram p)`. `#print axioms` on every theorem here reports only Lean's standard
  axioms, so the audit (`scripts/audit_all.py`) still sees exactly what it saw before, and
  the conditional status of a result is visible in its *statement* (a non-empty `Γ`), not
  in an axiom list.

The vacuity guards of `Contracts.lean` are re-proved for this relation — an empty `Γ`
changes nothing (`underS_nil_iff`), an unsatisfiable `Γ` proves everything
(`underS_of_unsatisfiable`) so satisfiability is a proof obligation, a false `post` is
detectably unsatisfiable (`unsatisfiableS_of_false_post`), and the unconstrained contract
proves nothing about a real function (`delitem_not_provable_under_top`).

`docs/contracts.md` §"Statement holes" is the reader's guide.
-/

namespace Autoform.HoleContracts

open Autoform.Core Autoform.Refine

/-! ## 1. Site-scoped statement contracts -/

/-- A contract on the statement hole labelled `label` inside the function `site`.

* `post h ρ (h', c)` — the assumed behaviour: executed in heap `h` and environment `ρ`,
  the hole leaves heap `h'` and control outcome `c`. Load-bearing.
* `fuel` — the budget the hole's implementation is assumed to need.
* `stmt` — **unchecked** prose for the assurance case; never used in a proof. -/
structure SContract where
  /-- Fully qualified name of the function that contains the hole. -/
  site  : String
  /-- The CPG hole label, as in `Ledger.tally`. -/
  label : String
  /-- Human-readable rendering of `post`, for SACM. Unchecked. -/
  stmt  : String
  /-- Fuel budget the hole's implementation is assumed to need. -/
  fuel  : Nat
  /-- The assumed behaviour of the hole. -/
  post  : Heap → Env → Heap × Ctl → Prop

/-- The key a contract and an implementation agree on. -/
def SContract.key (c : SContract) : String × String := (c.site, c.label)

/-- A set of statement-hole assumptions. -/
abbrev SContractEnv := List SContract

/-- The `(site, label)` keys an environment speaks about. -/
def SContractEnv.keys (Γ : SContractEnv) : List (String × String) := Γ.map SContract.key

/-! ## 2. Implementations: filling statement holes with statements -/

/-- A witness: `(site, label) ↦ replacement statement`. -/
abbrev SImpl := List ((String × String) × Stmt)

/-- The keys an implementation fills. -/
def SImpl.keys (τ : SImpl) : List (String × String) := τ.map (·.1)

/-- The part of an implementation that applies inside one function. -/
def SImpl.atSite (τ : SImpl) (site : String) : List (String × Stmt) :=
  τ.filterMap fun e => if e.1.1 == site then some (e.1.2, e.2) else none

/-- Replace statement holes by label. Expressions — and therefore expression holes — are
untouched: those belong to `Contracts.substE`, and keeping the two substitutions disjoint
means neither can silently repair the other's holes. -/
def fillS (ι : List (String × Stmt)) : Stmt → Stmt
  | .hole l          => match ι.lookup l with
                        | some s => s
                        | none   => .hole l
  | .seq a b         => .seq (fillS ι a) (fillS ι b)
  | .ifte c a b      => .ifte c (fillS ι a) (fillS ι b)
  | .loop c a        => .loop c (fillS ι a)
  | .breakBlock a    => .breakBlock (fillS ι a)
  | .forIn x e b     => .forIn x e (fillS ι b)
  | .tryCatch b x hd => .tryCatch (fillS ι b) x (fillS ι hd)
  | .tryFinally b f  => .tryFinally (fillS ι b) (fillS ι f)
  | s                => s

/-- Apply an implementation to one function: only that function's own sites are filled. -/
def SImpl.onFunc (τ : SImpl) (f : Func) : Func :=
  { f with body := fillS (τ.atSite f.name) f.body }

/-- Apply an implementation to a whole program. Names, dialect and builtin bases are
untouched, so name resolution in the instantiated program is that of the original
(`resolve_onProgram`, `resolveMethod_onProgram`). -/
def SImpl.onProgram (τ : SImpl) (p : Program) : Program :=
  { p with funcs := p.funcs.map τ.onFunc }

theorem fillS_nil : ∀ s : Stmt, fillS [] s = s := by
  intro s
  induction s <;> simp [fillS, *]

@[simp] theorem onFunc_nil (f : Func) : SImpl.onFunc [] f = f := by
  simp [SImpl.onFunc, SImpl.atSite, fillS_nil]

@[simp] theorem onProgram_nil (p : Program) : SImpl.onProgram [] p = p := by
  have : SImpl.onFunc [] = id := funext onFunc_nil
  simp [SImpl.onProgram, this]

@[simp] theorem onFunc_name (τ : SImpl) (f : Func) : (τ.onFunc f).name = f.name := rfl

/-- Looking up a label at a site is looking up the pair. -/
theorem atSite_lookup (τ : SImpl) (site l : String) :
    (τ.atSite site).lookup l = τ.lookup (site, l) := by
  induction τ with
  | nil => rfl
  | cons e τ ih =>
    obtain ⟨⟨s, l'⟩, b⟩ := e
    by_cases hs : s = site
    · subst hs
      by_cases hl : l = l'
      · subst hl; simp [SImpl.atSite, List.lookup]
      · have : (l == l') = false := by simp [hl]
        have h2 : ((s, l) == (s, l')) = false := by simp [hl]
        simp only [SImpl.atSite, List.filterMap_cons, beq_self_eq_true, if_true,
          List.lookup, this, h2] at ih ⊢
        exact ih
    · have h2 : ((site, l) == (s, l')) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq, Prod.mk.injEq, not_and]; intro h; exact absurd h.symm hs
      have hb : (s == site) = false := by simp [hs]
      simp only [SImpl.atSite, List.filterMap_cons, hb, List.lookup, h2] at ih ⊢
      exact ih

/-! ### Name resolution is unchanged by filling

These are what let a proof about the instantiated program use the *original* program's
resolution facts, which are decidable by computation (`rfl`). -/

theorem table_onProgram (τ : SImpl) (p : Program) :
    (τ.onProgram p).table = p.table.map (fun e => (e.1, τ.onFunc e.2)) := by
  simp [SImpl.onProgram, Program.table, List.map_map, Function.comp_def]

private theorem find?_map_fst (τ : SImpl) (t : FuncTable) (n : String) :
    (t.map (fun e => (e.1, τ.onFunc e.2))).find? (·.1 == n)
      = (t.find? (·.1 == n)).map (fun e => (e.1, τ.onFunc e.2)) := by
  simp [List.find?_map, Function.comp_def]

private theorem resolve_go_map (τ : SImpl) (suffix : String) :
    ∀ (t : FuncTable) (acc : Option Func),
      Ctx.resolve.go suffix (t.map (fun e => (e.1, τ.onFunc e.2))) (acc.map τ.onFunc)
        = (Ctx.resolve.go suffix t acc).map τ.onFunc := by
  intro t
  induction t with
  | nil => intro acc; rfl
  | cons e t ih =>
    intro acc
    obtain ⟨k, f⟩ := e
    cases acc with
    | none =>
      simp only [List.map_cons, Option.map_none, Ctx.resolve.go]
      split
      · exact ih (some f)
      · exact ih none
    | some g =>
      simp only [List.map_cons, Option.map_some, Ctx.resolve.go]
      split
      · rfl
      · exact ih (some g)

theorem resolve_onProgram (τ : SImpl) (p : Program) (n : String) :
    (ctxOf (τ.onProgram p)).resolve n = ((ctxOf p).resolve n).map τ.onFunc := by
  simp only [Ctx.resolve, ctxOf, table_onProgram]
  rw [find?_map_fst]
  cases hf : p.table.find? (·.1 == n) with
  | some e => simp
  | none =>
    simp only [Option.map_none]
    exact resolve_go_map τ _ p.table none

theorem resolveMethod_onProgram (τ : SImpl) (p : Program) (cls meth : String) :
    (ctxOf (τ.onProgram p)).resolveMethod cls meth
      = ((ctxOf p).resolveMethod cls meth).map τ.onFunc := by
  have hr := resolve_onProgram τ p meth
  simp only [Ctx.resolveMethod, ctxOf, table_onProgram] at hr ⊢
  rw [List.filter_map]
  simp only [Function.comp_def]
  cases hfl : List.filter (fun q => q.1.endsWith ("." ++ cls ++ "." ++ meth)) p.table with
  | nil => simpa using hr
  | cons e es => simp

/-- Method resolution on a large concrete table, without unfolding the table in `simp`:
if exactly one key matches the method suffix, the method is the function stored under
that key. Both hypotheses are decidable by evaluation. -/
theorem resolveMethod_of_unique (ctx : Ctx) (cls meth n : String) (f : Func)
    (hf : (ctx.table.filter (fun p => p.1.endsWith ("." ++ cls ++ "." ++ meth))).map (·.1) = [n])
    (hr : ctx.table.find? (·.1 == n) = some (n, f)) :
    ctx.resolveMethod cls meth = some f := by
  unfold Ctx.resolveMethod
  generalize hF : ctx.table.filter (fun p => p.1.endsWith ("." ++ cls ++ "." ++ meth)) = F at hf
  match F, hf with
  | [x], hx =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hx
    have hmem : (n, f) ∈ ctx.table := List.mem_of_find?_eq_some hr
    have hin : (n, f) ∈ [x] := by
      rw [← hF, List.mem_filter]
      refine ⟨hmem, ?_⟩
      have hx' : x ∈ ctx.table.filter (fun p => p.1.endsWith ("." ++ cls ++ "." ++ meth)) := by
        rw [hF]; simp
      rw [List.mem_filter] at hx'
      simpa [hx] using hx'.2
    simp at hin
    simp [← hin]

theorem dialect_onProgram (τ : SImpl) (p : Program) : (τ.onProgram p).dialect = p.dialect := rfl
theorem builtinBases_onProgram (τ : SImpl) (p : Program) :
    (τ.onProgram p).builtinBases = p.builtinBases := rfl

/-! ## 3. Consistency, satisfiability, and the hole-aware wrapper `UnderS` -/

/-- `τ` is a legal witness for `Γ` in `p`:

* it fills only `(site, label)` pairs that `Γ` names — so `Γ` is an exact inventory of
  what is assumed, and no undeclared hole is silently repaired;
* every replacement meets its contract in **every** heap and environment, at **every**
  fuel at or above the declared budget, run in the instantiated program. -/
def ConsistentS (Γ : SContractEnv) (p : Program) (τ : SImpl) : Prop :=
  (∀ k ∈ τ.keys, k ∈ Γ.keys) ∧
  (∀ c ∈ Γ, ∀ s, τ.lookup c.key = some s →
     ∀ k, c.fuel ≤ k → ∀ h ρ, c.post h ρ (execStmt (ctxOf (τ.onProgram p)) k h ρ s))

/-- `τ` fills every site `Γ` names. -/
def TotalS (Γ : SContractEnv) (τ : SImpl) : Prop :=
  ∀ c ∈ Γ, (τ.lookup c.key).isSome

/-- Some implementation meets `Γ`. The anti-vacuity obligation (`underS_of_unsatisfiable`). -/
def SatisfiableS (Γ : SContractEnv) (p : Program) : Prop :=
  ∃ τ, ConsistentS Γ p τ ∧ TotalS Γ τ

/-- **The hole-aware wrapper.** `UnderS Γ p Q`: the property `Q` holds of *every*
instantiation of `p` whose statement holes are filled consistently with `Γ`.

`Q` is arbitrary, so this covers `Refines` (`RefinesUnderS`) and also heap-level
post-conditions of methods, which is what an effect footprint is for. The assumptions are
the hypotheses `ConsistentS Γ p τ` and `TotalS Γ τ`; nothing is postulated. -/
def UnderS (Γ : SContractEnv) (p : Program) (Q : Program → Prop) : Prop :=
  ∀ τ, ConsistentS Γ p τ → TotalS Γ τ → Q (τ.onProgram p)

/-- Refinement relative to statement-hole contracts. -/
def RefinesUnderS (Γ : SContractEnv) (p : Program) (name : String) (N : Nat)
    (dom : List Val → Prop) (spec : List Val → Outcome) : Prop :=
  UnderS Γ p (fun q => Refines q name N dom spec)

/-- **No contracts, no difference**: with `Γ = []` the wrapper is the property itself, in
both directions. A result is unconditional iff its `Γ` is literally `[]`. -/
theorem underS_nil_iff (p : Program) (Q : Program → Prop) : UnderS [] p Q ↔ Q p := by
  constructor
  · intro h
    have hc : ConsistentS [] p [] := ⟨(by intro k hk; cases hk), (by intro c hc; cases hc)⟩
    simpa using h [] hc (by intro c hc; cases hc)
  · intro h τ hc _
    have hτ : τ = [] := by
      cases τ with
      | nil => rfl
      | cons a as => exact absurd (hc.1 a.1 (by simp [SImpl.keys])) (by simp [SContractEnv.keys])
    subst hτ; simpa using h

theorem refinesUnderS_nil_iff (p : Program) (name : String) (N : Nat)
    (dom : List Val → Prop) (spec : List Val → Outcome) :
    RefinesUnderS [] p name N dom spec ↔ Refines p name N dom spec :=
  underS_nil_iff p _

/-- The only way back to an unconditional statement: exhibit a consistent, total
implementation. The result is about the *repaired* program `τ.onProgram p`, never `p`. -/
theorem UnderS.discharge {Γ p Q} (h : UnderS Γ p Q) {τ : SImpl}
    (hc : ConsistentS Γ p τ) (ht : TotalS Γ τ) : Q (τ.onProgram p) := h τ hc ht

theorem UnderS.mono {Γ p} {Q Q' : Program → Prop} (hq : ∀ q, Q q → Q' q)
    (h : UnderS Γ p Q) : UnderS Γ p Q' := fun τ hc ht => hq _ (h τ hc ht)

/-- **An unsatisfiable environment proves everything** — every property of every
instantiation, including `False`. Hence a contract-relative result carries information
only together with a proof of `SatisfiableS Γ p`. -/
theorem underS_of_unsatisfiable {Γ p} (h : ¬ SatisfiableS Γ p) (Q : Program → Prop) :
    UnderS Γ p Q := fun τ hc ht => absurd ⟨τ, hc, ht⟩ h

/-- …and with a satisfiable environment, `False` is *not* provable: the guard has teeth. -/
theorem not_underS_false {Γ p} (h : SatisfiableS Γ p) : ¬ UnderS Γ p (fun _ => False) := by
  obtain ⟨τ, hc, ht⟩ := h
  exact fun hu => hu τ hc ht

/-- A contract whose `post` nothing satisfies is detectably unsatisfiable. -/
theorem unsatisfiableS_of_false_post {Γ : SContractEnv} {p : Program} {c : SContract}
    (hmem : c ∈ Γ) (hfalse : ∀ h ρ st, ¬ c.post h ρ st) : ¬ SatisfiableS Γ p := by
  rintro ⟨τ, hc, ht⟩
  have hs := ht c hmem
  match hlk : τ.lookup c.key with
  | none   => rw [hlk] at hs; exact absurd hs (by simp)
  | some s => exact hfalse [] [] _ (hc.2 c hmem s hlk c.fuel (Nat.le_refl _) [] [])

/-! ### The hole-aware evaluation lemma

At a contracted site, the instantiated function body contains *some* statement `s` in place
of the hole, and running `s` satisfies the contract. A proof never learns what `s` is —
only `post` — which is exactly what makes the result hold for every implementation. -/
theorem filled_hole {Γ p τ} (hc : ConsistentS Γ p τ) (ht : TotalS Γ τ)
    {c : SContract} (hm : c ∈ Γ) :
    ∃ s, (τ.atSite c.site).lookup c.label = some s ∧
      ∀ k, c.fuel ≤ k → ∀ h ρ, c.post h ρ (execStmt (ctxOf (τ.onProgram p)) k h ρ s) := by
  have hs := ht c hm
  match hlk : τ.lookup c.key with
  | none   => rw [hlk] at hs; exact absurd hs (by simp)
  | some s =>
    refine ⟨s, ?_, hc.2 c hm s hlk⟩
    rw [atSite_lookup]; exact hlk

/-- …and the filled site *is* that statement. -/
theorem fillS_hole_of_lookup {ι : List (String × Stmt)} {l : String} {s : Stmt}
    (h : ι.lookup l = some s) : fillS ι (.hole l) = s := by
  simp [fillS, h]

/-! ## 4. Standard statement contracts -/

/-- **Assume nothing.** Always satisfiable, provably useless on a reachable hole
(`delitem_not_provable_under_top`). The honest default for a site nobody has examined. -/
def topSContract (site label : String) : SContract :=
  { site, label, stmt := "may do anything (no assumption)", fuel := 0,
    post := fun _ _ _ => True }

/-- **Effect footprint: attributes.** Every object that existed before still exists after,
with the same class, the same attributes (`fields`) and the same captured bindings. The
container payload and version are *not* constrained — they are what `del d[k]` changes. -/
def AttrFrame (h h' : Heap) : Prop :=
  ∀ r o, h.get r = some o →
    ∃ o', h'.get r = some o' ∧ o'.cls = o.cls ∧ o'.fields = o.fields ∧ o'.captured = o.captured

theorem AttrFrame.refl (h : Heap) : AttrFrame h h := fun _ o ho => ⟨o, ho, rfl, rfl, rfl⟩

/-- **"Completes or raises, touching no attribute."** The result relation: control leaves
normally with the environment unchanged, or by raising; never `return`/`break`/`continue`,
never a hole, never out of fuel at or above budget `1`. The footprint: `AttrFrame`. -/
def completesOrRaisesFramed (site label stmt : String) : SContract :=
  { site, label, stmt, fuel := 1,
    post := fun h ρ r => AttrFrame h r.1 ∧ (r.2 = .normal ρ ∨ ∃ v, r.2 = .exn v) }

/-- Satisfiable in every program, by `skip`. -/
theorem satisfiable_completesOrRaisesFramed (site label stmt : String) (p : Program) :
    SatisfiableS [completesOrRaisesFramed site label stmt] p := by
  refine ⟨[((site, label), .skip)], ⟨?_, ?_⟩, ?_⟩
  · intro k hk; simp [SImpl.keys] at hk; simp [SContractEnv.keys, SContract.key,
      completesOrRaisesFramed, hk]
  · intro c hc s hs k hk h ρ
    simp at hc; subst hc
    simp [SContract.key, completesOrRaisesFramed, List.lookup] at hs; subst hs
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by simp [completesOrRaisesFramed] at hk; omega⟩
    simp [completesOrRaisesFramed, execStmt, AttrFrame.refl]
  · intro c hc; simp at hc; subst hc; simp [SContract.key, completesOrRaisesFramed, List.lookup]

theorem satisfiable_topS (site label : String) (p : Program) :
    SatisfiableS [topSContract site label] p := by
  refine ⟨[((site, label), .hole label)], ⟨?_, ?_⟩, ?_⟩
  · intro k hk; simp [SImpl.keys] at hk; simp [SContractEnv.keys, SContract.key, topSContract, hk]
  · intro c hc _ _ _ _ _ _; simp at hc; subst hc; trivial
  · intro c hc; simp at hc; subst hc; simp [SContract.key, topSContract, List.lookup]

/-! ## 5. The assumption record

Statement contracts are exported in the same registry as expression contracts
(`scripts/emit_contracts.py` → `contracts-<Module>.json` → `scripts/sacm.py`), with two
extra fields: `site` and `kind = "stmt"`. -/

/-- Assumption record for one statement contract. -/
def SContract.toJson (c : SContract) : Lean.Json :=
  Lean.Json.mkObj
    [ ("label", .str c.label), ("site", .str c.site), ("kind", .str "stmt")
    , ("statement", .str c.stmt), ("fuelBound", .num c.fuel) ]

/-- Registry record for a theorem relative to statement contracts. -/
def assumptionsJsonS (theoremName : String) (Γ : SContractEnv)
    (satisfiabilityProof : Option String) : Lean.Json :=
  Lean.Json.mkObj
    [ ("theorem",     .str theoremName)
    , ("relativeTo",  .arr (Γ.map SContract.toJson).toArray)
    , ("satisfiable", .bool satisfiabilityProof.isSome)
    , ("satisfiabilityProof", match satisfiabilityProof with
                              | some n => .str n
                              | none   => .null) ]

/-! ## 6. Worked example: `cachetools` `Cache.__delitem__`, *as currently translated*

```python
def __delitem__(self, key):
    size = self.__size.pop(key)
    del self.__data[key]
    self.__currsize -= size
```

The generated `f_cachetools___init___py__module__Cache___delitem__` is **partially
translated**: `del self.__data[key]` is `Stmt.hole "op:delete-index"`. Today that hole
puts the function outside every unconditional statement (`delitem_reaches_hole`). The
theorem below is about the generated `Program` *unmodified* — `Autoform.Generated.
Cachetools.program`, all functions, imported — instantiated at that one site.

Assumption made (and only this one): at `Cache.__delitem__`, `op:delete-index` completes
normally or raises, and changes no object's attributes. That is true of `del d[k]` on a
CPython `dict` *provided* `k`'s `__hash__`/`__eq__` have no attribute side effects — a
condition a reader must check (`docs/contracts.md`), and which is not in `Γ`.

Conclusion: for a `Cache` whose size table is a `_DefaultSize` (the class `cachetools`
uses when no `getsizeof` is given), `__delitem__` either returns `None` having decreased
`_Cache__currsize` by exactly 1, or raises having left `_Cache__currsize` unchanged. The
footprint is load-bearing: without `AttrFrame` the hole could rewrite `_Cache__currsize`
and the first disjunct would be false. -/

namespace Demo

open Autoform.Generated.Cachetools

/-- The translated program, imported, not copied. -/
abbrev P : Program := Autoform.Generated.Cachetools.program

theorem P_dialect : P.dialect = Dialect.python := rfl

/-- Call a method of `q` on an explicit receiver; heap and result. -/
def runMethodIn (q : Program) (fuel : Nat) (h : Heap) (name : String) (self : Val)
    (args : List Val) : Heap × EResult :=
  match (ctxOf q).resolve name with
  | none    => (h, .hole s!"entry:{name}")
  | some fn => applyFunc (ctxOf q) fuel h fn (some self) args []

def delitemName : String := "cachetools/__init__.py:<module>.Cache.__delitem__"

/-- The one assumption. -/
def delContract : SContract :=
  completesOrRaisesFramed delitemName "op:delete-index"
    "`del self.__data[key]` in Cache.__delitem__ completes normally (environment unchanged) \
     or raises, and changes no object's class, attributes or captured bindings"

def Γdel : SContractEnv := [delContract]

theorem satisfiable_delContract : SatisfiableS Γdel P :=
  satisfiable_completesOrRaisesFramed _ _ _ P

/-- The receiver shape the theorem is about. Stated as attributes the object *has*, so the
domain is checkable and non-empty (`sampleCache`). -/
def CacheShape (h : Heap) (r d : Ref) (c : Int) : Prop :=
  ∃ o od, h.get r = some o
    ∧ o.fields.find? (·.1 == "_Cache__size") = some ("_Cache__size", .ref d)
    ∧ o.fields.find? (·.1 == "_Cache__currsize") = some ("_Cache__currsize", .int c)
    ∧ o.captured = []
    ∧ h.get d = some od ∧ od.cls = "_DefaultSize" ∧ od.captured = []

/-- What is proved of every admissible instantiation. -/
def DelitemPost (q : Program) : Prop :=
  ∀ h r d c key, CacheShape h r d c → ∀ fuel, 12 ≤ fuel →
    (∃ h', runMethodIn q fuel h delitemName (.ref r) [key] = (h', .val .unit)
        ∧ h'.getField r "_Cache__currsize" = .int (c - 1))
    ∨ (∃ h' v, runMethodIn q fuel h delitemName (.ref r) [key] = (h', .exn v)
        ∧ h'.getField r "_Cache__currsize" = .int c)

theorem resolve_delitem :
    (ctxOf P).resolve delitemName = some f_cachetools___init___py__module__Cache___delitem__ := by
  rfl

theorem resolveMethod_pop :
    (ctxOf P).resolveMethod "_DefaultSize" "pop"
      = some f_cachetools___init___py__module___DefaultSize_pop := by
  apply resolveMethod_of_unique _ _ _ "cachetools/__init__.py:<module>._DefaultSize.pop"
  · decide +kernel
  · rfl

theorem getField_setField_self (h : Heap) (r : Ref) (f : String) (v : Val) {o : Obj}
    (ho : h.get r = some o) : (h.setField r f v).getField r f = v := by
  simp only [Heap.get] at ho
  simp [Heap.getField, Heap.setField, Heap.get, List.getElem?_mapIdx, ho]

theorem delitem_under : UnderS Γdel P DelitemPost := by
  intro τ hc ht h r d c key hshape fuel hfuel
  obtain ⟨s, hlk, hpost⟩ := filled_hole hc ht (c := delContract) (by simp [Γdel])
  obtain ⟨o, od, hro, hsz, hcur, hcap, hdo, hdcls, hdcap⟩ := hshape
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 12 := ⟨fuel - 12, by omega⟩
  have hpop : (ctxOf (τ.onProgram P)).resolveMethod "_DefaultSize" "pop"
      = some f_cachetools___init___py__module___DefaultSize_pop := by
    rw [resolveMethod_onProgram, resolveMethod_pop]
    simp [SImpl.onFunc, f_cachetools___init___py__module___DefaultSize_pop, fillS]
  have hdial : (ctxOf (τ.onProgram P)).dialect = .python := rfl
  unfold runMethodIn
  rw [resolve_onProgram, resolve_delitem]
  simp only [Option.map_some, SImpl.onFunc, f_cachetools___init___py__module__Cache___delitem__,
    fillS]
  simp only [delContract, completesOrRaisesFramed, delitemName] at hlk hpost
  simp only [hlk]
  simp [applyFunc, bindParams, Func.posParams, kwargsRejected, posRejected,
    execStmt, evalExpr, Env.set, Env.get, evalList, Val.truthy, hro, hsz, hdo, hdcls, hdcap, hpop,
    f_cachetools___init___py__module___DefaultSize_pop]
  -- The only thing known about the filled site is its contract.
  have hP := hpost (k + 8) (by omega) h
    [("size", Val.int 1), ("tmp0", Val.ref d), ("key", key), ("self", Val.ref r)]
  generalize execStmt (ctxOf (τ.onProgram P)) (k + 8) h
    [("size", Val.int 1), ("tmp0", Val.ref d), ("key", key), ("self", Val.ref r)] s = E at hP ⊢
  obtain ⟨h', ctl⟩ := E
  obtain ⟨hframe, hctl⟩ := hP
  obtain ⟨o', ho', -, hf', -⟩ := hframe r o hro
  rcases hctl with hn | ⟨v, hx⟩
  · simp only at hn; subst hn
    left
    simp [ho', hf', hcur, hdial]
    exact getField_setField_self h' r _ _ ho'
  · simp only at hx; subst hx
    right
    simp [Heap.getField, ho', hf', hcur]

/-! ### The status quo, and why the contract is needed

Leaving the site unfilled — or filling it with itself — reaches the hole. So the generated
program as it stands admits *no* statement of this kind, and the unconstrained contract
(which permits leaving the hole in place) proves nothing. -/

/-- Any instantiation that leaves this site a hole reaches it, on every `Cache`-shaped
receiver, at every fuel at or above the bound. -/
theorem delitem_reaches_hole_of (τ : SImpl)
    (hfill : fillS (τ.atSite delitemName) (.hole "op:delete-index") = .hole "op:delete-index")
    (h : Heap) (r d : Ref) (c : Int) (key : Val) (hshape : CacheShape h r d c) (k : Nat) :
    (runMethodIn (τ.onProgram P) (k + 12) h delitemName (.ref r) [key]).2
      = .hole "op:delete-index" := by
  obtain ⟨o, od, hro, hsz, hcur, hcap, hdo, hdcls, hdcap⟩ := hshape
  have hpop : (ctxOf (τ.onProgram P)).resolveMethod "_DefaultSize" "pop"
      = some f_cachetools___init___py__module___DefaultSize_pop := by
    rw [resolveMethod_onProgram, resolveMethod_pop]
    simp [SImpl.onFunc, f_cachetools___init___py__module___DefaultSize_pop, fillS]
  unfold runMethodIn
  rw [resolve_onProgram, resolve_delitem]
  simp only [Option.map_some, SImpl.onFunc, f_cachetools___init___py__module__Cache___delitem__,
    fillS]
  simp only [delitemName, fillS] at hfill
  simp only [hfill]
  simp [applyFunc, bindParams, Func.posParams, kwargsRejected, posRejected,
    execStmt, evalExpr, Env.set, Env.get, evalList, Val.truthy, hro, hsz, hdo, hdcls, hdcap, hpop,
    f_cachetools___init___py__module___DefaultSize_pop]

/-- **On the generated program itself**, `Cache.__delitem__` reaches the hole. -/
theorem delitem_reaches_hole (h : Heap) (r d : Ref) (c : Int) (key : Val)
    (hshape : CacheShape h r d c) (k : Nat) :
    (runMethodIn P (k + 12) h delitemName (.ref r) [key]).2 = .hole "op:delete-index" := by
  have := delitem_reaches_hole_of [] (by simp [fillS, SImpl.atSite]) h r d c key hshape k
  simpa using this

/-- The domain is inhabited: a concrete `Cache` with `_DefaultSize` sizes and size 5. -/
def sampleHeap : Heap :=
  [ { cls := "Cache", fields := [("_Cache__size", .ref 1), ("_Cache__currsize", .int 5)] }
  , { cls := "_DefaultSize", fields := [] } ]

theorem sample_shape : CacheShape sampleHeap 0 1 5 :=
  ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The site filled with itself. Legal under `topSContract`, which is the point. -/
def idImplS : SImpl := [((delitemName, "op:delete-index"), .hole "op:delete-index")]

/-- **Assuming nothing proves nothing.** Under the unconstrained contract the property is
not provable, because leaving the hole in place is one of the implementations it admits. -/
theorem delitem_not_provable_under_top :
    ¬ UnderS [topSContract delitemName "op:delete-index"] P DelitemPost := by
  intro hU
  have hc : ConsistentS [topSContract delitemName "op:delete-index"] P idImplS := by
    refine ⟨?_, ?_⟩
    · intro k hk
      simp [idImplS, SImpl.keys] at hk
      simp [SContractEnv.keys, SContract.key, topSContract, hk]
    · intro c hc _ _ _ _ _ _; simp at hc; subst hc; trivial
  have ht : TotalS [topSContract delitemName "op:delete-index"] idImplS := by
    intro c hc; simp at hc; subst hc; simp [SContract.key, topSContract, idImplS]
  have hfill : fillS (idImplS.atSite delitemName) (.hole "op:delete-index")
      = .hole "op:delete-index" := by
    simp [idImplS, SImpl.atSite, fillS]
  have hh := delitem_reaches_hole_of idImplS hfill sampleHeap 0 1 5 (.int 7) sample_shape 0
  rcases hU idImplS hc ht sampleHeap 0 1 5 (.int 7) sample_shape 12 (Nat.le_refl _) with
    ⟨h', he, -⟩ | ⟨h', v, he, -⟩
  · rw [he] at hh; cases hh
  · rw [he] at hh; cases hh

/-- With the contract satisfiable, the conditional result is not vacuous: `False` does not
follow from `Γdel` (`not_underS_false`). -/
theorem delitem_not_vacuous : ¬ UnderS Γdel P (fun _ => False) :=
  not_underS_false satisfiable_delContract

/-! ### Cross-checks on the whole program

Evidence for a reader, not part of any proof: the full generated program, with the site
filled by two implementations that meet the contract — `skip` (the deletion succeeded) and
`raise` (it raised `KeyError`) — on `sampleHeap`. The first prints `val unit` and a
`_Cache__currsize` of 4; the second an exception and 5. Unfilled, it prints the hole. -/

def skipImpl : SImpl := [((delitemName, "op:delete-index"), .skip)]
def raiseImpl : SImpl := [((delitemName, "op:delete-index"), .raise (.lit (.str "KeyError")))]

#eval let (h', r) := runMethodIn (skipImpl.onProgram P) 40 sampleHeap delitemName (.ref 0) [.int 7]
      (reprStr r, reprStr (h'.getField 0 "_Cache__currsize"))
#eval let (h', r) := runMethodIn (raiseImpl.onProgram P) 40 sampleHeap delitemName (.ref 0) [.int 7]
      (reprStr r, reprStr (h'.getField 0 "_Cache__currsize"))
#eval reprStr (runMethodIn P 40 sampleHeap delitemName (.ref 0) [.int 7]).2

/-! ### Axiom audit

No hole contract is an axiom: each theorem's assumptions are hypotheses in its statement,
and the axiom base is Lean's standard three. -/

#print axioms delitem_under
#print axioms delitem_not_provable_under_top
#print axioms delitem_reaches_hole
#print axioms underS_of_unsatisfiable

/-! ### Registry records

What `scripts/emit_contracts.py` writes to `contracts-Cachetools.json`. Each record also
names the `program` it is about and the `function`, so the assurance case can count
*conditionally verified* functions of the current module separately from the historical
`methodkey` slice in `Contracts.lean`. -/

/-- Tag a record with its subject. -/
def withSubject (j : Lean.Json) (program function : String) : Lean.Json :=
  (j.setObjVal! "program" (.str program)).setObjVal! "function" (.str function)

def holeContractRecords : List Lean.Json :=
  [ withSubject
      (assumptionsJsonS "Autoform.HoleContracts.Demo.delitem_under" Γdel
        (some "Autoform.HoleContracts.Demo.satisfiable_delContract"))
      "Autoform.Generated.Cachetools.program" delitemName ]

/-- Every contract-relative record: the expression-hole demonstrations of
`Contracts.lean` (about the historical slice `keysProgramHoled`, so tagged with that
program and *not* counted as a conditionally verified function of the current module),
then this file's. -/
def allContractRecords : List Lean.Json :=
  (Autoform.Contracts.Demo.contractRecords.map fun j =>
      withSubject j "Autoform.Contracts.Demo.keysProgramHoled"
        "cachetools/keys.py:<module>.methodkey")
  ++ holeContractRecords

def allContractRecordsJson (module : String) : Lean.Json :=
  Lean.Json.mkObj [("module", .str module), ("theorems", .arr allContractRecords.toArray)]

#eval (allContractRecordsJson "Cachetools").compress

end Demo

end Autoform.HoleContracts
