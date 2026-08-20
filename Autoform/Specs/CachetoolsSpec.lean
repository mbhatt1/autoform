import Autoform.Refine
import Autoform.Generated.Cachetools

/-!
# Specifications about *translated* code — `cachetools`

`Autoform/Refine.lean` proves refinement theorems about deep terms that were **copied**
into it. That is fine for demonstrating the technique, but it means the mutation gate
(`scripts/mutate.py`) has never been pointed at a machine-generated module: G4 of the
SACM case ("the specifications are non-vacuous") could only ever cite
`Autoform.Lang.Imp.Semantics`, a hand-written toy.

This file states theorems about `Autoform/Generated/Cachetools.lean` **by import**, so
every deep term named below is the literal output of `cartographer/render_lean.py` and a
mutation of that file is a mutation of the subject of these theorems. That is the whole
point: `scripts/mutate.py --spec-module` mutates `Generated/Cachetools.lean` and rebuilds
*this* module, so a specification that does not notice the bug is exposed as vacuous.

## What is (and is not) claimed

Each theorem is a `Refines`/`MRefines` statement, i.e. it fixes the *entire* observable
behaviour — result value **and** resulting heap — of one entry point, for every fuel
budget at or above a stated bound, on a stated domain. `Refine.lean`'s non-vacuity
theorems apply verbatim: `Outcome` has no `hole` and no `outOfFuel` constructor, so none
of these can be satisfied by a function that fails to translate or fails to terminate
(`refines_not_hole`, `refines_terminates`).

The functions are drawn from the 45-function call-closed core (`Program.callClosed`).
They are small: accessors, a comparison, two constructors, a decrement, a membership
test. That is honest — the call-closed core of a real Python library *is* mostly small
methods, and the large ones are exactly the ones that still carry holes. Section 4
records what could not be proved, as stated obligations rather than `sorry`.
-/

namespace Autoform.Specs.Cachetools

open Autoform.Core Autoform.Refine Autoform.Generated

/-! ## 0. The subject

`P` is the translated `cachetools` program, imported, not copied. Every theorem below
resolves its entry point through `P`'s function table by its fully-qualified CPG name —
so deleting or renaming a function in the generated module breaks these proofs too. -/

/-- The translated program: `Autoform/Generated/Cachetools.lean`, unmodified. -/
abbrev P : Program := Autoform.Generated.program

/-! ## 1. Method calls

`runFunc` calls with `self? = none`, which is right for module-level functions but wrong
for the bound methods that make up most of `cachetools`. `runMethod` is the receiver-
carrying analogue, and `MRefines` is `Refines` for it — extended to also pin the
resulting **heap**, because a method that mutates its receiver is not specified by its
return value alone. -/

/-- Invoke a *method* — a function applied to an explicit receiver — returning the
resulting heap alongside the result. An unresolvable name is a hole, exactly as in
`runFunc`. -/
def runMethod (fuel : Nat) (h : Heap) (name : String) (self : Val)
    (args : List Val) : Heap × EResult :=
  match (ctxOf P).resolve name with
  | none    => (h, .hole s!"entry:{name}")
  | some fn => applyFunc (ctxOf P) fuel h fn (some self) args

theorem runMethod_of_resolve (fuel : Nat) (name : String) (h : Heap) (self : Val)
    (args : List Val) (fn : Func) (hres : (ctxOf P).resolve name = some fn) :
    runMethod fuel h name self args = applyFunc (ctxOf P) fuel h fn (some self) args := by
  unfold runMethod; rw [hres]

/-- **Method refinement.** For every receiver/argument tuple in `dom` and every fuel
budget at least `N`, the method's heap effect *and* its result are exactly those of the
total Lean function `spec`.

`spec` lands in `Heap × Outcome`, and `Outcome` (from `Refine.lean`) has no `hole` and no
`outOfFuel`: a method that reaches an untranslated construct, or that needs more fuel
than `N`, provably has no `MRefines` specification. -/
def MRefines (name : String) (N : Nat)
    (dom : Heap → Val → List Val → Prop)
    (spec : Heap → Val → List Val → Heap × Outcome) : Prop :=
  ∀ h self args, dom h self args → ∀ fuel, N ≤ fuel →
    runMethod fuel h name self args
      = ((spec h self args).1, ((spec h self args).2).toEResult)

/-- `MRefines` inherits `Refine.lean`'s non-vacuity: a refined method never reports an
untranslated construct. -/
theorem mrefines_not_hole {name N dom spec} (hm : MRefines name N dom spec)
    (h : Heap) (self : Val) (args : List Val) (hd : dom h self args)
    (fuel : Nat) (hf : N ≤ fuel) (l : String) :
    (runMethod fuel h name self args).2 ≠ .hole l := by
  rw [hm h self args hd fuel hf]
  exact Outcome.toEResult_ne_hole _ l

/-- …and never runs out of fuel at or above the stated bound. -/
theorem mrefines_terminates {name N dom spec} (hm : MRefines name N dom spec)
    (h : Heap) (self : Val) (args : List Val) (hd : dom h self args)
    (fuel : Nat) (hf : N ≤ fuel) :
    (runMethod fuel h name self args).2 ≠ .outOfFuel := by
  rw [hm h self args hd fuel hf]
  exact Outcome.toEResult_ne_outOfFuel _

/-- Two specifications of the same method agree wherever both are declared to hold. -/
theorem mrefines_unique {name N₁ N₂ dom s₁ s₂}
    (h₁ : MRefines name N₁ dom s₁) (h₂ : MRefines name N₂ dom s₂)
    (h : Heap) (self : Val) (args : List Val) (hd : dom h self args) :
    ((s₁ h self args).1, ((s₁ h self args).2).toEResult)
      = ((s₂ h self args).1, ((s₂ h self args).2).toEResult) := by
  rw [← h₁ h self args hd (max N₁ N₂) (Nat.le_max_left _ _),
      ← h₂ h self args hd (max N₁ N₂) (Nat.le_max_right _ _)]

/-! ## 2. The theorems

Simp sets are spelled out per theorem rather than hidden in a tactic, so that when a
mutant changes the deep term the failure is a *proof* failure and not a tactic that
quietly adapts. -/

/-- The dialect of the translated module, as a rewrite: `simp` must not be allowed to
unfold `program` itself (a 233-entry list literal). -/
theorem P_dialect : P.dialect = Dialect.python := rfl

/-- Field lookup as a *shallow* function: own fields first, then the bindings captured by
the class the object came from, then `unit`.

`Heap.getField` is not the right model any more — `Expr.field` also consults `captured`
(classes defined inside a function). This mirrors that lookup once, in one place, so that
no individual theorem has to unfold the interpreter's field case, and so that the field
*name* stays an argument: renaming a field in the generated AST changes which
`readField` is being claimed, and the theorem becomes false. -/
def readField (h : Heap) (r : Ref) (f : String) : Val :=
  match h.get r with
  | some o =>
    match o.fields.find? (·.1 == f) with
    | some (_, v) => v
    | none        => match o.captured.find? (·.1 == f) with
                     | some (_, v) => v
                     | none        => .unit
  | none => .unit

/-- `h` stores an object at `r` whose **own** field `f` holds `v`.

Used as the domain of the accessor theorems. Requiring the field to be present is not a
weakening dodge: Python attribute access on a missing attribute raises, and the semantics
answers `unit`, so a specification that claimed a value for an absent field would be
claiming something false. -/
def HasField (h : Heap) (r : Ref) (f : String) (v : Val) : Prop :=
  ∃ o, h.get r = some o ∧ o.fields.find? (·.1 == f) = some (f, v)

theorem readField_of_has {h r f v} (hv : HasField h r f v) : readField h r f = v := by
  obtain ⟨o, hg, hf⟩ := hv; simp [readField, hg, hf]

/-! ### `Cache.getsizeof` — the size model is the constant 1

`cachetools.Cache.getsizeof` is the default cost function: every entry costs 1. This is
the assumption the whole `currsize`/`maxsize` accounting rests on, so it is worth
pinning rather than assuming. -/

theorem Cache_getsizeof_refines :
    Refines₁ (α := Int) (β := Int) P
      "cachetools/__init__.py:<module>.Cache.getsizeof" 8 (fun _ => True) (fun _ => 1) := by
  intro v _
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_cachetools___init___py__module__Cache_getsizeof rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module__Cache_getsizeof, ctxOf, P, Marshal.toVal]

/-! ### `_DefaultSize.__getitem__` / `.pop` — the degenerate size table

`_DefaultSize` is the object `Cache` uses when no `getsizeof` was supplied: a mapping
that answers `1` to every lookup and forgets every write. Both halves are specified. -/

theorem DefaultSize_getitem_refines :
    Refines₁ (α := Int) (β := Int) P
      "cachetools/__init__.py:<module>._DefaultSize.__getitem__" 8
      (fun _ => True) (fun _ => 1) := by
  intro v _
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_cachetools___init___py__module___DefaultSize___getitem__ rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module___DefaultSize___getitem__, ctxOf, P, Marshal.toVal]

theorem DefaultSize_pop_refines :
    Refines₁ (α := Int) (β := Int) P
      "cachetools/__init__.py:<module>._DefaultSize.pop" 8
      (fun _ => True) (fun _ => 1) := by
  intro v _
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_cachetools___init___py__module___DefaultSize_pop rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module___DefaultSize_pop, ctxOf, P, Marshal.toVal]

/-- `_DefaultSize.__setitem__` is a no-op **on the heap as well as on the result**: this
is the theorem that would catch the store being silently implemented. -/
theorem DefaultSize_setitem_mrefines :
    MRefines "cachetools/__init__.py:<module>._DefaultSize.__setitem__" 8
      (fun _ _ args => ∃ k v, args = [k, v])
      (fun h _ _ => (h, .ret .unit)) := by
  rintro h self _ ⟨a, b, rfl⟩
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module___DefaultSize___setitem__ rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module___DefaultSize___setitem__, ctxOf, P]

/-! ### `Cache.maxsize` / `Cache.currsize` — the two accessors must read *different* fields

Stated for an arbitrary heap and an arbitrary receiver reference, so the field name is
not free to move: swapping `_Cache__maxsize` for `_Cache__currsize` makes the statement
false at any heap where the two differ. `Cache_size_fields_distinct` exhibits such a
heap explicitly, so the separation is witnessed and not merely implied. -/

theorem Cache_maxsize_mrefines :
    MRefines "cachetools/__init__.py:<module>.Cache.maxsize" 10
      (fun h self _ => ∃ r v, self = .ref r ∧ HasField h r "_Cache__maxsize" v)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (readField h r "_Cache__maxsize")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨r, v, rfl, o, hg, hfld⟩
  refine forall_ge_of_forall_add (N := 10) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__Cache_maxsize rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set, f_cachetools___init___py__module__Cache_maxsize, ctxOf, P, readField, hg, hfld]

theorem Cache_currsize_mrefines :
    MRefines "cachetools/__init__.py:<module>.Cache.currsize" 10
      (fun h self _ => ∃ r v, self = .ref r ∧ HasField h r "_Cache__currsize" v)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (readField h r "_Cache__currsize")
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨r, v, rfl, o, hg, hfld⟩
  refine forall_ge_of_forall_add (N := 10) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__Cache_currsize rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set, f_cachetools___init___py__module__Cache_currsize, ctxOf, P, readField, hg, hfld]

/-- A concrete cache object whose capacity and occupancy differ. -/
def sampleCache : Heap :=
  [{ cls := "Cache"
   , fields := [("_Cache__maxsize", .int 128), ("_Cache__currsize", .int 3)] }]

/-- The two accessors read the two fields, and are therefore observably different
functions on a cache whose capacity and occupancy differ.

**This statement was strengthened because the mutation gate said so.** It first read only
`maxsize ≠ currsize`, and scored **0/8** — every single-function mutant preserves a
*difference* (breaking one accessor leaves the other alone, so the two still disagree),
so an inequality between two functions is not evidence about either of them. Pinning both
values is what gives it teeth. The lesson generalises: a witness that asserts a relation
between two computations tests neither unless the relation is pinned on both sides. -/
theorem Cache_size_fields_distinct (fuel : Nat) (hf : 10 ≤ fuel) :
    (runMethod fuel sampleCache "cachetools/__init__.py:<module>.Cache.maxsize" (.ref 0) []).2
        = .val (.int 128)
  ∧ (runMethod fuel sampleCache "cachetools/__init__.py:<module>.Cache.currsize" (.ref 0) []).2
        = .val (.int 3)
  ∧ (runMethod fuel sampleCache "cachetools/__init__.py:<module>.Cache.maxsize" (.ref 0) []).2
      ≠ (runMethod fuel sampleCache "cachetools/__init__.py:<module>.Cache.currsize" (.ref 0) []).2 := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 10 := ⟨fuel - 10, by omega⟩
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__Cache_maxsize rfl,
      runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__Cache_currsize rfl]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [applyFunc, execStmt, evalExpr, Env.set, ctxOf, P, sampleCache, Heap.get,
          f_cachetools___init___py__module__Cache_maxsize,
          f_cachetools___init___py__module__Cache_currsize]

/-! ### `Cache.__contains__` — membership, and the *polarity* of `in`

`Expr.inOp` carries a negation flag. `__contains__` must use the positive one; a flipped
flag is a silent inversion of every containment test in the library, which this theorem
refutes on any dict receiver. -/

theorem Cache_contains_mrefines :
    MRefines "cachetools/__init__.py:<module>.Cache.__contains__" 12
      (fun h self args => ∃ r k kvs, self = .ref r ∧ args = [k]
                            ∧ HasField h r "_Cache__data" (.dict kvs))
      (fun h self args => (h, match self, args with
                              | .ref r, [k] =>
                                  match readField h r "_Cache__data" with
                                  | .dict kvs => .ret (.bool (kvs.any (fun kv => Val.beq k kv.1)))
                                  | _         => .ret .unit
                              | _, _ => .ret .unit)) := by
  rintro h _ _ ⟨r, k, kvs, rfl, rfl, o, hg, hfld⟩
  refine forall_ge_of_forall_add (N := 12) ?_
  intro n
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__Cache___contains__ rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module__Cache___contains__, ctxOf, P, valIn, readField,
        hg, hfld]

/-- Membership is not constant: it answers `true` for a present key and `false` for an
absent one. This is the anti-vacuity witness for `Cache_contains_mrefines` — a
specification satisfied by `fun _ => true` would pass the equation above only if that
equation were itself wrong, and this makes the discrimination concrete. -/
theorem Cache_contains_discriminates (fuel : Nat) (hf : 12 ≤ fuel) :
    (runMethod fuel [{ cls := "Cache", fields := [("_Cache__data", .dict [(.int 1, .int 9)])] }]
        "cachetools/__init__.py:<module>.Cache.__contains__" (.ref 0) [.int 1]).2 = .val (.bool true)
  ∧ (runMethod fuel [{ cls := "Cache", fields := [("_Cache__data", .dict [(.int 1, .int 9)])] }]
        "cachetools/__init__.py:<module>.Cache.__contains__" (.ref 0) [.int 2]).2 = .val (.bool false) := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 12 := ⟨fuel - 12, by omega⟩
  refine ⟨?_, ?_⟩ <;>
    rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__Cache___contains__ rfl] <;>
    simp [applyFunc, execStmt, evalExpr, Env.set, ctxOf, P, valIn, Val.beq, Heap.get,
          f_cachetools___init___py__module__Cache___contains__]

/-! ### `TLRUCache._Item.__lt__` — a strict order, and it must stay strict

The TLRU cache keeps its items in a heap ordered by `__lt__`. Relaxing `<` to `<=` is the
classic off-by-one that turns a strict weak order into a non-order; the equation below is
false under that mutation at any pair of equal expiry times. -/

theorem TLRUItem_lt_mrefines :
    MRefines "cachetools/__init__.py:<module>.TLRUCache._Item.__lt__" 12
      (fun h self args => ∃ r s a b, self = .ref r ∧ args = [.ref s]
                            ∧ HasField h r "expires" (.int a)
                            ∧ HasField h s "expires" (.int b))
      (fun h self args => (h, match self, args with
                              | .ref r, [.ref s] =>
                                  match readField h r "expires", readField h s "expires" with
                                  | .int a, .int b => .ret (.bool (decide (a < b)))
                                  | _, _ => .ret .unit
                              | _, _ => .ret .unit)) := by
  rintro h _ _ ⟨r, s, a, b, rfl, rfl, ⟨o, hg, hfld⟩, ⟨o', hg', hfld'⟩⟩
  refine forall_ge_of_forall_add (N := 12) ?_
  intro n
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__TLRUCache__Item___lt__ rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module__TLRUCache__Item___lt__, ctxOf, P,
        applyBinop_int_lt, readField, hg, hfld, hg', hfld']

/-- Irreflexivity: an item does not precede itself. False the moment `<` becomes `<=`. -/
theorem TLRUItem_lt_irrefl (fuel : Nat) (hf : 12 ≤ fuel) :
    (runMethod fuel [{ cls := "_Item", fields := [("expires", .int 7)] }]
        "cachetools/__init__.py:<module>.TLRUCache._Item.__lt__" (.ref 0) [.ref 0]).2
      = .val (.bool false) := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 12 := ⟨fuel - 12, by omega⟩
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__TLRUCache__Item___lt__ rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set, ctxOf, P, applyBinop_int_lt, Heap.get,
        f_cachetools___init___py__module__TLRUCache__Item___lt__]

/-! ### `_TimedCache._Timer.__exit__` — a heap effect, specified exactly

The timer's re-entrancy counter is decremented on exit. This is the only place in these
specifications where the *heap* is the observable, and it is stated as an exact equation
on `Heap.setField`, so `-` → `+` and `1` → `2` are both refuted. -/

theorem Timer_exit_mrefines :
    MRefines "cachetools/__init__.py:<module>._TimedCache._Timer.__exit__" 12
      (fun h self args => ∃ r n e, self = .ref r ∧ args = [e]
                            ∧ HasField h r "_Timer__nesting" (.int n))
      (fun h self _ => match self with
                       | .ref r =>
                           match readField h r "_Timer__nesting" with
                           | .int n => (h.setField r "_Timer__nesting" (.int (n - 1)), .ret .unit)
                           | _      => (h, .ret .unit)
                       | _ => (h, .ret .unit)) := by
  rintro h _ _ ⟨r, n, e, rfl, rfl, o, hg, hfld⟩
  refine forall_ge_of_forall_add (N := 12) ?_
  intro m
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module___TimedCache__Timer___exit__ rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module___TimedCache__Timer___exit__, ctxOf, P,
        P_dialect, readField, hg, hfld]

/-- The decrement is a decrement: on a concrete timer at nesting 1, exit leaves 0. -/
theorem Timer_exit_decrements (fuel : Nat) (hf : 12 ≤ fuel) :
    readField ((runMethod fuel [{ cls := "_Timer", fields := [("_Timer__nesting", .int 1)] }]
        "cachetools/__init__.py:<module>._TimedCache._Timer.__exit__" (.ref 0) [.unit]).1) 0
        "_Timer__nesting" = .int 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 12 := ⟨fuel - 12, by omega⟩
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module___TimedCache__Timer___exit__ rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set, ctxOf, P, P_dialect, readField, Heap.get, Heap.setField,
        f_cachetools___init___py__module___TimedCache__Timer___exit__]

/-! ### `_TimedCache._Timer.__init__` — both assignments happen

A constructor is specified by the *whole* post-state. Deleting either branch of the
`Stmt.seq` changes the resulting heap, so the mutation gate's `seq`-deletion operator has
something to break here. -/

theorem Timer_init_mrefines :
    MRefines "cachetools/__init__.py:<module>._TimedCache._Timer.__init__" 12
      (fun _ self args => ∃ r t, self = .ref r ∧ args = [t])
      (fun h self args => match self, args with
                          | .ref r, [t] =>
                              (((h.setField r "_Timer__timer" t).setField r "_Timer__nesting" (.int 0)),
                               .ret .unit)
                          | _, _ => (h, .ret .unit)) := by
  rintro h _ _ ⟨r, t, rfl, rfl⟩
  refine forall_ge_of_forall_add (N := 12) ?_
  intro m
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module___TimedCache__Timer___init__ rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module___TimedCache__Timer___init__, ctxOf, P]

/-- Both fields are actually written, with the right values in the right places. -/
theorem Timer_init_sets_both (fuel : Nat) (hf : 12 ≤ fuel) :
    readField (runMethod fuel [{ cls := "_Timer", fields := [] }]
        "cachetools/__init__.py:<module>._TimedCache._Timer.__init__" (.ref 0) [.int 99]).1
      0 "_Timer__timer" = .int 99
  ∧ readField (runMethod fuel [{ cls := "_Timer", fields := [] }]
        "cachetools/__init__.py:<module>._TimedCache._Timer.__init__" (.ref 0) [.int 99]).1
      0 "_Timer__nesting" = .int 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 12 := ⟨fuel - 12, by omega⟩
  refine ⟨?_, ?_⟩ <;>
    rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module___TimedCache__Timer___init__ rfl] <;>
    simp [applyFunc, execStmt, evalExpr, Env.set, ctxOf, P, readField, Heap.get, Heap.setField,
          f_cachetools___init___py__module___TimedCache__Timer___init__]

/-! ### `TTLCache._Link.__init__` — the same shape, a different pair of fields -/

theorem TTLLink_init_mrefines :
    MRefines "cachetools/__init__.py:<module>.TTLCache._Link.__init__" 12
      (fun _ self args => ∃ r k e, self = .ref r ∧ args = [k, e])
      (fun h self args => match self, args with
                          | .ref r, [k, e] =>
                              (((h.setField r "key" k).setField r "expires" e), .ret .unit)
                          | _, _ => (h, .ret .unit)) := by
  rintro h _ _ ⟨r, k, e, rfl, rfl⟩
  refine forall_ge_of_forall_add (N := 12) ?_
  intro m
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__TTLCache__Link___init__ rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module__TTLCache__Link___init__, ctxOf, P]

/-! ### `TTLCache.__setstate__.<lambda>0` — a projection out of an *argument*, not `self` -/

theorem TTLSetstate_lambda_mrefines :
    MRefines "cachetools/__init__.py:<module>.TTLCache.__setstate__.<lambda>0" 10
      (fun h _ args => ∃ r v, args = [.ref r] ∧ HasField h r "expires" v)
      (fun h _ args => (h, match args with
                           | [.ref r] => .ret (readField h r "expires")
                           | _        => .ret .unit)) := by
  rintro h self _ ⟨r, v, rfl, o, hg, hfld⟩
  refine forall_ge_of_forall_add (N := 10) ?_
  intro m
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__TTLCache___setstate____lambda_0 rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module__TTLCache___setstate____lambda_0, ctxOf, P,
        readField, hg, hfld]

/-! ### `_TimedCache.expire` — an *exception* is a specification

`_TimedCache.expire` is Python's abstract-method idiom: it raises. `Outcome.raise` is a
legitimate refinement target (see `Refine.lean` §1), so "this method always raises" is a
complete specification rather than a gap, and `.raise` → `.ret` is refuted by it.

**Recorded caveat, not smoothed over:** the payload is `Val.unit`, not a
`NotImplementedError` object. `Expr.name "NotImplementedError"` is a builtin the
transpiler does not model, and the semantics evaluates an unbound name to `unit`. The
statement therefore says "raises", not "raises `NotImplementedError`" — see obligation (3)
in §4. -/

/-- Evaluating a bare name never holes and never consumes the heap: every branch of the
`Expr.name` case — local, global, function value, unbound — returns a value. Needed
because `NotImplementedError` is an unbound builtin, and `Ctx.resolve` on a 233-entry
table does not reduce in the kernel. -/
theorem evalExpr_name_isVal (ctx : Ctx) (n : Nat) (h : Heap) (ρ : Env) (x : String) :
    ∃ v, evalExpr ctx (n + 1) h ρ (.name x) = (h, .val v) := by
  simp only [evalExpr]
  repeat' split
  all_goals exact ⟨_, rfl⟩

theorem TimedCache_expire_raises (t : Val) (fuel : Nat) (hf : 10 ≤ fuel) :
    ∃ v, runFunc P fuel "cachetools/__init__.py:<module>._TimedCache.expire" [t] = .exn v := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 10 := ⟨fuel - 10, by omega⟩
  rw [runFunc_of_resolve _ _ _ _ f_cachetools___init___py__module___TimedCache_expire rfl]
  obtain ⟨v, hv⟩ := evalExpr_name_isVal (ctxOf P) (k + 6) [] _ "NotImplementedError"
  refine ⟨v, ?_⟩
  simp only [applyFunc, execStmt, f_cachetools___init___py__module___TimedCache_expire,
        Env.set]
  rw [hv]

/-! ### `_cachedmethod._none` — the sentinel is constant -/

theorem cachedmethod_none_refines :
    Refines P "cachetools/_cachedmethod.py:<module>._none" 8
      (fun args => ∃ x, args = [x]) (fun _ => .ret .unit) := by
  rintro _ ⟨x, rfl⟩
  refine forall_ge_of_forall_add (N := 8) ?_
  intro m
  rw [runFunc_of_resolve _ _ _ _ f_cachetools__cachedmethod_py__module___none rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set,
        f_cachetools__cachedmethod_py__module___none, ctxOf, P]

/-! ## 3. A negative result on the translated module

`Refine.lean` proves `sample_id_not_refinable` on a copied term. The same argument is
worth having on the *real* module, because holes in `cachetools` are the reason the SACM
top claim is UNDEVELOPED. `_uncached_info.cache_clear` is one of the 102: it writes a
closed-over variable, and `nonlocal` *writes* are an honest hole
(`Stmt.hole "scope:nonlocal-write"`, README "Not yet built").

The theorem says: no shallow specification, at any fuel bound, on any inhabited domain,
refines it. Holes are not an inconvenience to be routed around — they are provably
unspecifiable, and this is now stated about generated code rather than a copy. -/

theorem cache_clear_reaches_hole (k : Nat) (h : Heap) (self : Val) :
    (runMethod (k + 4) h "cachetools/_cached.py:<module>._uncached_info.cache_clear"
      self []).2 = .hole "scope:nonlocal-write" := by
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools__cached_py__module___uncached_info_cache_clear rfl]
  simp [applyFunc, execStmt, Env.set,
        f_cachetools__cached_py__module___uncached_info_cache_clear]

theorem cache_clear_not_refinable (N : Nat)
    (dom : Heap → Val → List Val → Prop) (spec : Heap → Val → List Val → Heap × Outcome)
    (h : Heap) (self : Val) (hd : dom h self []) :
    ¬ MRefines "cachetools/_cached.py:<module>._uncached_info.cache_clear" N dom spec := by
  intro hm
  have h1 := congrArg Prod.snd (hm h self [] hd (N + 4) (Nat.le_add_right _ _))
  rw [cache_clear_reaches_hole N h self] at h1
  exact Outcome.toEResult_ne_hole _ _ h1.symm

/-! ## 4. Open obligations

Stated, never admitted. Nothing above is `sorry`, `partial`, `unsafe`, or
`native_decide`.

1. **The specified functions are small.** Ten entry points out of a 45-function
   call-closed core, and out of 233 translated. The large call-closed functions
   (`Cache.__setitem__`, `LRUCache.popitem`, the `_Link` splice/unlink pair) mutate
   containers through `Stmt.setIndex`, which is still an honest hole, or need a
   representation predicate relating a heap region to a shallow record — obligation (4)
   of `Refine.lean` §5, still open.

2. **No loop is refined here.** `Refine.lean` obligation (3) (loop-invariant rule) blocks
   `_Link.unlink` and the eviction loops, which are the functions whose specifications
   would actually be interesting to a `cachetools` user.

3. **Exception payloads are unmodelled.** `TimedCache_expire_raises` pins the *fact* of a
   raise but not its class, because `NotImplementedError` is an unbound builtin name that
   the semantics evaluates to `unit`. Modelling builtin exception classes is a transpiler
   and semantics change, not something this file can repair, and until it happens no
   statement in this file can distinguish `raise NotImplementedError` from `raise
   KeyError`.

4. **`Cache.get` is not specified.** Its body is `if key in self: return self[key]`, and
   `Expr.inOp`/`Expr.index` applied to a `ref` receiver hole out (`in:non-container`)
   rather than dispatching to `__contains__`/`__getitem__`. That is a genuine fidelity
   gap in the semantics — Python's `in` on an object *is* a method call — and it means
   `Cache.get` currently joins the not-refinable set for a reason the ledger does not
   record as a hole, because the hole is dynamic rather than static.
-/

end Autoform.Specs.Cachetools
