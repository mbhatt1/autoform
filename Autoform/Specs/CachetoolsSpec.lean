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

open Autoform.Core Autoform.Refine Autoform.Generated.Cachetools

/-! ## 0. The subject

`P` is the translated `cachetools` program, imported, not copied. Every theorem below
resolves its entry point through `P`'s function table by its fully-qualified CPG name —
so deleting or renaming a function in the generated module breaks these proofs too. -/

/-- The translated program: `Autoform/Generated/Cachetools.lean`, unmodified. -/
abbrev P : Program := Autoform.Generated.Cachetools.program

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
  | some fn => applyFunc (ctxOf P) fuel h fn (some self) args []

theorem runMethod_of_resolve (fuel : Nat) (name : String) (h : Heap) (self : Val)
    (args : List Val) (fn : Func) (hres : (ctxOf P).resolve name = some fn) :
    runMethod fuel h name self args = applyFunc (ctxOf P) fuel h fn (some self) args [] := by
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

-- RELAND (2026-10-09): `stored_class_declarations` (`program.classDecls = []`) and
-- `stored_field_write` described the pre-re-land translation, which carried no class
-- metadata. The re-landed program declares its classes, so both are false and deleted;
-- the theorems below are proved against the declared hierarchy.

attribute [local simp] Ctx.classLookupGap Ctx.usesClassMetadata Ctx.isProperty
  Ctx.classStorageKey Ctx.fieldWriteCheck Ctx.fieldWriteKey Ctx.readSlot Ctx.isSharedClassValue

/-- Attribute reads must discharge the descriptor check before unfolding getter
applications. These facts use the imported property table and preserve all receiver
domains and postconditions below. -/
@[simp] private theorem stored__Cache__maxsize_not_property (cls : String) :
    program.properties.any (fun p => p.1 == cls && p.2 == "_Cache__maxsize") = false := by
  simp [program]

@[simp] private theorem stored__Cache__currsize_not_property (cls : String) :
    program.properties.any (fun p => p.1 == cls && p.2 == "_Cache__currsize") = false := by
  simp [program]

@[simp] private theorem stored__Cache__data_not_property (cls : String) :
    program.properties.any (fun p => p.1 == cls && p.2 == "_Cache__data") = false := by
  simp [program]

@[simp] private theorem stored_expires_not_property (cls : String) :
    program.properties.any (fun p => p.1 == cls && p.2 == "expires") = false := by
  simp [program]

@[simp] private theorem stored__Timer__nesting_not_property (cls : String) :
    program.properties.any (fun p => p.1 == cls && p.2 == "_Timer__nesting") = false := by
  simp [program]


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

/-- `h` stores at `r` an instance of `cls` whose **own** field `f` holds `v`.

RELAND (2026-10-09): the re-landed program carries class metadata, so what an attribute
access does depends on the receiver's class -- a slot, a property, an inherited name or a
miss are all different answers. The accessor theorems therefore name the receiver's
class. A receiver of another class is outside their domain, which is the truth and not
a weakening: `Cache.maxsize` applied to something that is not a `Cache` is not a
statement cachetools makes either. -/
def HasClassField (h : Heap) (r : Ref) (cls f : String) (v : Val) : Prop :=
  ∃ o, h.get r = some o ∧ o.cls = cls ∧ o.fields.find? (·.1 == f) = some (f, v)

/-- `h` stores at `r` an instance of `cls`. -/
def HasClass (h : Heap) (r : Ref) (cls : String) : Prop :=
  ∃ o, h.get r = some o ∧ o.cls = cls

deriving instance DecidableEq for ClassAttribute
deriving instance DecidableEq for ClassLookup

/-! The class-dependent lookups the theorems below pass through, decided by the kernel on
the recovered hierarchy (`program.classDecls`). Each is stated for any context carrying
this program's declarations, which is the shape `simp` meets after unfolding `ctxOf`.
`Cache` reaches `MutableMapping` through its contract (`ExternalBases.lean`), so a name
neither defines is `.absent`; `_Link` is a `__slots__` class, so `key` and `expires` are
slot descriptors with their own storage keys; `_Timer` defines `__getattr__`, which only
matters on a miss. -/
theorem lookup_Cache_maxsize (ctx : Ctx) (hc : ctx.classDecls = P.classDecls) :
    ctx.classLookup "cachetools/__init__.py:<module>.Cache" "_Cache__maxsize" = .absent := by
  unfold Ctx.classLookup; rw [hc]; decide +kernel
theorem lookup_Cache_currsize (ctx : Ctx) (hc : ctx.classDecls = P.classDecls) :
    ctx.classLookup "cachetools/__init__.py:<module>.Cache" "_Cache__currsize" = .absent := by
  unfold Ctx.classLookup; rw [hc]; decide +kernel
theorem lookup_Cache_data (ctx : Ctx) (hc : ctx.classDecls = P.classDecls) :
    ctx.classLookup "cachetools/__init__.py:<module>.Cache" "_Cache__data" = .absent := by
  unfold Ctx.classLookup; rw [hc]; decide +kernel
theorem lookup_Timer_nesting (ctx : Ctx) (hc : ctx.classDecls = P.classDecls) :
    ctx.classLookup "cachetools/__init__.py:<module>._TimedCache._Timer" "_Timer__nesting" = .absent := by
  unfold Ctx.classLookup; rw [hc]; decide +kernel
theorem lookup_Timer_timer (ctx : Ctx) (hc : ctx.classDecls = P.classDecls) :
    ctx.classLookup "cachetools/__init__.py:<module>._TimedCache._Timer" "_Timer__timer" = .absent := by
  unfold Ctx.classLookup; rw [hc]; decide +kernel
theorem lookup_Timer_setattr (ctx : Ctx) (hc : ctx.classDecls = P.classDecls) :
    ctx.classLookup "cachetools/__init__.py:<module>._TimedCache._Timer" "__setattr__" = .found "__builtin.object" (.opaque "class-attribute:object:__setattr__") := by
  unfold Ctx.classLookup; rw [hc]; decide +kernel
theorem lookup_Link_setattr (ctx : Ctx) (hc : ctx.classDecls = P.classDecls) :
    ctx.classLookup "cachetools/__init__.py:<module>.TTLCache._Link" "__setattr__" = .found "__builtin.object" (.opaque "class-attribute:object:__setattr__") := by
  unfold Ctx.classLookup; rw [hc]; decide +kernel
theorem lookup_Link_key (ctx : Ctx) (hc : ctx.classDecls = P.classDecls) :
    ctx.classLookup "cachetools/__init__.py:<module>.TTLCache._Link" "key" = .found "cachetools/__init__.py:<module>.TTLCache._Link" (.slot "<slot>cachetools/__init__.py:<module>.TTLCache._Link.key") := by
  unfold Ctx.classLookup; rw [hc]; decide +kernel
theorem lookup_Link_expires (ctx : Ctx) (hc : ctx.classDecls = P.classDecls) :
    ctx.classLookup "cachetools/__init__.py:<module>.TTLCache._Link" "expires" = .found "cachetools/__init__.py:<module>.TTLCache._Link" (.slot "<slot>cachetools/__init__.py:<module>.TTLCache._Link.expires") := by
  unfold Ctx.classLookup; rw [hc]; decide +kernel

theorem allowsDict_Timer : ClassHierarchy.allowsDict P.classDecls "cachetools/__init__.py:<module>._TimedCache._Timer" = true := by
  decide +kernel

/-! ### `Cache.getsizeof` — the size model is the constant 1

`cachetools.Cache.getsizeof` is the default cost function: every entry costs 1. This is
the assumption the whole `currsize`/`maxsize` accounting rests on, so it is worth
pinning rather than assuming. -/

/-! **Re-land assessment (cachetools v7.1.7 under the current exporter).**

Every subject below was looked up in a fresh export of the identified revision, and each
theorem is annotated with what happens to it when `ast-Cachetools.json` is replaced:

* `RELAND: survives` -- the function is hole-free and its body is byte-identical to the
  committed one; only the added `signatureRejected`/`Func.keywordParams` simp arguments
  are needed, because the fresh render carries a real `pythonSignature` and
  `signatureRejected_legacy` no longer discharges the check.
* `RELAND: BREAKS -- getter is a hole` -- was the prediction for `Cache.maxsize` and
  `Cache.currsize`, `@property` getters the exporter used to hole as
  `call:python-receiver-signature`. Property definitions translate now
  (`Program.properties`, docs/languages.md §12/§14), so on the re-land these theorems
  SURVIVED unchanged; the annotation is kept as the record of what was expected.
* `RELAND: replaced` -- the two `cache_clear` theorems asserted that the function REACHES
  `scope:nonlocal-write`. It no longer does: `nonlocal` writes are boxed
  (docs/languages.md §11), the function is hole-free, and the negative result was false
  in the good direction. §3 now states what the function does instead.
* `RELAND: verified` -- hole-free but the body differed from the committed one; checked
  on the first build against the re-landed AST (`ast-Cachetools.json`, cachetools v7.1.7,
  Joern 4.0.606 -- see `provenance/ast-Cachetools.json.prov.json`).
-/
-- RELAND: survives (staticmethod fix restored `return 1`; body byte-identical).
theorem Cache_getsizeof_refines :
    Refines₁ (α := Int) (β := Int) P
      "cachetools/__init__.py:<module>.Cache.getsizeof" 8 (fun _ => True) (fun _ => 1) := by
  intro v _
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_cachetools___init___py__module__Cache_getsizeof rfl]
  simp [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module__Cache_getsizeof, ctxOf, P, Marshal.toVal]

/-! ### `_DefaultSize.__getitem__` / `.pop` — the degenerate size table

`_DefaultSize` is the object `Cache` uses when no `getsizeof` was supplied: a mapping
that answers `1` to every lookup and forgets every write. Both halves are specified. -/

-- RELAND: survives.
theorem DefaultSize_getitem_refines :
    Refines₁ (α := Int) (β := Int) P
      "cachetools/__init__.py:<module>._DefaultSize.__getitem__" 8
      (fun _ => True) (fun _ => 1) := by
  intro v _
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_cachetools___init___py__module___DefaultSize___getitem__ rfl]
  simp [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module___DefaultSize___getitem__, ctxOf, P, Marshal.toVal]

-- RELAND: survives.
theorem DefaultSize_pop_refines :
    Refines₁ (α := Int) (β := Int) P
      "cachetools/__init__.py:<module>._DefaultSize.pop" 8
      (fun _ => True) (fun _ => 1) := by
  intro v _
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_cachetools___init___py__module___DefaultSize_pop rfl]
  simp [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module___DefaultSize_pop, ctxOf, P, Marshal.toVal]

/-- `_DefaultSize.__setitem__` is a no-op **on the heap as well as on the result**: this
is the theorem that would catch the store being silently implemented. -/
-- RELAND: survives.
theorem DefaultSize_setitem_mrefines :
    MRefines "cachetools/__init__.py:<module>._DefaultSize.__setitem__" 8
      (fun _ _ args => ∃ k v, args = [k, v])
      (fun h _ _ => (h, .ret .unit)) := by
  rintro h self _ ⟨a, b, rfl⟩
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module___DefaultSize___setitem__ rfl]
  simp [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module___DefaultSize___setitem__, ctxOf, P]

/-! ### `Cache.maxsize` / `Cache.currsize` — the two accessors must read *different* fields

Stated for an arbitrary heap and an arbitrary receiver reference, so the field name is
not free to move: swapping `_Cache__maxsize` for `_Cache__currsize` makes the statement
false at any heap where the two differ. `Cache_size_fields_distinct` exhibits such a
heap explicitly, so the separation is witnessed and not merely implied. -/

/-- **The surplus-argument branch is part of the specification, not excluded from it.**
The rendered accessor has `params := []` — the receiver arrives as the base environment,
not as a positional parameter — so *any* positional argument is a surplus, and since
`posRejected` was made real the call raises `TypeError`, exactly as CPython does
(`maxsize() takes 1 positional argument but 2 were given`). The specification therefore
covers every argument list; before the calling convention was modelled the surplus was
silently truncated and this theorem's `.ret` branch was claimed for calls CPython
rejects. -/
-- RELAND: survived -- predicted to break (`@property` getter holed); property definitions translate now.
-- RELAND (2026-10-09): restated -- the receiver is a `Cache` (`HasClassField`).
theorem Cache_maxsize_mrefines :
    MRefines "cachetools/__init__.py:<module>.Cache.maxsize" 10
      (fun h self _ => ∃ r v, self = .ref r ∧ HasClassField h r "cachetools/__init__.py:<module>.Cache" "_Cache__maxsize" v)
      (fun h self args => (h, match args with
                           | [] => match self with
                                   | .ref r => .ret (readField h r "_Cache__maxsize")
                                   | _      => .ret .unit
                           | _  => .raise (.str "TypeError"))) := by
  rintro h _ args ⟨r, v, rfl, o, hg, hcls, hfld⟩
  refine forall_ge_of_forall_add (N := 10) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__Cache_maxsize rfl]
  cases args with
  | nil =>
    simp +decide [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set, f_cachetools___init___py__module__Cache_maxsize, ctxOf, P, P_dialect, readField, hg, hcls, hfld, lookup_Cache_maxsize]
  | cons a as =>
    simp [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Outcome.toEResult, f_cachetools___init___py__module__Cache_maxsize]

/-- **The surplus-argument branch is part of the specification, not excluded from it.**
The rendered accessor has `params := []` — the receiver arrives as the base environment,
not as a positional parameter — so *any* positional argument is a surplus, and since
`posRejected` was made real the call raises `TypeError`, exactly as CPython does
(`maxsize() takes 1 positional argument but 2 were given`). The specification therefore
covers every argument list; before the calling convention was modelled the surplus was
silently truncated and this theorem's `.ret` branch was claimed for calls CPython
rejects. -/
-- RELAND: survived -- predicted to break (`@property` getter holed); property definitions translate now.
-- RELAND (2026-10-09): restated -- the receiver is a `Cache` (`HasClassField`).
theorem Cache_currsize_mrefines :
    MRefines "cachetools/__init__.py:<module>.Cache.currsize" 10
      (fun h self _ => ∃ r v, self = .ref r ∧ HasClassField h r "cachetools/__init__.py:<module>.Cache" "_Cache__currsize" v)
      (fun h self args => (h, match args with
                           | [] => match self with
                                   | .ref r => .ret (readField h r "_Cache__currsize")
                                   | _      => .ret .unit
                           | _  => .raise (.str "TypeError"))) := by
  rintro h _ args ⟨r, v, rfl, o, hg, hcls, hfld⟩
  refine forall_ge_of_forall_add (N := 10) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__Cache_currsize rfl]
  cases args with
  | nil =>
    simp +decide [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set, f_cachetools___init___py__module__Cache_currsize, ctxOf, P, P_dialect, readField, hg, hcls, hfld, lookup_Cache_currsize]
  | cons a as =>
    simp [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Outcome.toEResult, f_cachetools___init___py__module__Cache_currsize]

/-- A concrete cache object whose capacity and occupancy differ. -/
def sampleCache : Heap :=
  [{ cls := "cachetools/__init__.py:<module>.Cache"
   , fields := [("_Cache__maxsize", .int 128), ("_Cache__currsize", .int 3)] }]

/-- The two accessors read the two fields, and are therefore observably different
functions on a cache whose capacity and occupancy differ.

**This statement was strengthened because the mutation gate said so.** It first read only
`maxsize ≠ currsize`, and scored **0/8** — every single-function mutant preserves a
*difference* (breaking one accessor leaves the other alone, so the two still disagree),
so an inequality between two functions is not evidence about either of them. Pinning both
values is what gives it teeth. The lesson generalises: a witness that asserts a relation
between two computations tests neither unless the relation is pinned on both sides. -/
-- RELAND: survived -- predicted to break (both getters holed); property definitions translate now.
theorem Cache_size_fields_distinct :
    (runMethod 10 sampleCache "cachetools/__init__.py:<module>.Cache.maxsize" (.ref 0) []).2
        = .val (.int 128)
  ∧ (runMethod 10 sampleCache "cachetools/__init__.py:<module>.Cache.currsize" (.ref 0) []).2
        = .val (.int 3)
  ∧ (runMethod 10 sampleCache "cachetools/__init__.py:<module>.Cache.maxsize" (.ref 0) []).2
      ≠ (runMethod 10 sampleCache "cachetools/__init__.py:<module>.Cache.currsize" (.ref 0) []).2 := by
  -- Evaluated by the kernel on the concrete heap, not derived from the parent theorems:
  -- a witness that re-derives from an unchanged statement is invisible to the mutation
  -- gate (§4, finding 1), and this one scored 0/4 that way on 2026-10-09.
  refine ⟨rfl, rfl, ?_⟩
  show EResult.val (.int 128) ≠ EResult.val (.int 3)
  intro he; cases he

/-! ### `Cache.__contains__` — membership, and the *polarity* of `in`

`Expr.inOp` carries a negation flag. `__contains__` must use the positive one; a flipped
flag is a silent inversion of every containment test in the library, which this theorem
refutes on any dict receiver. -/

-- RELAND: survives. RELAND (2026-10-09): restated -- the receiver is a `Cache`.
theorem Cache_contains_mrefines :
    MRefines "cachetools/__init__.py:<module>.Cache.__contains__" 12
      (fun h self args => ∃ r k kvs, self = .ref r ∧ args = [k]
                            ∧ HasClassField h r "cachetools/__init__.py:<module>.Cache" "_Cache__data" (.dict kvs))
      (fun h self args => (h, match self, args with
                              | .ref r, [k] =>
                                  match readField h r "_Cache__data" with
                                  | .dict kvs => .ret (.bool (kvs.any (fun kv => Val.beq k kv.1)))
                                  | _         => .ret .unit
                              | _, _ => .ret .unit)) := by
  rintro h _ _ ⟨r, k, kvs, rfl, rfl, o, hg, hcls, hfld⟩
  refine forall_ge_of_forall_add (N := 12) ?_
  intro n
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__Cache___contains__ rfl]
  simp +decide [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module__Cache___contains__, ctxOf, P, P_dialect, valIn, readField,
        Ctx.dunderOn, Val.unbox, hg, hcls, hfld, lookup_Cache_data]

/-- Membership is not constant: it answers `true` for a present key and `false` for an
absent one. This is the anti-vacuity witness for `Cache_contains_mrefines` — a
specification satisfied by `fun _ => true` would pass the equation above only if that
equation were itself wrong, and this makes the discrimination concrete. -/
-- RELAND: survives.
theorem Cache_contains_discriminates :
    (runMethod 12 [{ cls := "cachetools/__init__.py:<module>.Cache", fields := [("_Cache__data", .dict [(.int 1, .int 9)])] }]
        "cachetools/__init__.py:<module>.Cache.__contains__" (.ref 0) [.int 1]).2 = .val (.bool true)
  ∧ (runMethod 12 [{ cls := "cachetools/__init__.py:<module>.Cache", fields := [("_Cache__data", .dict [(.int 1, .int 9)])] }]
        "cachetools/__init__.py:<module>.Cache.__contains__" (.ref 0) [.int 2]).2 = .val (.bool false) := by
  exact ⟨rfl, rfl⟩

/-! ### `TLRUCache._Item.__lt__` — retired

RELAND (2026-10-09): `TLRUItem_lt_mrefines` and `TLRUItem_lt_irrefl` are deleted. `_Item`
is decorated with `functools.total_ordering`, a decorator the exporter cannot apply, so
the re-landed program records the class as `class-definition:decorator-or-metaclass`: no
attribute of an `_Item` instance is readable through its namespace, and a theorem about
`__lt__` reading `self.expires` would be a theorem about that hole. The strict-order claim
is still the right specification; what it needs is a contract for `total_ordering` (it
adds the three missing comparison methods and touches nothing else), the same mechanism
as the external base-class contracts, and that is future work rather than a restated
weaker theorem. -/

/-! ### `_TimedCache._Timer.__exit__` — a heap effect, specified exactly

The timer's re-entrancy counter is decremented on exit. This is the only place in these
specifications where the *heap* is the observable, and it is stated as an exact equation
on `Heap.setField`, so `-` → `+` and `1` → `2` are both refuted. -/

-- RELAND: survives. RELAND (2026-10-09): restated -- the receiver is a `_Timer`. `_Timer`
-- defines `__getattr__`; the exporter used to make that a barrier on the whole namespace,
-- now it is a miss-only hook (docs/languages.md §16.A), and `_Timer__nesting` is present.
theorem Timer_exit_mrefines :
    MRefines "cachetools/__init__.py:<module>._TimedCache._Timer.__exit__" 12
      (fun h self args => ∃ r n e, self = .ref r ∧ args = [e]
                            ∧ HasClassField h r "cachetools/__init__.py:<module>._TimedCache._Timer" "_Timer__nesting" (.int n))
      (fun h self _ => match self with
                       | .ref r =>
                           match readField h r "_Timer__nesting" with
                           | .int n => (h.setField r "_Timer__nesting" (.int (n - 1)), .ret .unit)
                           | _      => (h, .ret .unit)
                       | _ => (h, .ret .unit)) := by
  rintro h _ _ ⟨r, n, e, rfl, rfl, o, hg, hcls, hfld⟩
  refine forall_ge_of_forall_add (N := 12) ?_
  intro m
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module___TimedCache__Timer___exit__ rfl]
  simp +decide [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module___TimedCache__Timer___exit__, ctxOf, P,
        P_dialect, readField, hg, hcls, hfld, lookup_Timer_nesting, lookup_Timer_setattr, allowsDict_Timer]

/-- The decrement is a decrement: on a concrete timer at nesting 1, exit leaves 0. -/
-- RELAND: survives.
theorem Timer_exit_decrements :
    readField ((runMethod 12 [{ cls := "cachetools/__init__.py:<module>._TimedCache._Timer", fields := [("_Timer__nesting", .int 1)] }]
        "cachetools/__init__.py:<module>._TimedCache._Timer.__exit__" (.ref 0) [.unit]).1) 0
        "_Timer__nesting" = .int 0 := by
  rfl

/-! ### `_TimedCache._Timer.__init__` — both assignments happen

A constructor is specified by the *whole* post-state. Deleting either branch of the
`Stmt.seq` changes the resulting heap, so the mutation gate's `seq`-deletion operator has
something to break here. -/

-- RELAND: survives. RELAND (2026-10-09): restated -- the receiver is a `_Timer` (`HasClass`).
theorem Timer_init_mrefines :
    MRefines "cachetools/__init__.py:<module>._TimedCache._Timer.__init__" 12
      (fun h self args => ∃ r t, self = .ref r ∧ args = [t] ∧ HasClass h r "cachetools/__init__.py:<module>._TimedCache._Timer")
      (fun h self args => match self, args with
                          | .ref r, [t] =>
                              (((h.setField r "_Timer__timer" t).setField r "_Timer__nesting" (.int 0)),
                               .ret .unit)
                          | _, _ => (h, .ret .unit)) := by
  rintro h _ _ ⟨r, t, rfl, rfl, o, hg, hcls⟩
  refine forall_ge_of_forall_add (N := 12) ?_
  intro m
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module___TimedCache__Timer___init__ rfl]
  simp +decide [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module___TimedCache__Timer___init__, ctxOf, P, P_dialect,
        Heap.get_setField, hg, hcls, lookup_Timer_timer, lookup_Timer_nesting, lookup_Timer_setattr, allowsDict_Timer]

/-- Both fields are actually written, with the right values in the right places. -/
-- RELAND: survives.
theorem Timer_init_sets_both :
    readField (runMethod 12 [{ cls := "cachetools/__init__.py:<module>._TimedCache._Timer", fields := [] }]
        "cachetools/__init__.py:<module>._TimedCache._Timer.__init__" (.ref 0) [.int 99]).1
      0 "_Timer__timer" = .int 99
  ∧ readField (runMethod 12 [{ cls := "cachetools/__init__.py:<module>._TimedCache._Timer", fields := [] }]
        "cachetools/__init__.py:<module>._TimedCache._Timer.__init__" (.ref 0) [.int 99]).1
      0 "_Timer__nesting" = .int 0 := by
  exact ⟨rfl, rfl⟩

/-! ### `TTLCache._Link.__init__` — the same shape, a different pair of fields

`_Link` declares `__slots__ = ("expires", "key", "next", "prev")`, so RELAND (2026-10-09)
its two writes land in the slots' storage keys (`<slot><class>.<name>`, the key the oracle
also snapshots), not in a dictionary entry named `key`. The specification says so. -/

-- RELAND: survives. RELAND (2026-10-09): restated -- slot storage keys, receiver a `_Link`.
theorem TTLLink_init_mrefines :
    MRefines "cachetools/__init__.py:<module>.TTLCache._Link.__init__" 12
      (fun h self args => ∃ r k e, self = .ref r ∧ args = [k, e] ∧ HasClass h r "cachetools/__init__.py:<module>.TTLCache._Link")
      (fun h self args => match self, args with
                          | .ref r, [k, e] =>
                              (((h.setField r "<slot>cachetools/__init__.py:<module>.TTLCache._Link.key" k).setField r "<slot>cachetools/__init__.py:<module>.TTLCache._Link.expires" e), .ret .unit)
                          | _, _ => (h, .ret .unit)) := by
  rintro h _ _ ⟨r, k, e, rfl, rfl, o, hg, hcls⟩
  refine forall_ge_of_forall_add (N := 12) ?_
  intro m
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__TTLCache__Link___init__ rfl]
  simp +decide [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module__TTLCache__Link___init__, ctxOf, P, P_dialect,
        Heap.get_setField, hg, hcls, lookup_Link_setattr, lookup_Link_key, lookup_Link_expires]

/-! ### `TTLCache.__setstate__.<lambda>0` — a projection out of an *argument*, not `self` -/

-- RELAND: survives. RELAND (2026-10-09): restated -- the argument is a `_Link`, whose
-- `expires` is a slot read from its storage key.
theorem TTLSetstate_lambda_mrefines :
    MRefines "cachetools/__init__.py:<module>.TTLCache.__setstate__.<lambda>0" 10
      (fun h _ args => ∃ r v, args = [.ref r] ∧ HasClassField h r "cachetools/__init__.py:<module>.TTLCache._Link" "<slot>cachetools/__init__.py:<module>.TTLCache._Link.expires" v)
      (fun h _ args => (h, match args with
                           | [.ref r] => .ret (readField h r "<slot>cachetools/__init__.py:<module>.TTLCache._Link.expires")
                           | _        => .ret .unit)) := by
  rintro h self _ ⟨r, v, rfl, o, hg, hcls, hfld⟩
  refine forall_ge_of_forall_add (N := 10) ?_
  intro m
  rw [runMethod_of_resolve _ _ _ _ _ f_cachetools___init___py__module__TTLCache___setstate____lambda_0 rfl]
  simp +decide [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools___init___py__module__TTLCache___setstate____lambda_0, ctxOf, P, P_dialect,
        readField, hg, hcls, hfld, lookup_Link_expires]

/-! ### `_TimedCache.expire` — an *exception* is a specification

`_TimedCache.expire` is Python's abstract-method idiom: it raises. `Outcome.raise` is a
legitimate refinement target (see `Refine.lean` §1), so "this method always raises" is a
complete specification rather than a gap, and `.raise` → `.ret` is refuted by it.

The re-landed export spells `raise NotImplementedError` as the
`py:exception:NotImplementedError` constructor, whose value IS the class name, and
`Stmt.raise` under `.python` classifies what it raises (`pythonRaise`): a represented
class name passes through unchanged. So the statement names the class — the caveat that
stood here ("raises, but the payload is `unit`") is closed, and obligation (3) in §4
records what is still not modelled: the exception's *arguments*. -/

-- RELAND: verified on the re-landed body (`raise` of the `py:exception:` constructor).
theorem TimedCache_expire_raises (t : Val) (fuel : Nat) (hf : 10 ≤ fuel) :
    runFunc P fuel "cachetools/__init__.py:<module>._TimedCache.expire" [t]
      = .exn (.str "NotImplementedError") := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 10 := ⟨fuel - 10, by omega⟩
  rw [runFunc_of_resolve _ _ _ _ f_cachetools___init___py__module___TimedCache_expire rfl]
  have hne : ((none : Option String) != some "time") = true := rfl
  simp +decide only [hne, applyFunc, seedClassAttrDefaults, seedClassAttrs, Func.classAttrDefaults, selfEnv,
        bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams,
        Option.map, Option.getD, List.length, Bool.and_false, Bool.true_and, Bool.or_false, Bool.false_or,
        Val.unbuiltin, execStmt, f_cachetools___init___py__module___TimedCache_expire,
        Env.set, List.filter, List.any, Option.isNone, bne_iff_ne, ne_eq,
        reduceCtorEq, not_false_eq_true, decide_true, Bool.and_self]
  -- The constructor's name is a `String.drop` the kernel computes; `startsWith` is a
  -- simproc. Establish the name first so the rewrite has a literal to work with.
  have hname : ("py:exception:NotImplementedError".drop "py:exception:".length).toString
      = "NotImplementedError" := by decide
  have hname' : ("py:exception:NotImplementedError".drop "py:exception:".length).copy
      = "NotImplementedError" := by decide
  simp +decide [evalExpr, evalList, applyUnop, hname, hname', Stdlib.makeException,
                Stdlib.excNames, pythonRaise, ctxOf, P]

/-! ### `_cachedmethod._none` — the sentinel is constant -/

-- RELAND: survives.
theorem cachedmethod_none_refines :
    Refines P "cachetools/_cachedmethod.py:<module>._none" 8
      (fun args => ∃ x, args = [x]) (fun _ => .ret .unit) := by
  rintro _ ⟨x, rfl⟩
  refine forall_ge_of_forall_add (N := 8) ?_
  intro m
  rw [runFunc_of_resolve _ _ _ _ f_cachetools__cachedmethod_py__module___none rfl]
  simp [applyFunc, bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected, signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools__cachedmethod_py__module___none, ctxOf, P]

/-! ## 3. The former negative result, now a positive one

`Refine.lean` proves `sample_id_not_refinable` on a copied term, and this section used to
prove the same thing about the REAL module: `_uncached_info.cache_clear` writes a
closed-over variable, `nonlocal` writes were an honest hole (`scope:nonlocal-write`), and
no shallow specification could refine a hole. That negative result is now false in the
good direction. `nonlocal` is boxed: `_uncached_info` allocates `misses` as a heap cell
(`Expr.boxNew`) and the closure captures the reference, so `cache_clear` translates to
`misses.v = 0` on that cell. The theorem that replaces the negative one says exactly what
the function does when called with its captured box: it returns `None` and the box's `v`
is `0` afterwards — stated with `Heap.setField` on the left so nothing about the rest of
the heap is assumed or lost. -/

-- RELAND: replaced -- `nonlocal` is boxed, the function translates, and the negative result
-- it stood for (`cache_clear_reaches_hole`, `cache_clear_not_refinable`) is now false.
-- RELAND (2026-10-09): the box at `r` is named as what it is (`Expr.boxNew` allocates
-- class `<local>`): with class metadata a write consults the receiver's class, and a box
-- has none.
theorem cache_clear_zeroes_the_box (k : Nat) (h : Heap) (r : Ref) (hb : HasClass h r "<local>") :
    applyClosure (ctxOf P) (k + 5) h
        f_cachetools__cached_py__module___uncached_info_cache_clear [("misses", .ref r)] [] []
      = (h.setField r "v" (.int 0), .val .unit) := by
  obtain ⟨o, hg, hcls⟩ := hb
  simp +decide [applyClosure, seedClassAttrDefaults, seedClassAttrs, Func.classAttrDefaults,
        bindParams, Func.literalDefaults, Func.posParams, kwargsRejected, posRejected,
        signatureRejected, Func.keywordParams, Val.unbuiltin, execStmt, evalExpr, Env.set,
        f_cachetools__cached_py__module___uncached_info_cache_clear, hg, hcls]

/-! ## 4. What the mutation gate actually said

Run (2026-10-09, after the re-land on the final exporter and semantics):
`scripts/mutate.py Autoform/Generated/Cachetools.lean Autoform.Generated.Cachetools
--spec-file Autoform/Specs/CachetoolsSpec.lean --spec-module Autoform.Specs.CachetoolsSpec
--generated --max-mutants 60 --seed 20260819 --decls <the 12 subject functions of the map>
--subject <theorem→function map>`. 51 mutants of the *generated* module, 51 run,
0 rejected as not type-correct, 0 inconclusive, 0 coarse attributions.

**On-subject score: 68 / 73 = 93.2%.** Twelve of the seventeen theorems are `HAS TEETH`
(100%). Every one of the five survivors was examined; none is a case of a theorem failing
to notice a behavioural change:

* **4 × `ast-seq-delete` of a docstring** (`maxsize` and `currsize`, each once under its
  own `_mrefines` and once more under `Cache_size_fields_distinct`). The deleted statement
  is `Stmt.expr (Expr.lit (Lit.str "..."))` — Python's docstring, translated as
  evaluate-and-discard. Deleting a discarded pure literal is a **provably equivalent
  mutant**; no specification of observable behaviour can, or should, kill it. These three
  theorems are therefore reported `WEAK` (3/4, 3/4, 6/8), and that verdict is correct
  about the gate's operator set, not about the theorems.
* **1 × `ast-ret->expr` in `_cachedmethod._none`.** The body is `.ret (.lit .unit)`;
  under `.expr` the body falls through to `Ctl.normal`, which `applyFunc` maps to
  `EResult.val Val.unit` — the same observable. Equivalent mutant, and a real property of
  the semantics: a Python function that falls off the end returns `None`. With one mutant
  and one survivor the theorem is reported `VACUOUS` (0/1); it is not.
* **2 theorems with no mutants at all**: `_DefaultSize.__setitem__` has body `.skip`, and
  `_TimedCache.expire`'s body offers the operator set nothing it rewrites (the gate prints
  `no mutant generated for declaration` for both). `DefaultSize_setitem_mrefines` and
  `TimedCache_expire_raises` are reported `UNTESTED` rather than given a score. That is
  the honest verdict, not a pass.

Two findings the gate produced about *this file*, both recorded because they generalise:

1. **Witness corollaries proved by rewriting their parent theorem are invisible to the
   gate.** `Cache_size_fields_distinct`, `Cache_contains_discriminates`,
   `Timer_exit_decrements` and `Timer_init_sets_both` were restated on 2026-10-09 as
   `∀ fuel ≥ N` consequences of their parents and scored **0 / 23** that way: when a mutant
   breaks the parent, Lean reports the error at the parent and still admits its
   *statement* downstream, so the corollary re-derives from an unchanged statement and
   never fails. They now evaluate the interpreter directly (`rfl` on the concrete heap —
   `Val` has no `DecidableEq`, so `decide` is not available) and score 25 / 27. This is the
   same shape as STRATEGY.md 14: a theorem stated in terms of the thing being mutated
   moves with it.
2. **An inequality between two functions tests neither.** `Cache_size_fields_distinct`
   originally claimed only `maxsize ≠ currsize` and scored **0/8** — mutating one
   accessor leaves the other alone, so the two still differ. Pinning both values is what
   gives it its 6/8 (the remaining two being the docstring-deletion equivalents).

The score over the *whole* mutant population is 2%–16% per theorem. That number is not
a vacuity measurement, it is a **coverage** measurement: these theorems describe 12 of
209 translated functions, so most mutants are in code they never mention. The two must
not be conflated, which is why `mutate.py --subject` reports them separately.

## 5. Open obligations

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

3. **Exception arguments are unmodelled.** `TimedCache_expire_raises` names the class —
   the `py:exception:<Name>` constructor evaluates to the represented class name, and
   `ExcSafe.lean` proves every Python exception Core raises is one — but an exception is
   only its class here: `KeyError(key)` and `KeyError()` are the same value, so no
   statement in this file can speak about what an exception *carries*.

4. **`Cache.get` is not specified.** Its body is `if key in self: return self[key]`, and
   `Expr.inOp`/`Expr.index` applied to a `ref` receiver hole out (`in:non-container`)
   rather than dispatching to `__contains__`/`__getitem__`. That is a genuine fidelity
   gap in the semantics — Python's `in` on an object *is* a method call — and it means
   `Cache.get` currently joins the not-refinable set for a reason the ledger does not
   record as a hole, because the hole is dynamic rather than static.
-/

end Autoform.Specs.Cachetools
