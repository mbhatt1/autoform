import Autoform.Refine
import Autoform.Generated.Cachetools

/-!
# Shared context of `Autoform/Specs/CachetoolsSpec.lean`

The subject, the method-call refinement predicate, the field-lookup model and the
class-lookup facts every theorem of the specification rewrites with. The theorems
themselves are in `CachetoolsSpec/PartN.lean`: one Lean process retains every proof term
it elaborates, and the single-file module held 13.6 GB (measured 2026-10-10 with
`/usr/bin/time -l lake env lean`), so the parts are what bound the memory of a build.
All files share the namespace `Autoform.Specs.Cachetools`; every name is unchanged.
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

/-- Attribute reads must discharge the descriptor check before unfolding getter
applications. These facts use the imported property table and preserve all receiver
domains and postconditions below. -/
@[simp] theorem stored__Cache__maxsize_not_property (cls : String) :
    program.properties.any (fun p => p.1 == cls && p.2 == "_Cache__maxsize") = false := by
  simp [program]

@[simp] theorem stored__Cache__currsize_not_property (cls : String) :
    program.properties.any (fun p => p.1 == cls && p.2 == "_Cache__currsize") = false := by
  simp [program]

@[simp] theorem stored__Cache__data_not_property (cls : String) :
    program.properties.any (fun p => p.1 == cls && p.2 == "_Cache__data") = false := by
  simp [program]

@[simp] theorem stored_expires_not_property (cls : String) :
    program.properties.any (fun p => p.1 == cls && p.2 == "expires") = false := by
  simp [program]

@[simp] theorem stored__Timer__nesting_not_property (cls : String) :
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

end Autoform.Specs.Cachetools
