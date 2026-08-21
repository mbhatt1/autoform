import Autoform.Refine
import Autoform.FuelMono

/-!
# `SpecsGen.Basis` — the hand-written substrate the synthesized specifications stand on

`scripts/synth_specs.py` (Layer 4 of `STRATEGY.md` §4) generates specifications about
translated code. Generated Lean is only as trustworthy as the vocabulary it is generated
*in*, so the vocabulary lives here, is hand-written, and is small enough to read:

* `Case` — one concrete input to a translated function: a heap, an optional receiver, and
  an argument list. This is exactly what `scripts/differential.py` records when it traces
  the repository's own test suite, so a `Case` is a real call that really happened.
* `Obs` — a `Case` together with the outcome **the real runtime produced**. An `Obs`
  carries information the interpreter did not manufacture; a theorem stated against one
  is a cross-implementation claim (§4 source 4), not the interpreter agreeing with itself.
* The `law*` predicates — the algebraic laws the generator mines (§4 source 3). Each is a
  `Bool`-valued function of a `Case`, so a mined law is *checkable by computation* (the
  refutation pass) and *provable by `decide`/`rfl`* over a finite domain.
* `MRefines` — the receiver-carrying analogue of `Refine.lean`'s `Refines`, for the
  universally quantified specs the generator can also prove.

## Why the finite-domain theorems are not tests

They are tests — kernel-checked ones, which is the point. `Autoform/Harness/Conformance.lean`
refutes; a `by decide` proof over an explicit domain *records* the refutation attempt as a
theorem with an axiom basis, so `scripts/mutate.py` can mutate the subject and see whether
the statement notices. A statement that survives mutation of the code it describes is
reported as worthless by the generator's own screen, not by a human reading it.

## What is deliberately absent

No `sorry`, and no admitted statements of any kind. Anything the generator states but
cannot prove is emitted as an `Obligation`: a `Prop`-valued `def` plus a data record. A
`def` of a `Prop` asserts nothing, so recording one is honest in a way `sorry` is not.
-/

namespace Autoform.SpecsGen

open Autoform.Core Autoform.Refine

/-! ## 1. Cases and observations -/

/-- One concrete call: the heap it ran against, the receiver (`none` for a module-level
function), and the arguments. -/
structure Case where
  heap : Heap
  self : Option Val
  args : List Val
  deriving Repr, Inhabited

/-- Run a translated function on a case.

The `Ctx` is passed rather than a `Program` because the heap a case runs against is not
empty: module-level bindings live in a globals frame that `initGlobals` allocates, and the
context has to point at it. The generated module builds exactly the same context
`scripts/differential.py` uses, so a case that was recorded against CPython is replayed
here in the configuration it was recorded in. -/
def runCase (ctx : Ctx) (fuel : Nat) (fn : Func) (c : Case) : Heap × EResult :=
  applyFunc ctx fuel c.heap fn c.self c.args []

/-! ### Structural predicates on results

`EResult` has four constructors and they mean four different things (`README.md`:
"ignorance ≠ behaviour"). `runs` accepts the two that are *behaviour* and rejects the two
that are statements about our own ignorance. -/

/-- The function produced a value. -/
def isVal : EResult → Bool
  | .val _ => true
  | _      => false

/-- The function raised — which is behaviour, not failure. -/
def isExn : EResult → Bool
  | .exn _ => true
  | _      => false

/-- The function reached an untranslated construct. -/
def isHole : EResult → Bool
  | .hole _ => true
  | _       => false

/-- The function did something, rather than telling us we do not know what it does:
neither an untranslated construct nor an exhausted fuel budget. -/
def runs (r : EResult) : Bool := isVal r || isExn r

/-- Structural equality on results, so that laws are decidable by computation. -/
def EResult.beq : EResult → EResult → Bool
  | .val a,     .val b     => Val.beq a b
  | .exn a,     .exn b     => Val.beq a b
  | .hole a,    .hole b    => a == b
  | .outOfFuel, .outOfFuel => true
  | _,          _          => false

/-- Structural equality on heap objects. -/
def Obj.beq (a b : Obj) : Bool :=
  a.cls == b.cls && a.fields.length == b.fields.length
    && (a.fields.zip b.fields).all (fun kv => kv.1.1 == kv.2.1 && Val.beq kv.1.2 kv.2.2)

/-- Structural equality on heaps. -/
def Heap.beq (h g : Heap) : Bool :=
  h.length == g.length && (h.zip g).all (fun ab => Obj.beq ab.1 ab.2)

/-- A case paired with the outcome the **real runtime** produced for it. -/
structure Obs where
  case     : Case
  /-- What CPython did. Recorded by `scripts/differential.py`'s trace hook, not by the
  interpreter this file is about. -/
  expected : EResult
  deriving Repr, Inhabited

/-! ## 2. The laws

Every law is `Bool`-valued and takes the program, a fuel budget, the translated `Func`,
and a case. Passing the `Func` explicitly (rather than resolving a name) means the
generated theorem mentions the generated definition, which is what `#audit_depends`
looks for. -/

/-- **Cross-runtime conformance.** The interpreter reproduces what CPython did.
The right-hand side comes from outside this system, so this is not the interpreter
agreeing with itself. -/
def lawConform (ctx : Ctx) (fuel : Nat) (fn : Func) (o : Obs) : Bool :=
  EResult.beq (runCase ctx fuel fn o.case).2 o.expected

/-- **Totality / no-hole / termination.** The three-in-one structural spec of §4 source 2:
within `fuel`, the function neither reaches an untranslated construct nor runs out. -/
def lawRuns (ctx : Ctx) (fuel : Nat) (fn : Func) (c : Case) : Bool :=
  runs (runCase ctx fuel fn c).2

/-- The stronger form: it returns a value, and does not even raise. -/
def lawReturns (ctx : Ctx) (fuel : Nat) (fn : Func) (c : Case) : Bool :=
  isVal (runCase ctx fuel fn c).2

/-- **Purity of the heap.** The call leaves the heap structurally unchanged. False for
anything that writes a field, so `Stmt.setField` mutations are caught by it. -/
def lawHeapPreserved (ctx : Ctx) (fuel : Nat) (fn : Func) (c : Case) : Bool :=
  Heap.beq (runCase ctx fuel fn c).1 c.heap

/-- **Constant output.** -/
def lawConst (ctx : Ctx) (fuel : Nat) (fn : Func) (v : Val) (c : Case) : Bool :=
  EResult.beq (runCase ctx fuel fn c).2 (.val v)

/-- **Field projection.** The result is the named field of the receiver — the spec of an
accessor, and it fails the moment the accessor reads a different field. -/
def lawProjects (ctx : Ctx) (fuel : Nat) (fn : Func) (fld : String) (c : Case) : Bool :=
  match c.self with
  | some (.ref r) => EResult.beq (runCase ctx fuel fn c).2 (.val (c.heap.getField r fld))
  | _             => false

/-- **Identity.** The result is the first argument, unchanged. -/
def lawIdentity (ctx : Ctx) (fuel : Nat) (fn : Func) (c : Case) : Bool :=
  match c.args with
  | a :: _ => EResult.beq (runCase ctx fuel fn c).2 (.val a)
  | []     => false

/-- **Idempotence.** Feeding the result back as the (single) argument changes nothing.
Stated with the *resulting* heap, so a stateful function is not let off the hook. -/
def lawIdempotent (ctx : Ctx) (fuel : Nat) (fn : Func) (c : Case) : Bool :=
  match runCase ctx fuel fn c with
  | (h₁, .val v) =>
      EResult.beq (runCase ctx fuel fn { c with heap := h₁, args := [v] }).2 (.val v)
  | _            => false

/-- **Involution.** Applying twice returns the original argument. -/
def lawInvolutive (ctx : Ctx) (fuel : Nat) (fn : Func) (c : Case) : Bool :=
  match c.args, runCase ctx fuel fn c with
  | a :: _, (h₁, .val v) =>
      EResult.beq (runCase ctx fuel fn { c with heap := h₁, args := [v] }).2 (.val a)
  | _, _ => false

/-- **Commutativity** in the first two arguments. -/
def lawCommutes (ctx : Ctx) (fuel : Nat) (fn : Func) (c : Case) : Bool :=
  match c.args with
  | a :: b :: rest =>
      EResult.beq (runCase ctx fuel fn c).2
        (runCase ctx fuel fn { c with args := b :: a :: rest }).2
  | _ => false

/-- **Non-negative integer result** — a range bound, the cheapest useful postcondition. -/
def lawNonneg (ctx : Ctx) (fuel : Nat) (fn : Func) (c : Case) : Bool :=
  match (runCase ctx fuel fn c).2 with
  | .val (.int n) => decide (0 ≤ n)
  | _             => false

/-- **Always raises**, with this exception payload. The postcondition form of a guard
(`raise ValueError(...)`) that the trace actually exercised. -/
def lawRaises (ctx : Ctx) (fuel : Nat) (fn : Func) (v : Val) (c : Case) : Bool :=
  EResult.beq (runCase ctx fuel fn c).2 (.exn v)

/-- **Determinism** — generated deliberately, and never emitted.

§15 measured that determinism properties (`f(x) == f(x)`) dominate the 41% of FVSpec that
is vacuous: they are meaningful in a language with mutable state and nondeterminism, and
contentless the moment they are moved into a pure setting. This is the shape such a
property takes here, written out so the claim can be checked rather than asserted. The
generator mines it like any other law, then rejects every instance under the
`reflexive_conclusion` screen and reports the count. -/
def Deterministic (ctx : Ctx) (fuel : Nat) (fn : Func) (c : Case) : Prop :=
  runCase ctx fuel fn c = runCase ctx fuel fn c

/-- …and here is the proof that it says nothing: one `rfl` discharges it for *every*
program, function and case — including a function whose body is a single hole. `runCase`
is a function, so in Lean this property has no content at all. -/
theorem deterministic_vacuous : ∀ ctx fuel fn c, Deterministic ctx fuel fn c :=
  fun _ _ _ _ => rfl

/-! ## 3. Universally quantified specifications

`Refine.lean`'s `Refines` covers module-level functions. Methods need the receiver and the
resulting heap, so this is `Refines` extended with both. It is the same definition as the
hand-written one in `Autoform/Specs/`, restated here because generated code must not
depend on a hand-written spec module that may or may not exist. -/

/-- Invoke a *method*: a resolved function applied to an explicit receiver, returning the
resulting heap alongside the result. -/
def runMethod (p : Program) (fuel : Nat) (h : Heap) (name : String) (self : Val)
    (args : List Val) : Heap × EResult :=
  match (ctxOf p).resolve name with
  | none    => (h, .hole s!"entry:{name}")
  | some fn => applyFunc (ctxOf p) fuel h fn (some self) args []

theorem runMethod_of_resolve (p : Program) (fuel : Nat) (name : String) (h : Heap)
    (self : Val) (args : List Val) (fn : Func)
    (hres : (ctxOf p).resolve name = some fn) :
    runMethod p fuel h name self args = applyFunc (ctxOf p) fuel h fn (some self) args [] := by
  unfold runMethod; rw [hres]

/-- **Method refinement.** For every receiver/argument tuple in `dom` and every fuel budget
at least `N`, the method's heap effect *and* its result are exactly those of the total Lean
function `spec`. `Outcome` (from `Refine.lean`) has no `hole` and no `outOfFuel`, so a
method that reaches an untranslated construct provably has no `MRefines` specification. -/
def MRefines (p : Program) (name : String) (N : Nat)
    (dom : Heap → Val → List Val → Prop)
    (spec : Heap → Val → List Val → Heap × Autoform.Refine.Outcome) : Prop :=
  ∀ h self args, dom h self args → ∀ fuel, N ≤ fuel →
    runMethod p fuel h name self args
      = ((spec h self args).1, ((spec h self args).2).toEResult)

/-- `MRefines` inherits the non-vacuity of `Refines`: a refined method never reports an
untranslated construct. -/
theorem mrefines_not_hole {p name N dom spec} (hm : MRefines p name N dom spec)
    (h : Heap) (self : Val) (args : List Val) (hd : dom h self args)
    (fuel : Nat) (hf : N ≤ fuel) (l : String) :
    (runMethod p fuel h name self args).2 ≠ .hole l := by
  rw [hm h self args hd fuel hf]
  exact Autoform.Refine.Outcome.toEResult_ne_hole _ l

/-- …and never runs out of fuel at or above the stated bound. -/
theorem mrefines_terminates {p name N dom spec} (hm : MRefines p name N dom spec)
    (h : Heap) (self : Val) (args : List Val) (hd : dom h self args)
    (fuel : Nat) (hf : N ≤ fuel) :
    (runMethod p fuel h name self args).2 ≠ .outOfFuel := by
  rw [hm h self args hd fuel hf]
  exact Autoform.Refine.Outcome.toEResult_ne_outOfFuel _

/-! ### Accessors

The single most common shape in a real library's call-closed core is `return self.x`, so
it gets a lemma of its own rather than a generated proof script per instance.

`fieldOf` mirrors the *interpreter's* lookup order for `Expr.field` — own fields first,
then bindings captured by the class — rather than `Heap.getField`, which only looks at
`fields`. The two agree on every object whose field is present, and stating the spec in
terms of the wrong one would produce a theorem that is false exactly on the objects a
closure-defined class produces. -/

/-- Field lookup in the order `Expr.field` uses. -/
def fieldOf (h : Heap) (r : Ref) (f : String) : Val :=
  match h.get r with
  | some o => match o.fields.find? (·.1 == f) with
              | some (_, v) => v
              | none        => match o.captured.find? (·.1 == f) with
                               | some (_, v) => v
                               | none        => .unit
  | none => .unit

/-- **An accessor returns the field it names**, for every heap, every receiver and every
argument list, at every fuel budget of at least four.

Stated for an arbitrary `Func` whose body has the accessor shape, so a generated theorem
discharges both hypotheses by `rfl` against the *generated* definition: change the field
name in `Autoform/Generated/…` and the `rfl` fails.

`hp : fn.params = []` is not decoration. If a parameter were also called `self` it would
shadow the receiver in `Env`, and the theorem would be false — the hypothesis is the
honest way to say the proof depends on that not happening.

Two more hypotheses came from the semantics growing, and both are honest for the same
reason. `hv`/`hkw` say the function has no `*args`/`**kwargs`: `applyFunc` now binds
through `bindParams` and rejects unexpected keywords, and a variadic accessor would bind
differently. `hmod` says the receiver is not a **module object** — since module objects
were modelled, reading an absent attribute off one is `.hole "module-attr:…"`, not
`.unit`, so an accessor spec that ignored the distinction would be false exactly on
those receivers. Weakening the statement to a domain where it is true beats stating a
convenient falsehood. -/
theorem applyFunc_ret_field_self (ctx : Ctx) (n : Nat) (h : Heap) (fn : Func)
    (fld : String) (hb : fn.body = .ret (.field (.name "self") fld))
    (hp : fn.params = []) (hv : fn.vararg = none) (hkw : fn.kwarg = none)
    (r : Ref) (args : List Val)
    (hmod : ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false) :
    applyFunc ctx (n + 4) h fn (some (.ref r)) args [] = (h, .val (fieldOf h r fld)) := by
  unfold applyFunc
  simp only [hb, bindParams_plain _ _ hv hkw, hp, kwargsRejected_nil,
    execStmt, evalExpr, Env.set, fieldOf, List.zip_nil_left]
  rcases hgr : h.get r with _ | o
  · simp [hgr]
  · have hm := hmod o hgr
    rcases hf : o.fields.find? (fun x => x.1 == fld) with _ | ⟨a, v⟩
    · rcases hc : o.captured.find? (fun x => x.1 == fld) with _ | ⟨b, w⟩ <;>
        simp [hgr, hf, hc, hm]
    · simp [hgr, hf]

/-- The same theorem for the shape a *documented* accessor actually has.

Python puts the docstring in the function body, and the transpiler keeps it: the body of
`Cache.maxsize` is `seq (expr (lit (str "…"))) (ret (field (name "self") …))`. Discarding
the docstring statement to make the shapes match would be a lie about what is executed,
so the extra statement is stepped through instead — it costs one more unit of fuel and
nothing else. -/
theorem applyFunc_doc_ret_field_self (ctx : Ctx) (n : Nat) (h : Heap) (fn : Func)
    (fld doc : String)
    (hb : fn.body = .seq (.expr (.lit (.str doc))) (.ret (.field (.name "self") fld)))
    (hp : fn.params = []) (hv : fn.vararg = none) (hkw : fn.kwarg = none)
    (r : Ref) (args : List Val)
    (hmod : ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false) :
    applyFunc ctx (n + 5) h fn (some (.ref r)) args [] = (h, .val (fieldOf h r fld)) := by
  unfold applyFunc
  simp only [hb, bindParams_plain _ _ hv hkw, hp, kwargsRejected_nil,
    execStmt, evalExpr, Env.set, fieldOf, List.zip_nil_left]
  rcases hgr : h.get r with _ | o
  · simp [hgr]
  · have hm := hmod o hgr
    rcases hf : o.fields.find? (fun x => x.1 == fld) with _ | ⟨a, v⟩
    · rcases hc : o.captured.find? (fun x => x.1 == fld) with _ | ⟨b, w⟩ <;>
        simp [hgr, hf, hc, hm]
    · simp [hgr, hf]

/-! ## 3b. Fuel independence

Every mined law is checked, and proved, at one concrete fuel budget. That is a weaker
statement than it looks: `FUEL` is an arbitrary constant, and a reader is entitled to ask
whether the law is a fact about the program or an artefact of the budget. `Autoform/FuelMono.lean`
answers it in general — for a `tryFinally`-free context, raising the budget cannot change a
result that did not run out of fuel — and this section lifts that from `applyFunc` to the
laws, so a generated theorem can quantify over *every* budget at or above the one it was
checked at.

Two things are load-bearing and neither is decoration:

* **`tryFinally` is genuinely excluded.** `FuelMono.tryFinally_breaks_fuel_mono` exhibits a
  program that returns `1` at fuel 4 and `2` at fuel 5. A law about a subject whose body
  contains `tryFinally` therefore stays an open obligation; it is not routed around.
* **The `≠ outOfFuel` side condition is checked, not assumed.** Some laws force it
  (`lawRuns` rejects `outOfFuel` by construction); others do *not*. `lawCommutes` is
  `EResult.beq r₁ r₂`, which is `true` when both sides are `outOfFuel` — precisely the
  shape that would make a "law" hold for the reason that nothing ran. Each family
  therefore carries an explicit guard, evaluated over the same domain as the law itself.
-/

/-- The result is something rather than an admission that we did not run long enough.
Note that `.hole` counts as defined here: an untranslated construct is not a fuel problem,
and fuel monotonicity applies to it unchanged. Whether a hole is acceptable is `lawRuns`'
question, not this one. -/
def defined (r : EResult) : Bool :=
  match r with
  | .outOfFuel => false
  | _          => true

/-- **Fuel monotonicity, at the level of a `Case`.** -/
theorem runCase_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {fn : Func}
    (hfn : tfFreeS fn.body = true) {k k' : Nat} (hk : k ≤ k') {c : Case}
    (hd : defined (runCase ctx k fn c).2 = true) :
    runCase ctx k' fn c = runCase ctx k fn c := by
  have hne : (runCase ctx k fn c).2 ≠ .outOfFuel := by
    intro hEq; rw [hEq] at hd; simp [defined] at hd
  have he : applyFunc ctx k c.heap fn c.self c.args []
      = ((runCase ctx k fn c).1, (runCase ctx k fn c).2) := rfl
  simpa [runCase] using applyFunc_fuel_mono hctx hfn hk he hne

/-- Lift a per-element implication over a list, with a guard that also has to hold.

This is the shape every generated fuel-independence proof has: the law was checked at
`FUEL` by computation, the guard was checked at `FUEL` by computation, and the step lemma
turns the pair into the law at any larger budget. -/
theorem all_transfer {α : Type} (l : List α) (guard f g : α → Bool)
    (hstep : ∀ a, guard a = true → f a = true → g a = true)
    (hg : l.all guard = true) (hf : l.all f = true) : l.all g = true := by
  rw [List.all_eq_true] at hg hf ⊢
  exact fun a ha => hstep a (hg a ha) (hf a ha)

/-! ### Guards

One per law shape, naming exactly the runs that law performs. A guard that mentions fewer
runs than its law would leave a gap through which `outOfFuel` could still change the
answer. -/

/-- Guard for the laws that run the function once on the case itself. -/
def gRun (ctx : Ctx) (fuel : Nat) (fn : Func) (c : Case) : Bool :=
  defined (runCase ctx fuel fn c).2

/-- Guard for the conformance law, whose case sits inside an `Obs`. -/
def gRunObs (ctx : Ctx) (fuel : Nat) (fn : Func) (o : Obs) : Bool :=
  defined (runCase ctx fuel fn o.case).2

/-- Guard for `lawIdempotent`: both the first run and the run on its result. -/
def gIdem (ctx : Ctx) (fuel : Nat) (fn : Func) (c : Case) : Bool :=
  match runCase ctx fuel fn c with
  | (h₁, .val v) => defined (runCase ctx fuel fn { c with heap := h₁, args := [v] }).2
  | _            => false

/-- Guard for `lawInvolutive`, same two runs. -/
def gInvol (ctx : Ctx) (fuel : Nat) (fn : Func) (c : Case) : Bool :=
  match c.args, runCase ctx fuel fn c with
  | _ :: _, (h₁, .val v) =>
      defined (runCase ctx fuel fn { c with heap := h₁, args := [v] }).2
  | _, _ => false

/-- Guard for `lawCommutes`: **both** orders.

`lawCommutes` compares two results with `EResult.beq`, and `beq .outOfFuel .outOfFuel` is
`true`. Without this guard, a function too big for the budget would "commute" for the
reason that neither side ran. -/
def gComm (ctx : Ctx) (fuel : Nat) (fn : Func) (c : Case) : Bool :=
  match c.args with
  | a :: b :: rest =>
      defined (runCase ctx fuel fn c).2
        && defined (runCase ctx fuel fn { c with args := b :: a :: rest }).2
  | _ => false

/-! ### Step lemmas -/

theorem lawConform_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {fn : Func}
    (hfn : tfFreeS fn.body = true) {k k' : Nat} (hk : k ≤ k') {o : Obs}
    (hg : gRunObs ctx k fn o = true) (h : lawConform ctx k fn o = true) :
    lawConform ctx k' fn o = true := by
  unfold lawConform at h ⊢
  rw [runCase_fuel_mono hctx hfn hk hg]; exact h

theorem lawRuns_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {fn : Func}
    (hfn : tfFreeS fn.body = true) {k k' : Nat} (hk : k ≤ k') {c : Case}
    (hg : gRun ctx k fn c = true) (h : lawRuns ctx k fn c = true) :
    lawRuns ctx k' fn c = true := by
  unfold lawRuns at h ⊢
  rw [runCase_fuel_mono hctx hfn hk hg]; exact h

theorem lawReturns_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {fn : Func}
    (hfn : tfFreeS fn.body = true) {k k' : Nat} (hk : k ≤ k') {c : Case}
    (hg : gRun ctx k fn c = true) (h : lawReturns ctx k fn c = true) :
    lawReturns ctx k' fn c = true := by
  unfold lawReturns at h ⊢
  rw [runCase_fuel_mono hctx hfn hk hg]; exact h

theorem lawHeapPreserved_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {fn : Func}
    (hfn : tfFreeS fn.body = true) {k k' : Nat} (hk : k ≤ k') {c : Case}
    (hg : gRun ctx k fn c = true) (h : lawHeapPreserved ctx k fn c = true) :
    lawHeapPreserved ctx k' fn c = true := by
  unfold lawHeapPreserved at h ⊢
  rw [runCase_fuel_mono hctx hfn hk hg]; exact h

theorem lawConst_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {fn : Func}
    (hfn : tfFreeS fn.body = true) {k k' : Nat} (hk : k ≤ k') {v : Val} {c : Case}
    (hg : gRun ctx k fn c = true) (h : lawConst ctx k fn v c = true) :
    lawConst ctx k' fn v c = true := by
  unfold lawConst at h ⊢
  rw [runCase_fuel_mono hctx hfn hk hg]; exact h

theorem lawProjects_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {fn : Func}
    (hfn : tfFreeS fn.body = true) {k k' : Nat} (hk : k ≤ k') {fld : String} {c : Case}
    (hg : gRun ctx k fn c = true) (h : lawProjects ctx k fn fld c = true) :
    lawProjects ctx k' fn fld c = true := by
  unfold lawProjects at h ⊢
  rw [runCase_fuel_mono hctx hfn hk hg]; exact h

theorem lawIdentity_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {fn : Func}
    (hfn : tfFreeS fn.body = true) {k k' : Nat} (hk : k ≤ k') {c : Case}
    (hg : gRun ctx k fn c = true) (h : lawIdentity ctx k fn c = true) :
    lawIdentity ctx k' fn c = true := by
  unfold lawIdentity at h ⊢
  rw [runCase_fuel_mono hctx hfn hk hg]; exact h

theorem lawNonneg_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {fn : Func}
    (hfn : tfFreeS fn.body = true) {k k' : Nat} (hk : k ≤ k') {c : Case}
    (hg : gRun ctx k fn c = true) (h : lawNonneg ctx k fn c = true) :
    lawNonneg ctx k' fn c = true := by
  unfold lawNonneg at h ⊢
  rw [runCase_fuel_mono hctx hfn hk hg]; exact h

theorem lawRaises_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {fn : Func}
    (hfn : tfFreeS fn.body = true) {k k' : Nat} (hk : k ≤ k') {v : Val} {c : Case}
    (hg : gRun ctx k fn c = true) (h : lawRaises ctx k fn v c = true) :
    lawRaises ctx k' fn v c = true := by
  unfold lawRaises at h ⊢
  rw [runCase_fuel_mono hctx hfn hk hg]; exact h

theorem lawIdempotent_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {fn : Func}
    (hfn : tfFreeS fn.body = true) {k k' : Nat} (hk : k ≤ k') {c : Case}
    (hg : gIdem ctx k fn c = true) (h : lawIdempotent ctx k fn c = true) :
    lawIdempotent ctx k' fn c = true := by
  unfold gIdem at hg
  unfold lawIdempotent at h ⊢
  rcases hr : runCase ctx k fn c with ⟨h₁, r⟩
  simp only [hr] at hg h
  cases r with
  | val v =>
      have hd1 : defined (runCase ctx k fn c).2 = true := by rw [hr]; rfl
      rw [runCase_fuel_mono hctx hfn hk hd1]
      simp only [hr]
      rw [runCase_fuel_mono hctx hfn hk hg]
      exact h
  | exn v => simp at hg
  | hole l => simp at hg
  | outOfFuel => simp at hg

theorem lawInvolutive_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {fn : Func}
    (hfn : tfFreeS fn.body = true) {k k' : Nat} (hk : k ≤ k') {c : Case}
    (hg : gInvol ctx k fn c = true) (h : lawInvolutive ctx k fn c = true) :
    lawInvolutive ctx k' fn c = true := by
  unfold gInvol at hg
  unfold lawInvolutive at h ⊢
  rcases ha : c.args with _ | ⟨a, rest⟩
  · rw [ha] at hg; simp at hg
  · rcases hr : runCase ctx k fn c with ⟨h₁, r⟩
    simp only [ha, hr] at hg h
    cases r with
    | val v =>
        have hd1 : defined (runCase ctx k fn c).2 = true := by rw [hr]; rfl
        rw [runCase_fuel_mono hctx hfn hk hd1]
        simp only [hr]
        rw [runCase_fuel_mono hctx hfn hk hg]
        exact h
    | exn v => simp at hg
    | hole l => simp at hg
    | outOfFuel => simp at hg

theorem lawCommutes_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {fn : Func}
    (hfn : tfFreeS fn.body = true) {k k' : Nat} (hk : k ≤ k') {c : Case}
    (hg : gComm ctx k fn c = true) (h : lawCommutes ctx k fn c = true) :
    lawCommutes ctx k' fn c = true := by
  unfold gComm at hg
  unfold lawCommutes at h ⊢
  rcases ha : c.args with _ | ⟨a, as⟩
  · rw [ha] at hg; simp at hg
  · rcases has : as with _ | ⟨b, rest⟩
    · rw [ha, has] at hg; simp at hg
    · simp only [ha, has] at hg h
      obtain ⟨hg1, hg2⟩ := Bool.and_eq_true .. |>.mp hg
      dsimp only
      rw [runCase_fuel_mono hctx hfn hk hg1, runCase_fuel_mono hctx hfn hk hg2]
      exact h

/-! ## 4. Open obligations

What the generator could state but not prove. Recorded as *data* plus a `Prop`-valued
`def`; a `def` asserts nothing, so nothing here is admitted. This is the same discipline
as `Autoform/Tactics/Portfolio.lean`'s `Obligation`, kept separate so the generated module
carries its own list. -/

/-- One statement the generator emitted without a proof. -/
structure OpenObligation where
  /-- Name of the `Prop`-valued `def` holding the statement. -/
  name    : String
  /-- Which §4 source the candidate came from. -/
  source  : String
  /-- The function the statement is about. -/
  subject : String
  /-- Why no proof was produced. -/
  reason  : String
  deriving Repr, Inhabited

/-- Render an obligation list for the trust ledger. -/
def renderObligations (m : String) (os : List OpenObligation) : String :=
  let rows := os.map (fun o => s!"\n│ {o.name}  [{o.source}]  {o.subject}  — {o.reason}")
  s!"╭─ open obligations ─ {m} ({os.length})" ++ String.join rows ++
    "\n╰──────────────────────────────────────────"

end Autoform.SpecsGen
