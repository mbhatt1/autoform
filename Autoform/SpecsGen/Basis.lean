import Autoform.Refine

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
  applyFunc ctx fuel c.heap fn c.self c.args

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
  | some fn => applyFunc (ctxOf p) fuel h fn (some self) args

theorem runMethod_of_resolve (p : Program) (fuel : Nat) (name : String) (h : Heap)
    (self : Val) (args : List Val) (fn : Func)
    (hres : (ctxOf p).resolve name = some fn) :
    runMethod p fuel h name self args = applyFunc (ctxOf p) fuel h fn (some self) args := by
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
argument list, at every fuel budget of at least three. Stated for an arbitrary `Func`
whose body has the accessor shape, so a generated theorem discharges its hypothesis by
`rfl` against the *generated* definition: change the field name in
`Autoform/Generated/…` and the `rfl` fails. -/
theorem applyFunc_ret_field_self (ctx : Ctx) (n : Nat) (h : Heap) (fn : Func)
    (fld : String) (hb : fn.body = .ret (.field (.name "self") fld))
    (r : Ref) (args : List Val) :
    applyFunc ctx (n + 3) h fn (some (.ref r)) args = (h, .val (fieldOf h r fld)) := by
  unfold applyFunc
  rw [hb]
  simp [execStmt, evalExpr, Env.set, Env.get, fieldOf]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

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
