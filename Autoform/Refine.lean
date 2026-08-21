import Autoform.Lang.Core.Semantics

/-!
# Deep ≈ shallow refinement

`Core` gives us a *deep* embedding: a translated function is a term of type `Func`,
and its meaning is `runFunc` — an interpreter applied to a concrete AST. Proving
anything in that form means unfolding `evalExpr`/`execStmt` at every step, and it does
not survive contact with real code.

This file builds the bridge that STRATEGY.md §0.4 calls "the only thing that scales":
prove **once**, per translated function, that the deep term is observationally
equivalent to a clean Lean function, and thereafter reason about the clean function.

## What refinement means here

`Refines p name N dom spec` says: for every argument list in the declared domain `dom`,
and for **every** fuel budget at least `N`,

    runFunc p N' name args = (spec args).toEResult

where `spec : List Val → Outcome` is a *total* Lean function into

    Outcome := ret Val | raise Val

The design choices that make this non-vacuous are all in that sentence:

* **`Outcome` has no `hole` and no `outOfFuel` constructor.** `Outcome.toEResult` lands
  in `EResult.val` or `EResult.exn` only. So a refinement statement *cannot* be satisfied
  by a program that reaches an untranslated hole, and cannot be satisfied by a program
  that runs out of fuel. `refines_not_hole` and `refines_terminates` below turn this into
  explicit theorems. A "refinement" that admitted `.hole` would be exactly the vacuous
  specification this project exists to detect.
* **Fuel is quantified universally above a witness bound**, not existentially. `∃ fuel`
  would be satisfiable by picking whatever fuel happens to make a partial computation
  look right; `∀ fuel ≥ N` forces the answer to be fuel-stable, which is the semantic
  content of "this function terminates and returns this". The bound `N` is a concrete
  numeral in every theorem below, so the cost is visible rather than hidden.
* **The domain is explicit.** `dom` is a hypothesis of the statement, so a refinement
  that only holds for, say, non-zero divisors has to say so. `dom := fun _ => True` is
  the honest default and is what the demonstrations below use wherever it is true.
* **Exceptions are behaviour, not failure.** `Outcome.raise` is a legitimate refinement
  target: a function that provably raises `ZeroDivisionError` is fully specified. Only
  `hole` (we did not translate it) and `outOfFuel` (we did not run it) are excluded,
  because those are statements about *our ignorance*, not about the program.

## Contents

1. `Outcome`, `Refines`, and the arity/type-specialised wrappers.
2. Non-vacuity theorems: refinement rules out holes, exceptions-as-holes, and divergence.
3. Mechanical evaluation lemmas for every `Expr`/`Stmt` constructor (`evalSimp` set).
4. A genuine fuel-independence theorem for the pure expression fragment, then a
   Hoare-style **loop rule** with a termination measure (`execStmt_loop_rule`,
   `execFor_rule`) and a **heap representation predicate** (`Represents`) with its frame
   and update rules — the two pieces straight-line pure code does not need and real code
   cannot do without.
5. End-to-end refinement theorems for real translated functions from
   `Generated/CMath.lean` (C) and `Generated/Stress.lean`, `Generated/Sample.lean`
   (Python), including the dialect-sensitive division/modulo pair, the two loops
   (`sumto`, `gcdish`), and a class whose method mutates its receiver.
6. Two *negative* results: a function containing a reachable hole provably refines
   nothing (`sample_id_not_refinable`), and a C function provably does **not** refine its
   mathematical model on an unrestricted domain once fixed-width arithmetic is in play
   (`poly_not_refinable`).
-/

namespace Autoform.Refine

open Autoform.Core

/-! ## 1. The refinement relation -/

/-- The observable outcomes a *shallow* specification is allowed to predict.

Deliberately smaller than `EResult`: there is no `hole` and no `outOfFuel`. A shallow
model of a program says what the program *does*; "we failed to translate it" and "we
did not run it long enough" are not things a program does. -/
inductive Outcome where
  /-- The function returned a value. -/
  | ret   : Val → Outcome
  /-- The function raised an exception carrying this payload. -/
  | raise : Val → Outcome
  deriving Repr, Inhabited

/-- Embed a shallow outcome into the interpreter's result type. Note that the image
misses `.hole` and `.outOfFuel` entirely — that is the whole point. -/
def Outcome.toEResult : Outcome → EResult
  | .ret v   => .val v
  | .raise v => .exn v

@[simp] theorem Outcome.toEResult_ret (v : Val) : (Outcome.ret v).toEResult = .val v := rfl
@[simp] theorem Outcome.toEResult_raise (v : Val) : (Outcome.raise v).toEResult = .exn v := rfl

/-- No shallow outcome denotes a hole. -/
theorem Outcome.toEResult_ne_hole (o : Outcome) (l : String) : o.toEResult ≠ .hole l := by
  cases o <;> simp [Outcome.toEResult]

/-- No shallow outcome denotes fuel exhaustion. -/
theorem Outcome.toEResult_ne_outOfFuel (o : Outcome) : o.toEResult ≠ .outOfFuel := by
  cases o <;> simp [Outcome.toEResult]

/-- **The refinement relation.**

`Refines p name N dom spec`: within program `p`, the entry point `name` is observationally
equivalent to the total Lean function `spec` on every argument list satisfying `dom`,
using any fuel budget of at least `N`.

`N` is the *proved* fuel bound: a numeral appearing in the statement, so nobody can hide
non-termination behind an unbounded existential. -/
def Refines (p : Program) (name : String) (N : Nat)
    (dom : List Val → Prop) (spec : List Val → Outcome) : Prop :=
  ∀ args, dom args → ∀ fuel, N ≤ fuel →
    runFunc p fuel name args = (spec args).toEResult

/-- The bound-free form, for when the caller does not care what the fuel bound is.
Every `Refines` implies it; the converse would lose the concrete cost. -/
def RefinesSome (p : Program) (name : String)
    (dom : List Val → Prop) (spec : List Val → Outcome) : Prop :=
  ∃ N, Refines p name N dom spec

theorem Refines.toSome {p name N dom spec} (h : Refines p name N dom spec) :
    RefinesSome p name dom spec := ⟨N, h⟩

/-! ### Non-vacuity

These are theorems, not comments: they are what stops `Refines` from being a statement
about nothing. -/

/-- A refined entry point never reaches an untranslated hole, at any adequate fuel.
So a `Func` containing a *reachable* hole cannot be refined at all. -/
theorem refines_not_hole {p name N dom spec} (h : Refines p name N dom spec)
    (args : List Val) (hd : dom args) (fuel : Nat) (hf : N ≤ fuel) (l : String) :
    runFunc p fuel name args ≠ .hole l := by
  rw [h args hd fuel hf]; exact Outcome.toEResult_ne_hole _ l

/-- A refined entry point terminates within the stated budget: it never reports
`outOfFuel`. This is what makes the fuel bound `N` meaningful rather than decorative. -/
theorem refines_terminates {p name N dom spec} (h : Refines p name N dom spec)
    (args : List Val) (hd : dom args) (fuel : Nat) (hf : N ≤ fuel) :
    runFunc p fuel name args ≠ .outOfFuel := by
  rw [h args hd fuel hf]; exact Outcome.toEResult_ne_outOfFuel _

/-- Refinement is fuel-monotone by construction: raising the budget cannot change the
answer. (With an existential fuel quantifier this would be a hard theorem *and* the
statement would be vacuous without it.) -/
theorem refines_fuel_mono {p name N dom spec} (h : Refines p name N dom spec)
    (args : List Val) (hd : dom args) {f₁ f₂ : Nat} (h₁ : N ≤ f₁) (h₂ : f₁ ≤ f₂) :
    runFunc p f₁ name args = runFunc p f₂ name args := by
  rw [h args hd f₁ h₁, h args hd f₂ (Nat.le_trans h₁ h₂)]

/-- Refinement pins the shallow model uniquely: two shallow specs that both refine the
same entry point agree on the whole domain. -/
theorem refines_unique {p name N₁ N₂ dom s₁ s₂}
    (h₁ : Refines p name N₁ dom s₁) (h₂ : Refines p name N₂ dom s₂)
    (args : List Val) (hd : dom args) : (s₁ args).toEResult = (s₂ args).toEResult := by
  have e₁ := h₁ args hd (N₁ + N₂) (Nat.le_add_right _ _)
  have e₂ := h₂ args hd (N₁ + N₂) (Nat.le_add_left _ _)
  rw [← e₁, ← e₂]

/-! ### From `∀ k, P (k + N)` to `∀ fuel ≥ N, P fuel`

This is the small lemma that makes the whole approach work mechanically. Writing the
fuel as `k + N` with `N` a numeral means `k + 9` is *definitionally* `((k+8)+1)`, so the
interpreter's `n+1` equations fire under an arbitrary `k`. One `simp` then discharges the
obligation for **all** sufficiently large fuel at once, and fuel-monotonicity for the
concrete function comes out as a corollary rather than as a prerequisite. -/
theorem forall_ge_of_forall_add {N : Nat} {P : Nat → Prop} (h : ∀ k, P (k + N)) :
    ∀ fuel, N ≤ fuel → P fuel := by
  intro fuel hf
  obtain ⟨k, rfl⟩ := Nat.le.dest hf
  simpa [Nat.add_comm] using h k

/-! ### Argument / result marshalling

Deep values are `Val`; shallow specs are ordinary Lean functions. These wrappers fix the
marshalling once so that individual theorems read like statements about `Int → Int`. -/

/-- Marshalling into and out of `Val`, with `ofVal` partial: not every `Val` is an `Int`,
and pretending otherwise is how unsound specs get written. -/
class Marshal (α : Type) where
  toVal : α → Val
  ofVal : Val → Option α
  ofVal_toVal : ∀ a, ofVal (toVal a) = some a

instance : Marshal Int where
  toVal := Val.int
  ofVal := fun | .int i => some i | _ => none
  ofVal_toVal := fun _ => rfl

instance : Marshal Bool where
  toVal := Val.bool
  ofVal := fun | .bool b => some b | _ => none
  ofVal_toVal := fun _ => rfl

instance : Marshal String where
  toVal := Val.str
  ofVal := fun | .str s => some s | _ => none
  ofVal_toVal := fun _ => rfl

/-- Unary refinement at marshalled types. -/
def Refines₁ {α β} [Marshal α] [Marshal β] (p : Program) (name : String) (N : Nat)
    (dom : α → Prop) (f : α → β) : Prop :=
  ∀ a, dom a → ∀ fuel, N ≤ fuel →
    runFunc p fuel name [Marshal.toVal a] = .val (Marshal.toVal (f a))

/-- Binary refinement at marshalled types. -/
def Refines₂ {α β γ} [Marshal α] [Marshal β] [Marshal γ] (p : Program) (name : String)
    (N : Nat) (dom : α → β → Prop) (f : α → β → γ) : Prop :=
  ∀ a b, dom a b → ∀ fuel, N ≤ fuel →
    runFunc p fuel name [Marshal.toVal a, Marshal.toVal b] = .val (Marshal.toVal (f a b))

/-- Ternary refinement at marshalled types. -/
def Refines₃ {α β γ δ} [Marshal α] [Marshal β] [Marshal γ] [Marshal δ]
    (p : Program) (name : String) (N : Nat)
    (dom : α → β → γ → Prop) (f : α → β → γ → δ) : Prop :=
  ∀ a b c, dom a b c → ∀ fuel, N ≤ fuel →
    runFunc p fuel name [Marshal.toVal a, Marshal.toVal b, Marshal.toVal c]
      = .val (Marshal.toVal (f a b c))

/-- The typed wrappers really are instances of `Refines`, so the non-vacuity theorems
above apply to them. -/
theorem Refines₂.toRefines {α β γ} [Marshal α] [Marshal β] [Marshal γ]
    {p name N dom f} (h : @Refines₂ α β γ _ _ _ p name N dom f) :
    Refines p name N
      (fun args => ∃ a b, args = [Marshal.toVal a, Marshal.toVal b] ∧ dom a b)
      (fun args => match args with
        | [x, y] => match (Marshal.ofVal x : Option α), (Marshal.ofVal y : Option β) with
                    | some a, some b => .ret (Marshal.toVal (f a b))
                    | _, _ => .ret .unit
        | _ => .ret .unit) := by
  rintro args ⟨a, b, rfl, hd⟩ fuel hf
  simp [Marshal.ofVal_toVal, h a b hd fuel hf]

/-! ## 2. Mechanical evaluation lemmas

Every constructor of `Expr` and `Stmt` gets an equation at fuel `k+1`. They are all
`rfl`, but having them named and in a dedicated simp set means a refinement obligation
is discharged by rewriting with named lemmas rather than by unfolding the interpreter by
hand. They are deliberately *not* `@[simp]`: this module is imported by `Autoform`, and
interpreter equations in the global simp set would fire everywhere. -/

section EvalLemmas
variable (ctx : Ctx) (k : Nat) (h : Heap) (ρ : Env)

theorem evalExpr_zero (e : Expr) :
    evalExpr ctx 0 h ρ e = (h, .outOfFuel) := rfl
theorem evalExpr_lit_int (i : Int) :
    evalExpr ctx (k+1) h ρ (.lit (.int i)) = (h, .val (.int i)) := rfl
theorem evalExpr_lit_str (s : String) :
    evalExpr ctx (k+1) h ρ (.lit (.str s)) = (h, .val (.str s)) := rfl
theorem evalExpr_lit_bool (b : Bool) :
    evalExpr ctx (k+1) h ρ (.lit (.bool b)) = (h, .val (.bool b)) := rfl
theorem evalExpr_lit_unit :
    evalExpr ctx (k+1) h ρ (.lit .unit) = (h, .val .unit) := rfl
/-- A name bound locally evaluates to its binding. Unbound names now fall back to the
function table (a module-level function used as a value), so this lemma is conditional on
the name actually being local — see `evalExpr_name_free` for the other case. -/
theorem evalExpr_name (x : String) {v : Val} (hx : ρ.find? (·.1 == x) = some (x, v)) :
    evalExpr ctx (k+1) h ρ (.name x) = (h, .val v) := by
  simp [evalExpr, hx]

/-- A name that is neither local nor a known function evaluates to `unit`. -/
theorem evalExpr_name_free (x : String)
    (hx : ρ.find? (·.1 == x) = none) (hf : ctx.resolve x = none)
    (hg : h.get ctx.globals = none) :
    evalExpr ctx (k+1) h ρ (.name x) = (h, .val .unit) := by
  simp [evalExpr, hx, hf, hg]
theorem evalExpr_fnref (f : String) :
    evalExpr ctx (k+1) h ρ (.fnref f) = (h, .val (.fn f)) := rfl
theorem evalExpr_hole (l : String) :
    evalExpr ctx (k+1) h ρ (.hole l) = (h, .hole l) := rfl

/-- Value-passing form for `unop`: the shape actually used when discharging obligations. -/
theorem evalExpr_unop_val {a : Expr} {h₁ : Heap} {v : Val} (op : String)
    (ha : evalExpr ctx k h ρ a = (h₁, .val v)) :
    evalExpr ctx (k+1) h ρ (.unop op a) = (h₁, applyUnop ctx.dialect op v) := by
  simp [evalExpr, ha]

/-- Value-passing form for `binop` at a **strict** operator. Note the heap threads
left-to-right; this lemma is where that evaluation order is pinned.

The strictness side conditions are not bureaucracy: `&&` and `||` short-circuit, so for
those two operators the right operand may never be evaluated at all and this equation is
false. See `evalExpr_and_short` / `evalExpr_or_short`. -/
theorem evalExpr_binop_val {a b : Expr} {h₁ h₂ : Heap} {x y : Val} (op : String)
    (hand : op ≠ "&&") (hor : op ≠ "||")
    (ha : evalExpr ctx k h ρ a = (h₁, .val x))
    (hb : evalExpr ctx k h₁ ρ b = (h₂, .val y)) :
    evalExpr ctx (k+1) h ρ (.binop op a b) = (h₂, applyBinop ctx.dialect op x y) := by
  simp [evalExpr, ha, hb, hand, hor]

/-- `&&` does not evaluate its right operand once the left is falsy, and yields the
**left operand itself** under Python value semantics (`0 and 5` is `0`, not `False`).
Only C-like dialects collapse it to a boolean. -/
theorem evalExpr_and_short {a b : Expr} {h₁ : Heap} {x : Val}
    (ha : evalExpr ctx k h ρ a = (h₁, .val x)) (hx : x.truthy = false) :
    evalExpr ctx (k+1) h ρ (.binop "&&" a b)
      = (h₁, .val (if ctx.dialect.boolOpsAreValues then x else .bool false)) := by
  cases hd : ctx.dialect <;> simp [evalExpr, ha, hx, hd, Dialect.boolOpsAreValues]

/-- `||` does not evaluate its right operand once the left is truthy, and yields the
**left operand itself** under Python value semantics (`5 or 0` is `5`, not `True`). -/
theorem evalExpr_or_short {a b : Expr} {h₁ : Heap} {x : Val}
    (ha : evalExpr ctx k h ρ a = (h₁, .val x)) (hx : x.truthy = true) :
    evalExpr ctx (k+1) h ρ (.binop "||" a b)
      = (h₁, .val (if ctx.dialect.boolOpsAreValues then x else .bool true)) := by
  cases hd : ctx.dialect <;> simp [evalExpr, ha, hx, hd, Dialect.boolOpsAreValues]

/-- A non-value in the left operand short-circuits and is propagated unchanged. This is
what stops a hole in one operand from being silently absorbed. -/
theorem evalExpr_binop_stuck {a b : Expr} {h₁ : Heap} {r : EResult} (op : String)
    (ha : evalExpr ctx k h ρ a = (h₁, r)) (hr : ∀ v, r ≠ .val v) :
    evalExpr ctx (k+1) h ρ (.binop op a b) = (h₁, r) := by
  cases r <;> simp [evalExpr, ha] <;> exact absurd rfl (hr _)

theorem evalExpr_cond_true {c t e : Expr} {h₁ : Heap} {v : Val}
    (hc : evalExpr ctx k h ρ c = (h₁, .val v)) (hv : v.truthy = true) :
    evalExpr ctx (k+1) h ρ (.cond c t e) = evalExpr ctx k h₁ ρ t := by
  simp [evalExpr, hc, hv]

theorem evalExpr_cond_false {c t e : Expr} {h₁ : Heap} {v : Val}
    (hc : evalExpr ctx k h ρ c = (h₁, .val v)) (hv : v.truthy = false) :
    evalExpr ctx (k+1) h ρ (.cond c t e) = evalExpr ctx k h₁ ρ e := by
  simp [evalExpr, hc, hv]

theorem evalList_nil :
    evalList ctx (k+1) h ρ [] = (h, .inr ([], [])) := rfl

/-- One ordinary (non-starred) argument. `plainArg` is the side condition that makes this
true: `*e`, `k = e` and `**e` are dispatched on syntactically by `evalList`, so they do
*not* contribute one value each and this equation would be false for them. Every use site
supplies a concrete argument, so the condition is discharged by `rfl`. -/
theorem evalList_cons_val {a : Expr} {as : List Expr} {h₁ h₂ : Heap} {v : Val}
    {vs : List Val} {kws : List (String × Val)}
    (hp : a.plainArg = true)
    (ha : evalExpr ctx k h ρ a = (h₁, .val v))
    (has : evalList ctx k h₁ ρ as = (h₂, .inr (vs, kws))) :
    evalList ctx (k+1) h ρ (a :: as) = (h₂, .inr (v :: vs, kws)) := by
  cases a <;> simp_all [evalList, Expr.plainArg]

theorem execStmt_zero (s : Stmt) :
    execStmt ctx 0 h ρ s = (h, .outOfFuel) := rfl
theorem execStmt_skip :
    execStmt ctx (k+1) h ρ .skip = (h, .normal ρ) := rfl
theorem execStmt_brk :
    execStmt ctx (k+1) h ρ .brk = (h, .brk ρ) := rfl
theorem execStmt_cont :
    execStmt ctx (k+1) h ρ .cont = (h, .cont ρ) := rfl
theorem execStmt_hole (l : String) :
    execStmt ctx (k+1) h ρ (.hole l) = (h, .hole l) := rfl
theorem execStmt_del (x : String) :
    execStmt ctx (k+1) h ρ (.del x) = (h, .normal (ρ.del x)) := rfl

theorem execStmt_ret_val {e : Expr} {h₁ : Heap} {v : Val}
    (he : evalExpr ctx k h ρ e = (h₁, .val v)) :
    execStmt ctx (k+1) h ρ (.ret e) = (h₁, .ret v) := by simp [execStmt, he]

/-- Assignment binds locally, provided `x` was not declared `global` in this scope.
The hypothesis is not decoration: `declGlobal` installs a marker that redirects the write
to the module frame, and a lemma that ignored it would be unsound for such functions. -/
theorem execStmt_assign_val {x : String} {e : Expr} {h₁ : Heap} {v : Val}
    (he : evalExpr ctx k h ρ e = (h₁, .val v))
    (hg : (ρ.get ("<glob>" ++ x)).truthy = false) :
    execStmt ctx (k+1) h ρ (.assign x e) = (h₁, .normal (ρ.set x v)) := by
  simp [execStmt, he, hg]

theorem execStmt_expr_val {e : Expr} {h₁ : Heap} {v : Val}
    (he : evalExpr ctx k h ρ e = (h₁, .val v)) :
    execStmt ctx (k+1) h ρ (.expr e) = (h₁, .normal ρ) := by simp [execStmt, he]

theorem execStmt_raise_val {e : Expr} {h₁ : Heap} {v : Val}
    (he : evalExpr ctx k h ρ e = (h₁, .val v)) :
    execStmt ctx (k+1) h ρ (.raise e) = (h₁, .exn v) := by simp [execStmt, he]

theorem execStmt_seq_normal {a b : Stmt} {h₁ : Heap} {ρ' : Env}
    (ha : execStmt ctx k h ρ a = (h₁, .normal ρ')) :
    execStmt ctx (k+1) h ρ (.seq a b) = execStmt ctx k h₁ ρ' b := by simp [execStmt, ha]

theorem execStmt_seq_ret {a b : Stmt} {h₁ : Heap} {v : Val}
    (ha : execStmt ctx k h ρ a = (h₁, .ret v)) :
    execStmt ctx (k+1) h ρ (.seq a b) = (h₁, .ret v) := by simp [execStmt, ha]

theorem execStmt_ifte_true {c : Expr} {t e : Stmt} {h₁ : Heap} {v : Val}
    (hc : evalExpr ctx k h ρ c = (h₁, .val v)) (hv : v.truthy = true) :
    execStmt ctx (k+1) h ρ (.ifte c t e) = execStmt ctx k h₁ ρ t := by
  simp [execStmt, hc, hv]

theorem execStmt_ifte_false {c : Expr} {t e : Stmt} {h₁ : Heap} {v : Val}
    (hc : evalExpr ctx k h ρ c = (h₁, .val v)) (hv : v.truthy = false) :
    execStmt ctx (k+1) h ρ (.ifte c t e) = execStmt ctx k h₁ ρ e := by
  simp [execStmt, hc, hv]

theorem execStmt_tryCatch_exn {b : Stmt} {x : String} {hd : Stmt} {h₁ : Heap} {v : Val}
    (hb : execStmt ctx k h ρ b = (h₁, .exn v)) :
    execStmt ctx (k+1) h ρ (.tryCatch b x hd) = execStmt ctx k h₁ (ρ.set x v) hd := by
  simp [execStmt, hb]

theorem execStmt_loop_false {c : Expr} {body : Stmt} {h₁ : Heap} {v : Val}
    (hc : evalExpr ctx k h ρ c = (h₁, .val v)) (hv : v.truthy = false) :
    execStmt ctx (k+1) h ρ (.loop c body) = (h₁, .normal ρ) := by
  simp [execStmt, hc, hv]

/-- One turn of the loop, when the body finishes normally. Unrolling a loop by hand is
exactly this lemma applied `n` times. -/
theorem execStmt_loop_step {c : Expr} {body : Stmt} {h₁ h₂ : Heap} {v : Val} {ρ' : Env}
    (hc : evalExpr ctx k h ρ c = (h₁, .val v)) (hv : v.truthy = true)
    (hb : execStmt ctx k h₁ ρ body = (h₂, .normal ρ')) :
    execStmt ctx (k+1) h ρ (.loop c body) = execStmt ctx k h₂ ρ' (.loop c body) := by
  simp [execStmt, hc, hv, hb]

theorem execFor_nil (x : String) (body : Stmt) :
    execFor ctx (k+1) h ρ x [] body = (h, .normal ρ) := rfl

/-- `applyFunc` at successor fuel: bind parameters, run the body, and map the control
outcome back into a result. Stray `break`/`continue` escaping a function body becomes a
hole, not a silent success. -/
theorem applyFunc_succ (fn : Func) (self? : Option Val) (vs : List Val)
    (kws : List (String × Val)) :
    applyFunc ctx (k+1) h fn self? vs kws =
      (let base : Env := match self? with | some s => [("self", s)] | none => []
       let ρ' := bindParams fn base vs kws
       if kwargsRejected fn kws || posRejected fn vs then (h, .exn (.str "TypeError")) else
       match execStmt ctx k h ρ' fn.body with
       | (h₁, .ret v)     => (h₁, .val v)
       | (h₁, .normal _)  => (h₁, .val .unit)
       | (h₁, .exn v)     => (h₁, .exn v)
       | (h₁, .hole l)    => (h₁, .hole l)
       | (h₁, .outOfFuel) => (h₁, .outOfFuel)
       | (h₁, _)          => (h₁, .hole "call:stray-control-flow")) := rfl

end EvalLemmas

/-! ### Operator equations for comparison and unary operators

`Semantics.lean` supplies the arithmetic equations (unconditional for Python, conditional
on 32-bit representability for C). Comparisons and unary minus are dialect-independent
and are not routed through `NumConfig`, so their equations live here. All are `rfl`;
having them named means a refinement proof never has to unfold `applyBinop` itself —
unfolding past the conditional C equations is what silently discards the overflow side
condition. -/

theorem applyBinop_int_eq (d : Dialect) (x y : Int) :
    applyBinop d "==" (.int x) (.int y) = .val (.bool (x == y)) := rfl
theorem applyBinop_int_ne (d : Dialect) (x y : Int) :
    applyBinop d "!=" (.int x) (.int y) = .val (.bool (!(x == y))) := rfl
theorem applyBinop_int_lt (d : Dialect) (x y : Int) :
    applyBinop d "<" (.int x) (.int y) = .val (.bool (decide (x < y))) := rfl
theorem applyBinop_int_gt (d : Dialect) (x y : Int) :
    applyBinop d ">" (.int x) (.int y) = .val (.bool (decide (y < x))) := rfl
theorem applyBinop_int_le (d : Dialect) (x y : Int) :
    applyBinop d "<=" (.int x) (.int y) = .val (.bool (decide (x ≤ y))) := rfl
theorem applyBinop_int_ge (d : Dialect) (x y : Int) :
    applyBinop d ">=" (.int x) (.int y) = .val (.bool (decide (y ≤ x))) := rfl

/-- Unary minus under the unbounded (Python) dialect. Open obligation 6 — `applyUnop`
bypassing `NumConfig`, so that `-INT_MIN` yielded the unrepresentable `2^31` — is now
**closed**: negation routes through `NumConfig.neg`, and the C-side equation
`applyUnop_c_neg` carries a `Fits32` hypothesis exactly as the binary operators do. -/
theorem applyUnop_int_neg (x : Int) :
    applyUnop .python "-" (.int x) = .val (.int (-x)) := rfl

/-- The context `runFunc` builds internally. Exposed so that resolution facts can be
stated and proved once per program. -/
def ctxOf (p : Program) : Ctx :=
  { dialect := p.dialect, table := p.table, builtinBases := p.builtinBases }

/-- Entry-point resolution, factored out. Every demonstration below discharges its
`resolve` side condition by `rfl` — name resolution on a concrete program is decidable
by computation, so it never becomes a proof obligation. -/
theorem runFunc_of_resolve (p : Program) (fuel : Nat) (name : String) (args : List Val)
    (fn : Func) (hres : (ctxOf p).resolve name = some fn) :
    runFunc p fuel name args = (applyFunc (ctxOf p) fuel [] fn none args []).2 := by
  unfold runFunc
  simp only [ctxOf] at hres ⊢
  rw [hres]

/-- Resolution failure is a hole, and a hole is not a refinement — so an entry point that
does not resolve provably refines nothing. -/
theorem runFunc_unresolved (p : Program) (fuel : Nat) (name : String) (args : List Val)
    (hres : (ctxOf p).resolve name = none) :
    runFunc p fuel name args = .hole s!"entry:{name}" := by
  unfold runFunc
  simp only [ctxOf] at hres ⊢
  rw [hres]

/-! ## 3. Fuel independence for the pure expression fragment

The `∀ k, P (k + N)` trick above gives fuel-stability *per concrete function*. This
section gives it *once and for all* for a syntactic fragment: expressions built from
literals, variables, function references, unary and binary operators, and conditional
expressions. For those, evaluation is a function of the environment alone as soon as the
fuel exceeds the expression's depth — no heap effects, no calls, no divergence.

This is the general fuel-monotonicity result. It is stated for the fragment rather than
for all expressions because for the full language it is simply false as an unconditional
equation (a call can diverge), and the honest conditional version is listed as an open
obligation at the end of this file. -/

/-- The expression fragment that is pure and call-free. -/
inductive PureE : Expr → Prop where
  | lit   (l : Lit)      : PureE (.lit l)
  | name  (x : String)   : PureE (.name x)
  | fnref (f : String)   : PureE (.fnref f)
  | unop  {a} (op : String) : PureE a → PureE (.unop op a)
  | binop {a b} (op : String) : PureE a → PureE b → PureE (.binop op a b)
  | cond  {c t e} : PureE c → PureE t → PureE e → PureE (.cond c t e)

/-- Evaluation depth: the fuel needed to evaluate a pure expression. -/
def edepth : Expr → Nat
  | .unop _ a    => 1 + edepth a
  | .binop _ a b => 1 + max (edepth a) (edepth b)
  | .cond c t e  => 1 + max (edepth c) (max (edepth t) (edepth e))
  | _            => 1

theorem edepth_pos (e : Expr) : 1 ≤ edepth e := by
  cases e <;> simp [edepth] <;> omega

/-- **Fuel independence.** On the pure fragment, any two fuel budgets that both cover the
expression's depth give the *same* heap and the *same* result. Monotonicity is the
immediate corollary, and with it the fact that a `Refines` bound `N` can be taken to be
any adequate number. -/
theorem evalExpr_pure_fuel_indep (ctx : Ctx) :
    ∀ {e : Expr}, PureE e → ∀ {k₁ k₂ : Nat} {h : Heap} {ρ : Env},
      edepth e ≤ k₁ → edepth e ≤ k₂ →
      evalExpr ctx k₁ h ρ e = evalExpr ctx k₂ h ρ e := by
  intro e pe
  induction pe with
  | lit l =>
      intro k₁ k₂ h ρ h₁ h₂
      obtain ⟨m₁, rfl⟩ : ∃ m, k₁ = m + 1 := ⟨k₁ - 1, by simp [edepth] at h₁; omega⟩
      obtain ⟨m₂, rfl⟩ : ∃ m, k₂ = m + 1 := ⟨k₂ - 1, by simp [edepth] at h₂; omega⟩
      cases l <;> rfl
  | name x =>
      intro k₁ k₂ h ρ h₁ h₂
      obtain ⟨m₁, rfl⟩ : ∃ m, k₁ = m + 1 := ⟨k₁ - 1, by simp [edepth] at h₁; omega⟩
      obtain ⟨m₂, rfl⟩ : ∃ m, k₂ = m + 1 := ⟨k₂ - 1, by simp [edepth] at h₂; omega⟩
      rfl
  | fnref f =>
      intro k₁ k₂ h ρ h₁ h₂
      obtain ⟨m₁, rfl⟩ : ∃ m, k₁ = m + 1 := ⟨k₁ - 1, by simp [edepth] at h₁; omega⟩
      obtain ⟨m₂, rfl⟩ : ∃ m, k₂ = m + 1 := ⟨k₂ - 1, by simp [edepth] at h₂; omega⟩
      rfl
  | unop op _ ih =>
      intro k₁ k₂ h ρ h₁ h₂
      simp only [edepth] at h₁ h₂
      obtain ⟨m₁, rfl⟩ : ∃ m, k₁ = m + 1 := ⟨k₁ - 1, by omega⟩
      obtain ⟨m₂, rfl⟩ : ∃ m, k₂ = m + 1 := ⟨k₂ - 1, by omega⟩
      simp only [evalExpr, ih (k₁ := m₁) (k₂ := m₂) (h := h) (ρ := ρ) (by omega) (by omega)]
  | binop op _ _ iha ihb =>
      intro k₁ k₂ h ρ h₁ h₂
      simp only [edepth] at h₁ h₂
      obtain ⟨m₁, rfl⟩ : ∃ m, k₁ = m + 1 := ⟨k₁ - 1, by omega⟩
      obtain ⟨m₂, rfl⟩ : ∃ m, k₂ = m + 1 := ⟨k₂ - 1, by omega⟩
      simp only [evalExpr, iha (h := h) (ρ := ρ) (k₁ := m₁) (k₂ := m₂) (by omega) (by omega)]
      rcases hA : evalExpr ctx m₂ h ρ _ with ⟨hA', rA⟩
      cases rA <;>
        simp only [ihb (h := hA') (ρ := ρ) (k₁ := m₁) (k₂ := m₂) (by omega) (by omega)]
  | cond _ _ _ ihc iht ihe =>
      intro k₁ k₂ h ρ h₁ h₂
      simp only [edepth] at h₁ h₂
      obtain ⟨m₁, rfl⟩ : ∃ m, k₁ = m + 1 := ⟨k₁ - 1, by omega⟩
      obtain ⟨m₂, rfl⟩ : ∃ m, k₂ = m + 1 := ⟨k₂ - 1, by omega⟩
      simp only [evalExpr, ihc (h := h) (ρ := ρ) (k₁ := m₁) (k₂ := m₂) (by omega) (by omega)]
      rcases hC : evalExpr ctx m₂ h ρ _ with ⟨hC', rC⟩
      cases rC <;>
        simp only [iht (h := hC') (ρ := ρ) (k₁ := m₁) (k₂ := m₂) (by omega) (by omega),
                   ihe (h := hC') (ρ := ρ) (k₁ := m₁) (k₂ := m₂) (by omega) (by omega)]

/-- Monotonicity on the pure fragment, the form usually wanted. -/
theorem evalExpr_pure_fuel_mono (ctx : Ctx) {e : Expr} (pe : PureE e) {k₁ k₂ : Nat}
    {h : Heap} {ρ : Env} (h₁ : edepth e ≤ k₁) (h₁₂ : k₁ ≤ k₂) :
    evalExpr ctx k₂ h ρ e = evalExpr ctx k₁ h ρ e :=
  evalExpr_pure_fuel_indep ctx pe (Nat.le_trans h₁ h₁₂) h₁

/-- Pure expressions do not touch the heap. Together with fuel independence this is what
licenses reasoning about a pure translated function as an ordinary Lean function of its
arguments. -/
theorem evalExpr_pure_heap_inert (ctx : Ctx) :
    ∀ {e : Expr}, PureE e → ∀ {k : Nat} {h : Heap} {ρ : Env},
      (evalExpr ctx k h ρ e).1 = h := by
  intro e pe
  induction pe with
  | lit l => intro k h ρ; cases k with | zero => rfl | succ m => cases l <;> rfl
  | name x =>
      intro k h ρ
      cases k with
      | zero => rfl
      | succ m =>
          -- The name case now branches on local lookup then on table resolution; the
          -- heap is returned unchanged on every branch.
          simp only [evalExpr]
          repeat' (first | rfl | split)
  | fnref f => intro k h ρ; cases k <;> rfl
  | unop op _ ih =>
      intro k h ρ; cases k with
      | zero => rfl
      | succ m =>
        have ha := ih (k := m) (h := h) (ρ := ρ)
        rcases hA : evalExpr ctx m h ρ _ with ⟨hA', rA⟩
        rw [hA] at ha; simp only at ha; subst ha
        simp only [evalExpr, hA]
        cases rA <;> rfl
  | binop op _ _ iha ihb =>
      intro k h ρ; cases k with
      | zero => rfl
      | succ m =>
        have ha := iha (k := m) (h := h) (ρ := ρ)
        rcases hA : evalExpr ctx m h ρ _ with ⟨hA', rA⟩
        rw [hA] at ha; simp only at ha; subst ha
        cases rA with
        | val x =>
          have hb := ihb (k := m) (h := hA') (ρ := ρ)
          rcases hB : evalExpr ctx m hA' ρ _ with ⟨hB', rB⟩
          rw [hB] at hb; simp only at hb; subst hb
          simp only [evalExpr, hA, hB]
          -- three cases: the two short-circuit exits (heap untouched by construction)
          -- and the strict path (heap untouched by both induction hypotheses).
          by_cases hs1 : (op == "&&" && !x.truthy) = true
          · simp [hs1]
          · by_cases hs2 : (op == "||" && x.truthy) = true
            · simp [hs1, hs2]
            · simp only [hs1, hs2, Bool.false_eq_true, if_false]
              cases rB <;> rfl
        | _ => simp only [evalExpr, hA]
  | cond _ _ _ ihc iht ihe =>
      intro k h ρ; cases k with
      | zero => rfl
      | succ m =>
        have hc := ihc (k := m) (h := h) (ρ := ρ)
        rcases hC : evalExpr ctx m h ρ _ with ⟨hC', rC⟩
        rw [hC] at hc; simp only at hc; subst hc
        simp only [evalExpr, hC]
        cases rC with
        | val v =>
          by_cases hv : v.truthy
          · simpa [hv] using iht (k := m) (h := hC') (ρ := ρ)
          · simp only [hv, Bool.false_eq_true, if_false]
            exact ihe (k := m) (h := hC') (ρ := ρ)
        | _ => rfl

/-! ## 3b. A loop rule, and a heap representation predicate

Sections 1–3 handle straight-line pure code. Everything a real library does — iteration
and mutable objects — needs two more pieces, and they are the two open obligations this
section closes.

### The loop rule

`execStmt_loop_step` unrolls a loop *once*. Unrolling `n` times by hand only works when
`n` is a numeral, which is exactly the case that does not matter. What is needed is the
Hoare while-rule, adapted to a fuel-indexed interpreter, which means it must carry two
things a textbook while-rule does not:

* a **termination measure**, because the interpreter is total and a loop that does not
  provably terminate simply reports `outOfFuel` — and `Outcome` cannot denote that; and
* a **fuel bound derived from the measure**, because the conclusion is an equation about
  a concrete fuel budget, not about a partial-correctness judgement.

Both are folded into one index: the invariant `I : Nat → Heap → Env → Prop` is indexed by
a `Nat` that must **strictly decrease** at every iteration. The rule then says a loop
started in `I m` needs `B + m + 1` fuel and stops in the postcondition `Q`. Note what
`m = 0` forces: the step obligation would have to produce `m' < 0`, so an invariant at
index `0` can only exit. Partial correctness and termination are proved together, which
is the honest packaging — a "loop refinement" that did not prove termination would be
satisfiable by a program that hangs.
-/

/-- **The while-rule.** `I` is the loop invariant indexed by a decreasing measure, `Q`
the postcondition, `B` the per-iteration fuel cost.

The single step obligation covers both the test and the body: evaluating the test must
yield a value (never a hole, never `outOfFuel`); if it is truthy the body must complete
normally and re-establish the invariant at a *strictly smaller* index; if it is falsy the
postcondition must hold. -/
theorem execStmt_loop_rule (ctx : Ctx) (c : Expr) (body : Stmt) (B : Nat)
    (I : Nat → Heap → Env → Prop) (Q : Heap → Env → Prop)
    (hstep : ∀ m h ρ k, B ≤ k → I m h ρ →
      ∃ h₁ v, evalExpr ctx k h ρ c = (h₁, .val v) ∧
        (v.truthy = true →
          ∃ m' h₂ ρ', m' < m ∧ execStmt ctx k h₁ ρ body = (h₂, .normal ρ') ∧ I m' h₂ ρ') ∧
        (v.truthy = false → Q h₁ ρ)) :
    ∀ k m h ρ, I m h ρ → B + m + 1 ≤ k →
      ∃ h' ρ', execStmt ctx k h ρ (.loop c body) = (h', .normal ρ') ∧ Q h' ρ' := by
  intro k
  induction k with
  | zero => intro m h ρ _ hk; omega
  | succ k ih =>
    intro m h ρ hI hk
    obtain ⟨h₁, v, hc, htrue, hfalse⟩ := hstep m h ρ k (by omega) hI
    cases hv : v.truthy with
    | false =>
      refine ⟨h₁, ρ, ?_, hfalse hv⟩
      simp [execStmt, hc, hv]
    | true =>
      obtain ⟨m', h₂, ρ', hm', hb, hI'⟩ := htrue hv
      have hstep' : execStmt ctx (k+1) h ρ (.loop c body) = execStmt ctx k h₂ ρ' (.loop c body) := by
        simp [execStmt, hc, hv, hb]
      rw [hstep']
      exact ih m' h₂ ρ' hI' (by omega)

/-- The same rule for `for`-loops. Here the measure is not invented: it is the length of
the remaining sequence, which the interpreter itself consumes. -/
theorem execFor_rule (ctx : Ctx) (x : String) (body : Stmt) (B : Nat)
    (I : List Val → Heap → Env → Prop)
    (hstep : ∀ v vs h ρ k, B ≤ k → I (v :: vs) h ρ →
      ∃ h' ρ', execStmt ctx k h (ρ.set x v) body = (h', .normal ρ') ∧ I vs h' ρ') :
    ∀ k vs h ρ, I vs h ρ → B + vs.length + 1 ≤ k →
      ∃ h' ρ', execFor ctx k h ρ x vs body = (h', .normal ρ') ∧ I [] h' ρ' := by
  intro k
  induction k with
  | zero => intro vs h ρ _ hk; omega
  | succ k ih =>
    intro vs h ρ hI hk
    cases vs with
    | nil => exact ⟨h, ρ, rfl, hI⟩
    | cons v vs =>
      obtain ⟨h', ρ', hb, hI'⟩ := hstep v vs h ρ k (by simp at hk; omega) hI
      have hstep' : execFor ctx (k+1) h ρ x (v :: vs) body = execFor ctx k h' ρ' x vs body := by
        simp [execFor, hb]
      rw [hstep']
      exact ih vs h' ρ' hI' (by simp at hk ⊢; omega)

/-! ### Heap representation

`evalExpr_pure_heap_inert` says the pure fragment does not touch the heap. That is the
easy half. The other half — what it means for a *heap object* to stand for an abstract
Lean value, and what survives a field write — is what a method that mutates its receiver
needs, and it is the second obligation this section closes.

A `HeapRep α` is an abstraction function from a heap object to an `α`, tagged with the
class the object must belong to. `Represents R h r a` then says "at address `r` the heap
holds an object of class `R.cls` whose abstraction is `a`". Two lemmas make it usable,
and they are the two halves of the separation-logic story in their simplest concrete
form:

* `Represents.frame` — a write to a *different* address preserves the representation.
  This is what makes mutation local; without it every method call would invalidate every
  fact about every object.
* `Represents.update` — a write to *this* address re-establishes the representation at
  the new abstract value.

`Heap.get_setField` is the single computational fact both rest on, and it is proved once
against the real `Heap.setField` (a `List.mapIdx`) rather than assumed.
-/

/-- How a heap object is read as an abstract Lean value. `abs` is partial on purpose: an
object whose fields are missing or ill-typed represents *nothing*, and a representation
predicate that quietly defaulted such an object to some value would be the same class of
vacuity `Outcome` was designed to exclude. -/
structure HeapRep (α : Type) where
  /-- The class name an object must carry to be read at this type. -/
  cls : String
  /-- The abstraction function, partial. -/
  abs : Obj → Option α

/-- `Represents R h r a`: the heap `h` holds, at address `r`, an object of class `R.cls`
which abstracts to the Lean value `a`. -/
def Represents {α : Type} (R : HeapRep α) (h : Heap) (r : Ref) (a : α) : Prop :=
  ∃ o, h.get r = some o ∧ o.cls = R.cls ∧ R.abs o = some a

/-- What a field write does to the heap, at every address at once. Everything below is a
corollary of this one equation. -/
theorem Heap.get_setField {h : Heap} {r s : Ref} {f : String} {v : Val} :
    (h.setField r f v).get s
      = (h.get s).map (fun o => if s == r then { o with fields := (f, v) :: o.fields } else o) := by
  simp [Heap.setField, Heap.get, List.getElem?_mapIdx]

/-- **Frame rule.** Mutating one object leaves the representation of every other object
intact. -/
theorem Represents.frame {α : Type} {R : HeapRep α} {h : Heap} {r : Ref} {a : α}
    {s : Ref} {f : String} {v : Val} (hs : s ≠ r) (hR : Represents R h r a) :
    Represents R (h.setField s f v) r a := by
  obtain ⟨o, ho, hc, ha⟩ := hR
  refine ⟨o, ?_, hc, ha⟩
  simp only [Heap.get_setField, ho, Option.map_some]
  simp [Ne.symm hs]

/-- **Update rule.** A write to the represented object re-establishes the representation
at whatever the new fields abstract to. -/
theorem Represents.update {α : Type} {R : HeapRep α} {h : Heap} {r : Ref} {a a' : α}
    {f : String} {v : Val} {o : Obj}
    (hR : Represents R h r a) (ho : h.get r = some o)
    (ha : R.abs { o with fields := (f, v) :: o.fields } = some a') :
    Represents R (h.setField r f v) r a' := by
  obtain ⟨o', ho', hc, _⟩ := hR
  rw [ho] at ho'; cases ho'
  refine ⟨{ o with fields := (f, v) :: o.fields }, ?_, hc, ha⟩
  simp [Heap.get_setField, ho]

/-! ### Evaluation lemmas for the object fragment

The `evalSimp` set of §2 stops at the pure fragment. Field access, field assignment,
method dispatch, object construction and `for`-iteration each get one equation here, in
the same value-passing style, so that a proof about a method never has to unfold the
interpreter by hand. Each carries the side conditions the interpreter actually checks —
notably `o.captured = []`, because a class captured from an enclosing scope dispatches
through `applyClosure`, not `applyFunc`, and a lemma that ignored that would be unsound
for exactly the code the closure work was added to support. -/

theorem evalExpr_field_obj (ctx : Ctx) (k : Nat) (h : Heap) (ρ : Env)
    {a : Expr} {h₁ : Heap} {r : Ref} {o : Obj} {f : String} {v : Val}
    (ha : evalExpr ctx k h ρ a = (h₁, .val (.ref r)))
    (ho : h₁.get r = some o)
    (hf : o.fields.find? (·.1 == f) = some (f, v)) :
    evalExpr ctx (k+1) h ρ (.field a f) = (h₁, .val v) := by
  simp [evalExpr, ha, ho, hf]

theorem execStmt_setField_val (ctx : Ctx) (k : Nat) (h : Heap) (ρ : Env)
    {a e : Expr} {h₁ h₂ : Heap} {r : Ref} {f : String} {w : Val}
    (ha : evalExpr ctx k h ρ a = (h₁, .val (.ref r)))
    (he : evalExpr ctx k h₁ ρ e = (h₂, .val w)) :
    execStmt ctx (k+1) h ρ (.setField a f e) = (h₂.setField r f w, .normal ρ) := by
  simp [execStmt, ha, he]

theorem evalExpr_mcall_obj (ctx : Ctx) (k : Nat) (h : Heap) (ρ : Env)
    {recv : Expr} {h₁ h₂ : Heap} {r : Ref} {o : Obj} {fn : Func}
    {m : String} {args : List Expr} {vs : List Val} {kws : List (String × Val)}
    (hr : evalExpr ctx k h ρ recv = (h₁, .val (.ref r)))
    (has : evalList ctx k h₁ ρ args = (h₂, .inr (vs, kws)))
    (ho : h₂.get r = some o)
    (hcap : o.captured = [])
    (hm : ctx.resolveMethod o.cls m = some fn) :
    evalExpr ctx (k+1) h ρ (.mcall recv m args)
      = applyFunc ctx k h₂ fn (some (.ref r)) vs kws := by
  simp [evalExpr, hr, has, ho, hm, hcap]

theorem evalExpr_alloc_obj (ctx : Ctx) (k : Nat) (h : Heap) (ρ : Env)
    {cls : String} {args : List Expr} {h₁ h₃ : Heap} {vs : List Val}
    {kws : List (String × Val)} {fn : Func} {w : Val}
    (has : evalList ctx k h ρ args = (h₁, .inr (vs, kws)))
    (hcap : (∀ c cap, ρ.get cls ≠ .clsClos c cap))
    -- `cls` is an ordinary class, not one with a builtin base: those allocate a
    -- `Val.bobj` and never reach `__init__` (see `Semantics.allocBuiltin`).
    (hbb : ctx.builtinBase cls = none)
    (hm : ctx.resolveMethod cls "__init__" = some fn)
    (hinit : applyFunc ctx k (h₁ ++ [{ cls := cls, fields := [], captured := [] }]) fn
        (some (.ref h₁.length)) vs kws = (h₃, .val w)) :
    evalExpr ctx (k+1) h ρ (.alloc cls args) = (h₃, .val (.ref h₁.length)) := by
  have hc : (match ρ.get cls with | .clsClos _ c => c | _ => []) = ([] : List (String × Val)) := by
    cases hg : ρ.get cls <;> simp [hg]
    case clsClos c cap => exact absurd hg (hcap c cap)
  simp only [evalExpr, has, hbb, hc, Heap.alloc, hm, hinit]

theorem execStmt_forIn_val (ctx : Ctx) (k : Nat) (h : Heap) (ρ : Env)
    {x : String} {e : Expr} {body : Stmt} {h₁ : Heap} {v : Val} {vs : List Val}
    (he : evalExpr ctx k h ρ e = (h₁, .val v)) (hv : v.iterable = some vs) :
    execStmt ctx (k+1) h ρ (.forIn x e body) = execFor ctx k h₁ ρ x vs body := by
  simp [execStmt, he, hv]

/-! ## 4. End-to-end: real translated functions

Entry points are named by their **fully-qualified CPG name** (`ops.py:<module>.absval`,
not `absval`). `Ctx.resolve` will also accept the short name via suffix matching, but that
is documented in `Semantics.lean` as a heuristic, and a refinement theorem should not
depend on a heuristic to decide which function it is about.

Every theorem below is about a `Func` emitted by `cartographer/render_lean.py` from a
Joern code property graph — the deep terms in `Autoform/Generated/`, unmodified. -/

namespace Demo

/-! ### Verbatim copy of `Autoform/Generated/CMath.lean` (C, from `math.c`)`

Copied rather than imported: when this was written every generated module declared
`Autoform.Generated.program`, so no two of them could be imported into the same file.
That restriction is gone -- each corpus now lives in `Autoform.Generated.<Module>` --
but the copy is kept deliberately: this section's point is that the terms below are
byte-identical to the renderer's output, which a reader can check here without
chasing an import.
Only the `program` binder is renamed; every `Func` is character-for-character as
emitted by `cartographer/render_lean.py`. -/

/-- `clamp`  (from `math.c`) -/
def f_clamp : Func :=
  { name := "clamp"
  , params := ["x", "lo", "hi"]
  , body := (.seq
            (.ifte (.binop "<" (.name "x") (.name "lo")) (.ret (.name "lo")) .skip)
            (.seq
              (.ifte (.binop ">" (.name "x") (.name "hi")) (.ret (.name "hi")) .skip)
              (.ret (.name "x")))) }

/-- `poly`  (from `math.c`) -/
def f_poly : Func :=
  { name := "poly"
  , params := ["a", "b", "c"]
  , body := (.ret
            (.binop "-" (.binop "+" (.binop "*" (.name "a") (.name "b")) (.name "c")) (.name "a"))) }

/-- `sumto`  (from `math.c`) -/
def f_sumto : Func :=
  { name := "sumto"
  , params := ["n"]
  , body := (.seq
            .skip
            (.seq
              (.assign "acc" (.lit (.int 0)))
              (.seq
                .skip
                (.seq
                  (.assign "i" (.lit (.int 0)))
                  (.seq
                    (.loop
                      (.binop "<=" (.name "i") (.name "n"))
                      (.seq
                        (.assign "acc" (.binop "+" (.name "acc") (.name "i")))
                        (.assign "i" (.binop "+" (.name "i") (.lit (.int 1))))))
                    (.ret (.name "acc"))))))) }

/-- `cdiv`  (from `math.c`) -/
def f_cdiv : Func :=
  { name := "cdiv"
  , params := ["a", "b"]
  , body := (.seq
            (.ifte (.binop "==" (.name "b") (.lit (.int 0))) (.ret (.lit (.int 0))) .skip)
            (.ret (.binop "/" (.name "a") (.name "b")))) }

/-- `cmod`  (from `math.c`) -/
def f_cmod : Func :=
  { name := "cmod"
  , params := ["a", "b"]
  , body := (.seq
            (.ifte (.binop "==" (.name "b") (.lit (.int 0))) (.ret (.lit (.int 0))) .skip)
            (.ret (.binop "%" (.name "a") (.name "b")))) }

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def CMathProgram : Program := { dialect := .cLike, funcs := [
  f_clamp,
  f_poly,
  f_sumto,
  f_cdiv,
  f_cmod
] }

/-! ### Verbatim copy of `Autoform/Generated/Sample.lean` (Python, from `lib.py`)`

Copied rather than imported: when this was written every generated module declared
`Autoform.Generated.program`, so no two of them could be imported into the same file.
That restriction is gone -- each corpus now lives in `Autoform.Generated.<Module>` --
but the copy is kept deliberately: this section's point is that the terms below are
byte-identical to the renderer's output, which a reader can check here without
chasing an import.
Only the `program` binder is renamed; every `Func` is character-for-character as
emitted by `cartographer/render_lean.py`. -/

/-- `lib.py:<module>.add`  (from `lib.py`) -/
def f_lib_py__module__add : Func :=
  { name := "lib.py:<module>.add"
  , params := ["a", "b"]
  , body := (.ret (.binop "+" (.name "a") (.name "b"))) }

/-- `lib.py:<module>.clamp`  (from `lib.py`) -/
def f_lib_py__module__clamp : Func :=
  { name := "lib.py:<module>.clamp"
  , params := ["x", "lo", "hi"]
  , body := (.seq
            (.ifte (.binop "<" (.name "x") (.name "lo")) (.ret (.name "lo")) .skip)
            (.seq
              (.ifte (.binop ">" (.name "x") (.name "hi")) (.ret (.name "hi")) .skip)
              (.ret (.name "x")))) }

/-- `lib.py:<module>.encode`  (from `lib.py`) -/
def f_lib_py__module__encode : Func :=
  { name := "lib.py:<module>.encode"
  , params := ["xs"]
  , body := (.seq
            (.assign "out" (.listE []))
            (.seq
              .skip
              (.seq
                (.forIn
                  "x"
                  (.name "xs")
                  (.expr
                    (.mcall (.name "out") "append" [(.call "add" [(.name "x"), (.lit (.int 1))])])))
                (.seq .skip (.seq (.ret (.name "out")) (.seq .skip .skip)))))) }

/-- `lib.py:<module>.save`  (from `lib.py`) -/
def f_lib_py__module__save : Func :=
  { name := "lib.py:<module>.save"
  , params := ["path", "xs"]
  , body := (.seq
            (.seq
              (.assign "manager_tmp0" (.call "open" [(.name "path"), (.lit (.str "w"))]))
              (.seq
                (.assign "enter_tmp0" (.field (.name "manager_tmp0") "__enter__"))
                (.seq
                  (.assign "exit_tmp0" (.field (.name "manager_tmp0") "__exit__"))
                  (.seq
                    (.assign "value_tmp0" (.call "" []))
                    (.seq
                      (.tryCatch
                        (.seq
                          (.assign "f" (.name "value_tmp0"))
                          (.expr
                            (.mcall
                              (.name "f")
                              "write"
                              [(.call "str" [(.call "encode" [(.name "xs")])])])))
                        "__exc"
                        (.seq (.expr (.call "" [])) (.raise (.name "__exc"))))
                      (.expr (.call "" [])))))))
            (.seq
              .skip
              (.seq
                .skip
                (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))) }

/-- `lib.py:<module>.sample_id`  (from `lib.py`) -/
def f_lib_py__module__sample_id : Func :=
  { name := "lib.py:<module>.sample_id"
  , params := []
  , body := (.seq
            (.assign "random" (.call "import" [(.lit .unit), (.hole "lit:unquoted")]))
            (.seq .skip (.seq (.ret (.mcall (.name "random") "random" [])) .skip))) }

/-- Source dialect: `.python` (integer division/modulo convention). -/
def SampleProgram : Program := { dialect := .python, funcs := [
  f_lib_py__module__add,
  f_lib_py__module__clamp,
  f_lib_py__module__encode,
  f_lib_py__module__save,
  f_lib_py__module__sample_id
] }

/-! ### Verbatim copy of `Autoform/Generated/Stress.lean` (Python, from `ops.py`) -/


/-- `ops.py:<module>.fdiv`  (from `ops.py`) -/
def f_ops_py__module__fdiv : Func :=
  { name := "ops.py:<module>.fdiv"
  , params := ["a", "b"]
  , body := (.seq
            (.ifte (.binop "==" (.name "b") (.lit (.int 0))) (.ret (.lit (.int 0))) .skip)
            (.ret (.binop "/" (.name "a") (.name "b")))) }

/-- `ops.py:<module>.fmod`  (from `ops.py`) -/
def f_ops_py__module__fmod : Func :=
  { name := "ops.py:<module>.fmod"
  , params := ["a", "b"]
  , body := (.seq
            (.ifte (.binop "==" (.name "b") (.lit (.int 0))) (.ret (.lit (.int 0))) .skip)
            (.ret (.binop "%" (.name "a") (.name "b")))) }

/-- `ops.py:<module>.poly`  (from `ops.py`) -/
def f_ops_py__module__poly : Func :=
  { name := "ops.py:<module>.poly"
  , params := ["a", "b", "c"]
  , body := (.ret
            (.binop "-" (.binop "+" (.binop "*" (.name "a") (.name "b")) (.name "c")) (.name "a"))) }

/-- `ops.py:<module>.cmpchain`  (from `ops.py`) -/
def f_ops_py__module__cmpchain : Func :=
  { name := "ops.py:<module>.cmpchain"
  , params := ["x", "y"]
  , body := (.seq
            (.ifte (.binop "<" (.name "x") (.name "y")) (.ret (.unop "-" (.lit (.int 1)))) .skip)
            (.seq
              (.ifte (.binop ">" (.name "x") (.name "y")) (.ret (.lit (.int 1))) .skip)
              (.ret (.lit (.int 0))))) }

/-- `ops.py:<module>.absval`  (from `ops.py`) -/
def f_ops_py__module__absval : Func :=
  { name := "ops.py:<module>.absval"
  , params := ["x"]
  , body := (.seq
            (.ifte (.binop "<" (.name "x") (.lit (.int 0))) (.ret (.unop "-" (.name "x"))) .skip)
            (.ret (.name "x"))) }

/-- `ops.py:<module>.gcdish`  (from `ops.py`) -/
def f_ops_py__module__gcdish : Func :=
  { name := "ops.py:<module>.gcdish"
  , params := ["a", "b"]
  , body := (.seq
            (.loop
              (.binop "!=" (.name "b") (.lit (.int 0)))
              (.seq
                (.assign "t" (.name "b"))
                (.seq (.assign "b" (.binop "%" (.name "a") (.name "b"))) (.assign "a" (.name "t")))))
            (.seq .skip (.ret (.name "a")))) }

/-- Source dialect: `.python` (integer division/modulo convention). -/
def StressProgram : Program := { dialect := .python, funcs := [
  f_ops_py__module__fdiv,
  f_ops_py__module__fmod,
  f_ops_py__module__poly,
  f_ops_py__module__cmpchain,
  f_ops_py__module__absval,
  f_ops_py__module__gcdish
] }


/-- 32-bit signed representability, the shape a C refinement domain takes.

With `Numeric.lean` wired into `applyBinop`, a C function refines its mathematical model
only where **every intermediate result** is representable. Outside that domain the
machine answer wraps (`.cLike` maps to `NumConfig.c32Wrapv`) and the clean model is
simply wrong — see `poly_not_refinable` below, which proves exactly that. This is what
the `dom` parameter of `Refines` is for, and it is why the parameter is not decoration. -/
abbrev fits32 (x : Int) : Prop := Fits32 x

/-! ### C: `poly` from `math.c`

Source: `int poly(int a, int b, int c) { return a*b + c - a; }`.
Deep term: `f_poly`. Shallow model: `fun a b c => a*b + c - a`, **on the no-overflow
domain**. The three conjuncts of `dom` are one per intermediate operation, in evaluation
order — which is the only correct granularity: `a*b` can overflow even when the final
`a*b + c - a` is representable. -/

theorem poly_refines :
    Refines₃ (α := Int) (β := Int) (γ := Int) (δ := Int)
      CMathProgram "poly" 9
      (fun a b c => fits32 (a * b) ∧ fits32 (a * b + c) ∧ fits32 (a * b + c - a))
      (fun a b c => a * b + c - a) := by
  intro a b c hdom
  obtain ⟨h1, h2, h3⟩ := hdom
  refine forall_ge_of_forall_add (N := 9) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_poly rfl]
  simp [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, Env.set, Env.get, f_poly, ctxOf,
        CMathProgram, Marshal.toVal, applyBinop_c_mul h1, applyBinop_c_add h2,
        applyBinop_c_sub h3]

/-! ### The overflow negative result

`poly` does **not** refine `fun a b c => a*b + c - a` on the unrestricted domain, and the
witness is the one the conformance oracle measured: `100000 * 100000` is `10^10`, which
wraps to `1410065408` in 32-bit two's complement. The deep term therefore returns
`1409965408` where the mathematical model says `9999900000`.

This is the same shape as `fdiv_not_refinable`, and it is the reason the `dom` conjuncts
above are not conservatism: without them `poly_refines` would be false. -/

theorem poly_overflows (k : Nat) :
    runFunc CMathProgram (k + 9) "poly" [.int 100000, .int 100000, .int 0]
      = .val (.int 1409965408) := by
  rw [runFunc_of_resolve _ _ _ _ f_poly rfl]
  simp only [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, Env.set, Env.get, f_poly, ctxOf, CMathProgram]
  rfl

/-- No fuel bound makes `poly` refine its mathematical model on the full domain. -/
theorem poly_not_refinable (N : Nat) :
    ¬ Refines₃ (α := Int) (β := Int) (γ := Int) (δ := Int)
        CMathProgram "poly" N (fun _ _ _ => True) (fun a b c => a * b + c - a) := by
  intro hR
  have key := hR 100000 100000 0 trivial (N + 9) (Nat.le_add_right _ _)
  simp only [Marshal.toVal, show N + 9 = 9 + N from Nat.add_comm _ _] at key
  have hov := poly_overflows N
  simp only [show N + 9 = 9 + N from Nat.add_comm _ _] at hov
  rw [hov] at key
  simp at key

/-! ### C: `clamp` from `math.c`

Source: three-branch guard with early returns. `clamp` performs no arithmetic — only
comparisons and returns — so it is representability-clean and keeps `dom = True`. That
asymmetry with `poly` is the point: the domain restriction tracks the actual arithmetic,
it is not a blanket disclaimer. -/

/-- The shallow model of `clamp`: an ordinary Lean function, no interpreter. -/
def clampS (x lo hi : Int) : Int := if x < lo then lo else if hi < x then hi else x

theorem clamp_refines :
    Refines₃ (α := Int) (β := Int) (γ := Int) (δ := Int)
      CMathProgram "clamp" 12 (fun _ _ _ => True) clampS := by
  intro x lo hi _
  simp only [clampS]
  refine forall_ge_of_forall_add (N := 12) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_clamp rfl]
  by_cases h1 : x < lo
  · simp [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, Env.set, Env.get, f_clamp, ctxOf,
          CMathProgram, Marshal.toVal, Val.truthy, applyBinop_int_lt, h1]
  · by_cases h2 : hi < x
    · simp [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, Env.set, Env.get, f_clamp, ctxOf,
            CMathProgram, Marshal.toVal, Val.truthy, applyBinop_int_lt, applyBinop_int_gt,
            h1, h2]
    · simp [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, Env.set, Env.get, f_clamp, ctxOf,
            CMathProgram, Marshal.toVal, Val.truthy, applyBinop_int_lt, applyBinop_int_gt,
            h1, h2]

/-! ### C: `cdiv` — dialect *and* width

`math.c` is `.cLike`, so `/` truncates toward zero (`Int.tdiv`), not Python's floor
division. The domain carries the one genuine C division overflow, `INT_MIN / -1`, whose
mathematical quotient `2^31` is one past the top of the signed range. The source's own
zero guard means the `ZeroDivisionError` path is unreachable. -/

theorem cdiv_refines :
    Refines₂ (α := Int) (β := Int) (γ := Int)
      CMathProgram "cdiv" 10 (fun a b => fits32 (Int.tdiv a b))
      (fun a b => if b = 0 then 0 else Int.tdiv a b) := by
  intro a b hdom
  refine forall_ge_of_forall_add (N := 10) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_cdiv rfl]
  by_cases hb : b = 0
  · subst hb
    simp [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, Env.set, Env.get, f_cdiv, ctxOf,
          CMathProgram, Marshal.toVal, Val.truthy, applyBinop_int_eq]
  · simp [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, Env.set, Env.get, f_cdiv, ctxOf,
          CMathProgram, Marshal.toVal, Val.truthy, applyBinop_int_eq,
          applyBinop_c_div hb hdom, hb]

/-! ### Python: `add` from `lib.py`

Python is unbounded, so the Python theorems keep `dom = True` — the width story is a
property of the *dialect*, and `Dialect.toNumConfig .python` is `NumConfig.python` with
`IntType.unbounded`. -/

theorem add_refines :
    Refines₂ (α := Int) (β := Int) (γ := Int)
      SampleProgram "lib.py:<module>.add" 8 (fun _ _ => True) (fun a b => a + b) := by
  intro a b _
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_lib_py__module__add rfl]
  simp [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, Env.set, Env.get, f_lib_py__module__add, ctxOf,
        SampleProgram, Marshal.toVal]

/-! ### Python: `absval` from `ops.py` -/

theorem absval_refines :
    Refines₁ (α := Int) (β := Int)
      StressProgram "ops.py:<module>.absval" 10 (fun _ => True)
      (fun x => if x < 0 then -x else x) := by
  intro x _
  refine forall_ge_of_forall_add (N := 10) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_ops_py__module__absval rfl]
  by_cases h1 : x < 0
  · simp [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, Env.set, Env.get, applyUnop_int_neg,
          f_ops_py__module__absval, ctxOf, StressProgram, Marshal.toVal, Val.truthy,
          applyBinop_int_lt, h1]
  · simp [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, Env.set, Env.get,
          f_ops_py__module__absval, ctxOf, StressProgram, Marshal.toVal, Val.truthy,
          applyBinop_int_lt, h1]

/-! ### Python: `cmpchain` from `ops.py` -/

theorem cmpchain_refines :
    Refines₂ (α := Int) (β := Int) (γ := Int)
      StressProgram "ops.py:<module>.cmpchain" 12 (fun _ _ => True)
      (fun x y => if x < y then -1 else if y < x then 1 else 0) := by
  intro x y _
  refine forall_ge_of_forall_add (N := 12) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_ops_py__module__cmpchain rfl]
  by_cases h1 : x < y
  · simp [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, Env.set, Env.get, applyUnop_int_neg,
          f_ops_py__module__cmpchain, ctxOf, StressProgram, Marshal.toVal, Val.truthy,
          applyBinop_int_lt, h1]
  · by_cases h2 : y < x
    · simp [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, Env.set, Env.get,
            f_ops_py__module__cmpchain, ctxOf, StressProgram, Marshal.toVal, Val.truthy,
            applyBinop_int_lt, applyBinop_int_gt, h1, h2]
    · simp [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, Env.set, Env.get,
            f_ops_py__module__cmpchain, ctxOf, StressProgram, Marshal.toVal, Val.truthy,
            applyBinop_int_lt, applyBinop_int_gt, h1, h2]

/-! ### Python: `fmod` — the other side of the dialect split

`ops.py` is `.python`, so `%` floors (`Int.fmod`). This is the exact pair that
`scripts/differential.py` caught: the same deep term under a different dialect tag has a
different shallow model, and both are proved. Unlike `cdiv`, no representability side
condition is needed — Python has no width. -/

theorem fmod_refines :
    Refines₂ (α := Int) (β := Int) (γ := Int)
      StressProgram "ops.py:<module>.fmod" 10 (fun _ _ => True)
      (fun a b => if b = 0 then 0 else Int.fmod a b) := by
  intro a b _
  refine forall_ge_of_forall_add (N := 10) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_ops_py__module__fmod rfl]
  by_cases hb : b = 0
  · subst hb
    simp [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, Env.set, Env.get, f_ops_py__module__fmod, ctxOf,
          StressProgram, Marshal.toVal, Val.truthy, applyBinop_int_eq]
  · simp [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, Env.set, Env.get, f_ops_py__module__fmod, ctxOf,
          StressProgram, Marshal.toVal, Val.truthy, applyBinop_int_eq,
          applyBinop_py_mod a b hb, hb]

/-! ### Python: `fdiv` — regenerated, and now refinable

When this file was first written, `ops.py`'s `//` was untranslated and `f_ops_py__module__fdiv`
carried `Expr.hole "op:floorDiv"`, which made it the hole negative result. The transpiler
has since been regenerated and now emits `Expr.binop "/"`, which under the `.python`
dialect is floor division. So the same function has moved from "provably refines nothing"
to "provably refines `Int.fdiv`" — which is exactly the transition the ledger exists to
record. -/

theorem fdiv_refines :
    Refines₂ (α := Int) (β := Int) (γ := Int)
      StressProgram "ops.py:<module>.fdiv" 10 (fun _ _ => True)
      (fun a b => if b = 0 then 0 else Int.fdiv a b) := by
  intro a b _
  refine forall_ge_of_forall_add (N := 10) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ f_ops_py__module__fdiv rfl]
  by_cases hb : b = 0
  · subst hb
    simp [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, Env.set, Env.get, f_ops_py__module__fdiv, ctxOf,
          StressProgram, Marshal.toVal, Val.truthy, applyBinop_int_eq]
  · simp [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, Env.set, Env.get, f_ops_py__module__fdiv, ctxOf,
          StressProgram, Marshal.toVal, Val.truthy, applyBinop_int_eq,
          applyBinop_py_div a b hb, hb]

/-! ### The hole negative result: untranslated constructs are not refinable

`lib.py`'s `sample_id` does `import random` and returns `random.random()`. The import's
module-name argument is still untranslated: the deep term carries
`Expr.hole "lit:unquoted"` inside the argument list of `Expr.call "import"`. Evaluating
the arguments left to right reaches it, and the hole propagates out through `evalList`,
the assignment and the function boundary.

Because `Outcome` cannot denote a hole, **no** shallow function refines `sample_id`.
Together with `poly_not_refinable` these are the two ways a refinement claim can fail —
we did not translate it, or the machine does not agree with the mathematics — and both
are visible in the statement rather than absorbed by it. -/

theorem sample_id_reaches_hole (k : Nat) :
    runFunc SampleProgram (k + 10) "lib.py:<module>.sample_id" []
      = .hole "lit:unquoted" := by
  rw [runFunc_of_resolve _ _ _ _ f_lib_py__module__sample_id rfl]
  simp [applyFunc, bindParams, Func.posParams, kwargsRejected, execStmt, evalExpr, evalList, Env.set,
        f_lib_py__module__sample_id, ctxOf, SampleProgram]

/-- No shallow specification refines `sample_id`, at any fuel bound, on any domain that
contains its (empty) argument list. -/
theorem sample_id_not_refinable (N : Nat) (dom : List Val → Prop) (spec : List Val → Outcome)
    (hd : dom []) :
    ¬ Refines SampleProgram "lib.py:<module>.sample_id" N dom spec := by
  intro hR
  have hne := refines_not_hole hR [] hd (N + 10) (Nat.le_add_right _ _) "lit:unquoted"
  exact hne (by simpa [Nat.add_comm] using sample_id_reaches_hole N)

/-! ### Reasoning in the shallow world

The payoff. Once `clamp_refines` is available, facts about the *translated C function*
are proved by ordinary arithmetic on `clampS`, with no interpreter in sight. -/

theorem clampS_idem (x lo hi : Int) (h : lo ≤ hi) :
    clampS (clampS x lo hi) lo hi = clampS x lo hi := by
  unfold clampS
  by_cases h1 : x < lo <;> by_cases h2 : hi < x <;> simp [h1, h2] <;> omega

/-- …and the fact transfers back to the deep term for free. -/
theorem clamp_deep_idem (x lo hi : Int) (h : lo ≤ hi) (fuel : Nat) (hf : 12 ≤ fuel) :
    runFunc CMathProgram fuel "clamp"
        [.int (clampS x lo hi), .int lo, .int hi] = .val (.int (clampS x lo hi)) := by
  have key := clamp_refines (clampS x lo hi) lo hi trivial fuel hf
  simp only [Marshal.toVal, clampS_idem x lo hi h] at key
  exact key


/-! ### C: `sumto` from `math.c` — the first loop

Source: `int sumto(int n){ int acc=0; for(int i=0;i<=n;i++) acc+=i; return acc; }`.
Deep term: `f_sumto`, verbatim above. Shallow model: `n*(n+1)/2`.

The invariant is indexed by the number of iterations still to run, `m`, and the state is
pinned by `d = n+1-m`: `i` holds `d` and `acc` holds the `d`-th triangular number. The
`fits32` obligations are discharged per iteration from a *closed-form* domain by
monotonicity of `triN`, which is what stops the domain from being a per-step quantified
mess: every partial sum is between `0` and the final one.

Two things the fuel bound makes visible. First, a loop's cost depends on its input, so
the `Refines₁` instance below quantifies a *concrete* bound `65547` and must restrict the
domain to `n ≤ 65535` to justify it — the parametric `sumto_run` is the sharp statement
and `sumto_refines` is its constant-bound corollary. Second, `n ≤ 65535` is not an extra
assumption in substance: `Fits32 (n*(n+1)/2)` already forces it. It is stated rather than
derived because deriving it needs nonlinear arithmetic that is not available here. -/

def triN : Nat → Int
  | 0 => 0
  | k+1 => triN k + (k : Int)

theorem triN_nonneg : ∀ k, 0 ≤ triN k
  | 0 => Int.le_refl 0
  | k+1 => by have := triN_nonneg k; simp [triN]; omega

theorem triN_mono {d e : Nat} (h : d ≤ e) : triN d ≤ triN e := by
  induction e with
  | zero => simp [Nat.le_zero.mp h]
  | succ e ih =>
    rcases Nat.lt_or_ge d (e+1) with hd | hd
    · have := ih (by omega); simp [triN]; omega
    · have : d = e+1 := by omega
      subst this; exact Int.le_refl _

theorem two_mul_triN : ∀ k : Nat, 2 * triN k = (k : Int) * ((k : Int) - 1)
  | 0 => by simp [triN]
  | k+1 => by
    have ih := two_mul_triN k
    have e1 : (k : Int) * ((k:Int) - 1) = (k:Int)*(k:Int) - (k:Int) := by
      rw [Int.mul_sub, Int.mul_one]
    have e2 : (((k:Int)+1)) * ((((k:Int)+1)) - 1) = (k:Int)*(k:Int) + (k:Int) := by
      have h : (((k:Int)+1)) - 1 = (k:Int) := by omega
      rw [h, Int.add_mul, Int.one_mul]
    rw [e1] at ih
    show 2 * (triN k + (k:Int)) = ((k:Int) + 1) * (((k:Int) + 1) - 1)
    rw [e2]; revert ih; generalize (k:Int)*(k:Int) = q; omega

theorem triN_closed {n : Int} (hn : 0 ≤ n) : triN (n.toNat + 1) = n * (n + 1) / 2 := by
  have h := two_mul_triN (n.toNat + 1)
  have hc : ((n.toNat + 1 : Nat) : Int) = n + 1 := by omega
  rw [hc] at h
  have h2 : (n + 1) * (n + 1 - 1) = n * (n + 1) := by
    have e : n + 1 - 1 = n := by omega
    rw [e, Int.mul_comm]
  rw [h2] at h
  revert h; generalize n * (n+1) = q; omega

theorem fits32_of_le {x y : Int} (h0 : 0 ≤ x) (hxy : x ≤ y) (hy : Fits32 y) : Fits32 x := by
  simp only [Fits32, IntType.inRange, Width.bits, decide_eq_true_eq, Bool.and_eq_true] at hy ⊢
  have h : (2:Int)^(32-1) = 2147483648 := by rfl
  omega

theorem fits32_small {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 100000) : Fits32 x := by
  simp only [Fits32, IntType.inRange, Width.bits, decide_eq_true_eq, Bool.and_eq_true]
  have h : (2:Int)^(32-1) = 2147483648 := by rfl
  omega

/-- The invariant. -/
def sumtoInv (n : Int) (m : Nat) (h : Heap) (ρ : Env) : Prop :=
  h = [] ∧ ∃ d : Nat, d + m = n.toNat + 1 ∧
    ρ.find? (·.1 == "n") = some ("n", .int n) ∧
    ρ.find? (·.1 == "i") = some ("i", .int (d : Int)) ∧
    ρ.find? (·.1 == "acc") = some ("acc", .int (triN d)) ∧
    ρ.find? (·.1 == "<glob>acc") = none ∧
    ρ.find? (·.1 == "<glob>i") = none

def sumtoPost (n : Int) (h : Heap) (ρ : Env) : Prop :=
  h = [] ∧ ρ.find? (·.1 == "acc") = some ("acc", .int (triN (n.toNat + 1)))

abbrev ctxC : Ctx := ctxOf CMathProgram

theorem sumto_step (n : Int) (hn : 0 ≤ n) (hb : n ≤ 65535)
    (hfitN : Fits32 (triN (n.toNat + 1))) :
    ∀ m h ρ k, 4 ≤ k → sumtoInv n m h ρ →
      ∃ h₁ v, evalExpr ctxC k h ρ (.binop "<=" (.name "i") (.name "n")) = (h₁, .val v) ∧
        (v.truthy = true → ∃ m' h₂ ρ', m' < m ∧
          execStmt ctxC k h₁ ρ
            (.seq (.assign "acc" (.binop "+" (.name "acc") (.name "i")))
                  (.assign "i" (.binop "+" (.name "i") (.lit (.int 1)))))
            = (h₂, .normal ρ') ∧ sumtoInv n m' h₂ ρ') ∧
        (v.truthy = false → sumtoPost n h₁ ρ) := by
  intro m h ρ k hk hI
  obtain ⟨rfl, d, hdm, hnv, hiv, haccv, hga, hgi⟩ := hI
  obtain ⟨k1, rfl⟩ : ∃ q, k = q + 4 := ⟨k - 4, by omega⟩
  have hcond : evalExpr ctxC (k1+4) [] ρ (.binop "<=" (.name "i") (.name "n"))
      = ([], .val (.bool (decide ((d:Int) ≤ n)))) := by
    rw [evalExpr_binop_val ctxC (k1+3) [] ρ "<=" (by decide) (by decide)
          (evalExpr_name ctxC (k1+2) [] ρ "i" hiv) (evalExpr_name ctxC (k1+2) [] ρ "n" hnv)]
    rfl
  refine ⟨[], .bool (decide ((d:Int) ≤ n)), hcond, ?_, ?_⟩
  · intro hv
    have hdn : (d:Int) ≤ n := by
      simpa [Val.truthy] using hv
    have hdN : d < n.toNat + 1 := by omega
    -- Fits32 side conditions
    have hf1 : Fits32 (triN d + (d:Int)) := by
      have e : triN d + (d:Int) = triN (d+1) := rfl
      rw [e]
      exact fits32_of_le (triN_nonneg _) (triN_mono (by omega)) hfitN
    have hf2 : Fits32 ((d:Int) + 1) := fits32_small (by omega) (by omega)
    have e1 : evalExpr ctxC (k1+2) [] ρ (.binop "+" (.name "acc") (.name "i"))
        = ([], .val (.int (triN d + (d:Int)))) := by
      rw [evalExpr_binop_val ctxC (k1+1) [] ρ "+" (by decide) (by decide)
            (evalExpr_name ctxC k1 [] ρ "acc" haccv) (evalExpr_name ctxC k1 [] ρ "i" hiv)]
      simp [applyBinop_c_add hf1, ctxC, ctxOf, CMathProgram]
    have hgA : (ρ.get ("<glob>" ++ "acc")).truthy = false := by
      simp [Env.get, hga, Val.truthy]
    have a1 : execStmt ctxC (k1+3) [] ρ (.assign "acc" (.binop "+" (.name "acc") (.name "i")))
        = ([], .normal (ρ.set "acc" (.int (triN d + (d:Int))))) :=
      execStmt_assign_val ctxC (k1+2) [] ρ e1 hgA
    have hiv1 : (ρ.set "acc" (.int (triN d + (d:Int)))).find? (·.1 == "i") = some ("i", .int (d:Int)) := by
      simp [Env.set, hiv]
    have e2 : evalExpr ctxC (k1+2) [] (ρ.set "acc" (.int (triN d + (d:Int)))) (.binop "+" (.name "i") (.lit (.int 1)))
        = ([], .val (.int ((d:Int) + 1))) := by
      rw [evalExpr_binop_val ctxC (k1+1) [] (ρ.set "acc" (.int (triN d + (d:Int)))) "+" (by decide) (by decide)
            (evalExpr_name ctxC k1 [] (ρ.set "acc" (.int (triN d + (d:Int)))) "i" hiv1) (evalExpr_lit_int ctxC k1 [] (ρ.set "acc" (.int (triN d + (d:Int)))) 1)]
      simp [applyBinop_c_add hf2, ctxC, ctxOf, CMathProgram]
    have hgI : ((ρ.set "acc" (.int (triN d + (d:Int)))).get ("<glob>" ++ "i")).truthy = false := by
      simp [Env.set, Env.get, hgi, Val.truthy]
    have a2 : execStmt ctxC (k1+3) [] (ρ.set "acc" (.int (triN d + (d:Int)))) (.assign "i" (.binop "+" (.name "i") (.lit (.int 1))))
        = ([], .normal ((ρ.set "acc" (.int (triN d + (d:Int)))).set "i" (.int ((d:Int) + 1)))) :=
      execStmt_assign_val ctxC (k1+2) [] (ρ.set "acc" (.int (triN d + (d:Int)))) e2 hgI
    refine ⟨m - 1, [], (ρ.set "acc" (.int (triN d + (d:Int)))).set "i" (.int ((d:Int) + 1)), by omega, ?_, ?_⟩
    · rw [execStmt_seq_normal ctxC (k1+3) [] ρ a1]; exact a2
    · refine ⟨rfl, d + 1, by omega, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Env.set, hnv]
      · have : ((d+1 : Nat) : Int) = (d:Int) + 1 := by omega
        simp [Env.set, this]
      · have : triN (d+1) = triN d + (d:Int) := rfl
        simp [Env.set, this]
      · simp [Env.set, hga]
      · simp [Env.set, hgi]
  · intro hv
    have hdn : ¬ ((d:Int) ≤ n) := by simpa [Val.truthy] using hv
    have : d = n.toNat + 1 := by omega
    subst this
    exact ⟨rfl, haccv⟩

theorem sumto_run (n : Int) (hn : 0 ≤ n) (hb : n ≤ 65535)
    (hfit : Fits32 (n * (n + 1) / 2)) (fuel : Nat) (hf : n.toNat + 12 ≤ fuel) :
    runFunc CMathProgram fuel "sumto" [.int n] = .val (.int (n * (n + 1) / 2)) := by
  have hfitN : Fits32 (triN (n.toNat + 1)) := by rw [triN_closed hn]; exact hfit
  obtain ⟨G, rfl⟩ : ∃ q, fuel = q + 8 := ⟨fuel - 8, by omega⟩
  have hG : n.toNat + 4 ≤ G := by omega
  rw [runFunc_of_resolve _ _ _ _ f_sumto rfl]
  have s1 : execStmt ctxC (G+6) [] [("n", Val.int n)] .skip
      = ([], .normal [("n", Val.int n)]) := execStmt_skip ctxC (G+5) [] _
  have s2 : execStmt ctxC (G+5) [] [("n", Val.int n)] (.assign "acc" (.lit (.int 0)))
      = ([], .normal [("acc", Val.int 0), ("n", Val.int n)]) :=
    execStmt_assign_val ctxC (G+4) [] _ (evalExpr_lit_int ctxC (G+3) [] _ 0) (by rfl)
  have s3 : execStmt ctxC (G+4) [] [("acc", Val.int 0), ("n", Val.int n)] .skip
      = ([], .normal [("acc", Val.int 0), ("n", Val.int n)]) := execStmt_skip ctxC (G+3) [] _
  have s4 : execStmt ctxC (G+3) [] [("acc", Val.int 0), ("n", Val.int n)]
        (.assign "i" (.lit (.int 0)))
      = ([], .normal [("i", Val.int 0), ("acc", Val.int 0), ("n", Val.int n)]) :=
    execStmt_assign_val ctxC (G+2) [] _ (evalExpr_lit_int ctxC (G+1) [] _ 0) (by rfl)
  have hinv : sumtoInv n (n.toNat + 1) []
      [("i", Val.int 0), ("acc", Val.int 0), ("n", Val.int n)] := by
    refine ⟨rfl, 0, by omega, by rfl, ?_, ?_, by rfl, by rfl⟩
    · simp [triN]
    · simp [triN]
  obtain ⟨h', ρ', hloop, hpost⟩ :=
    execStmt_loop_rule ctxC (.binop "<=" (.name "i") (.name "n"))
      (.seq (.assign "acc" (.binop "+" (.name "acc") (.name "i")))
            (.assign "i" (.binop "+" (.name "i") (.lit (.int 1)))))
      4 (sumtoInv n) (sumtoPost n) (sumto_step n hn hb hfitN)
      (G+2) (n.toNat + 1) [] [("i", Val.int 0), ("acc", Val.int 0), ("n", Val.int n)]
      hinv (by omega)
  obtain ⟨rfl, hacc⟩ := hpost
  have hret : execStmt ctxC (G+2) [] ρ' (.ret (.name "acc"))
      = ([], .ret (.int (triN (n.toNat + 1)))) :=
    execStmt_ret_val ctxC (G+1) [] ρ' (evalExpr_name ctxC G [] ρ' "acc" hacc)
  have hbody : execStmt ctxC (G+7) [] [("n", Val.int n)] f_sumto.body
      = ([], .ret (.int (triN (n.toNat + 1)))) := by
    simp only [f_sumto]
    rw [execStmt_seq_normal ctxC (G+6) [] _ s1,
        execStmt_seq_normal ctxC (G+5) [] _ s2,
        execStmt_seq_normal ctxC (G+4) [] _ s3,
        execStmt_seq_normal ctxC (G+3) [] _ s4,
        execStmt_seq_normal ctxC (G+2) [] _ hloop,
        hret]
  rw [triN_closed hn] at hbody
  simp only [f_sumto, ctxC] at hbody
  simp [applyFunc, bindParams, Func.posParams, kwargsRejected, f_sumto, Env.set, hbody]

theorem sumto_refines :
    Refines₁ (α := Int) (β := Int)
      CMathProgram "sumto" 65547
      (fun n => 0 ≤ n ∧ n ≤ 65535 ∧ Fits32 (n * (n + 1) / 2))
      (fun n => n * (n + 1) / 2) := by
  rintro n ⟨hn, hb, hfit⟩ fuel hf
  exact sumto_run n hn hb hfit fuel (by omega)



/-! ### Python: `gcdish` from `ops.py` — a loop whose measure is not a counter

`while b != 0: t=b; b=a%b; a=t`. Here the invariant's index is not an iteration count that
can be computed up front — it is a *bound* on `b`, and each iteration must prove it
strictly decreases. That is exactly what the `m' < m` obligation of `execStmt_loop_rule`
asks for, and it is why the rule takes a measure rather than a step count.

The correctness half is `Int.gcd`-preservation, `gcd a b = gcd b (a % b)`, on the
nonnegative domain. `%` here is `.python`, i.e. `Int.fmod`, which on nonnegative operands
agrees with `Int.emod` — the dialect split of `fmod_refines` reappearing inside a loop. -/

theorem nat_gcd_step (X Y : Nat) : Nat.gcd X Y = Nat.gcd Y (X % Y) := by
  rw [Nat.gcd_comm X Y, Nat.gcd_rec Y X, Nat.gcd_comm (X % Y) Y]

theorem int_gcd_step {x y : Int} (hx : 0 ≤ x) (hy : 0 < y) :
    Int.gcd x y = Int.gcd y (x % y) := by
  show Nat.gcd x.natAbs y.natAbs = Nat.gcd y.natAbs (x % y).natAbs
  rw [Int.natAbs_emod_of_nonneg hx]
  exact nat_gcd_step _ _

abbrev ctxS : Ctx := ctxOf StressProgram

def gcdInv (g : Nat) (m : Nat) (h : Heap) (ρ : Env) : Prop :=
  h = [] ∧ ∃ x y : Int, 0 ≤ x ∧ 0 ≤ y ∧ y.toNat ≤ m ∧ Int.gcd x y = g ∧
    ρ.find? (·.1 == "a") = some ("a", .int x) ∧
    ρ.find? (·.1 == "b") = some ("b", .int y) ∧
    ρ.find? (·.1 == "<glob>a") = none ∧
    ρ.find? (·.1 == "<glob>b") = none ∧
    ρ.find? (·.1 == "<glob>t") = none

def gcdPost (g : Nat) (h : Heap) (ρ : Env) : Prop :=
  h = [] ∧ ρ.find? (·.1 == "a") = some ("a", .int (g : Int))

theorem gcdish_step (g : Nat) :
    ∀ m h ρ k, 5 ≤ k → gcdInv g m h ρ →
      ∃ h₁ v, evalExpr ctxS k h ρ (.binop "!=" (.name "b") (.lit (.int 0))) = (h₁, .val v) ∧
        (v.truthy = true → ∃ m' h₂ ρ', m' < m ∧
          execStmt ctxS k h₁ ρ
            (.seq (.assign "t" (.name "b"))
              (.seq (.assign "b" (.binop "%" (.name "a") (.name "b")))
                    (.assign "a" (.name "t"))))
            = (h₂, .normal ρ') ∧ gcdInv g m' h₂ ρ') ∧
        (v.truthy = false → gcdPost g h₁ ρ) := by
  intro m h ρ k hk hI
  obtain ⟨rfl, x, y, hx, hy, hym, hgcd, hav, hbv, hga, hgb, hgt⟩ := hI
  obtain ⟨k1, rfl⟩ : ∃ q, k = q + 5 := ⟨k - 5, by omega⟩
  have hcond : evalExpr ctxS (k1+5) [] ρ (.binop "!=" (.name "b") (.lit (.int 0)))
      = ([], .val (.bool (!(y == 0)))) := by
    rw [evalExpr_binop_val ctxS (k1+4) [] ρ "!=" (by decide) (by decide)
          (evalExpr_name ctxS (k1+3) [] ρ "b" hbv) (evalExpr_lit_int ctxS (k1+3) [] ρ 0)]
    rfl
  refine ⟨[], .bool (!(y == 0)), hcond, ?_, ?_⟩
  · intro hv
    have hy0 : y ≠ 0 := by
      simp [Val.truthy] at hv; omega
    have hypos : 0 < y := by omega
    -- t := b
    have hgT : (ρ.get ("<glob>" ++ "t")).truthy = false := by simp [Env.get, hgt, Val.truthy]
    have a1 : execStmt ctxS (k1+4) [] ρ (.assign "t" (.name "b"))
        = ([], .normal (ρ.set "t" (.int y))) :=
      execStmt_assign_val ctxS (k1+3) [] ρ (evalExpr_name ctxS (k1+2) [] ρ "b" hbv) hgT
    have hav1 : (ρ.set "t" (.int y)).find? (·.1 == "a") = some ("a", .int x) := by
      simp [Env.set, hav]
    have hbv1 : (ρ.set "t" (.int y)).find? (·.1 == "b") = some ("b", .int y) := by
      simp [Env.set, hbv]
    have e2 : evalExpr ctxS (k1+2) [] (ρ.set "t" (.int y)) (.binop "%" (.name "a") (.name "b"))
        = ([], .val (.int (x % y))) := by
      rw [evalExpr_binop_val ctxS (k1+1) [] _ "%" (by decide) (by decide)
            (evalExpr_name ctxS k1 [] _ "a" hav1) (evalExpr_name ctxS k1 [] _ "b" hbv1)]
      simp [ctxS, ctxOf, StressProgram, applyBinop_py_mod x y hy0,
            Int.fmod_eq_emod_of_nonneg x (Int.le_of_lt hypos)]
    have hgB : ((ρ.set "t" (.int y)).get ("<glob>" ++ "b")).truthy = false := by
      simp [Env.set, Env.get, hgb, Val.truthy]
    have a2 : execStmt ctxS (k1+3) [] (ρ.set "t" (.int y))
          (.assign "b" (.binop "%" (.name "a") (.name "b")))
        = ([], .normal ((ρ.set "t" (.int y)).set "b" (.int (x % y)))) :=
      execStmt_assign_val ctxS (k1+2) [] _ e2 hgB
    have htv2 : ((ρ.set "t" (.int y)).set "b" (.int (x % y))).find? (·.1 == "t")
        = some ("t", .int y) := by simp [Env.set]
    have hgA : (((ρ.set "t" (.int y)).set "b" (.int (x % y))).get ("<glob>" ++ "a")).truthy
        = false := by simp [Env.set, Env.get, hga, Val.truthy]
    have a3 : execStmt ctxS (k1+3) [] ((ρ.set "t" (.int y)).set "b" (.int (x % y)))
          (.assign "a" (.name "t"))
        = ([], .normal (((ρ.set "t" (.int y)).set "b" (.int (x % y))).set "a" (.int y))) :=
      execStmt_assign_val ctxS (k1+2) [] _
        (evalExpr_name ctxS (k1+1) [] _ "t" htv2) hgA
    have hmod0 : 0 ≤ x % y := Int.emod_nonneg x hy0
    have hmodlt : x % y < y := Int.emod_lt_of_pos x hypos
    refine ⟨m - 1, [], ((ρ.set "t" (.int y)).set "b" (.int (x % y))).set "a" (.int y), by omega, ?_, ?_⟩
    · rw [execStmt_seq_normal ctxS (k1+4) [] ρ a1,
          execStmt_seq_normal ctxS (k1+3) [] _ a2]
      exact a3
    · refine ⟨rfl, y, x % y, Int.le_of_lt hypos, hmod0, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← int_gcd_step hx hypos]; exact hgcd
      · simp [Env.set]
      · simp [Env.set]
      · simp [Env.set, hga]
      · simp [Env.set, hgb]
      · simp [Env.set, hgt]
  · intro hv
    have hy0 : y = 0 := by simp [Val.truthy] at hv; omega
    subst hy0
    refine ⟨rfl, ?_⟩
    have : Int.gcd x 0 = x.natAbs := by simp [Int.gcd]
    rw [this] at hgcd
    have hxg : x = (g : Int) := by omega
    rw [← hxg]; exact hav

theorem gcdish_run (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (fuel : Nat)
    (hf : b.toNat + 8 ≤ fuel) :
    runFunc StressProgram fuel "ops.py:<module>.gcdish" [.int a, .int b]
      = .val (.int ((Int.gcd a b : Nat) : Int)) := by
  obtain ⟨G, rfl⟩ : ∃ q, fuel = q + 6 := ⟨fuel - 6, by omega⟩
  have hG : b.toNat + 2 ≤ G := by omega
  rw [runFunc_of_resolve _ _ _ _ f_ops_py__module__gcdish rfl]
  have hinv : gcdInv (Int.gcd a b) b.toNat [] [("b", Val.int b), ("a", Val.int a)] := by
    exact ⟨rfl, a, b, ha, hb, Nat.le_refl _, rfl, by rfl, by rfl, by rfl, by rfl, by rfl⟩
  obtain ⟨h', ρ', hloop, hpost⟩ :=
    execStmt_loop_rule ctxS (.binop "!=" (.name "b") (.lit (.int 0)))
      (.seq (.assign "t" (.name "b"))
        (.seq (.assign "b" (.binop "%" (.name "a") (.name "b")))
              (.assign "a" (.name "t"))))
      5 (gcdInv (Int.gcd a b)) (gcdPost (Int.gcd a b)) (gcdish_step (Int.gcd a b))
      (G+4) b.toNat [] [("b", Val.int b), ("a", Val.int a)] hinv (by omega)
  obtain ⟨rfl, hav⟩ := hpost
  have hskip : execStmt ctxS (G+3) [] ρ' .skip = ([], .normal ρ') := execStmt_skip ctxS (G+2) [] _
  have hret : execStmt ctxS (G+3) [] ρ' (.ret (.name "a"))
      = ([], .ret (.int ((Int.gcd a b : Nat) : Int))) :=
    execStmt_ret_val ctxS (G+2) [] ρ' (evalExpr_name ctxS (G+1) [] ρ' "a" hav)
  have hbody : execStmt ctxS (G+5) [] [("b", Val.int b), ("a", Val.int a)]
        f_ops_py__module__gcdish.body
      = ([], .ret (.int ((Int.gcd a b : Nat) : Int))) := by
    simp only [f_ops_py__module__gcdish]
    rw [execStmt_seq_normal ctxS (G+4) [] _ hloop,
        execStmt_seq_normal ctxS (G+3) [] _ hskip,
        hret]
  simp only [f_ops_py__module__gcdish, ctxS] at hbody
  simp [applyFunc, bindParams, Func.posParams, kwargsRejected, f_ops_py__module__gcdish, Env.set, hbody]

theorem gcdish_refines :
    Refines₂ (α := Int) (β := Int) (γ := Int)
      StressProgram "ops.py:<module>.gcdish" 1000008
      (fun a b => 0 ≤ a ∧ 0 ≤ b ∧ b ≤ 1000000)
      (fun a b => ((Int.gcd a b : Nat) : Int)) := by
  rintro a b ⟨ha, hb, hbb⟩ fuel hf
  exact gcdish_run a b ha hb fuel (by omega)


/-! ### A heap-mutating method: `Counter` and `total`

The refinement layer's remaining gap was objects. This is the smallest program that has
all of it: a class with an `__init__` that binds a field, a `bump` method that **mutates
its receiver** and returns the new value, and a `total` function that constructs an
instance and calls the method once per element of a list.

The `Func` values are written out here rather than imported, in the same style as the
generated modules above (`Autoform/Generated/Cachetools.lean` has classes of this shape;
this one is kept minimal so the theorem is about the mechanism, not the library).

What makes the proof go through is `Represents counterRep h r a` — "address `r` holds a
`Counter` abstracting to the integer `a`" — plus the two rules of §3b. `bump_step` proves
one method call in full: receiver evaluation, argument evaluation, dynamic dispatch
through `resolveMethod`, field read, field write, and the return, ending in a heap that
`counter_set` shows still represents, now at `a + k`. `total_for_step` then feeds that to
`execFor_rule`, and the loop invariant is "the counter holds the sum of the elements
consumed so far".

One incidental discovery: `String.endsWith` does not reduce definitionally (it is defined
through `String.Slice` pattern matching), so `Ctx.resolveMethod` — which resolves a method
by *suffix* — cannot be discharged by `rfl` the way `Ctx.resolve` can on an exact name.
The `ew1`…`ew6` lemmas below are that obstacle made explicit. -/

def f_counter_init : Func :=
  { name := "cnt.py:<module>.Counter.__init__"
  , params := ["n0"]
  , body := (.seq (.setField (.name "self") "n" (.name "n0")) .skip) }

def f_counter_bump : Func :=
  { name := "cnt.py:<module>.Counter.bump"
  , params := ["k"]
  , body := (.seq
              (.setField (.name "self") "n"
                (.binop "+" (.field (.name "self") "n") (.name "k")))
              (.ret (.field (.name "self") "n"))) }

def f_counter_total : Func :=
  { name := "cnt.py:<module>.total"
  , params := ["xs"]
  , body := (.seq
              (.assign "c" (.alloc "Counter" [(.lit (.int 0))]))
              (.seq
                (.forIn "x" (.name "xs") (.expr (.mcall (.name "c") "bump" [(.name "x")])))
                (.ret (.field (.name "c") "n")))) }

def CounterProgram : Program :=
  { dialect := .python, funcs := [f_counter_init, f_counter_bump, f_counter_total] }

abbrev ctxT : Ctx := ctxOf CounterProgram

def counterRep : HeapRep Int :=
  { cls := "Counter"
  , abs := fun o => if o.captured = [] then
                      (match o.fields.find? (·.1 == "n") with
                       | some (_, .int i) => some i
                       | _                => none)
                    else none }

theorem counter_getField {h : Heap} {r : Ref} {a : Int}
    (hR : Represents counterRep h r a) : h.getField r "n" = .int a := by
  obtain ⟨o, ho, _, ha⟩ := hR
  simp only [counterRep] at ha
  simp only [Heap.getField, ho]
  by_cases hcap : o.captured = [] <;> simp only [hcap, if_true, if_false, if_neg, reduceIte] at ha
  · cases hf : o.fields.find? (·.1 == "n") with
    | none => rw [hf] at ha; simp at ha
    | some p =>
      obtain ⟨kk, w⟩ := p
      rw [hf] at ha
      cases w <;> simp at ha
      subst ha; rfl
  · simp at ha

theorem counter_set {h : Heap} {r : Ref} {a b : Int} (hR : Represents counterRep h r a) :
    Represents counterRep (h.setField r "n" (.int b)) r b := by
  obtain ⟨o, ho, hc, ha⟩ := hR
  have hcap : o.captured = [] := by
    by_cases hcap : o.captured = []
    · exact hcap
    · simp only [counterRep, if_neg hcap] at ha; simp at ha
  exact Represents.update ⟨o, ho, hc, ha⟩ ho (by simp [counterRep, hcap])

/-- Suffix facts, needed because `String.endsWith` does not reduce definitionally. -/
theorem ew1 : "cnt.py:<module>.Counter.__init__".endsWith ".Counter.bump" = false := by simp [String.endsWith]; decide
theorem ew2 : "cnt.py:<module>.Counter.bump".endsWith ".Counter.bump" = true := by simp [String.endsWith]; decide
theorem ew3 : "cnt.py:<module>.total".endsWith ".Counter.bump" = false := by simp [String.endsWith]; decide
theorem ew4 : "cnt.py:<module>.Counter.__init__".endsWith ".Counter.__init__" = true := by simp [String.endsWith]; decide
theorem ew5 : "cnt.py:<module>.Counter.bump".endsWith ".Counter.__init__" = false := by simp [String.endsWith]; decide
theorem ew6 : "cnt.py:<module>.total".endsWith ".Counter.__init__" = false := by simp [String.endsWith]; decide

theorem resolve_bump : ctxT.resolveMethod "Counter" "bump" = some f_counter_bump := by
  simp only [ctxT, ctxOf, CounterProgram, Ctx.resolveMethod, Program.table, List.map,
        f_counter_init, f_counter_bump, f_counter_total, List.filter]
  rw [show ("." ++ "Counter" ++ "." ++ "bump") = ".Counter.bump" from rfl, ew1, ew2, ew3]

theorem resolve_init : ctxT.resolveMethod "Counter" "__init__" = some f_counter_init := by
  simp only [ctxT, ctxOf, CounterProgram, Ctx.resolveMethod, Program.table, List.map,
        f_counter_init, f_counter_bump, f_counter_total, List.filter]
  rw [show ("." ++ "Counter" ++ "." ++ "__init__") = ".Counter.__init__" from rfl, ew4, ew5, ew6]



theorem counter_find {h : Heap} {r : Ref} {a : Int} (hR : Represents counterRep h r a) :
    ∃ o, h.get r = some o ∧ o.cls = "Counter" ∧
      o.fields.find? (·.1 == "n") = some ("n", .int a) ∧ o.captured = [] := by
  obtain ⟨o, ho, hc, ha⟩ := hR
  have hcap : o.captured = [] := by
    by_cases hcap : o.captured = []
    · exact hcap
    · simp only [counterRep, if_neg hcap] at ha; simp at ha
  simp only [counterRep, if_pos hcap] at ha
  refine ⟨o, ho, hc, ?_, hcap⟩
  cases hf : o.fields.find? (·.1 == "n") with
  | none => rw [hf] at ha; simp at ha
  | some p =>
    obtain ⟨kk, w⟩ := p
    have hk : kk = "n" := by
      have hp := List.find?_some hf
      simpa using hp
    rw [hf] at ha
    cases w <;> simp at ha
    subst ha; subst hk; rfl

/-- One `bump` call: the heap-mutating method dispatch, proved end to end. -/
theorem bump_step {h : Heap} {r : Ref} {acc iv : Int} {ρ : Env} (j : Nat)
    (hR : Represents counterRep h r acc)
    (hc : ρ.find? (·.1 == "c") = some ("c", .ref r))
    (hx : ρ.find? (·.1 == "x") = some ("x", .int iv)) :
    execStmt ctxT (j+8) h ρ (.expr (.mcall (.name "c") "bump" [(.name "x")]))
      = (h.setField r "n" (.int (acc + iv)), .normal ρ) := by
  obtain ⟨o, ho, hcls, hfind, hcap⟩ := counter_find hR
  obtain ⟨o', ho', hcls', hfind', hcap'⟩ := counter_find (counter_set (b := acc + iv) hR)
  have hslf : ([("k", Val.int iv), ("self", Val.ref r)] : Env).find? (·.1 == "self")
      = some ("self", .ref r) := by simp
  have hkk : ([("k", Val.int iv), ("self", Val.ref r)] : Env).find? (·.1 == "k")
      = some ("k", .int iv) := by simp
  have hfield : evalExpr ctxT (j+2) h [("k", Val.int iv), ("self", Val.ref r)]
        ((Expr.name "self").field "n") = (h, .val (.int acc)) :=
    evalExpr_field_obj ctxT (j+1) h _
      (evalExpr_name ctxT j h _ "self" hslf) ho hfind
  have hplus : evalExpr ctxT (j+3) h [("k", Val.int iv), ("self", Val.ref r)]
        (.binop "+" ((Expr.name "self").field "n") (.name "k"))
      = (h, .val (.int (acc + iv))) := by
    rw [evalExpr_binop_val ctxT (j+2) h _ "+" (by decide) (by decide)
          hfield (evalExpr_name ctxT (j+1) h _ "k" hkk)]
    simp [ctxT, ctxOf, CounterProgram]
  have hsf : execStmt ctxT (j+4) h [("k", Val.int iv), ("self", Val.ref r)]
        (.setField (.name "self") "n" (.binop "+" ((Expr.name "self").field "n") (.name "k")))
      = (h.setField r "n" (.int (acc + iv)), .normal [("k", Val.int iv), ("self", Val.ref r)]) :=
    execStmt_setField_val ctxT (j+3) h _
      (evalExpr_name ctxT (j+2) h _ "self" hslf) hplus
  have hret : execStmt ctxT (j+4) (h.setField r "n" (.int (acc + iv)))
        [("k", Val.int iv), ("self", Val.ref r)] (.ret ((Expr.name "self").field "n"))
      = (h.setField r "n" (.int (acc + iv)), .ret (.int (acc + iv))) :=
    execStmt_ret_val ctxT (j+3) _ _
      (evalExpr_field_obj ctxT (j+2) _ _
        (evalExpr_name ctxT (j+1) _ _ "self" hslf) ho' hfind')
  have hbody : execStmt ctxT (j+5) h [("k", Val.int iv), ("self", Val.ref r)]
        f_counter_bump.body
      = (h.setField r "n" (.int (acc + iv)), .ret (.int (acc + iv))) := by
    simp only [f_counter_bump]
    rw [execStmt_seq_normal ctxT (j+4) h _ hsf]
    exact hret
  have happ : applyFunc ctxT (j+6) h f_counter_bump (some (.ref r)) [Val.int iv] []
      = (h.setField r "n" (.int (acc + iv)), .val (.int (acc + iv))) := by
    rw [applyFunc_succ ctxT (j+5) h f_counter_bump (some (.ref r)) [Val.int iv] []]
    simp only [f_counter_bump, kwargsRejected_nil, posRejected_mk, Bool.false_or,
      List.length_cons, List.length_nil, Nat.lt_irrefl, decide_false,
      Bool.false_eq_true, if_false, bindParams_mk,
      List.zip, List.zipWith, List.foldl, Env.set] at hbody ⊢
    rw [hbody]
  have hmc : evalExpr ctxT (j+7) h ρ (.mcall (.name "c") "bump" [(.name "x")])
      = (h.setField r "n" (.int (acc + iv)), .val (.int (acc + iv))) := by
    rw [evalExpr_mcall_obj ctxT (j+6) h ρ
      (evalExpr_name ctxT (j+5) h ρ "c" hc)
      (evalList_cons_val ctxT (j+5) h ρ rfl (evalExpr_name ctxT (j+4) h ρ "x" hx)
        (evalList_nil ctxT (j+4) h ρ))
      ho hcap (by rw [hcls]; exact resolve_bump)]
    exact happ
  exact execStmt_expr_val ctxT (j+7) h ρ hmc

def isum : List Int → Int
  | []     => 0
  | a :: r => a + isum r

def totalInv (S : Int) (vs : List Val) (h : Heap) (ρ : Env) : Prop :=
  ∃ (ys : List Int) (acc : Int), vs = ys.map Val.int ∧ acc + isum ys = S ∧
    Represents counterRep h 0 acc ∧ ρ.find? (·.1 == "c") = some ("c", .ref 0)

theorem total_for_step (S : Int) :
    ∀ v vs h ρ k, 8 ≤ k → totalInv S (v :: vs) h ρ →
      ∃ h' ρ', execStmt ctxT k h (ρ.set "x" v)
          (.expr (.mcall (.name "c") "bump" [(.name "x")])) = (h', .normal ρ') ∧
        totalInv S vs h' ρ' := by
  intro v vs h ρ k hk hI
  obtain ⟨ys, acc, hys, hsum, hR, hc⟩ := hI
  obtain ⟨j, rfl⟩ : ∃ q, k = q + 8 := ⟨k - 8, by omega⟩
  cases ys with
  | nil => simp at hys
  | cons y ys' =>
    simp only [List.map_cons, List.cons.injEq] at hys
    obtain ⟨rfl, rfl⟩ := hys
    have hc' : (ρ.set "x" (Val.int y)).find? (·.1 == "c") = some ("c", .ref 0) := by
      simp [Env.set, hc]
    have hx' : (ρ.set "x" (Val.int y)).find? (·.1 == "x") = some ("x", .int y) := by
      simp [Env.set]
    refine ⟨h.setField 0 "n" (.int (acc + y)), ρ.set "x" (Val.int y),
      bump_step j hR hc' hx', ys', acc + y, rfl, ?_, counter_set hR, hc'⟩
    simp only [isum] at hsum
    omega

theorem total_run (ys : List Int) (fuel : Nat) (hf : ys.length + 13 ≤ fuel) :
    runFunc CounterProgram fuel "cnt.py:<module>.total" [.list (ys.map Val.int)]
      = .val (.int (isum ys)) := by
  obtain ⟨G, rfl⟩ : ∃ q, fuel = q + 13 := ⟨fuel - 13, by omega⟩
  have hG : ys.length ≤ G := by omega
  rw [runFunc_of_resolve _ _ _ _ f_counter_total rfl]
  -- allocation and __init__
  have hinitbody : execStmt ctxT (G+8) [{ cls := "Counter", fields := [], captured := [] }]
        [("n0", Val.int 0), ("self", Val.ref 0)] f_counter_init.body
      = ([{ cls := "Counter", fields := [("n", Val.int 0)], captured := [] }],
         .normal [("n0", Val.int 0), ("self", Val.ref 0)]) := by
    have hslf : ([("n0", Val.int 0), ("self", Val.ref 0)] : Env).find? (·.1 == "self")
        = some ("self", .ref 0) := by simp
    have hn0 : ([("n0", Val.int 0), ("self", Val.ref 0)] : Env).find? (·.1 == "n0")
        = some ("n0", .int 0) := by simp
    have hsf : execStmt ctxT (G+7) [{ cls := "Counter", fields := [], captured := [] }]
          [("n0", Val.int 0), ("self", Val.ref 0)]
          (.setField (.name "self") "n" (.name "n0"))
        = ([{ cls := "Counter", fields := [("n", Val.int 0)], captured := [] }],
           .normal [("n0", Val.int 0), ("self", Val.ref 0)]) :=
      execStmt_setField_val ctxT (G+6) _ _
        (evalExpr_name ctxT (G+5) _ _ "self" hslf)
        (evalExpr_name ctxT (G+5) _ _ "n0" hn0)
    simp only [f_counter_init]
    rw [execStmt_seq_normal ctxT (G+7) _ _ hsf]
    exact execStmt_skip ctxT (G+6) _ _
  have hinit : applyFunc ctxT (G+9) [{ cls := "Counter", fields := [], captured := [] }]
        f_counter_init (some (.ref 0)) [Val.int 0] []
      = ([{ cls := "Counter", fields := [("n", Val.int 0)], captured := [] }], .val .unit) := by
    rw [applyFunc_succ ctxT (G+8) _ f_counter_init (some (.ref 0)) [Val.int 0] []]
    simp only [f_counter_init, kwargsRejected_nil, posRejected_mk, Bool.false_or,
      List.length_cons, List.length_nil, Nat.lt_irrefl, decide_false,
      Bool.false_eq_true, if_false, bindParams_mk,
      List.zip, List.zipWith, List.foldl, Env.set] at hinitbody ⊢
    rw [hinitbody]
  have halloc : evalExpr ctxT (G+10) [] [("xs", Val.list (ys.map Val.int))]
        (.alloc "Counter" [(.lit (.int 0))])
      = ([{ cls := "Counter", fields := [("n", Val.int 0)], captured := [] }], .val (.ref 0)) := by
    have h := evalExpr_alloc_obj ctxT (G+9) [] [("xs", Val.list (ys.map Val.int))]
      (evalList_cons_val ctxT (G+8) [] _ rfl (evalExpr_lit_int ctxT (G+7) [] _ 0)
        (evalList_nil ctxT (G+7) [] _))
      (by intro c cap; simp [Env.get])
      (by simp [ctxT, ctxOf, CounterProgram, Ctx.builtinBase])
      resolve_init hinit
    simpa using h
  have hgc : (Env.get ([("xs", Val.list (ys.map Val.int))] : Env) ("<glob>" ++ "c")).truthy = false := by
    simp [Env.get, Val.truthy]
  have hassign : execStmt ctxT (G+11) [] [("xs", Val.list (ys.map Val.int))]
        (.assign "c" (.alloc "Counter" [(.lit (.int 0))]))
      = ([{ cls := "Counter", fields := [("n", Val.int 0)], captured := [] }],
         .normal [("c", Val.ref 0), ("xs", Val.list (ys.map Val.int))]) :=
    execStmt_assign_val ctxT (G+10) [] _ halloc hgc
  have hR0 : Represents counterRep
      [{ cls := "Counter", fields := [("n", Val.int 0)], captured := [] }] 0 0 := by
    refine ⟨_, rfl, rfl, ?_⟩
    simp [counterRep]
  have hcc : ([("c", Val.ref 0), ("xs", Val.list (ys.map Val.int))] : Env).find? (·.1 == "c")
      = some ("c", .ref 0) := by simp
  obtain ⟨h', ρ', hfor, hpost⟩ :=
    execFor_rule ctxT "x" (.expr (.mcall (.name "c") "bump" [(.name "x")])) 8
      (totalInv (isum ys)) (total_for_step (isum ys))
      (G+9) (ys.map Val.int) [{ cls := "Counter", fields := [("n", Val.int 0)], captured := [] }]
      [("c", Val.ref 0), ("xs", Val.list (ys.map Val.int))]
      ⟨ys, 0, rfl, by simp, hR0, hcc⟩ (by simp; omega)
  obtain ⟨zs, acc, hzs, hsum, hR', hc'⟩ := hpost
  have hacc : acc = isum ys := by
    cases zs with
    | nil => simp only [isum] at hsum; omega
    | cons a t => simp at hzs
  subst hacc
  obtain ⟨o', ho', hcls', hfind', hcap'⟩ := counter_find hR'
  have hforIn : execStmt ctxT (G+10)
        [{ cls := "Counter", fields := [("n", Val.int 0)], captured := [] }]
        [("c", Val.ref 0), ("xs", Val.list (ys.map Val.int))]
        (.forIn "x" (.name "xs") (.expr (.mcall (.name "c") "bump" [(.name "x")])))
      = (h', .normal ρ') := by
    rw [execStmt_forIn_val ctxT (G+9) _ _
      (evalExpr_name ctxT (G+8) _ _ "xs" (by simp)) (rfl : (Val.list (ys.map Val.int)).iterable = _)]
    exact hfor
  have hret : execStmt ctxT (G+10) h' ρ' (.ret ((Expr.name "c").field "n"))
      = (h', .ret (.int (isum ys))) :=
    execStmt_ret_val ctxT (G+9) _ _
      (evalExpr_field_obj ctxT (G+8) _ _ (evalExpr_name ctxT (G+7) _ _ "c" hc') ho' hfind')
  have hbody : execStmt ctxT (G+12) [] [("xs", Val.list (ys.map Val.int))] f_counter_total.body
      = (h', .ret (.int (isum ys))) := by
    simp only [f_counter_total]
    rw [execStmt_seq_normal ctxT (G+11) [] _ hassign,
        execStmt_seq_normal ctxT (G+10) _ _ hforIn]
    exact hret
  rw [applyFunc_succ ctxT (G+12) [] f_counter_total none [Val.list (ys.map Val.int)] []]
  simp only [f_counter_total, kwargsRejected_nil, posRejected_mk, Bool.false_or,
    List.length_cons, List.length_nil, Nat.lt_irrefl, decide_false,
    Bool.false_eq_true, if_false, bindParams_mk,
    List.zip, List.zipWith, List.foldl, Env.set] at hbody ⊢
  rw [hbody]

/-- The concrete run the project history records: `total([5,7,9]) = 21`, through object
construction, a heap-mutating method call per element, and a `for`-loop. -/
theorem total_21 :
    runFunc CounterProgram 20 "cnt.py:<module>.total" [.list [.int 5, .int 7, .int 9]]
      = .val (.int 21) := by
  have h := total_run [5, 7, 9] 20 (by simp)
  simpa [isum] using h

/-- …and in the `Refines` relation proper, so the non-vacuity theorems of §1 apply to it:
`total` provably reaches no hole and terminates within `|ys| + 13` fuel. -/
theorem total_refines (ys : List Int) :
    Refines CounterProgram "cnt.py:<module>.total" (ys.length + 13)
      (fun args => args = [.list (ys.map Val.int)])
      (fun _ => .ret (.int (isum ys))) := by
  rintro args rfl fuel hf
  exact total_run ys fuel hf

end Demo

/-! ## 5. Open obligations

Stated, not admitted. Nothing below is `sorry`ed; these are gaps in coverage, recorded
so they are visible in the ledger rather than papered over.

1. **General fuel monotonicity.** `evalExpr_pure_fuel_indep` covers the pure, call-free
   fragment. The full statement — for arbitrary `Expr`/`Stmt`,
   `evalExpr ctx k h ρ e = (h', r) → r ≠ .outOfFuel → evalExpr ctx (k+1) h ρ e = (h', r)`
   — needs a mutual induction over the five mutually recursive interpreter functions
   (`evalExpr`, `evalList`, `evalPairs`, `execStmt`, `execFor`) and is not proved here.
   The demonstrations do not depend on it: the `∀ k, P (k + N)` formulation makes each
   refinement theorem fuel-universal directly, and `refines_fuel_mono` derives
   monotonicity for refined functions as a corollary.

2. **Short-circuit `&&` / `||`.** `evalExpr_binop_val` is now
   split by strictness: `evalExpr_binop_val` carries `op ≠ "&&"` and `op ≠ "||"` side
   conditions, with `evalExpr_and_short` / `evalExpr_or_short` covering the other two
   cases. No demonstration here uses a boolean connective, so the short-circuit path is
   lemma-covered but not exercised end to end.

3. **Loops — closed.** `execStmt_loop_rule` is the while-rule: an invariant indexed by a
   termination measure that must strictly decrease, and a fuel bound `B + m + 1` derived
   from it. `execFor_rule` is its `for` counterpart, with the remaining sequence as the
   measure. Both are used: `sumto_run`/`sumto_refines` (C, `math.c`) prove
   `sumto n = n*(n+1)/2` on the no-overflow domain, and `gcdish_run`/`gcdish_refines`
   (Python, `ops.py`) prove `gcdish a b = Int.gcd a b` for nonnegative arguments, with
   `b.natAbs` as the measure. What is *not* closed: the fuel bound of a loop depends on
   its input, so a `Refines` instance — whose bound is a constant — needs a bounded
   domain (`n ≤ 65535`, `b ≤ 1000000` above). The parametric `_run` theorems are the sharp
   statements; making `Refines` carry an argument-dependent bound is the honest fix and is
   not done here.

4. **Heap-mutating methods — closed.** `HeapRep`/`Represents` is the representation
   predicate, with `Represents.frame` (a write to another address preserves it) and
   `Represents.update` (a write to this address re-establishes it) proved against the real
   `Heap.setField`. `bump_step` uses them to prove one dispatch of a method that mutates
   its receiver, and `total_run`/`total_21` put that inside a `for`-loop over a list:
   object construction, `__init__`, per-element heap mutation, and a final field read,
   `total [5,7,9] = 21`. What remains open is generality: `counterRep` abstracts a
   one-field object to an `Int`. A representation predicate for the *container* classes in
   `Generated/Cachetools.lean` needs boxed containers first (`Stmt.setIndex` is still
   `hole "setIndex:immutable-containers"`), so the separation-style frame reasoning here
   covers field-mutating objects only.

5. **Integer width — closed, and it changed the theorems.** `Numeric.lean` is now wired
   into `applyBinop`, so `.cLike` is 32-bit two's complement and `NumResult.ub` maps to
   `Expr.hole`. The C theorems accordingly carry representability domains
   (`poly_refines`), and `poly_not_refinable` proves that without them the claim is
   *false*, with the oracle's own witness `100000 * 100000`. What remains open is
   *inferring* those domains: `poly`'s three `fits32` conjuncts were written by hand, one
   per intermediate operation. Deriving them mechanically from the AST is the natural
   next piece of infrastructure.

6. **`applyUnop` bypasses `NumConfig`.** `applyUnop "-"` returns `.val (.int (-x))`
   without a width or overflow check (`applyUnop_int_neg`), so under `.cLike` the term
   `-INT_MIN` evaluates to the unrepresentable `2147483648` rather than wrapping or
   producing a hole — the exact class of silent-wrong-number defect `Numeric.lean` was
   built to remove, still present on the unary path. `absval` and `cmpchain` use unary
   minus but are Python, where the current behaviour is correct, so no theorem here is
   unsound because of it. **This needs a fix in `Semantics.lean`** (route `applyUnop` for
   `.int` through `NumConfig.neg`, with a `Dialect` parameter); it is not something this
   file can repair.
-/

end Autoform.Refine
