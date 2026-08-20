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
4. A genuine fuel-independence theorem for the pure expression fragment.
5. End-to-end refinement theorems for real translated functions from
   `Generated/CMath.lean` (C) and `Generated/Stress.lean`, `Generated/Sample.lean`
   (Python), including the dialect-sensitive division/modulo pair.
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

/-- `&&` does not evaluate its right operand once the left is falsy. -/
theorem evalExpr_and_short {a b : Expr} {h₁ : Heap} {x : Val}
    (ha : evalExpr ctx k h ρ a = (h₁, .val x)) (hx : x.truthy = false) :
    evalExpr ctx (k+1) h ρ (.binop "&&" a b) = (h₁, .val (.bool false)) := by
  simp [evalExpr, ha, hx]

/-- `||` does not evaluate its right operand once the left is truthy. -/
theorem evalExpr_or_short {a b : Expr} {h₁ : Heap} {x : Val}
    (ha : evalExpr ctx k h ρ a = (h₁, .val x)) (hx : x.truthy = true) :
    evalExpr ctx (k+1) h ρ (.binop "||" a b) = (h₁, .val (.bool true)) := by
  simp [evalExpr, ha, hx]

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
    evalList ctx (k+1) h ρ [] = (h, .inr []) := rfl

theorem evalList_cons_val {a : Expr} {as : List Expr} {h₁ h₂ : Heap} {v : Val}
    {vs : List Val}
    (ha : evalExpr ctx k h ρ a = (h₁, .val v))
    (has : evalList ctx k h₁ ρ as = (h₂, .inr vs)) :
    evalList ctx (k+1) h ρ (a :: as) = (h₂, .inr (v :: vs)) := by
  simp [evalList, ha, has]

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
theorem applyFunc_succ (fn : Func) (self? : Option Val) (vs : List Val) :
    applyFunc ctx (k+1) h fn self? vs =
      (let base : Env := match self? with | some s => [("self", s)] | none => []
       let ρ' := (fn.params.zip vs).foldl (fun e (x, v) => e.set x v) base
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
def ctxOf (p : Program) : Ctx := { dialect := p.dialect, table := p.table }

/-- Entry-point resolution, factored out. Every demonstration below discharges its
`resolve` side condition by `rfl` — name resolution on a concrete program is decidable
by computation, so it never becomes a proof obligation. -/
theorem runFunc_of_resolve (p : Program) (fuel : Nat) (name : String) (args : List Val)
    (fn : Func) (hres : (ctxOf p).resolve name = some fn) :
    runFunc p fuel name args = (applyFunc (ctxOf p) fuel [] fn none args).2 := by
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

/-! ## 4. End-to-end: real translated functions

Entry points are named by their **fully-qualified CPG name** (`ops.py:<module>.absval`,
not `absval`). `Ctx.resolve` will also accept the short name via suffix matching, but that
is documented in `Semantics.lean` as a heuristic, and a refinement theorem should not
depend on a heuristic to decide which function it is about.

Every theorem below is about a `Func` emitted by `cartographer/render_lean.py` from a
Joern code property graph — the deep terms in `Autoform/Generated/`, unmodified. -/

namespace Demo

/-! ### Verbatim copy of `Autoform/Generated/CMath.lean` (C, from `math.c`)`

Copied rather than imported: each generated module declares
`Autoform.Generated.program`, so no two of them can be imported into the same file.
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

Copied rather than imported: each generated module declares
`Autoform.Generated.program`, so no two of them can be imported into the same file.
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
  simp [applyFunc, execStmt, evalExpr, Env.set, Env.get, f_poly, ctxOf,
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
  simp only [applyFunc, execStmt, evalExpr, Env.set, Env.get, f_poly, ctxOf, CMathProgram]
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
  · simp [applyFunc, execStmt, evalExpr, Env.set, Env.get, f_clamp, ctxOf,
          CMathProgram, Marshal.toVal, Val.truthy, applyBinop_int_lt, h1]
  · by_cases h2 : hi < x
    · simp [applyFunc, execStmt, evalExpr, Env.set, Env.get, f_clamp, ctxOf,
            CMathProgram, Marshal.toVal, Val.truthy, applyBinop_int_lt, applyBinop_int_gt,
            h1, h2]
    · simp [applyFunc, execStmt, evalExpr, Env.set, Env.get, f_clamp, ctxOf,
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
    simp [applyFunc, execStmt, evalExpr, Env.set, Env.get, f_cdiv, ctxOf,
          CMathProgram, Marshal.toVal, Val.truthy, applyBinop_int_eq]
  · simp [applyFunc, execStmt, evalExpr, Env.set, Env.get, f_cdiv, ctxOf,
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
  simp [applyFunc, execStmt, evalExpr, Env.set, Env.get, f_lib_py__module__add, ctxOf,
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
  · simp [applyFunc, execStmt, evalExpr, Env.set, Env.get, applyUnop_int_neg,
          f_ops_py__module__absval, ctxOf, StressProgram, Marshal.toVal, Val.truthy,
          applyBinop_int_lt, h1]
  · simp [applyFunc, execStmt, evalExpr, Env.set, Env.get,
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
  · simp [applyFunc, execStmt, evalExpr, Env.set, Env.get, applyUnop_int_neg,
          f_ops_py__module__cmpchain, ctxOf, StressProgram, Marshal.toVal, Val.truthy,
          applyBinop_int_lt, h1]
  · by_cases h2 : y < x
    · simp [applyFunc, execStmt, evalExpr, Env.set, Env.get,
            f_ops_py__module__cmpchain, ctxOf, StressProgram, Marshal.toVal, Val.truthy,
            applyBinop_int_lt, applyBinop_int_gt, h1, h2]
    · simp [applyFunc, execStmt, evalExpr, Env.set, Env.get,
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
    simp [applyFunc, execStmt, evalExpr, Env.set, Env.get, f_ops_py__module__fmod, ctxOf,
          StressProgram, Marshal.toVal, Val.truthy, applyBinop_int_eq]
  · simp [applyFunc, execStmt, evalExpr, Env.set, Env.get, f_ops_py__module__fmod, ctxOf,
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
    simp [applyFunc, execStmt, evalExpr, Env.set, Env.get, f_ops_py__module__fdiv, ctxOf,
          StressProgram, Marshal.toVal, Val.truthy, applyBinop_int_eq]
  · simp [applyFunc, execStmt, evalExpr, Env.set, Env.get, f_ops_py__module__fdiv, ctxOf,
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
  simp [applyFunc, execStmt, evalExpr, evalList, Env.set,
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

3. **Loops.** `sumto` (C) and `gcdish` (Python) are hole-free but contain `Stmt.loop`.
   Refining them needs a loop-invariant lemma relating `execStmt ctx k h ρ (.loop c body)`
   to a shallow `Nat`-recursive function together with a decreasing measure. The
   single-step lemma `execStmt_loop_step` is the base for it; the invariant rule is not
   built.

4. **Heap-allocating functions.** `evalExpr_pure_heap_inert` establishes heap inertness
   only for the pure fragment. Refining a method that mutates fields needs a
   representation predicate relating a `Heap` region to a shallow record — the standard
   separation-style story — which is not started.

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
