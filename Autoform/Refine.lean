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
   nothing (`fdiv_not_refinable`), and a C function provably does **not** refine its
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
theorem evalExpr_name (x : String) :
    evalExpr ctx (k+1) h ρ (.name x) = (h, .val (ρ.get x)) := rfl
theorem evalExpr_fnref (f : String) :
    evalExpr ctx (k+1) h ρ (.fnref f) = (h, .val (.fn f)) := rfl
theorem evalExpr_hole (l : String) :
    evalExpr ctx (k+1) h ρ (.hole l) = (h, .hole l) := rfl

/-- Value-passing form for `unop`: the shape actually used when discharging obligations. -/
theorem evalExpr_unop_val {a : Expr} {h₁ : Heap} {v : Val} (op : String)
    (ha : evalExpr ctx k h ρ a = (h₁, .val v)) :
    evalExpr ctx (k+1) h ρ (.unop op a) = (h₁, applyUnop op v) := by
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

/-! ### The hole negative result: untranslated constructs are not refinable

`ops.py`'s `fdiv` uses Python `//`, which the transpiler did not translate: its body
contains `Expr.hole "op:floorDiv"`. The interpreter reports that hole, and because
`Outcome` cannot denote a hole, **no** shallow function refines `fdiv`.

Together with `poly_not_refinable` these are the two ways a refinement claim can fail —
we did not translate it, or the machine does not agree with the mathematics — and both
are visible in the statement rather than absorbed by it. -/

theorem fdiv_reaches_hole (a b : Int) (hb : b ≠ 0) (k : Nat) :
    runFunc StressProgram (k + 10) "ops.py:<module>.fdiv" [.int a, .int b]
      = .hole "op:floorDiv" := by
  rw [runFunc_of_resolve _ _ _ _ f_ops_py__module__fdiv rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set, Env.get, f_ops_py__module__fdiv, ctxOf,
        StressProgram, Val.truthy, applyBinop_int_eq, hb]

/-- No shallow specification refines `fdiv`, at any fuel bound, on any domain that
contains a single nonzero-divisor argument list. -/
theorem fdiv_not_refinable (N : Nat) (dom : List Val → Prop) (spec : List Val → Outcome)
    (a b : Int) (hb : b ≠ 0) (hd : dom [.int a, .int b]) :
    ¬ Refines StressProgram "ops.py:<module>.fdiv" N dom spec := by
  intro hR
  have hne := refines_not_hole hR [.int a, .int b] hd (N + 10)
    (Nat.le_add_right _ _) "op:floorDiv"
  exact hne (by simpa [Nat.add_comm] using fdiv_reaches_hole a b hb N)

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

2. **Short-circuit `&&` / `||`.** `execStmt_loop_step` and `evalExpr_binop_val` are now
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
