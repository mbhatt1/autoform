import Autoform.Refine
import Autoform.Generated.CMath

/-!
# Overflow — inferring representability domains from the AST

`Autoform/Refine.lean` §5 records an open obligation:

> `poly`'s three `fits32` conjuncts were written by hand, one per intermediate
> operation. Deriving them mechanically from the AST is the natural next piece of
> infrastructure.

This file closes it. It builds a static analysis

    Expr  ──conds──▶  List Expr        (the representability obligations)
    Stmt  ──analyze──▶ Analysis        (obligations + symbolic store + completeness)
    Func  ──analyze──▶ Analysis        (obligations in terms of the parameters)

together with a **soundness theorem**: if the generated obligations hold, evaluating the
expression agrees with its exact mathematical value — in particular it is never
`EResult.hole "ub:…"`. An unproved generator would be a heuristic, and would reintroduce
exactly the silent wrongness the `ub ↦ hole` mapping exists to prevent.

## The shape of an obligation

An obligation is itself an `Expr`. It denotes "the **exact mathematical** value of this
expression is representable in the target type". That representation was chosen for three
reasons:

* it needs no new syntax, so obligations can be substituted, printed and compared with
  the machinery `Syntax.lean` already has;
* it is *per intermediate operation*, which is the load-bearing granularity — `a*b` can
  overflow while `a*b + c - a` is representable, so a blanket condition on the result
  would be wrong (`poly_not_refinable` is the proof);
* the exact-value semantics `exact` is a separate, obviously-correct function, so the
  generated domain is readable as mathematics rather than as machine arithmetic.

## Which operations contribute

Read off `Numeric.lean`, which is precise about who can produce `ub`/`trap`/`divZero`:

| node | contributes | why |
|---|---|---|
| `a + b`, `a - b`, `a * b` | `fits (a ⊕ b)` | `finish` on the exact result |
| `- a` | `fits (-a)` | `neg` is `finish (-a)`; `-INT_MIN` is the case |
| `a / b` | `fits (a / b)` | `div` is `finish (quot a b)`; `INT_MIN / -1` |
| `a % b` | `fits (a / b)`, `fits (a % b)` | `mod` checks the **quotient**, then wraps the remainder |
| `<`,`<=`,`>`,`>=`,`==`,`!=` | nothing | comparisons are width-independent (`Refine.applyBinop_int_lt` &c.) |
| `!` | nothing | boolean |

Shifts (`shl`/`shr`) and the bitwise operators are *not* in `applyBinop`'s vocabulary at
all — `Core` has no `<<`/`>>`/`&` operator strings — so they cannot occur in a translated
program and the analysis marks any other operator as *incomplete* rather than clean.

## Discipline

Total functions only: no `sorry`, no `partial`, no `unsafe`, no `native_decide`.
-/

namespace Autoform.Overflow

open Autoform.Core
open Autoform.Refine

/-! ## 1. Exact (mathematical) evaluation

`exact` is the model the machine is being compared against. It is deliberately *not*
`evalExpr`: it never wraps, never traps and never produces a hole. It is partial
(`Option`) on purpose — outside the arithmetic fragment there is nothing to say, and
returning a plausible value there is the defect class this project exists to remove.

The only configuration-dependence is division rounding (`quot`/`rem`), which is the §12
dialect parameter. Division by zero is `none`: that is an *exception* in the machine
semantics, not a number, so no exact value corresponds to it. -/

/-- Exact value of a binary operator applied to two integers, mathematically. -/
def binExact (c : NumConfig) (op : String) (x y : Int) : Option Val :=
  match op with
  | "+"  => some (.int (x + y))
  | "-"  => some (.int (x - y))
  | "*"  => some (.int (x * y))
  | "/"  => if y = 0 then none else some (.int (c.quot x y))
  | "%"  => if y = 0 then none else some (.int (c.rem x y))
  | "<"  => some (.bool (decide (x < y)))
  | "<=" => some (.bool (decide (x ≤ y)))
  | ">"  => some (.bool (decide (y < x)))
  | ">=" => some (.bool (decide (y ≤ x)))
  | "==" => some (.bool (x == y))
  | "!=" => some (.bool (!(x == y)))
  | _    => none

/-- Exact evaluation of the analysable fragment: integer and boolean literals, locals
bound to integers or booleans, the arithmetic/relational binary operators, unary minus
and boolean negation. Everything else is `none`. -/
def exact (c : NumConfig) (ρ : Env) : Expr → Option Val
  | .lit (.int i)  => some (.int i)
  | .lit (.bool b) => some (.bool b)
  | .name x        =>
      match ρ.find? (·.1 == x) with
      | some (_, .int i)  => some (.int i)
      | some (_, .bool b) => some (.bool b)
      | _                 => none
  | .binop op a b =>
      match exact c ρ a, exact c ρ b with
      | some (.int x), some (.int y) => binExact c op x y
      | _, _ => none
  | .unop op a =>
      match op, exact c ρ a with
      | "-", some (.int x)  => some (.int (-x))
      | "!", some (.bool b) => some (.bool (!b))
      | _, _ => none
  | _ => none

/-! ## 2. Obligation generation -/

/-- The obligations a single operator *node* contributes, given its already-substituted
operands. One entry per way `Numeric.lean` can reach `finish` with a value that might not
be representable. `%` contributes two: `mod` gates on the **quotient** (that is what makes
`INT_MIN % -1` undefined even though the remainder is `0`) and then wraps the remainder. -/
def nodeConds (op : String) (a b : Expr) : List Expr :=
  match op with
  | "+" | "-" | "*" => [.binop op a b]
  | "/"             => [.binop "/" a b]
  | "%"             => [.binop "/" a b, .binop "%" a b]
  | _               => []

/-- All representability obligations of an expression, in **evaluation order**:
sub-obligations of the left operand, then the right, then the node's own. -/
def conds : Expr → List Expr
  | .binop op a b => conds a ++ conds b ++ nodeConds op a b
  | .unop op a    => conds a ++ (match op with | "-" => [Expr.unop "-" a] | _ => [])
  | _             => []

/-- Is this expression inside the analysable fragment? `conds` is only *meaningful* for
these; outside them the analysis reports incompleteness rather than an empty domain. -/
def supported : Expr → Bool
  | .lit (.int _)  => true
  | .lit (.bool _) => true
  | .name _        => true
  | .binop op a b  =>
      (op == "+" || op == "-" || op == "*" || op == "/" || op == "%" ||
       op == "<" || op == "<=" || op == ">" || op == ">=" || op == "==" || op == "!=")
      && supported a && supported b
  | .unop op a     => (op == "-" || op == "!") && supported a
  | _              => false

/-! ## 3. Substitution: obligations in terms of the *parameters*

Straight-line code introduces temporaries. `t = a*b; return t + c` must produce
`fits (a*b)` and `fits (a*b + c)`, not `fits (t + c)` — the latter mentions a name the
caller cannot see. A symbolic store maps each assigned local to an expression over the
parameters, and obligations are generated after substitution. -/

/-- A symbolic store: local name ↦ expression over the parameters. -/
abbrev Store := List (String × Expr)

/-- Substitute a symbolic store through the arithmetic fragment. Non-fragment nodes are
left alone: the analysis marks them incomplete, so no obligation depends on them. -/
def substE (σ : Store) : Expr → Expr
  | .name x => match σ.find? (·.1 == x) with
               | some (_, e) => e
               | none        => .name x
  | .binop op a b => .binop op (substE σ a) (substE σ b)
  | .unop op a    => .unop op (substE σ a)
  | e => e

/-! ## 4. Statements and functions -/

/-- The result of analysing a statement.

`complete` is the honesty flag, and it is the reason this is an analysis rather than a
guess. `false` means "this statement contains a construct whose obligations I did not
enumerate" — a loop, a call, a heap write, a hole. A domain generated from an incomplete
analysis is **not** claimed sufficient, and the soundness theorem does not apply to it. -/
structure Analysis where
  /-- Representability obligations, expressed over the parameters, in evaluation order. -/
  conds    : List Expr
  /-- Symbolic store after the statement. -/
  store    : Store
  /-- Did the analysis enumerate *every* obligation of this statement? -/
  complete : Bool
  deriving Repr, Inhabited

/-- Obligations of an expression under a store, with the fragment check. -/
def exprAnalysis (σ : Store) (e : Expr) : List Expr × Bool :=
  let e' := substE σ e
  (conds e', supported e')

/-- Analyse a statement. Branch handling is the conservative union: an `ifte` executes
only one arm, so requiring the obligations of *both* is sound and never misses one. If an
arm assigns, the two stores cannot be merged without a join lattice, so the analysis
reports incompleteness instead of inventing one. -/
def analyzeStmt (σ : Store) : Stmt → Analysis
  | .skip        => { conds := [], store := σ, complete := true }
  | .expr e      => let (cs, ok) := exprAnalysis σ e
                    { conds := cs, store := σ, complete := ok }
  | .ret e       => let (cs, ok) := exprAnalysis σ e
                    { conds := cs, store := σ, complete := ok }
  | .assign x e  => let (cs, ok) := exprAnalysis σ e
                    { conds := cs, store := (x, substE σ e) :: σ, complete := ok }
  | .seq a b     =>
      let ra := analyzeStmt σ a
      let rb := analyzeStmt ra.store b
      { conds := ra.conds ++ rb.conds, store := rb.store,
        complete := ra.complete && rb.complete }
  | .ifte c t e  =>
      let (cc, okc) := exprAnalysis σ c
      let rt := analyzeStmt σ t
      let re := analyzeStmt σ e
      -- Stores are merged only when neither arm wrote anything.
      let joined := rt.store.length == σ.length && re.store.length == σ.length
      { conds := cc ++ rt.conds ++ re.conds, store := σ,
        complete := okc && rt.complete && re.complete && joined }
  | .brk | .cont => { conds := [], store := σ, complete := true }
  | .declGlobal _ => { conds := [], store := σ, complete := true }
  | _            =>
      -- Loops, calls, heap writes, exceptions, globals, holes: not enumerated.
      { conds := [], store := σ, complete := false }

/-- Analyse a function. The initial store is empty, so parameter names stand for
themselves and every generated obligation is an expression over the parameters. -/
def analyzeFunc (f : Func) : Analysis := analyzeStmt [] f.body

/-! ## 5. The generated domain, as a proposition -/

/-- "The exact mathematical value of `e` under `ρ` exists and is representable." -/
def Fits (c : NumConfig) (ρ : Env) (e : Expr) : Prop :=
  ∃ i : Int, exact c ρ e = some (.int i) ∧ c.type.inRange i = true

/-- The generated domain: every obligation holds. A right-nested conjunction, so it reads
exactly like the hand-written domains in `Refine.lean`. -/
def CondsHold (c : NumConfig) (ρ : Env) : List Expr → Prop
  | []      => True
  | e :: es => Fits c ρ e ∧ CondsHold c ρ es

theorem condsHold_append (c : NumConfig) (ρ : Env) (xs ys : List Expr) :
    CondsHold c ρ (xs ++ ys) ↔ CondsHold c ρ xs ∧ CondsHold c ρ ys := by
  induction xs with
  | nil => simp [CondsHold]
  | cons x xs ih => simp [CondsHold, ih, and_assoc]

/-- The environment a call to `f` starts in. -/
def paramEnv (f : Func) (args : List Val) : Env := f.params.zip args

/-- **The generated domain of a function.** This is the thing that replaces a hand-written
`dom`. -/
def Domain (c : NumConfig) (f : Func) (args : List Val) : Prop :=
  CondsHold c (paramEnv f args) (analyzeFunc f).conds

/-! ## 6. Soundness

The obligations are not a heuristic. If they hold, machine evaluation of the expression
*equals* its exact mathematical value — hence in particular is not `.hole "ub:…"`.

The proof is by induction on fuel (not on `Expr`): `evalExpr` decrements fuel at every
node, so fuel dominating the expression's depth is exactly the induction measure, and it
sidesteps the nested-inductive recursor for `List Expr`. -/

/-- Nesting depth: the fuel `evalExpr` needs for the fragment. -/
def depth : Expr → Nat
  | .binop _ a b => 1 + depth a + depth b
  | .unop _ a    => 1 + depth a
  | _            => 1

theorem depth_pos (e : Expr) : 0 < depth e := by
  cases e <;> simp [depth] <;> omega

/-! ### Operator-level agreement -/

theorem finish_of_inRange {c : NumConfig} {x : Int} (h : c.type.inRange x = true) :
    c.finish x = .ok x := by simp [NumConfig.finish, h]


/-- The node obligations of `op`, read at concrete integer operands. Compare
`Numeric.lean`: `+`/`-`/`*` gate on `finish` of the exact result, `/` additionally needs a
nonzero divisor (zero is an *exception*, not a number), and `%` gates on the **quotient**
as well as the remainder — which is why `INT_MIN % -1` is undefined in C even though the
remainder `0` is perfectly representable. -/
def nodeOK (c : NumConfig) (op : String) (x y : Int) : Prop :=
  match op with
  | "+" => c.type.inRange (x + y) = true
  | "-" => c.type.inRange (x - y) = true
  | "*" => c.type.inRange (x * y) = true
  | "/" => y ≠ 0 ∧ c.type.inRange (c.quot x y) = true
  | "%" => y ≠ 0 ∧ c.type.inRange (c.quot x y) = true ∧ c.type.inRange (c.rem x y) = true
  | _   => True

/-- **Operator soundness.** Under its node obligations, every fragment binary operator
computes exactly what `binExact` says — no wrap, no trap, no `ub`. This is where
`Numeric.lean`'s four-way case analysis is discharged: the obligation makes the
non-`ok` branches of `finish` unreachable. -/
theorem applyBinop_agrees {d : Dialect} {op : String} {x y : Int} {v : Val}
    (hb : binExact d.toNumConfig op x y = some v)
    (hn : nodeOK d.toNumConfig op x y) :
    applyBinop d op (.int x) (.int y) = .val v := by
  unfold binExact at hb
  split at hb <;> simp only [nodeOK] at hn
  · cases hb
    simp [applyBinop, NumConfig.add, finish_of_inRange hn, numToE]
  · cases hb
    simp [applyBinop, NumConfig.sub, finish_of_inRange hn, numToE]
  · cases hb
    simp [applyBinop, NumConfig.mul, finish_of_inRange hn, numToE]
  · obtain ⟨hy, hq⟩ := hn
    simp only [hy, if_false, reduceIte] at hb
    cases hb
    simp [applyBinop, NumConfig.div, finish_of_inRange hq, numToE, hy]
  · obtain ⟨hy, hq, hr⟩ := hn
    simp only [hy, if_false, reduceIte] at hb
    cases hb
    simp [applyBinop, NumConfig.mod, numToE, hy, hq, IntType.wrap_of_inRange hr]
  · cases hb; simp [applyBinop, numToE]
  · cases hb; simp [applyBinop, numToE]
  · cases hb; simp [applyBinop, numToE]
  · cases hb; simp [applyBinop, numToE]
  · cases hb; exact applyBinop_int_eq d x y
  · cases hb; exact applyBinop_int_ne d x y
  · exact absurd hb (by simp)

/-- The generated obligations of a node really do imply `nodeOK` at the operands' exact
values. This is the link between the syntactic analysis and the semantic side condition. -/
theorem nodeOK_of_condsHold {c : NumConfig} {ρ : Env} {op : String} {a b : Expr}
    {x y : Int}
    (ha : exact c ρ a = some (.int x)) (hbv : exact c ρ b = some (.int y))
    (hc : CondsHold c ρ (nodeConds op a b)) : nodeOK c op x y := by
  have hex : ∀ o : String, exact c ρ (.binop o a b) = binExact c o x y := by
    intro o; simp [exact, ha, hbv]
  unfold nodeConds at hc
  split at hc
  · -- "+" / "-" / "*" : one obligation, the node itself
    obtain ⟨⟨i, hi, hr⟩, -⟩ := hc
    rw [hex] at hi; simp [binExact] at hi
    simpa [nodeOK, ← hi] using hr
  · obtain ⟨⟨i, hi, hr⟩, -⟩ := hc
    rw [hex] at hi; simp [binExact] at hi
    simpa [nodeOK, ← hi] using hr
  · obtain ⟨⟨i, hi, hr⟩, -⟩ := hc
    rw [hex] at hi; simp [binExact] at hi
    simpa [nodeOK, ← hi] using hr
  · -- "/" : the quotient must exist (nonzero divisor) and be representable
    obtain ⟨⟨i, hi, hr⟩, -⟩ := hc
    rw [hex] at hi
    simp only [binExact] at hi
    split at hi
    · exact absurd hi (by simp)
    · rename_i hy
      cases hi
      exact ⟨hy, hr⟩
  · -- "%" : quotient *and* remainder
    obtain ⟨⟨i, hi, hr⟩, ⟨j, hj, hs⟩, -⟩ := hc
    rw [hex] at hi
    rw [hex] at hj
    simp only [binExact] at hi hj
    split at hi
    · exact absurd hi (by simp)
    · rename_i hy
      cases hi
      split at hj
      · exact absurd hj (by simp)
      · cases hj
        exact ⟨hy, hr, hs⟩
  · -- comparisons and unknown operators contribute nothing
    simp only [nodeOK]

/-- Unary minus, likewise: `neg` is `finish (-x)` (§21), so it needs its own obligation. -/
theorem applyUnop_neg_agrees {d : Dialect} {x : Int}
    (h : (d.toNumConfig).type.inRange (-x) = true) :
    applyUnop d "-" (.int x) = .val (.int (-x)) := by
  simp [applyUnop, NumConfig.neg, finish_of_inRange h, numToE]

/-! ### The main theorem

Induction is on **fuel**, not on `Expr`: `evalExpr` burns one unit per node, so "fuel at
least the depth" is precisely the induction measure, and it avoids needing the nested
recursor for `List Expr`. -/

theorem exact_sound (ctx : Ctx) (h : Heap) (ρ : Env) :
    ∀ (n : Nat) (e : Expr) (v : Val),
      depth e ≤ n →
      exact ctx.dialect.toNumConfig ρ e = some v →
      CondsHold ctx.dialect.toNumConfig ρ (conds e) →
      evalExpr ctx n h ρ e = (h, .val v) := by
  intro n
  induction n with
  | zero => intro e v hd; exact absurd hd (by have := depth_pos e; omega)
  | succ m ih =>
    intro e v hd hex hc
    match e with
    | .lit (.int i)  => cases hex; simp [evalExpr]
    | .lit (.bool b) => cases hex; simp [evalExpr]
    | .lit (.str _)  => exact absurd hex (by simp [exact])
    | .lit .unit     => exact absurd hex (by simp [exact])
    | .name x =>
        simp only [exact] at hex
        split at hex
        · cases hex; simp [evalExpr, *]
        · cases hex; simp [evalExpr, *]
        · exact absurd hex (by simp)
    | .unop op a =>
        simp only [exact] at hex
        split at hex
        · rename_i _ x hxa
          cases hex
          have hda : depth a ≤ m := by simp only [depth] at hd; omega
          have hsp := (condsHold_append _ _ _ _).1 (by simpa only [conds] using hc)
          obtain ⟨⟨i, hi, hr⟩, -⟩ := hsp.2
          simp only [exact, hxa, Option.some.injEq, Val.int.injEq] at hi
          subst hi
          simp [evalExpr, ih a (.int x) hda hxa hsp.1, applyUnop_neg_agrees hr]
        · rename_i _ b hxa
          cases hex
          have hda : depth a ≤ m := by simp only [depth] at hd; omega
          have hca : CondsHold ctx.dialect.toNumConfig ρ (conds a) :=
            ((condsHold_append _ _ _ _).1 (by simpa only [conds] using hc)).1
          simp [evalExpr, ih a (.bool b) hda hxa hca, applyUnop, Val.truthy]
        · exact absurd hex (by simp)
    | .binop op a b =>
        simp only [exact] at hex
        split at hex
        · rename_i _ _ x y hxa hxb
          simp only [depth] at hd
          have hda : depth a ≤ m := by omega
          have hdb : depth b ≤ m := by omega
          have hsplit := (condsHold_append _ _ _ _).1 (by simpa only [conds] using hc)
          have hsplit2 := (condsHold_append _ _ _ _).1 hsplit.1
          have hea := ih a (.int x) hda hxa hsplit2.1
          have heb := ih b (.int y) hdb hxb hsplit2.2
          have hn := nodeOK_of_condsHold hxa hxb hsplit.2
          have hop := applyBinop_agrees (d := ctx.dialect) hex hn
          have hne1 : ¬ (op = "&&") := by
            rintro rfl; exact absurd hex (by simp [binExact])
          have hne2 : ¬ (op = "||") := by
            rintro rfl; exact absurd hex (by simp [binExact])
          simp [evalExpr, hea, heb, hne1, hne2, hop]
        · exact absurd hex (by simp)
    | .call _ _ | .index _ _ | .field _ _ | .mcall _ _ _ | .alloc _ _
    | .fnref _ | .closure _ | .classClosure _ | .listE _ | .tupleE _
    | .dictE _ | .cond _ _ _ | .isOp _ _ _ | .inOp _ _ _ | .hole _ =>
        exact absurd hex (by simp [exact])

/-! ### The corollary that matters

`ub` becomes `EResult.hole "ub:…"` (`Semantics.numToE`). The generated obligations rule
that out — which is the whole content of "the analysis is sound rather than heuristic". -/

/-- **No undefined behaviour.** Under its generated obligations, an analysable expression
never evaluates to a hole. -/
theorem no_ub_of_condsHold (ctx : Ctx) (h : Heap) (ρ : Env) (n : Nat) (e : Expr) (v : Val)
    (hd : depth e ≤ n)
    (hex : exact ctx.dialect.toNumConfig ρ e = some v)
    (hc : CondsHold ctx.dialect.toNumConfig ρ (conds e)) :
    ∀ s, (evalExpr ctx n h ρ e).2 ≠ .hole s := by
  intro s
  rw [exact_sound ctx h ρ n e v hd hex hc]
  simp

/-- …and never runs out of fuel, and never raises. Together with `exact_sound` this says
the generated domain is a *sufficient* condition for the deep term to agree with its
mathematical model, which is exactly what `Refines.dom` is asked to supply. -/
theorem terminates_of_condsHold (ctx : Ctx) (h : Heap) (ρ : Env) (n : Nat) (e : Expr)
    (v : Val) (hd : depth e ≤ n)
    (hex : exact ctx.dialect.toNumConfig ρ e = some v)
    (hc : CondsHold ctx.dialect.toNumConfig ρ (conds e)) :
    (evalExpr ctx n h ρ e).2 ≠ .outOfFuel ∧ (∀ w, (evalExpr ctx n h ρ e).2 ≠ .exn w) := by
  rw [exact_sound ctx h ρ n e v hd hex hc]
  exact ⟨by simp, by intro w; simp⟩

/-! ## 7. Demonstration on the real translated functions

`Autoform/Refine.lean` re-declares `CMath`'s functions locally; this file imports it and
uses those same terms, so the comparison is against the very AST the hand-written
theorems were proved about. -/

section CMath

open Autoform.Refine Autoform.Refine.Demo

/-- The 32-bit signed C configuration the `.cLike` dialect denotes. -/
abbrev cfg : NumConfig := Dialect.toNumConfig .cLike

theorem cfg_type : cfg.type = .signed .w32 := rfl

/-! ### `poly` — the three hand-written conjuncts, generated

The analysis produces exactly three obligations, one per arithmetic node, in evaluation
order — which is the granularity the hand-written domain used, and the granularity
`poly_not_refinable` shows is necessary. -/

/-- The generated obligations for `poly`, as a syntactic identity. -/
theorem poly_conds :
    (analyzeFunc f_poly).conds =
      [ .binop "*" (.name "a") (.name "b")
      , .binop "+" (.binop "*" (.name "a") (.name "b")) (.name "c")
      , .binop "-" (.binop "+" (.binop "*" (.name "a") (.name "b")) (.name "c"))
                   (.name "a") ] := rfl

/-- The analysis reports itself complete on `poly`. -/
theorem poly_complete : (analyzeFunc f_poly).complete = true := rfl

/-- **The generated domain is exactly the hand-written one.** This is the obligation
`Refine.lean` §5 left open, discharged as an `Iff` rather than asserted. -/
theorem poly_domain_eq (a b c : Int) :
    Domain cfg f_poly [.int a, .int b, .int c]
      ↔ (fits32 (a * b) ∧ fits32 (a * b + c) ∧ fits32 (a * b + c - a)) := by
  simp [Domain, paramEnv, f_poly, analyzeFunc, analyzeStmt, exprAnalysis, substE,
        conds, nodeConds, CondsHold, Fits, exact, binExact, fits32, Fits32, cfg_type]

/-- …and therefore `poly_refines` holds on the **generated** domain, with no hand-written
`fits32` conjunct anywhere in the statement. -/
theorem poly_refines_generated :
    Refines₃ (α := Int) (β := Int) (γ := Int) (δ := Int)
      CMathProgram "poly" 9
      (fun a b c => Domain cfg f_poly [.int a, .int b, .int c])
      (fun a b c => a * b + c - a) := by
  intro a b c hdom
  exact poly_refines a b c ((poly_domain_eq a b c).1 hdom)

/-! ### `clamp` — no arithmetic, hence no obligations

The asymmetry with `poly` is the evidence that the analysis tracks the actual arithmetic
rather than emitting a blanket disclaimer: `clamp` only compares and returns, so its
generated domain is literally `True`. -/

theorem clamp_conds : (analyzeFunc f_clamp).conds = [] := rfl
theorem clamp_complete : (analyzeFunc f_clamp).complete = true := rfl

theorem clamp_domain_eq (x lo hi : Int) :
    Domain cfg f_clamp [.int x, .int lo, .int hi] ↔ True := by
  simp [Domain, analyzeFunc, f_clamp, analyzeStmt, exprAnalysis, substE, conds,
        nodeConds, CondsHold]

theorem clamp_refines_generated :
    Refines₃ (α := Int) (β := Int) (γ := Int) (δ := Int)
      CMathProgram "clamp" 12
      (fun x lo hi => Domain cfg f_clamp [.int x, .int lo, .int hi]) clampS := by
  intro x lo hi _
  exact clamp_refines x lo hi trivial

/-! ### `cdiv` — the generated domain is *stronger* than the hand-written one

The hand-written domain is `fits32 (Int.tdiv a b)` alone: the source's own `b == 0` guard
makes the divide-by-zero path unreachable, and *that* is a path-sensitivity argument the
analysis does not make. Being path-insensitive, the analysis takes the union over both
arms of the `if` and additionally demands `b ≠ 0`, since a division node has no exact
mathematical value at a zero divisor.

That is the honest direction to be wrong in: the generated domain **implies** the
hand-written one, so refinement transfers, and the gap is a stated limitation
(open obligation 1 below) rather than a silent unsoundness. -/

theorem cdiv_conds :
    (analyzeFunc f_cdiv).conds = [ .binop "/" (.name "a") (.name "b") ] := rfl
theorem cdiv_complete : (analyzeFunc f_cdiv).complete = true := rfl

theorem cdiv_domain_eq (a b : Int) :
    Domain cfg f_cdiv [.int a, .int b] ↔ (b ≠ 0 ∧ fits32 (Int.tdiv a b)) := by
  simp [Domain, paramEnv, f_cdiv, analyzeFunc, analyzeStmt, exprAnalysis, substE,
        conds, nodeConds, CondsHold, Fits, exact, binExact, fits32, Fits32,
        NumConfig.quot, NumConfig.c32Wrapv, NumConfig.c32, Dialect.toNumConfig]
  constructor
  · rintro ⟨i, ⟨hb, rfl⟩, hr⟩; exact ⟨hb, hr⟩
  · rintro ⟨hb, hr⟩; exact ⟨_, ⟨hb, rfl⟩, hr⟩

/-- The generated domain implies the hand-written one, so `cdiv_refines` transfers. -/
theorem cdiv_refines_generated :
    Refines₂ (α := Int) (β := Int) (γ := Int)
      CMathProgram "cdiv" 10
      (fun a b => Domain cfg f_cdiv [.int a, .int b])
      (fun a b => if b = 0 then 0 else Int.tdiv a b) := by
  intro a b hdom
  exact cdiv_refines a b ((cdiv_domain_eq a b).1 hdom).2

/-! ### `cmod` — the `%` obligation pair, never written by hand

`cmod` has no hand-written refinement theorem in `Refine.lean`, so this is the analysis
producing a domain for a function nobody had analysed: the quotient obligation (which is
what makes `INT_MIN % -1` undefined) *and* the remainder obligation. -/

theorem cmod_conds :
    (analyzeFunc f_cmod).conds =
      [ .binop "/" (.name "a") (.name "b"), .binop "%" (.name "a") (.name "b") ] := rfl
theorem cmod_complete : (analyzeFunc f_cmod).complete = true := rfl

/-! ### `sumto` — a loop, and the analysis says so

`sumto` is hole-free but contains `Stmt.loop`. The analysis emits no obligations and sets
`complete := false`, which is the machine-checkable form of "I did not enumerate this".
Reading `conds = []` as "no overflow possible" would be precisely the silent wrongness
this file exists to avoid, and `complete` is what makes that misreading impossible. -/

theorem sumto_incomplete : (analyzeFunc f_sumto).complete = false := rfl

end CMath

/-! ## 8. Coverage over the C corpus

`math.c` translates to six `Func`s (five, in `Refine.lean`'s copy, which omits the module
initializer). All but one are analysable end to end (`complete = true`); the exception is
`sumto`, which is a loop. -/

section Coverage

open Autoform.Refine Autoform.Refine.Demo

/-- Functions the analysis can generate a domain for. -/
def analysable (p : Program) : List Func := p.funcs.filter (fun f => (analyzeFunc f).complete)

/-- Fraction, as a pair (analysable, total). -/
def coverage (p : Program) : Nat × Nat := ((analysable p).length, p.funcs.length)

/-- **Measured, not estimated**, on `Refine.lean`'s character-identical copy of the
generated `math.c` module: 4 of its 5 functions get a domain automatically. The one that
does not is `sumto`, the loop — the same construct `Refine.lean` §3 lists as its own open
obligation. -/
theorem cmath_coverage : coverage CMathProgram = (4, 5) := by decide

theorem cmath_analysable_names :
    (analysable CMathProgram).map Func.name = ["clamp", "poly", "cdiv", "cmod"] := by decide

/-- The same measurement against the **machine-generated** module itself, which also
carries `math.c`'s module-level initializer: 5 of 6. -/
theorem cmath_generated_coverage :
    coverage Autoform.Generated.program = (5, 6) := by decide

end Coverage

/-! ## 9. What is proved, and what is not

**Proved.**

* `applyBinop_agrees`, `applyUnop_neg_agrees` — every fragment operator agrees with its
  exact mathematical value under the node obligation. All four `NumResult` branches are
  accounted for: `ok` is the conclusion, `ub`/`trap` are made unreachable by the
  representability obligation, `divZero` by the divisor obligation.
* `nodeOK_of_condsHold` — the *syntactic* obligations imply the *semantic* side
  conditions.
* `exact_sound` — the whole-expression theorem: obligations ⟹ `evalExpr` returns exactly
  the mathematical value, for every fuel above the expression's depth.
* `no_ub_of_condsHold` — the corollary that matters: no `.hole "ub:…"`.
* `poly_domain_eq` — the generated domain for `poly` is *equivalent* to the three
  hand-written `fits32` conjuncts, and `poly_refines_generated` restates `poly_refines`
  with no hand-written conjunct in it.
* `cmath_coverage` / `cmath_generated_coverage` — 4/5 and 5/6 of the C corpus, by
  evaluation rather than by claim.

**Open obligations, stated rather than admitted.**

1. **Path sensitivity.** `analyzeStmt` takes the union over both arms of an `ifte`. That
   is sound but not complete: `cdiv`'s own `b == 0` guard already discharges the divisor
   obligation, and the analysis cannot see it, so `cdiv_domain_eq` carries a `b ≠ 0` the
   hand-written domain did not need. Closing this needs a path condition threaded through
   `analyzeStmt` and a decision procedure to discharge obligations against it.

2. **Statement-level soundness.** `exact_sound` is proved for `Expr`. The corresponding
   theorem for `Stmt` — "if `(analyzeStmt σ s).complete` and its obligations hold then
   `execStmt` reaches no `Ctl.hole` tagged `ub:`" — is *not* proved here. It needs an
   invariant relating the symbolic store `σ` to the runtime `Env`, and a join for `ifte`
   arms that assign. The demonstrations in §7 do not depend on it: each is proved by
   reducing the generated domain to a hand-written one and invoking the existing
   expression-level refinement theorem, so nothing in this file rests on the unproved
   statement-level claim.

3. **Loops.** `analyzeStmt` reports `complete := false` on `Stmt.loop`/`Stmt.forIn`.
   Generating a domain for `sumto` needs the loop-invariant rule that `Refine.lean` §3
   also lists as missing; the obligation there is `∀ i ≤ n, fits32 (i * (i+1) / 2)`-shaped
   and is not derivable by a syntactic walk.

4. **Calls.** An `Expr.call` is outside the fragment, so a function whose body calls
   another gets `complete := false`. Interprocedural domains need a summary — the callee's
   generated domain instantiated at the call site — which is the natural next step and is
   purely mechanical given (2).

5. **Shifts and bitwise operators.** `nodeConds` handles them by producing nothing, which
   is safe only because `Core.applyBinop` has no `<<`/`>>`/`&`/`|`/`^` cases at all: such a
   node is already an `Expr.hole` by the time it reaches this file. If `Semantics.lean`
   ever gains those operators, `nodeConds` must gain the `shiftCount` obligations from
   `Numeric.shl`/`shr` at the same time, or this analysis becomes unsound. That coupling
   is a liability and is recorded here deliberately.
-/

end Autoform.Overflow
