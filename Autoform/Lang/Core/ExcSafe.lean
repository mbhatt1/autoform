import Autoform.Lang.Core.Semantics

/-!
# Every exception the Python interpreter raises names a represented class

The exporter's Python `try`/`except` lowering dispatches on the pending exception by
comparing it, as a string, against the names of the exception classes Core represents
(`Stdlib.excNames`). Until this file existed that comparison sat behind a guard that holed
(`control:TRY-exception-representation`) whenever the pending value was not one of those
names -- because `Stmt.raise` used to raise whatever value it was handed, and comparing an
arbitrary object against class names would have invented a miss.

This file is the reason the guard is gone. `execStmt_exn_excSafe` and
`evalExpr_exn_excSafe` say that under `.python`, every `.exn v` the interpreter can
produce -- from any expression, statement, call, or loop, at any fuel -- has `v` a
represented class name (`Stdlib.ExcSafe v`). The proof is one simultaneous induction over
the eight mutually recursive interpreter functions, the same shape as
`Autoform/FuelMono.lean`'s `FuelStep`, with the leaves supplied by:

* `Stdlib.makeException_excSafe`, `Stdlib.raiseValue_excSafe`, `pythonRaise_excSafe` --
  the three ways a Python program constructs or raises an exception value;
* `NumConfig.python_shiftCount_trap` and the `numOk_*` lemmas below -- the integer
  operators, whose only trap under the unbounded Python configuration is the
  `ValueError` on a negative shift count;
* `FConfig.div_exn`, `FConfig.fmod_exn`, `FConfig.pyMod_exn`, `FConfig.ofInt_exn`
  (`Float.lean`) -- the float operators, which raise `ZeroDivisionError` and
  `OverflowError` and nothing else;
* `Stdlib.builtin_excSafe`, `Stdlib.method_pure_excSafe`,
  `Stdlib.method_mutating_not_exn` -- the modelled builtins and container methods;
* the literal `.exn (.str "<Name>")` sites in `Semantics.lean` itself (`IndexError`,
  `KeyError`, `TypeError`, `RuntimeError`), each discharged by `decide`.

Two places in the semantics were changed to make this a theorem rather than a
convention, and both are recorded in `docs/languages.md` §10: `Stmt.raise` classifies
the raised value under `.python` (`pythonRaise`), and the typed-numeric fallthroughs
(`TypedNumeric.binary`/`unary`, whose traps are prose such as `panic:...`) are refused
under `.python`, where the exporter never emits them.

No case is left open. Every leaf of the induction is closed by the `exc_close`
combinator below, which tries the constructor-mismatch, literal-name, induction-hypothesis
and leaf-lemma discharges in turn.
-/

namespace Autoform.Core

open Stdlib (ExcSafe excSafe_str)

/-! ## `Stmt.raise` -/

/-- `pythonRaise` raises only represented names: a represented `.str` passes through
unchanged, and everything else is classified by `raiseValue`. -/
theorem pythonRaise_excSafe {u v : Val} : pythonRaise u = .exn v → ExcSafe v := by
  intro h
  unfold pythonRaise at h
  split at h
  · split at h
    · rename_i hc
      cases h
      exact excSafe_str (List.contains_iff_mem.mp hc)
    · exact Stdlib.raiseValue_excSafe h
  · exact Stdlib.raiseValue_excSafe h

/-! ## Integer operators

`numToE` turns `.divZero` into `ZeroDivisionError` and `.trap r` into `.exn (.str r)`, so
an integer result is safe exactly when any trap it carries is named `ValueError` -- the
one trap the Python configuration can produce. -/

/-- A machine-integer result whose trap, if any, names `ValueError`. -/
def NumTrapOk (r : NumResult) : Prop := ∀ s, r = .trap s → s = "ValueError"

theorem numToE_excSafe {r : NumResult} {v : Val} (hr : NumTrapOk r) :
    numToE r = .exn v → ExcSafe v := by
  intro h
  cases r with
  | ok n => cases h
  | ub s => cases h
  | divZero => cases h; exact excSafe_str (by decide)
  | trap s =>
      cases h
      have hs := hr s rfl
      subst hs
      exact excSafe_str (by decide)

theorem numTrapOk_ok (n : Int) : NumTrapOk (.ok n) := fun _ h => by cases h
theorem numTrapOk_divZero : NumTrapOk .divZero := fun _ h => by cases h
theorem numTrapOk_ub (r : String) : NumTrapOk (.ub r) := fun _ h => by cases h

/-- On an unbounded type `finish` is the identity: nothing is out of range. -/
theorem finish_of_unbounded {c : NumConfig} (hu : c.type = .unbounded) (x : Int) :
    c.finish x = .ok x := by
  simp [NumConfig.finish, hu, IntType.inRange]

theorem numTrapOk_python_add (a b : Int) : NumTrapOk (NumConfig.python.add a b) := by
  rw [NumConfig.python_add]; exact numTrapOk_ok _
theorem numTrapOk_python_sub (a b : Int) : NumTrapOk (NumConfig.python.sub a b) := by
  rw [NumConfig.python_sub]; exact numTrapOk_ok _
theorem numTrapOk_python_mul (a b : Int) : NumTrapOk (NumConfig.python.mul a b) := by
  rw [NumConfig.python_mul]; exact numTrapOk_ok _
theorem numTrapOk_python_neg (a : Int) : NumTrapOk (NumConfig.python.neg a) := by
  rw [NumConfig.python_neg]; exact numTrapOk_ok _

theorem numTrapOk_python_div (a b : Int) : NumTrapOk (NumConfig.python.div a b) := by
  intro s h
  unfold NumConfig.div at h
  split at h
  · cases h
  · rw [finish_of_unbounded (c := NumConfig.python) rfl] at h; cases h

theorem numTrapOk_python_mod (a b : Int) : NumTrapOk (NumConfig.python.mod a b) := by
  intro s h
  by_cases hb : b = 0
  · subst hb
    unfold NumConfig.mod at h
    simp at h
  · rw [NumConfig.python_mod a b hb] at h; cases h

/-- Any configuration whose shift-count fault is `ValueError` traps only with that name
on a shift count. Generalised over the configuration because `>>>` runs on
`{ python with negRightShift := .logical }`, which `python_shiftCount_trap` does not
cover. -/
theorem shiftCount_trap_of_fault {c : NumConfig} (hf : c.shiftCountFault = some "ValueError")
    (k : Int) (s : String) : c.shiftCount k = .trap s → s = "ValueError" := by
  intro h
  unfold NumConfig.shiftCount at h
  (try dsimp only at h)
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; simp [hf])

theorem numTrapOk_shl {c : NumConfig} (hu : c.type = .unbounded)
    (hf : c.shiftCountFault = some "ValueError") (a k : Int) : NumTrapOk (c.shl a k) := by
  intro s h
  unfold NumConfig.shl at h
  cases hs : c.shiftCount k with
  | ok k' => simp only [hs, finish_of_unbounded hu] at h; try cases h
  | divZero => simp only [hs] at h; try cases h
  | ub r => simp only [hs] at h; try cases h
  | trap r => simp only [hs] at h; cases h; exact shiftCount_trap_of_fault hf k _ hs

theorem numTrapOk_shr {c : NumConfig} (hu : c.type = .unbounded)
    (hf : c.shiftCountFault = some "ValueError") (a k : Int) : NumTrapOk (c.shr a k) := by
  intro s h
  unfold NumConfig.shr at h
  cases hs : c.shiftCount k with
  | ok k' =>
      simp only [hs] at h
      repeat' split at h
      all_goals cases h
  | divZero => simp only [hs] at h; try cases h
  | ub r => simp only [hs] at h; try cases h
  | trap r => simp only [hs] at h; cases h; exact shiftCount_trap_of_fault hf k _ hs

theorem numTrapOk_bitwise (c : NumConfig) (f : Nat → Nat → Nat) (a b : Int) :
    NumTrapOk (c.bitwise f a b) := by
  intro s h
  unfold NumConfig.bitwise at h
  split at h <;> cases h

theorem numTrapOk_band (c : NumConfig) (a b : Int) : NumTrapOk (c.band a b) := by
  intro s h
  unfold NumConfig.band at h
  split at h
  · cases h
  · exact numTrapOk_bitwise _ _ _ _ _ h

theorem numTrapOk_bor (c : NumConfig) (a b : Int) : NumTrapOk (c.bor a b) := by
  intro s h
  unfold NumConfig.bor at h
  repeat' split at h
  all_goals first | (cases h; done) | exact numTrapOk_bitwise _ _ _ _ _ h

theorem numTrapOk_bxor (c : NumConfig) (a b : Int) : NumTrapOk (c.bxor a b) := by
  intro s h
  unfold NumConfig.bxor at h
  repeat' split at h
  all_goals first | (cases h; done) | exact numTrapOk_bitwise _ _ _ _ _ h

theorem numTrapOk_bnot (c : NumConfig) (a : Int) : NumTrapOk (c.bnot a) := by
  intro s h
  unfold NumConfig.bnot at h
  cases h

/-! ## Float operators -/

/-- A float result whose exception, if any, is one of the two Python raises. -/
def FExnOk (r : FResult) : Prop :=
  ∀ s, r = .exn s → s = "ZeroDivisionError" ∨ s = "OverflowError"

theorem fresToE_excSafe {r : FResult} {v : Val} (hr : FExnOk r) :
    fresToE r = .exn v → ExcSafe v := by
  intro h
  cases r with
  | ok f => cases h
  | ub s => cases h
  | unmodelled s => cases h
  | exn s =>
      cases h
      rcases hr s rfl with hs | hs <;> subst hs <;> exact excSafe_str (by decide)

theorem fExnOk_add (c : FConfig) (x y : Fl) : FExnOk (c.add x y) :=
  fun s h => absurd h (FConfig.add_ne_exn c x y s)
theorem fExnOk_sub (c : FConfig) (x y : Fl) : FExnOk (c.sub x y) :=
  fun s h => absurd h (FConfig.sub_ne_exn c x y s)
theorem fExnOk_mul (c : FConfig) (x y : Fl) : FExnOk (c.mul x y) :=
  fun s h => absurd h (FConfig.mul_ne_exn c x y s)
theorem fExnOk_div (c : FConfig) (x y : Fl) : FExnOk (c.div x y) :=
  fun s h => Or.inl (FConfig.div_exn c x y s h)
theorem fExnOk_fmod (c : FConfig) (x y : Fl) : FExnOk (c.fmod x y) :=
  fun s h => Or.inl (FConfig.fmod_exn c x y s h)
theorem fExnOk_pyMod (c : FConfig) (x y : Fl) : FExnOk (c.pyMod x y) :=
  fun s h => Or.inl (FConfig.pyMod_exn c x y s h)

/-- A failed promotion is Python's `OverflowError` on an integer too large for a double;
a float operand never fails to promote. -/
theorem flOfVal_fExnOk (d : Dialect) (a : Val) (r : FResult) :
    flOfVal d a = some r → FExnOk r := by
  intro hr s hs
  subst hs
  unfold flOfVal at hr
  split at hr
  · split at hr <;> cases hr
  · exact Or.inr (FConfig.ofInt_exn _ _ _ (Option.some.inj hr))
  · cases hr

theorem ordToE_ne_exn (op : String) (o : Option Ordering) {v : Val} :
    ordToE op o = .exn v → False := by
  intro h
  unfold ordToE at h
  repeat' split at h
  all_goals cases h

/-! ## The operator tables

Each is a scan over the operator's match: every arm is a value, a hole, a literal
represented name, or one of the numeric/float results pinned above. The typed-numeric
fallthrough (`TypedNumeric.binary`/`unary`) is refused under `.python` by `Semantics.lean`,
which is what keeps its prose traps (`panic:...`) out of this enumeration. -/

set_option maxHeartbeats 4000000 in
theorem flBinop_excSafe {d : Dialect} (hd : d = .python) (op : String) (a b : Val)
    {v : Val} : flBinop d op a b = .exn v → ExcSafe v := by
  intro h
  subst hd
  unfold flBinop at h
  (try dsimp only [Dialect.toFConfig] at h)
  repeat' split at h
  all_goals first
    | (cases h; done)
    | exact (ordToE_ne_exn _ _ h).elim
    | exact fresToE_excSafe (fExnOk_add _ _ _) h
    | exact fresToE_excSafe (fExnOk_sub _ _ _) h
    | exact fresToE_excSafe (fExnOk_mul _ _ _) h
    | exact fresToE_excSafe (fExnOk_div _ _ _) h
    | exact fresToE_excSafe (fExnOk_pyMod _ _ _) h
    | exact fresToE_excSafe (fExnOk_fmod _ _ _) h
    | exact fresToE_excSafe (flOfVal_fExnOk _ _ _ (by assumption)) h
    | (rename_i hne; cases hne; done)

set_option maxHeartbeats 4000000 in
theorem languageBinop_excSafe {d : Dialect} (hd : d = .python) (op : String) (a b : Val)
    {v : Val} : languageBinop d op a b = .exn v → ExcSafe v := by
  intro h
  subst hd
  unfold languageBinop at h
  (try dsimp only at h)
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact excSafe_str (by decide))
    | exact flBinop_excSafe rfl _ _ _ h
    | (rename_i hne; cases hne; done)

set_option maxHeartbeats 8000000 in
theorem applyBinop_excSafe {d : Dialect} (hd : d = .python) (op : String) (a b : Val)
    {v : Val} : applyBinop d op a b = .exn v → ExcSafe v := by
  intro h
  subst hd
  unfold applyBinop at h
  (try dsimp only [Dialect.toNumConfig] at h)
  repeat' split at h
  all_goals first
    | (cases h; done)
    | exact numToE_excSafe (numTrapOk_python_add _ _) h
    | exact numToE_excSafe (numTrapOk_python_sub _ _) h
    | exact numToE_excSafe (numTrapOk_python_mul _ _) h
    | exact numToE_excSafe (numTrapOk_python_div _ _) h
    | exact numToE_excSafe (numTrapOk_python_mod _ _) h
    | exact numToE_excSafe (numTrapOk_band _ _ _) h
    | exact numToE_excSafe (numTrapOk_bor _ _ _) h
    | exact numToE_excSafe (numTrapOk_bxor _ _ _) h
    | exact numToE_excSafe (numTrapOk_shl (c := NumConfig.python) rfl rfl _ _) h
    | exact numToE_excSafe (numTrapOk_shr (c := NumConfig.python) rfl rfl _ _) h
    | exact numToE_excSafe
        (numTrapOk_shr (c := { NumConfig.python with negRightShift := .logical }) rfl rfl _ _) h
    | exact flBinop_excSafe rfl _ _ _ h
    | exact languageBinop_excSafe rfl _ _ _ h
    | (rename_i hne; cases hne; done)

set_option maxHeartbeats 4000000 in
theorem applyUnop_excSafe {d : Dialect} (hd : d = .python) (op : String) (a : Val)
    {v : Val} : applyUnop d op a = .exn v → ExcSafe v := by
  intro h
  subst hd
  unfold applyUnop at h
  (try dsimp only [Dialect.toNumConfig] at h)
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact excSafe_str (by decide))
    | exact Stdlib.raiseValue_excSafe h
    | exact numToE_excSafe (numTrapOk_python_neg _) h
    | exact numToE_excSafe (numTrapOk_bnot _ _) h
    | exact Stdlib.makeException_excSafe (Or.inr h)
    | (rename_i hne; cases hne; done)

theorem valIn_ne_exn (x c : Val) {v : Val} : valIn x c = .exn v → False := by
  intro h
  unfold valIn at h
  repeat' split at h
  all_goals cases h

/-- Slice assignment fails only as CPython's `ValueError` (zero step, or an extended slice
whose lengths differ); `Stmt.setSlice` raises the string it returns. -/
theorem listSetSlice_error {vs : List Val} {lo hi st : Option Int} {ys : List Val}
    {ex : String} : Stdlib.listSetSlice vs lo hi st ys = .error ex → ex = "ValueError" := by
  intro h
  unfold Stdlib.listSetSlice at h
  -- The extended-slice branch binds `ks` with a `let`; zeta-reduce before splitting it.
  repeat' (first | split at h | dsimp only at h)
  all_goals first | exact (Except.error.inj h).symm | cases h

theorem listSetSlice_excSafe {vs : List Val} {lo hi st : Option Int} {ys : List Val}
    {ex : String} (h : Stdlib.listSetSlice vs lo hi st ys = .error ex) : ExcSafe (.str ex) := by
  rw [listSetSlice_error h]; exact Stdlib.excSafe_str (by decide)

/-- The type checks `len`/`bool`/`hash`/`str`/`repr` apply to a dunder's answer raise
only `TypeError`/`ValueError`, both represented. -/
theorem builtinDunderResult_excSafe (f m : String) (v : Val) {w : Val} :
    builtinDunderResult f m v = .exn w → ExcSafe w := by
  intro h
  unfold builtinDunderResult at h
  repeat' split at h
  all_goals first | (cases h; exact Stdlib.excSafe_str (by decide)) | cases h

/-- A JavaScript property read on a container never raises: a key, a length, or
`undefined`. -/
theorem jsContainerField_ne_exn (p : Payload) (f : String) {v : Val} :
    jsContainerField p f = .exn v → False := by
  intro h
  unfold jsContainerField at h
  repeat' split at h
  all_goals cases h

theorem allocBuiltin_ne_exn (ctx : Ctx) (cls : String) (b : BuiltinBase) (vs : List Val)
    {v : Val} : allocBuiltin ctx cls b vs = .exn v → False := by
  intro h
  unfold allocBuiltin at h
  repeat' split at h
  all_goals cases h

/-! ## The simultaneous induction

Mirrors `FuelMono.lean`'s `FuelStep`: one clause per interpreter function, all at fuel
`k`, proved together by induction on `k`. Each clause says that an `.exn v` result under
`.python` has `v` represented. The result binders are implicit so an induction hypothesis
applies as `ihE _ hd hy` whatever the arguments were. -/

private def ExcStep (k : Nat) : Prop :=
  (∀ (ctx : Ctx), ctx.dialect = .python →
      ∀ {h : Heap} {ρ : Env} {e : Expr} {h' : Heap} {v : Val},
      evalExpr ctx k h ρ e = (h', .exn v) → ExcSafe v)
  ∧ (∀ (ctx : Ctx), ctx.dialect = .python →
      ∀ {h : Heap} {fn : Func} {self? : Option Val} {vs : List Val}
        {kws : List (String × Val)} {h' : Heap} {v : Val},
      applyFunc ctx k h fn self? vs kws = (h', .exn v) → ExcSafe v)
  ∧ (∀ (ctx : Ctx), ctx.dialect = .python →
      ∀ {h : Heap} {fn : Func} {cap : List (String × Val)} {vs : List Val}
        {kws : List (String × Val)} {h' : Heap} {v : Val},
      applyClosure ctx k h fn cap vs kws = (h', .exn v) → ExcSafe v)
  ∧ (∀ (ctx : Ctx), ctx.dialect = .python →
      ∀ {h : Heap} {ρ : Env} {es : List Expr} {h' : Heap} {v : Val},
      evalList ctx k h ρ es = (h', .inl (.exn v)) → ExcSafe v)
  ∧ (∀ (ctx : Ctx), ctx.dialect = .python →
      ∀ {h : Heap} {ρ : Env} {ps : List (Expr × Expr)} {h' : Heap} {v : Val},
      evalPairs ctx k h ρ ps = (h', .inl (.exn v)) → ExcSafe v)
  ∧ (∀ (ctx : Ctx), ctx.dialect = .python →
      ∀ {h : Heap} {ρ : Env} {s : Stmt} {h' : Heap} {v : Val} {ρ' : Env},
      execStmt ctx k h ρ s = (h', .exn v ρ') → ExcSafe v)
  ∧ (∀ (ctx : Ctx), ctx.dialect = .python →
      ∀ {h : Heap} {ρ : Env} {x : String} {vs : List Val} {body : Stmt} {h' : Heap}
        {v : Val} {ρ' : Env},
      execFor ctx k h ρ x vs body = (h', .exn v ρ') → ExcSafe v)
  ∧ (∀ (ctx : Ctx), ctx.dialect = .python →
      ∀ {h : Heap} {ρ : Env} {x : String} {r : Ref} {i ver : Nat} {body : Stmt}
        {h' : Heap} {v : Val} {ρ' : Env},
      execForRef ctx k h ρ x r i ver body = (h', .exn v ρ') → ExcSafe v)

/-! Close one leaf of the induction. `hy` is the (already case-split) result equation,
`hd` the dialect hypothesis, `ihE`..`ihRef` the eight induction hypotheses; hygiene is
off so the macro can name them. The alternatives, in order:

1. constructor mismatch (`.val`, `.hole`, `.outOfFuel`, `.normal`, ... against `.exn`);
2. a literal represented name (`IndexError`, `KeyError`, `TypeError`, `RuntimeError`);
3. the result IS a recursive call -- an induction hypothesis applies to `hy` directly;
4. an operator table -- `applyBinop`/`applyUnop`, or `allocBuiltin` (never raises);
5. the result is propagated from a recursive call whose equation `split` left in the
   context -- `cases hy` identifies the values, `assumption` finds the equation;
6. the value came from `pythonRaise`, a builtin, or a container method;
7. the `Stmt.raise` non-Python branch, contradicted by `hd`. -/
set_option hygiene false in
macro "exc_close" : tactic => `(tactic| first
  | (cases hy; done)
  | (cases hy; exact excSafe_str (by decide))
  | exact ihE _ hd hy
  | exact ihF _ hd hy
  | exact ihC _ hd hy
  | exact ihL _ hd hy
  | exact ihP _ hd hy
  | exact ihS _ hd hy
  | exact ihR _ hd hy
  | exact ihRef _ hd hy
  | exact applyBinop_excSafe hd _ _ _ (Prod.mk.inj hy).2
  | exact applyUnop_excSafe hd _ _ (Prod.mk.inj hy).2
  | exact (allocBuiltin_ne_exn _ _ _ _ (Prod.mk.inj hy).2).elim
  | (cases hy; exact ihE _ hd (by assumption))
  | (cases hy; exact ihF _ hd (by assumption))
  | (cases hy; exact ihC _ hd (by assumption))
  | (cases hy; exact ihL _ hd (by assumption))
  | (cases hy; exact ihP _ hd (by assumption))
  | (cases hy; exact ihS _ hd (by assumption))
  | (cases hy; exact ihR _ hd (by assumption))
  | (cases hy; exact ihRef _ hd (by assumption))
  | (cases hy; exact pythonRaise_excSafe (by assumption))
  | (cases hy; exact Stdlib.builtin_excSafe hd _ _ _ _ _ (by assumption))
  | (cases hy; exact Stdlib.method_pure_excSafe hd _ _ _ _ _ _ (by assumption))
  | (cases hy; exact (Stdlib.method_mutating_not_exn hd _ _ _ _ _ _ _ (by assumption)).elim)
  | exact (valIn_ne_exn _ _ (Prod.mk.inj hy).2).elim
  | exact (jsContainerField_ne_exn _ _ (Prod.mk.inj hy).2).elim
  | (cases hy; exact listSetSlice_excSafe (by assumption))
  | exact builtinDunderResult_excSafe _ _ _ (Prod.mk.inj hy).2
  | (exfalso; rename_i hne; rw [hd] at hne; exact hne (by decide))
  | (exfalso; rename_i hne; simp [hd] at hne)
  | (trace_state; fail "exc_close: no closer applies"))

/-! Reduce the finalizer helpers, split `hy` on every `match`/`if` it contains, and
close every leaf. -/
set_option hygiene false in
macro "exc_split" : tactic => `(tactic|
  ((try dsimp only [Ctl.env, Ctl.withEnv] at hy)
   (repeat' split at hy)
   all_goals exc_close))

set_option maxHeartbeats 40000000 in
private theorem excStep : ∀ k, ExcStep k := by
  intro k
  induction k with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
        (rename_i hy
         simp [evalExpr, applyFunc, applyClosure, evalList, evalPairs, execStmt,
           execFor, execForRef] at hy)
  | succ k ih =>
      obtain ⟨ihE, ihF, ihC, ihL, ihP, ihS, ihR, ihRef⟩ := ih
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- evalExpr. Literals have one equation per literal shape, so they are split
        -- first; every other constructor has a single equation at fuel `k+1`.
        intro ctx hd h ρ e h' v hy
        cases e
        case lit l => cases l <;> simp only [evalExpr] at hy <;> cases hy
        all_goals (simp only [evalExpr] at hy; exc_split)
      · intro ctx hd h fn self? vs kws h' v hy
        simp only [applyFunc] at hy
        exc_split
      · intro ctx hd h fn cap vs kws h' v hy
        simp only [applyClosure] at hy
        exc_split
      · -- evalList dispatches on the head argument's syntax before evaluating it, so
        -- the head is split first, exactly as in `FuelMono`.
        intro ctx hd h ρ es h' v hy
        cases es with
        | nil => simp only [evalList] at hy <;> cases hy
        | cons a as => cases a <;> (simp only [evalList] at hy; exc_split)
      · intro ctx hd h ρ ps h' v hy
        cases ps with
        | nil => simp only [evalPairs] at hy <;> cases hy
        | cons kv ps =>
            obtain ⟨ke, ve⟩ := kv
            simp only [evalPairs] at hy
            exc_split
      · -- execStmt. `tryFinally` re-enters the finalizer with the body's pending exit
        -- (`Ctl.env`/`Ctl.withEnv`), so the body's outcome is split by hand first;
        -- everything else is one equation followed by the generic split.
        intro ctx hd h ρ s h' v ρ' hy
        cases s
        case tryFinally body fin =>
          simp only [execStmt] at hy
          rcases hA : execStmt ctx k h ρ body with ⟨h₁, c₁⟩
          rw [hA] at hy
          cases c₁ <;> exc_split
        all_goals (simp only [execStmt] at hy; exc_split)
      · intro ctx hd h ρ x vs body h' v ρ' hy
        cases vs <;> (simp only [execFor] at hy; exc_split)
      · intro ctx hd h ρ x r i ver body h' v ρ' hy
        simp only [execForRef] at hy
        exc_split

/-! ## Public statements -/

/-- **Every exception an expression raises under Python is a represented class name.** -/
theorem evalExpr_exn_excSafe {ctx : Ctx} (hd : ctx.dialect = .python) {k : Nat}
    {h h' : Heap} {ρ : Env} {e : Expr} {v : Val}
    (he : evalExpr ctx k h ρ e = (h', .exn v)) : ExcSafe v :=
  (excStep k).1 ctx hd he

/-- `applyFunc` version. -/
theorem applyFunc_exn_excSafe {ctx : Ctx} (hd : ctx.dialect = .python) {k : Nat}
    {h h' : Heap} {fn : Func} {self? : Option Val} {vs : List Val}
    {kws : List (String × Val)} {v : Val}
    (he : applyFunc ctx k h fn self? vs kws = (h', .exn v)) : ExcSafe v :=
  (excStep k).2.1 ctx hd he

/-- `applyClosure` version. -/
theorem applyClosure_exn_excSafe {ctx : Ctx} (hd : ctx.dialect = .python) {k : Nat}
    {h h' : Heap} {fn : Func} {cap : List (String × Val)} {vs : List Val}
    {kws : List (String × Val)} {v : Val}
    (he : applyClosure ctx k h fn cap vs kws = (h', .exn v)) : ExcSafe v :=
  (excStep k).2.2.1 ctx hd he

/-- `evalList` version; its exception is spelled `Sum.inl (EResult.exn v)`. -/
theorem evalList_exn_excSafe {ctx : Ctx} (hd : ctx.dialect = .python) {k : Nat}
    {h h' : Heap} {ρ : Env} {es : List Expr} {v : Val}
    (he : evalList ctx k h ρ es = (h', .inl (.exn v))) : ExcSafe v :=
  (excStep k).2.2.2.1 ctx hd he

/-- `evalPairs` version. -/
theorem evalPairs_exn_excSafe {ctx : Ctx} (hd : ctx.dialect = .python) {k : Nat}
    {h h' : Heap} {ρ : Env} {ps : List (Expr × Expr)} {v : Val}
    (he : evalPairs ctx k h ρ ps = (h', .inl (.exn v))) : ExcSafe v :=
  (excStep k).2.2.2.2.1 ctx hd he

/-- **Every exception a statement raises under Python is a represented class name.**
This is the theorem the exporter's `try`/`except` lowering now relies on in place of the
`control:TRY-exception-representation` guard. -/
theorem execStmt_exn_excSafe {ctx : Ctx} (hd : ctx.dialect = .python) {k : Nat}
    {h h' : Heap} {ρ ρ' : Env} {s : Stmt} {v : Val}
    (he : execStmt ctx k h ρ s = (h', .exn v ρ')) : ExcSafe v :=
  (excStep k).2.2.2.2.2.1 ctx hd he

/-- `execFor` version. -/
theorem execFor_exn_excSafe {ctx : Ctx} (hd : ctx.dialect = .python) {k : Nat}
    {h h' : Heap} {ρ ρ' : Env} {x : String} {vs : List Val} {body : Stmt} {v : Val}
    (he : execFor ctx k h ρ x vs body = (h', .exn v ρ')) : ExcSafe v :=
  (excStep k).2.2.2.2.2.2.1 ctx hd he

/-- `execForRef` version. -/
theorem execForRef_exn_excSafe {ctx : Ctx} (hd : ctx.dialect = .python) {k : Nat}
    {h h' : Heap} {ρ ρ' : Env} {x : String} {r : Ref} {i ver : Nat} {body : Stmt} {v : Val}
    (he : execForRef ctx k h ρ x r i ver body = (h', .exn v ρ')) : ExcSafe v :=
  (excStep k).2.2.2.2.2.2.2 ctx hd he

/-- The form the exporter's dispatch actually needs: the pending exception, read as a
string, is one of the represented names it compares against. -/
theorem execStmt_exn_name {ctx : Ctx} (hd : ctx.dialect = .python) {k : Nat}
    {h h' : Heap} {ρ ρ' : Env} {s : Stmt} {v : Val}
    (he : execStmt ctx k h ρ s = (h', .exn v ρ')) :
    ∃ n, v = .str n ∧ n ∈ Stdlib.excNames :=
  execStmt_exn_excSafe hd he

-- Axiom audit: these must list only `propext`, `Classical.choice`, `Quot.sound`.
#print axioms evalExpr_exn_excSafe
#print axioms execStmt_exn_excSafe

end Autoform.Core
