import Batteries
import Autoform.Lang.Imp.Semantics

/-!
# Tiered proof portfolio (STRATEGY.md §5, Tier 3 of the gap list)

A proof portfolio is an *escalation ladder*: try the cheapest thing that could possibly
work, and only spend more when it fails. §5 specifies six tiers:

1. `rfl` / `decide` / `simp` / `omega` / `norm_cast` — pennies.
2. `aesop`, `exact?`, hammer, SMT.
3. Neural whole-proof proposer.
4. Best-first tree search over pickled REPL proof states.
5. Lemma decomposition / goal generalization.
6. Give up → **record an open obligation, not a lie.**

What is buildable inside this repository is tiers 1, 2 (partially — `aesop`, `duper`
and `lean-smt` are not dependencies, so the tier-2 rungs here are the core/Batteries
tactics `simp_all`, `solve_by_elim` and `exact?`), and tier 6. Tiers 3–5 need external
services and are represented by an explicit "not available in this build" note in the
failure transcript rather than by a stub that pretends to try.

## The one invariant

**The portfolio never closes a goal it did not prove.** There is no `sorry` rung, no
`admit`, no fallback axiom. Every candidate proof term is additionally screened for
`sorryAx` (`Expr.hasSorry`) *after* the rung reports success, because a rung that
manufactures evidence of its own success is precisely the failure mode this project
exists to catch (README: "the gate never manufactures its own evidence"). If nothing
works the tactic **fails**, printing everything it tried, so the goal stays visibly
open and the ledger can count it.

## Interface

* `portfolio` — run the ladder, fail loudly if the ladder is exhausted.
* `portfolio (maxTier := 1)` — bound the spend.
* `portfolio!` — also `logInfo` the full transcript (which rungs ran, which won).
  Without `!` the transcript goes to `trace[autoform.portfolio]`.
* `#portfolio_check <prop>` — run the ladder on a *statement* without introducing any
  declaration, and report the outcome as a message. This is how a refusal can be
  demonstrated in a file that still compiles: nothing is added to the environment
  either way.
* `#obligation name : <prop>` — record a goal nobody has proved as structured data
  (name + elaborated statement + position). It does **not** create a theorem, so it
  cannot be mistaken for one, and it cannot be `exact`-ed downstream.
* `#obligations` — dump the open-obligation table for the ledger.
-/

namespace Autoform.Tactics

open Lean Elab Meta Tactic Term

initialize registerTraceClass `autoform.portfolio

/-! ## Open obligations -/

/-- A goal the portfolio could not close. This is ledger data, not a proof: it asserts
only that *someone claimed this statement matters and nobody has proved it*.

Note the type: an `Obligation` is a record of **strings**, not a term of the `Prop` in
question. There is no way to turn one into a proof, by construction. -/
structure Obligation where
  /-- Caller-chosen identifier, for cross-referencing from the trust ledger. -/
  name : String
  /-- The statement, pretty-printed *after* elaboration — so it is a real, type-correct
  `Prop`, not an unparsed string that might not even parse. -/
  statement : String
  /-- Module the obligation was declared in. -/
  module : String
  /-- What the portfolio tried before giving up, if it was run. -/
  attempted : List String
  deriving Repr, Inhabited, ToExpr

/-- Read an `Obligation` back out of the `Expr` of a stored declaration. Obligations are
stored as ordinary definitions of type `Obligation`, so they persist across modules and
are visible to `#print axioms`-style auditing without any custom environment
extension. -/
private def ofExpr? (e : Expr) : Option (String × String × String) := do
  let args := e.getAppArgs
  guard (args.size ≥ 3)
  let str (x : Expr) : Option String :=
    match x with | .lit (.strVal s) => some s | _ => none
  return (← str args[0]!, ← str args[1]!, ← str args[2]!)

/-- Every open obligation visible from the current environment. -/
def openObligations (env : Environment) : Array (Name × String × String × String) := Id.run do
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    if ci.type.isConstOf ``Obligation then
      if let some v := ci.value? then
        if let some t := ofExpr? v then
          out := out.push (n, t)
  return out.qsort (fun a b => a.1.toString < b.1.toString)

/-! ## The ladder -/

/-- One rung of the escalation ladder. -/
structure Rung where
  /-- Escalation tier from STRATEGY.md §5. -/
  tier : Nat
  /-- Human-readable name, used in the transcript. -/
  label : String
  /-- The tactic to run. -/
  tac : TSyntax `tactic

/-- The rungs that exist in *this* build.

Tier 1 is the cheap decision-procedure tier. Tier 2 is search: `aesop`, `duper` and
`lean-smt` are not available (not dependencies — see `lakefile.toml`), so tier 2 is
`simp_all`, `solve_by_elim` and core's library search `exact?`.

`native_decide` is deliberately absent at every tier: it discharges goals by trusting
the compiler, which would put a non-kernel oracle inside a gate whose entire purpose is
kernel-checked evidence. -/
def ladder : TermElabM (Array Rung) := do
  let mk (t : Nat) (l : String) (s : TSyntax `tactic) : Rung := ⟨t, l, s⟩
  return #[
    mk 1 "rfl"                (← `(tactic| rfl)),
    mk 1 "trivial"            (← `(tactic| trivial)),
    mk 1 "decide"             (← `(tactic| decide)),
    mk 1 "simp"               (← `(tactic| simp)),
    mk 1 "simp_arith"         (← `(tactic| simp_arith)),
    mk 1 "omega"              (← `(tactic| omega)),
    mk 1 "norm_cast"          (← `(tactic| norm_cast)),
    mk 1 "intros; rfl"        (← `(tactic| (intros; rfl))),
    mk 1 "intros; decide"     (← `(tactic| (intros; decide))),
    mk 1 "intros; omega"      (← `(tactic| (intros; omega))),
    mk 1 "simp; omega"        (← `(tactic| (simp; omega))),
    mk 2 "simp_all"           (← `(tactic| simp_all)),
    mk 2 "intros; simp_all"   (← `(tactic| (intros; simp_all))),
    mk 2 "constructor"        (← `(tactic| constructor)),
    mk 2 "solve_by_elim"      (← `(tactic| solve_by_elim)),
    mk 2 "intros; solve_by_elim" (← `(tactic| (intros; solve_by_elim))),
    mk 2 "exact?"             (← `(tactic| exact?)),
    mk 2 "intros; exact?"     (← `(tactic| (intros; exact?)))
  ]

/-- Tiers that exist in the design but have no implementation here. Listed in the
failure transcript so a reader can tell "unproved" from "not even attempted". -/
def unavailableTiers : List String :=
  [ "tier 2: aesop / lean-auto+duper / lean-smt+cvc5 — not a dependency of this build"
  , "tier 3: neural whole-proof proposer — needs an external model service"
  , "tier 4: best-first search over pickled REPL proof states — needs leanprover-community/repl"
  , "tier 5: lemma decomposition / goal generalization — needs the agent loop" ]

/-- Run one rung against `goal`, restoring all state if it does not fully close it.

Success requires *both* that no goals remain **and** that the resulting proof term is
free of `sorryAx`. The second check is the anti-self-certification guard: a rung is not
trusted to report its own honesty. -/
def tryRung (goal : MVarId) (r : Rung) : TermElabM Bool := do
  let s ← saveState
  try
    let gs ← Tactic.run goal (Tactic.evalTactic r.tac)
    if !gs.isEmpty then
      s.restore; return false
    let prf ← instantiateMVars (mkMVar goal)
    if prf.hasSorry || prf.hasExprMVar then
      -- A "proof" containing `sorryAx` or an unassigned hole is not a proof.
      s.restore; return false
    return true
  catch _ =>
    s.restore
    return false

/-- Outcome of a portfolio run: the winning rung (if any) and the full transcript. -/
structure Report where
  /-- `some (tier, label)` of the rung that closed the goal. -/
  winner : Option (Nat × String)
  /-- Every rung attempted, in order, `label` prefixed by its tier. -/
  tried : List String

/-- Render a report as ledger evidence. -/
def Report.render (rep : Report) (goalStr : String) : String :=
  match rep.winner with
  | some (t, l) =>
      s!"portfolio: CLOSED at tier {t} by `{l}`\n  goal    : {goalStr}\n  \
         attempted: {rep.tried.length} rung(s): {String.intercalate ", " rep.tried}"
  | none =>
      s!"portfolio: OPEN — no rung closed the goal\n  goal    : {goalStr}\n  \
         attempted: {rep.tried.length} rung(s): {String.intercalate ", " rep.tried}\n  \
         not attempted:\n    " ++ String.intercalate "\n    " unavailableTiers

/-- Walk the ladder up to `maxTier`. Returns the report; the goal is assigned iff
`winner` is `some`. -/
def runPortfolio (goal : MVarId) (maxTier : Nat) : TermElabM Report := do
  let rungs ← ladder
  let mut tried : List String := []
  for r in rungs do
    if r.tier ≤ maxTier then
      tried := tried ++ [s!"[{r.tier}] {r.label}"]
      trace[autoform.portfolio] "trying [{r.tier}] {r.label}"
      if ← tryRung goal r then
        return { winner := some (r.tier, r.label), tried }
  return { winner := none, tried }

/-! ## The tactic -/

/-! Tiered proof portfolio: `portfolio`, `portfolio (maxTier := 1)`, `portfolio!`
(verbose). Fails — never `sorry`s — when the ladder is exhausted. -/

/-- Shared body of the `portfolio` tactic variants. -/
def portfolioCore (verbose : Bool) (maxTier : Nat) : TacticM Unit := do
  let goal ← getMainGoal
  let rest := (← getGoals).drop 1
  let goalStr := toString (← Meta.ppExpr (← goal.getType))
  let rep ← runPortfolio goal maxTier
  let msg := rep.render goalStr
  match rep.winner with
  | some _ =>
    if verbose then logInfo msg else trace[autoform.portfolio] msg
    setGoals rest
  | none =>
    throwError "{msg}\n\nThe portfolio does not close goals it cannot prove. \
      Either raise `maxTier`, prove it by hand, or record it honestly with\n  \
      #obligation myGoal : <statement>"

/-- Tiered proof portfolio, tiers 1–2. Fails — never `sorry`s — when exhausted. -/
elab "portfolio" : tactic => portfolioCore false 2

/-- `portfolio` with the transcript logged as an info message (ledger evidence). -/
elab "portfolio!" : tactic => portfolioCore true 2

/-- Cost-bounded portfolio: only rungs of tier ≤ `maxTier` are attempted. -/
elab "portfolio" "(" &"maxTier" ":=" n:num ")" : tactic => portfolioCore false n.getNat

/-- Cost-bounded, verbose. -/
elab "portfolio!" "(" &"maxTier" ":=" n:num ")" : tactic => portfolioCore true n.getNat

/-! ## Commands -/

/-- `#portfolio_check <prop>` runs the ladder on a statement and *reports* the outcome
without introducing any declaration. Nothing enters the environment either way, so a
refusal can be demonstrated in a file that still compiles cleanly. -/
syntax (name := portfolioCheckStx)
  "#portfolio_check" ("(" &"maxTier" ":=" num ")")? term : command

open Lean.Elab.Command in
@[command_elab portfolioCheckStx] def elabPortfolioCheck : CommandElab := fun stx => do
  let maxTier :=
    if stx[1].isNone then 2
    else match stx[1][0][3].isNatLit? with | some k => k | none => 2
  let t : Term := ⟨stx[2]⟩
  liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    unless ← Meta.isProp e do
      throwError "#portfolio_check expects a Prop, got{indentExpr e}"
    let goal ← Meta.mkFreshExprMVar e
    let goalStr := toString (← Meta.ppExpr e)
    let rep ← runPortfolio goal.mvarId! maxTier
    logInfo (rep.render goalStr)

/-- `#obligation name : <prop>` — record an open obligation.

This is the tier-6 exit. It elaborates the statement (so it is guaranteed to be a
well-formed `Prop`, not a typo) and stores it as data. It does **not** declare a
theorem, does not `sorry` anything, and produces no term anyone can `exact`. It emits a
warning so an open obligation is never silent in a build log. -/
syntax (name := obligationStx) "#obligation" ident " : " term : command

open Lean.Elab.Command in
@[command_elab obligationStx] def elabObligation : CommandElab := fun stx => do
  let id : Ident := ⟨stx[1]⟩
  let t : Term := ⟨stx[3]⟩
  let stmt ← liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    unless ← Meta.isProp e do
      throwError "#obligation expects a Prop, got{indentExpr e}"
    pure (toString (← Meta.ppExpr e))
  let modName := (← getEnv).mainModule
  let o : Obligation :=
    { name := id.getId.toString, statement := stmt
      module := modName.toString, attempted := [] }
  let declName := `openObligation ++ id.getId
  liftTermElabM do
    addAndCompile <| .defnDecl
      { name := declName, levelParams := [], type := mkConst ``Obligation
        value := toExpr o, hints := .abbrev, safety := .safe }
  logWarning s!"OPEN OBLIGATION `{id.getId}` : {stmt}\n  \
    (recorded as ledger data in `{declName}` — this is NOT a theorem, its type is \
    `Obligation`, and nothing can derive a proof from it)"

/-- Dump the open-obligation table. -/
syntax (name := obligationsStx) "#obligations" : command

open Lean.Elab.Command in
@[command_elab obligationsStx] def elabObligations : CommandElab := fun _ => do
  let os := openObligations (← getEnv)
  if os.isEmpty then
    logInfo "open obligations: none"
  else
    let body := os.toList.map fun (n, nm, st, m) =>
      s!"  {nm}  [{m}]  (decl: {n})\n    {st}"
    logInfo <| s!"open obligations: {os.size}\n" ++ String.intercalate "\n" body

end Autoform.Tactics

/-! ## Demonstration on real goals from this project

These are not toy goals invented to make the portfolio look good: they are statements
about `Autoform.Imp`'s actual semantics — the fuel-indexed interpreter the differential
harness runs, and the big-step relation that specifies it. Each `portfolio!` prints
which rung won, so the build log itself is the ledger evidence. -/

namespace Demo

open Autoform.Imp

/-- Expression evaluation on a closed term: tier 1, `rfl`. -/
example : evalExpr State.empty (.add (.lit 2) (.mul (.lit 3) (.lit 4))) = 14 := by
  portfolio!

/-- A variable read against a concrete store: tier 1. -/
example : evalExpr [7, 9] (.sub (.var 1) (.var 0)) = 2 := by portfolio!

/-- Boolean evaluation, decidable comparison over `Int`. -/
example : evalBExpr [4] (.and (.le (.var 0) (.lit 9)) (.not .ff)) = true := by
  portfolio!

/-- Running an actual program: assign then skip. The portfolio closes this by
computation, which is exactly the property that makes `evalStmt` an oracle. -/
example : evalStmt 4 State.empty (.seq (.assign 0 (.lit 7)) .skip) = .ok [7] := by
  portfolio!

/-- Zero fuel always runs out — bounded to the cheap tier to show `maxTier` works. -/
example (s : State) (c : Stmt) : evalStmt 0 s c = .outOfFuel := by
  portfolio! (maxTier := 1)

/-- The effect boundary is never silently executed: a hole is reported, not skipped. -/
example (n : Nat) (s : State) (h : Nat) :
    evalStmt (n + 1) s (.opaqueHole h) = .hitHole h := by
  portfolio! (maxTier := 1)

/-- A loop whose guard is false terminates in the same state, under the *relation*.
Needs the tier-2 rungs (`constructor` / `exact?`), not just computation. -/
example (s : State) (c : Stmt) : BigStep s (.loop .ff c) s := by portfolio!

/-- Assignment agrees with the relation, for *all* states and expressions. -/
example (s : State) (x : Var) (e : Expr) :
    BigStep s (.assign x e) (s.set x (evalExpr s e)) := by portfolio!

/-- Plain arithmetic side-condition of the kind the transpiler emits. -/
example (a b : Nat) : a + b + 0 = b + a := by portfolio! (maxTier := 1)

/-! ### Goals the portfolio correctly refuses

`#portfolio_check` runs the same ladder but introduces no declaration, so a refusal is
visible in the build log without anything being admitted. Both of these need induction
(over the derivation, and over fuel respectively) — genuinely beyond tiers 1–2, and the
portfolio says so instead of guessing. -/

#portfolio_check ∀ (s : State) (c : Stmt) (s₁ s₂ : State),
  BigStep s c s₁ → BigStep s c s₂ → s₁ = s₂

#portfolio_check ∀ (s s' : State) (c : Stmt),
  BigStep s c s' → ∃ n, evalStmt n s c = .ok s'

/-! The refusals are then recorded as structured open obligations rather than as
`sorry`-backed theorems. Nothing below is provable-by-citation: `#obligation` produces
no proof term, only an `Obligation` record. -/
#obligation Imp.bigStep_deterministic :
  ∀ (s : State) (c : Stmt) (s₁ s₂ : State), BigStep s c s₁ → BigStep s c s₂ → s₁ = s₂

#obligation Imp.evalStmt_complete :
  ∀ (s s' : State) (c : Stmt), BigStep s c s' → ∃ n, evalStmt n s c = .ok s'

#obligations

end Demo
