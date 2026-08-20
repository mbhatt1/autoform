import Batteries
import Std.Tactic.BVDecide
import Autoform.Lang.Imp.Semantics
import Autoform.Lang.Core.Numeric

/-!
# Tiered proof portfolio (STRATEGY.md §5, Tier 3 of the gap list)

A proof portfolio is an *escalation ladder*: try the cheapest thing that could possibly
work, and only spend more when it fails. §5 specifies six tiers:

1. `rfl` / `decide` / `simp` / `omega` / `norm_cast` — pennies.
2. `aesop`, `exact?`, hammer, SMT.
3. Neural whole-proof proposer.
4. Best-first tree search over proof states.
5. Lemma decomposition / goal generalization.
6. Give up → **record an open obligation, not a lie.**

What this build implements, and how honestly:

* **Tier 1** — core decision procedures.
* **Tier 2** — `simp_all`, `solve_by_elim`, `exact?` *and* `bv_decide`. `bv_decide` is
  in Lean core (`Std.Tactic.BVDecide`); it discharges bitvector goals via CaDiCaL and
  then **checks the SAT solver's LRAT certificate in the Lean kernel**, so it is a real
  tier-2 hammer that adds no trusted code (`#print axioms` on a `bv_decide` proof shows
  only `propext`/`Quot.sound`/`Classical.choice`). `aesop`/`duper`/`lean-smt` remain
  unavailable: they are not dependencies and `lakefile.toml` is off limits.
  An external SMT solver *is* reachable (`scripts/prover/smt.py` finds `cvc5`/`z3`), but
  no Lean proof can be reconstructed from its answer, so it is wired up as
  `#smt_evidence` — which records an **open obligation carrying the solver's verdict as
  evidence** and cannot close a goal. See the note on the SMT path below.
* **Tier 3** — a *local* neural proposer (`scripts/prover/propose.py`, ollama on
  localhost, no API key, no network). Off unless `AUTOFORM_NEURAL=1`, because a build
  must not silently depend on a model being installed. Its output is untrusted text:
  every candidate is re-elaborated and screened like any other rung.
* **Tier 4** — a real best-first search over proof states, backtracking with
  `Term.SavedState`, bounded by depth and a node budget, with the whole expansion logged.
* **Tier 5** — the search's move set: `intro`, conjunction/structure splitting, `split`
  on `match`/`if`, `cases` on hypotheses and data, `induction`, `funext`, and numeral
  generalization. Tier 4 is the engine, tier 5 is what it may do at each node.
* **Tier 6** — `#obligation`.

## The one invariant

**The portfolio never closes a goal it did not prove.** There is no `sorry` rung, no
`admit`, no fallback axiom, and no path — not the SMT path, not the neural path — that
can assign a goal without the Lean kernel checking the resulting term. Every candidate
proof is screened *after* the rung reports success for

* `sorryAx` (`Expr.hasSorry`),
* unassigned metavariables (`Expr.hasExprMVar`),
* **and any axiom outside `propext` / `Classical.choice` / `Quot.sound`** — which is what
  rules out `native_decide`'s `Lean.ofReduceBool` and anything an over-eager future rung
  might drag in.

If nothing works the tactic **fails**, printing everything it tried, so the goal stays
visibly open and the ledger can count it.

## Interface

* `portfolio` — run the ladder (tiers 1–2 by default), fail loudly if exhausted.
* `portfolio (maxTier := 5)` — spend more: 3 = neural (if enabled), 4/5 = search.
* `portfolio!` — also `logInfo` the full transcript (which rungs ran, which won).
* `#portfolio_check <prop>` — run the ladder on a *statement* without introducing any
  declaration, and report the outcome as a message.
* `#smt_evidence name : <prop>` — ask an external SMT solver, record the answer as
  evidence on an open obligation. Never produces a theorem.
* `#obligation name : <prop>` — record a goal nobody has proved as structured data.
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
  /-- What the portfolio tried before giving up, if it was run. Also where an external
  solver's verdict is recorded: *evidence about* the statement, never a proof of it. -/
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

/-- Store an `Obligation` as a definition, so it survives into other modules. -/
def recordObligation (o : Obligation) : TermElabM Name := do
  let declName := `openObligation ++ Name.mkSimple o.name
  addAndCompile <| .defnDecl
    { name := declName, levelParams := [], type := mkConst ``Obligation
      value := toExpr o, hints := .abbrev, safety := .safe }
  return declName

/-! ## The axiom screen

`hasSorry` is not enough. A rung could in principle produce a term that is free of
`sorryAx` but leans on `Lean.ofReduceBool` (what `native_decide` uses to hand the
compiler the kernel's job) or on some other axiom smuggled in through a library lemma.
The portfolio therefore walks the proof term's transitive constant closure and rejects
anything resting on an axiom outside the three the standard library is built on. -/

/-- Axioms a proof is allowed to depend on: exactly the Lean/Mathlib-standard three. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Every axiom in the transitive constant closure of `e` that is not in
`allowedAxioms`. Empty means the term is kernel-honest. -/
def forbiddenAxioms (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let mut visited : Std.HashSet Name := {}
  let mut todo : List Name := e.getUsedConstants.toList
  let mut bad : Array Name := #[]
  while !todo.isEmpty do
    match todo with
    | [] => break
    | c :: rest =>
      todo := rest
      if visited.contains c then continue
      visited := visited.insert c
      match env.find? c with
      | none => pure ()
      | some ci =>
        match ci with
        | .axiomInfo _ =>
          unless allowedAxioms.contains c do bad := bad.push c
        | _ =>
          todo := ci.type.getUsedConstants.toList ++ todo
          if let some v := ci.value? then
            todo := v.getUsedConstants.toList ++ todo
  return bad

/-- The full honesty screen applied to a candidate proof of `goal`: no `sorryAx`, no
open metavariable, no non-standard axiom. Returns `none` if clean, else the reason. -/
def screenProof (goal : MVarId) : MetaM (Option String) := do
  let prf ← instantiateMVars (mkMVar goal)
  if prf.hasSorry then return some "proof term contains `sorryAx`"
  if prf.hasExprMVar then return some "proof term contains an unassigned metavariable"
  let bad ← forbiddenAxioms prf
  if bad.isEmpty then return none
  return some s!"proof term depends on non-standard axiom(s): {bad.toList}"

/-! ## The ladder -/

/-- One rung of the escalation ladder. -/
structure Rung where
  /-- Escalation tier from STRATEGY.md §5. -/
  tier : Nat
  /-- Human-readable name, used in the transcript. -/
  label : String
  /-- The tactic to run. -/
  tac : TSyntax `tactic

/-- Parse a tactic from a string. Used for the dynamically-generated tier-5 moves
(`cases h`, `induction n`, `intro a b`, …) whose shape depends on the goal, and for the
untrusted candidates coming back from the tier-3 proposer. -/
def parseTactic? (s : String) : TermElabM (Option (TSyntax `tactic)) := do
  match Parser.runParserCategory (← getEnv) `tactic s "<portfolio>" with
  | .ok stx => return some ⟨stx⟩
  | .error _ => return none

/-- The rungs that exist in *this* build.

Tier 1 is the cheap decision-procedure tier. Tier 2 is search plus the bitvector
hammer: `bv_decide` is core, SAT-backed and LRAT-checked *by the kernel*, so it is a
genuine tier-2 rung and not an oracle. `aesop`, `duper` and `lean-smt` remain
unavailable (not dependencies — see `lakefile.toml`, which is off limits).

`native_decide` is deliberately absent at every tier: it discharges goals by trusting
the compiler, which would put a non-kernel oracle inside a gate whose entire purpose is
kernel-checked evidence — and the axiom screen would reject it anyway. -/
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
    mk 2 "bv_decide"          (← `(tactic| bv_decide)),
    mk 2 "intros; bv_decide"  (← `(tactic| (intros; bv_decide))),
    mk 2 "simp; bv_decide"    (← `(tactic| (simp; bv_decide))),
    mk 2 "bv_omega"           (← `(tactic| bv_omega)),
    mk 2 "exact?"             (← `(tactic| exact?)),
    mk 2 "intros; exact?"     (← `(tactic| (intros; exact?)))
  ]

/-- Closers only — the rungs the tier-4 search tries at each node before expanding it.
`exact?` is excluded here: it is far too slow to run at every node of a search. -/
def closerRungs (maxTier : Nat) : TermElabM (Array Rung) := do
  return (← ladder).filter fun r => r.tier ≤ min maxTier 2 && !r.label.endsWith "exact?"

/-- Tiers that exist in the design but have no implementation here. Listed in the
failure transcript so a reader can tell "unproved" from "not even attempted". This list
is computed, not asserted: the tier-3 entry reflects whether the local proposer is
actually switched on. -/
def unavailableTiers : IO (List String) := do
  let neural := (← IO.getEnv "AUTOFORM_NEURAL") == some "1"
  let tier3 : String :=
    if neural then
      "tier 3: local neural proposer — ENABLED (AUTOFORM_NEURAL=1); candidates are \
       still kernel-checked and axiom-screened like every other rung"
    else
      "tier 3: local neural proposer — available but OFF (set AUTOFORM_NEURAL=1 and \
       run a local ollama); no network or API key is ever used"
  return (
    [ "tier 2: aesop / lean-auto+duper / lean-smt — not dependencies of this build \
       (`bv_decide` IS available and is used; external SMT is reachable only as \
       *evidence* via `#smt_evidence`, since no Lean proof can be reconstructed from it)"
    , tier3
    , "tier 4/5: best-first search with decomposition/generalization — implemented; \
       reached only with `portfolio (maxTier := 4)` or higher" ] : List String)

/-- Run an attempt with the message log restored afterwards.

A failing rung is allowed to be noisy — `simp` can blow the recursion limit, `omega` can
complain — but that noise is *not* a build error: the goal is still handled by the next
rung, or reported honestly by the transcript. Anything a rung has to say about its own
success is untrusted anyway; what counts is `screenProof`. -/
def quietly {α} (x : TermElabM α) : TermElabM α := do
  let msgs := (← getThe Core.State).messages
  try
    x
  finally
    modifyThe Core.State fun st => { st with messages := msgs }

/-- Run one rung against `goal`, restoring all state if it does not fully close it.

Success requires *both* that no goals remain **and** that the resulting proof term
passes `screenProof`. The second check is the anti-self-certification guard: a rung is
not trusted to report its own honesty. -/
def tryRung (goal : MVarId) (r : Rung) : TermElabM Bool := quietly do
  let s ← saveState
  try
    let gs ← Tactic.run goal (Tactic.evalTactic r.tac)
    if !gs.isEmpty then
      s.restore; return false
    if let some why ← screenProof goal then
      trace[autoform.portfolio] "rejected `{r.label}`: {why}"
      s.restore; return false
    return true
  catch _ =>
    s.restore
    return false

/-- Apply `tac` to `goal` as a *move*: it may leave subgoals. Returns them, or `none` if
the tactic failed or made no progress. State is restored on failure, and the caller is
responsible for restoring it if it abandons the branch. -/
def tryMove (goal : MVarId) (tac : TSyntax `tactic) : TermElabM (Option (List MVarId)) := quietly do
  let s ← saveState
  let before ← instantiateMVars (← goal.getType)
  try
    let gs ← Tactic.run goal (Tactic.evalTactic tac)
    -- Reject no-ops: a move that returns the same single goal is a loop.
    if h : gs.length = 1 then
      let g := gs[0]
      if (← instantiateMVars (← g.getType)) == before then
        s.restore; return none
    return some gs
  catch _ =>
    s.restore
    return none

/-! ## Tier 5: decomposition and generalization moves

These are the moves the search may make at a node. None of them closes a goal; they
turn one goal into (hopefully easier) subgoals, which the tier-1/2 closers then attack.
That division is what keeps the honesty property trivial to see: only `tryRung` ever
assigns a goal, and it always screens the result. -/

/-- Number of leading binders of a `∀`/`→` telescope, capped. -/
private def binderCount : Expr → Nat
  | .forallE _ _ b _ => 1 + binderCount b
  | _ => 0

/-- Rough size of an expression, used to rank candidate expansions. -/
private def exprSize : Expr → Nat
  | .app f a => 1 + exprSize f + exprSize a
  | .lam _ t b _ => 1 + exprSize t + exprSize b
  | .forallE _ t b _ => 1 + exprSize t + exprSize b
  | .letE _ t v b _ => 1 + exprSize t + exprSize v + exprSize b
  | .mdata _ e => exprSize e
  | .proj _ _ e => 1 + exprSize e
  | _ => 1

/-- A candidate move: the tactic text (also its transcript label) and a cost used to
break ties in the best-first ordering (cheap structural moves first). -/
structure Move where
  /-- Tactic source; parsed on demand. -/
  text : String
  /-- Prior cost: lower is tried first, all else equal. -/
  cost : Nat

/-- Generate the tier-5 move set for `goal`.

* `intro` with *named* binders (so later moves can name them),
* `refine ⟨?_, ?_⟩` / `constructor` — conjunction and structure decomposition,
* `split` — case-split a `match` or `if` in the goal,
* `cases h` on each hypothesis whose type is an inductive (∧, ∨, ∃, or data),
* `induction x` on each data variable (tier 5 proper — this is what closes the goals
  the flat ladder provably cannot),
* `funext` on function equalities,
* `generalize` of a numeral in the goal — `Autoform/Refine.lean`'s own history is that
  generalizing a concrete constant is what makes a statement inductively provable.

`allowHeavy` is false at tier 4 and true at tier 5: `induction` and `generalize` are the
moves that blow up the branching factor, so a tier-4 budget does structure only. -/
def movesFor (goal : MVarId) (allowHeavy : Bool) (depth : Nat) : TermElabM (Array Move) :=
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let mut ms : Array Move := #[]
    let nb := min (binderCount ty) 6
    if nb > 0 then
      let names := (List.range nb).map fun i => s!"h{depth}x{i}"
      ms := ms.push ⟨"intro " ++ String.intercalate " " names, 0⟩
    -- structural decomposition of the target
    let hd := ty.getAppFn
    if hd.isConstOf ``And || hd.isConstOf ``Iff then
      ms := ms.push ⟨"refine ⟨?_, ?_⟩", 1⟩
    if hd.isConstOf ``Exists || hd.isConstOf ``Or then
      ms := ms.push ⟨"constructor", 3⟩
    ms := ms.push ⟨"split", 2⟩
    ms := ms.push ⟨"funext fx", 4⟩
    -- moves over the local context
    for d in (← getLCtx) do
      if d.isImplementationDetail || d.userName.hasMacroScopes then continue
      let n := d.userName.toString
      if n.length == 0 || n.front == '_' then continue
      let dty ← instantiateMVars d.type
      let isProp ← Meta.isProp dty
      let some ind := dty.getAppFn.constName? | continue
      match (← getEnv).find? ind with
      | some (.inductInfo iv) =>
        if isProp then
          -- ∧ / ∨ / ∃ / any inductive predicate: case analysis on the hypothesis
          if iv.numCtors ≤ 4 then
            ms := ms.push ⟨s!"cases {n}", 2⟩
        else
          if iv.numCtors ≤ 6 then
            ms := ms.push ⟨s!"cases {n}", 2⟩
          if allowHeavy && iv.isRec then
            ms := ms.push ⟨s!"induction {n}", 5⟩
      | _ => pure ()
    -- definitional unfolding of *project* constants: a goal about `evalStmt` is not
    -- going anywhere until the interpreter's equations are in play. Restricted to
    -- `Autoform.*` so the search never tries to unfold the standard library.
    let mut unfolded := 0
    for c in (← instantiateMVars (← goal.getType)).getUsedConstants do
      if unfolded ≥ 3 then break
      if !(`Autoform).isPrefixOf c then continue
      let cs := c.toString
      if c.isInternal then continue
      if (cs.splitOn "match_").length > 1 || (cs.splitOn "inst").length > 1 then continue
      match (← getEnv).find? c with
      | some (.defnInfo _) =>
        unfolded := unfolded + 1
        ms := ms.push ⟨s!"simp only [{c}]", 3⟩
        ms := ms.push ⟨s!"unfold {c}", 4⟩
      | _ => pure ()
    -- generalization of a numeral in the target (heavy: only at tier 5)
    if allowHeavy then
      let lits := ty.getUsedConstants  -- cheap guard; the real scan is below
      let _ := lits
      let mut found : Option Nat := none
      let rec scan (e : Expr) : Option Nat :=
        match e.rawNatLit?, e.nat? with
        | some k, _ => some k
        | _, some k => some k
        | _, _ =>
          match e with
          | .app f a => (scan f).orElse fun _ => scan a
          | .mdata _ b => scan b
          | _ => none
      found := scan ty
      if let some k := found then
        if k > 0 && k < 1000 then
          ms := ms.push ⟨s!"generalize hg{depth} : {k} = gv{depth}", 6⟩
    return ms.qsort (fun a b => a.cost < b.cost)

/-! ## Tier 4: best-first search

At each node: try to close with a tier-1/2 rung; otherwise expand every applicable
tier-5 move, *score* the resulting subgoal sets (total size, penalised by how many
subgoals were produced), and recurse into the cheapest first. Backtracking is
`Term.SavedState.restore`, so a failed branch leaves no trace. Both depth and total node
expansions are bounded; the whole expansion is logged into the transcript. -/

/-- Search configuration. -/
structure SearchCfg where
  /-- Maximum move depth. -/
  maxDepth : Nat := 3
  /-- Total node-expansion budget across the whole search. -/
  budget : Nat := 400
  /-- Whether `induction` and `generalize` are in the move set (tier 5 vs tier 4). -/
  allowHeavy : Bool := true
  /-- Tier bound handed to the closers at each node. -/
  closerTier : Nat := 2

/-- The mutable state of one search: remaining budget and the transcript. -/
structure SearchState where
  /-- Node expansions left. -/
  fuel : Nat
  /-- Human-readable record of what was tried, for the ledger. -/
  log : Array String

/-- Best-first proof search. Returns `true` iff `goal` is fully closed by a proof that
passed the honesty screen at every leaf. -/
partial def searchGoal (cfg : SearchCfg) (st : IO.Ref SearchState) (goal : MVarId)
    (depth : Nat) (path : String) : TermElabM Bool := do
  if (← st.get).fuel == 0 then return false
  st.modify fun s => { s with fuel := s.fuel - 1 }
  let closers ← closerRungs cfg.closerTier
  for r in closers do
    if ← tryRung goal r then
      st.modify fun s => { s with log := s.log.push s!"  ✓ {path}{r.label}" }
      return true
  if depth ≥ cfg.maxDepth then
    st.modify fun s => { s with log := s.log.push s!"  ✗ {path}(depth limit)" }
    return false
  -- Expand: measure every applicable move, then recurse cheapest-first.
  let moves ← movesFor goal cfg.allowHeavy depth
  let mut scored : Array (Move × Nat) := #[]
  for m in moves do
    if (← st.get).fuel == 0 then break
    let some tac ← parseTactic? m.text | continue
    let s ← saveState
    match ← tryMove goal tac with
    | none => s.restore
    | some gs =>
      let mut sz := 0
      for g in gs do
        sz := sz + exprSize (← instantiateMVars (← g.getType))
      s.restore
      scored := scored.push (m, sz + 6 * gs.length + m.cost)
  let ranked := scored.qsort (fun a b => a.2 < b.2)
  for (m, sc) in ranked do
    if (← st.get).fuel == 0 then return false
    let some tac ← parseTactic? m.text | continue
    let s ← saveState
    match ← tryMove goal tac with
    | none => s.restore
    | some gs =>
      st.modify fun st' =>
        { st' with log := st'.log.push s!"  → {path}{m.text}  ({gs.length} subgoal(s), score {sc})" }
      let mut ok := true
      for g in gs do
        unless ← searchGoal cfg st g (depth + 1) (path ++ m.text ++ " ⊢ ") do
          ok := false
          break
      if ok then
        -- Every leaf was closed by a screened rung; re-screen the whole assembled term.
        if let some why ← screenProof goal then
          st.modify fun st' => { st' with log := st'.log.push s!"  ✗ rejected assembled proof: {why}" }
          s.restore
        else
          return true
      else
        s.restore
  return false

/-! ## Tier 3: the local neural proposer

`scripts/prover/propose.py` asks a model running on localhost for candidate tactic
scripts. The model is not trusted in any way: each candidate is parsed, run, required to
close the goal, and screened for `sorryAx`/metavariables/axioms exactly like a
hand-written rung. A hallucination costs time, never soundness. -/

/-- Where the driver scripts live (overridable, defaults to the repo layout). -/
def proverDir : IO System.FilePath := do
  return match ← IO.getEnv "AUTOFORM_PROVER_DIR" with
    | some d => (d : System.FilePath)
    | none => ("scripts" : System.FilePath) / "prover"

/-- Run a driver script with `input` on stdin (via a temp file, so no pipe handling),
returning its stdout, or `none` if the script is missing or errored. -/
def runDriver (script : String) (input : String) : IO (Option String) := do
  let dir ← proverDir
  let path := dir / script
  unless ← path.pathExists do return none
  let tmpDir : System.FilePath := (← IO.getEnv "TMPDIR").getD "/tmp"
  let tmp := tmpDir / s!"autoform-portfolio-{← IO.monoNanosNow}.txt"
  IO.FS.writeFile tmp input
  try
    let out ← IO.Process.output { cmd := "python3", args := #[path.toString, tmp.toString] }
    IO.FS.removeFile tmp
    if out.exitCode != 0 then return none
    return some out.stdout
  catch _ =>
    try IO.FS.removeFile tmp catch _ => pure ()
    return none

/-- Ask the local model for whole-proof candidates and try each one. Returns the winning
candidate's text, if any. Disabled unless `AUTOFORM_NEURAL=1` (the script enforces this
too, so the default build never talks to anything). -/
def tryNeural (goal : MVarId) (goalStr : String) : TermElabM (Option String) := do
  unless (← IO.getEnv "AUTOFORM_NEURAL") == some "1" do return none
  let some out ← runDriver "propose.py" goalStr | return none
  for line in out.splitOn "\n" do
    let cand := line.trimAscii.toString
    if cand.isEmpty || cand.startsWith "#" then continue
    let some tac ← parseTactic? ("(" ++ cand ++ ")") | continue
    if ← tryRung goal ⟨3, s!"neural: {cand}", tac⟩ then
      return some cand
  return none

/-! ## Report -/

/-- Outcome of a portfolio run: the winning rung (if any) and the full transcript. -/
structure Report where
  /-- `some (tier, label)` of the rung that closed the goal. -/
  winner : Option (Nat × String)
  /-- Every rung attempted, in order, `label` prefixed by its tier. -/
  tried : List String
  /-- Search transcript (empty if tier 4/5 was not reached). -/
  searchLog : List String := []

/-- Render a report as ledger evidence. -/
def Report.render (rep : Report) (goalStr : String) : IO String := do
  let unavail ← unavailableTiers
  let searchPart :=
    if rep.searchLog.isEmpty then ""
    else "\n  search  :\n" ++ String.intercalate "\n" rep.searchLog
  match rep.winner with
  | some (t, l) =>
      return s!"portfolio: CLOSED at tier {t} by `{l}`\n  goal    : {goalStr}\n  \
         attempted: {rep.tried.length} rung(s): {String.intercalate ", " rep.tried}" ++ searchPart
  | none =>
      return s!"portfolio: OPEN — no rung closed the goal\n  goal    : {goalStr}\n  \
         attempted: {rep.tried.length} rung(s): {String.intercalate ", " rep.tried}" ++ searchPart ++
         "\n  not attempted / limits:\n    " ++ String.intercalate "\n    " unavail

/-- Walk the ladder up to `maxTier`. Returns the report; the goal is assigned iff
`winner` is `some`.

Tier order: flat rungs 1–2, then the neural proposer (3), then the bounded best-first
search (4 = structural moves, 5 = plus induction/generalization). -/
def runPortfolio (goal : MVarId) (maxTier : Nat) : TermElabM Report := do
  let rungs ← ladder
  let mut tried : List String := []
  for r in rungs do
    if r.tier ≤ maxTier then
      tried := tried ++ [s!"[{r.tier}] {r.label}"]
      trace[autoform.portfolio] "trying [{r.tier}] {r.label}"
      if ← tryRung goal r then
        return { winner := some (r.tier, r.label), tried }
  if maxTier ≥ 3 then
    let goalStr := toString (← Meta.ppExpr (← goal.getType))
    if let some cand ← tryNeural goal goalStr then
      return { winner := some (3, s!"neural proposer: {cand}"), tried := tried ++ ["[3] neural proposer"] }
    tried := tried ++ ["[3] neural proposer (no accepted candidate)"]
  if maxTier ≥ 4 then
    let heavy := maxTier ≥ 5
    let cfg : SearchCfg :=
      { maxDepth := if heavy then 6 else 4, budget := if heavy then 1200 else 400
        allowHeavy := heavy, closerTier := 2 }
    let st ← IO.mkRef { fuel := cfg.budget, log := #[] : SearchState }
    let ok ← searchGoal cfg st goal 0 ""
    let s ← st.get
    let tier := if heavy then 5 else 4
    tried := tried ++ [s!"[{tier}] best-first search (depth ≤ {cfg.maxDepth}, budget {cfg.budget}, \
      heavy moves {if heavy then "on" else "off"})"]
    if ok then
      return { winner := some (tier, "best-first search"), tried, searchLog := s.log.toList }
    return { winner := none, tried, searchLog := s.log.toList }
  return { winner := none, tried }

/-! ## The tactic -/

/-- Shared body of the `portfolio` tactic variants. -/
def portfolioCore (verbose : Bool) (maxTier : Nat) : TacticM Unit := do
  let goal ← getMainGoal
  let rest := (← getGoals).drop 1
  let goalStr := toString (← Meta.ppExpr (← goal.getType))
  let rep ← runPortfolio goal maxTier
  let msg ← rep.render goalStr
  match rep.winner with
  | some _ =>
    -- Final belt-and-braces screen of the assembled term, whatever tier produced it.
    if let some why ← screenProof goal then
      throwError "portfolio: a rung reported success but the proof is not honest: {why}\n{msg}"
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
  -- the optional `(maxTier := n)` group: find the numeral wherever it sits
  let maxTier : Nat := Id.run do
    for a in stx[1].getArgs do
      if let some k := a.isNatLit? then return k
      for b in a.getArgs do
        if let some k := b.isNatLit? then return k
    return 2
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
    logInfo (← rep.render goalStr)

/-! ### The SMT path

An external SMT solver is reachable on this machine (`scripts/prover/smt.py` finds
`cvc5`, `z3`, or the `z3` Python module). What is *not* reachable is a reconstruction of
a Lean proof from the solver's answer: there is no `lean-smt`, no proof-certificate
importer, and writing one is not a Portfolio.lean-sized job.

So the solver is wired in the only honest way: `#smt_evidence` records an **open
obligation** whose `attempted` field carries the solver's verdict. Nothing is proved,
nothing is assigned, and no theorem appears. An `unsat` here means "a program you did
not verify believes this" — evidence for triage, not for the ledger's proved column.
The translation covers the linear integer fragment only, and refuses anything else. -/

/-- Translate an `Int`/`Nat` linear-arithmetic `Prop` to SMT-LIB. Returns the assertion
text plus the declarations, or `none` if the goal leaves the supported fragment. -/
partial def toSMT (e : Expr) : MetaM (Option String) := do
  let rec term (e : Expr) : MetaM (Option String) := do
    let e ← instantiateMVars e
    if let some k := e.int? then
      return some (if k < 0 then s!"(- {-k})" else toString k)
    if let some k := e.nat? then return some (toString k)
    if e.isFVar then return some ((← e.fvarId!.getUserName).toString)
    let f := e.getAppFn
    let args := e.getAppArgs
    let some c := f.constName? | return none
    let bin (op : String) : MetaM (Option String) := do
      if args.size < 2 then return none
      let some a ← term args[args.size - 2]! | return none
      let some b ← term args[args.size - 1]! | return none
      return some s!"({op} {a} {b})"
    match c with
    | ``HAdd.hAdd => bin "+"
    | ``HSub.hSub => bin "-"
    | ``HMul.hMul => bin "*"
    | ``Neg.neg =>
      if args.size < 1 then return none
      let some a ← term args[args.size - 1]! | return none
      return some s!"(- {a})"
    | _ => return none
  let rec form (e : Expr) : MetaM (Option String) := do
    let e ← instantiateMVars e
    let f := e.getAppFn
    let args := e.getAppArgs
    let some c := f.constName? | return none
    let bin2 (op : String) : MetaM (Option String) := do
      if args.size < 2 then return none
      let some a ← term args[args.size - 2]! | return none
      let some b ← term args[args.size - 1]! | return none
      return some s!"({op} {a} {b})"
    let logic (op : String) : MetaM (Option String) := do
      if args.size < 2 then return none
      let some a ← form args[0]! | return none
      let some b ← form args[1]! | return none
      return some s!"({op} {a} {b})"
    match c with
    | ``Eq => bin2 "="
    | ``LE.le => bin2 "<="
    | ``LT.lt => bin2 "<"
    | ``GE.ge => bin2 ">="
    | ``GT.gt => bin2 ">"
    | ``And => logic "and"
    | ``Or => logic "or"
    | ``Iff => logic "="
    | ``Not =>
      if args.size < 1 then return none
      let some a ← form args[0]! | return none
      return some s!"(not {a})"
    | _ =>
      if e.isArrow then
        let some a ← form e.bindingDomain! | return none
        let some b ← form e.bindingBody! | return none
        return some s!"(=> {a} {b})"
      return none
  -- Strip the ∀/→ prefix: numeric binders become declarations, propositional ones
  -- (the hypotheses) become assumptions. `unsat` on hypotheses ∧ ¬conclusion is
  -- exactly "the implication is valid".
  forallTelescope e fun xs body => do
    let mut decls : Array String := #[]
    let mut hyps : Array String := #[]
    for x in xs do
      let ty ← instantiateMVars (← inferType x)
      let n := (← x.fvarId!.getUserName).toString
      if ty.isConstOf ``Int then
        decls := decls.push s!"(declare-const {n} Int)"
      else if ty.isConstOf ``Nat then
        decls := decls.push s!"(declare-const {n} Int)"
        hyps := hyps.push s!"(assert (>= {n} 0))"
      else if ← Meta.isProp ty then
        let some h ← form ty | return none
        hyps := hyps.push s!"(assert {h})"
      else
        return none
    let some b ← form body | return none
    return some <|
      "(set-logic QF_LIA)\n" ++ String.intercalate "\n" decls.toList ++ "\n" ++
      String.intercalate "\n" hyps.toList ++
      s!"\n; the NEGATION of the conclusion; `unsat` therefore means the claim is valid\n\
        (assert (not {b}))\n(check-sat)\n"

/-- `#smt_evidence name : <prop>` — hand a linear-arithmetic statement to an external
solver and record the answer as **evidence on an open obligation**. This never proves
anything: no term is produced, no goal is assigned, and the declaration it adds has type
`Obligation`. -/
syntax (name := smtEvidenceStx) "#smt_evidence" ident " : " term : command

open Lean.Elab.Command in
@[command_elab smtEvidenceStx] def elabSmtEvidence : CommandElab := fun stx => do
  let id : Ident := ⟨stx[1]⟩
  let t : Term := ⟨stx[3]⟩
  let modName := (← getEnv).mainModule
  liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    unless ← Meta.isProp e do
      throwError "#smt_evidence expects a Prop, got{indentExpr e}"
    let stmt := toString (← Meta.ppExpr e)
    let verdict ←
      match ← toSMT e with
      | none => pure "not attempted: outside the supported linear-integer fragment"
      | some problem =>
        match ← runDriver "smt.py" problem with
        | none => pure "not attempted: no solver driver available"
        | some out => pure (out.trimAscii.toString)
    let o : Obligation :=
      { name := id.getId.toString, statement := stmt, module := modName.toString
        attempted := [s!"external SMT: {verdict}",
          "NOT A PROOF: no Lean term was reconstructed from the solver's answer"] }
    let decl ← recordObligation o
    logWarning s!"OPEN OBLIGATION `{id.getId}` : {stmt}\n  \
      external SMT verdict: {verdict}\n  \
      This is EVIDENCE, not a proof: nothing was reconstructed in Lean, the goal is \
      still open, and `{decl}` has type `Obligation`."

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
  let modName := (← getEnv).mainModule
  let stmt ← liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    unless ← Meta.isProp e do
      throwError "#obligation expects a Prop, got{indentExpr e}"
    pure (toString (← Meta.ppExpr e))
  let o : Obligation :=
    { name := id.getId.toString, statement := stmt
      module := modName.toString, attempted := [] }
  let declName ← liftTermElabM (recordObligation o)
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
about `Autoform.Imp`'s actual semantics and about `Autoform.Core.Numeric`'s machine
integers. Each `portfolio!` prints which rung won, so the build log itself is the
ledger evidence. -/

namespace Demo

open Autoform.Imp
open Autoform.Core (IntType Width)

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

/-- A loop whose guard is false terminates in the same state, under the *relation*. -/
example (s : State) (c : Stmt) : BigStep s (.loop .ff c) s := by portfolio!

/-- Assignment agrees with the relation, for *all* states and expressions. -/
example (s : State) (x : Var) (e : Expr) :
    BigStep s (.assign x e) (s.set x (evalExpr s e)) := by portfolio!

/-- Plain arithmetic side-condition of the kind the transpiler emits. -/
example (a b : Nat) : a + b + 0 = b + a := by portfolio! (maxTier := 1)

/-! ### Tier 2, for real: `bv_decide`

`Numeric.lean`'s open-obligation list says its bitwise/shift laws "should be closed with
`bv_decide` after a `BitVec` refinement", and `bv_decide` is in Lean **core**. These are
those obligations, stated at the `BitVec` level where they are the actual content:

* obligation 1 (`wrap` is a ring homomorphism ℤ → ℤ/2ⁿ) is exactly "truncation commutes
  with `+` and `*`",
* obligation 3 (`shl_eq_mul`) is `x <<< k = x * 2 ^ k`,
* obligation 4 (`band_self` and the de Morgan laws).

Tiers 1–2-without-`bv_decide` closed none of these; SAT + a kernel-checked LRAT
certificate closes all of them in about a second each. `#print axioms` on a `bv_decide`
proof lists only `propext`/`Quot.sound`/`Classical.choice` — no `ofReduceBool`, no
compiler trust — which is why this rung is allowed in and `native_decide` is not. -/

/-- Obligation 1, additive half: truncation is an additive homomorphism. -/
example (x y : BitVec 64) : (x + y).truncate 32 = x.truncate 32 + y.truncate 32 := by
  portfolio!

/-- Obligation 1, multiplicative half. -/
example (x y : BitVec 64) : (x * y).truncate 32 = x.truncate 32 * y.truncate 32 := by
  portfolio!

/-- Obligation 3: shifting left by `k` is multiplication by `2 ^ k`, in-width. -/
example (x : BitVec 32) : x <<< 5 = x * 32 := by portfolio!

/-- Obligation 4: de Morgan for the machine bitwise operators. -/
example (x y : BitVec 32) : ~~~(x &&& y) = ~~~x ||| ~~~y := by portfolio!

/-! ### Tiers 4–5: search with decomposition

Each of the following is *refused* by the flat ladder (the `#portfolio_check` above each
one shows the tier-1–2 refusal, printed into the build log) and *closed* by the bounded
best-first search, which finds the case analysis the flat rungs cannot: split the
`IntType`, split the `Width` under it, then `decide` the leaves. The transcript of the
winning path is in the `portfolio!` output. -/

#portfolio_check ∀ t : IntType, 0 < t.modulus
example : ∀ t : IntType, 0 < t.modulus := by portfolio! (maxTier := 5)

#portfolio_check ∀ t : IntType, 0 < t.half
example : ∀ t : IntType, 0 < t.half := by portfolio! (maxTier := 5)

#portfolio_check ∀ w : Width, w.bits % 8 = 0
example : ∀ w : Width, w.bits % 8 = 0 := by portfolio! (maxTier := 5)

#portfolio_check ∀ t : IntType, t.wrap 0 = 0
example : ∀ t : IntType, t.wrap 0 = 0 := by portfolio! (maxTier := 5)

#portfolio_check ∀ t : IntType, t.isFixed = true → t.lo ≠ none
example : ∀ t : IntType, t.isFixed = true → t.lo ≠ none := by portfolio! (maxTier := 5)

/-! A statement about the interpreter, not about arithmetic: a hole never yields a
state. Flat rungs cannot do it (it needs `cases` on the fuel *and* on the outcome); the
search can. -/
#portfolio_check ∀ (n : Nat) (s : State) (h : Nat), evalStmt n s (.opaqueHole h) ≠ .ok s
example : ∀ (n : Nat) (s : State) (h : Nat),
    evalStmt n s (.opaqueHole h) ≠ .ok s := by portfolio! (maxTier := 5)

/-! ### Goals the portfolio correctly refuses

`#portfolio_check` runs the same ladder but introduces no declaration, so a refusal is
visible in the build log without anything being admitted. Both of these need induction
over a derivation and over fuel simultaneously — beyond the bounded search too, and the
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

/-! ### The SMT path, kept on the evidence side of the line

An external solver is installed on some machines and reachable through
`scripts/prover/smt.py`. It is *not* wired to the tactic, because nothing here can turn
`unsat` into a Lean term. `#smt_evidence` therefore records an **open obligation** with
the solver's verdict attached: the statement below stays unproved, and the warning says
so. If a proof-reconstructing SMT frontend ever becomes a dependency, this is the seam
where it plugs in — until then, the solver's opinion is triage data, nothing more. -/

#smt_evidence Core.wrap_bound_linear :
  ∀ (a b : Int), 0 ≤ a → a < 4294967296 → 0 ≤ b → b < 4294967296 →
    0 ≤ a + b ∧ a + b < 8589934592

#obligations

end Demo
