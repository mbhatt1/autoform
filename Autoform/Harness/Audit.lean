import Lean

/-!
# Trust audit — implemented as Lean metaprogramming

Lean is self-hosting, so none of this needs an external tool (the Coq analogue requires
MetaCoq). `Lean.Environment` and proof terms are ordinary data.

Three checks, corresponding to three ways a "proved" theorem can be worthless:

* `#audit_axioms` — what is the theorem actually standing on? `sorryAx` means it is not
  proved at all; `Lean.ofReduceBool`/`ofReduceNat` mean the Lean compiler was trusted.
* `#audit_depends` — **dependency vacuity.** If the proof term never mentions the
  implementation, the theorem says nothing about the implementation. This is a cheap,
  sound *necessary* condition for non-vacuity, and it catches the most common failure
  mode of LLM-generated specs.
* `#audit_ledger` — emit the evidence as JSON for the trust ledger.

Dependency vacuity is necessary, not sufficient; the source-level mutation gate
(`scripts/mutate.py`) is the sufficient test. Cheap check first, expensive check second.
-/

namespace Autoform.Audit

open Lean Elab Command Meta

/-- Axioms whose presence changes what a proof means. -/
def suspiciousAxioms : List Name :=
  [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat]

/-- Constants transitively referenced by `root`'s value and type, up to `fuel` steps. -/
partial def transitiveDeps (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := [root]
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      if let some ci := env.find? n then
        let mut es := #[ci.type]
        if let some v := ci.value? then es := es.push v
        for e in es do
          for c in e.getUsedConstants do
            unless seen.contains c do todo := c :: todo
  return seen

/-- The axioms a constant depends on. -/
def axiomsOf (n : Name) : CoreM (Array Name) := collectAxioms n

/-- Report the axiom basis of a declaration, flagging the suspicious ones. -/
elab "#audit_axioms " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let axs ← liftCoreM <| axiomsOf n
  let bad := axs.filter (suspiciousAxioms.contains ·)
  if bad.isEmpty then
    logInfo m!"{n}: axioms {axs.toList} — clean"
  else
    logError m!"{n}: TRUSTED-CODE LEAK {bad.toList} (full basis {axs.toList})"

/-- Fail unless `thm`'s proof transitively mentions every constant in `impls`.

A theorem that does not mention the implementation cannot constrain it. -/
elab "#audit_depends " thm:ident " on " impls:ident+ : command => do
  let t ← liftCoreM <| realizeGlobalConstNoOverload thm
  let env ← getEnv
  let deps := transitiveDeps env t
  for i in impls do
    let iName ← liftCoreM <| realizeGlobalConstNoOverload i
    if deps.contains iName then
      logInfo m!"{t} depends on {iName} — not dependency-vacuous"
    else
      logError m!"VACUOUS: {t} never mentions {iName}; it constrains nothing"

/-- Ledger evidence for one declaration. -/
structure Evidence where
  name        : Name
  axioms      : List Name
  clean       : Bool
  depCount    : Nat
  deriving Repr

/-- Collect evidence for a declaration. -/
def evidenceFor (n : Name) : CommandElabM Evidence := do
  let axs ← liftCoreM <| axiomsOf n
  let env ← getEnv
  return { name := n
           axioms := axs.toList
           clean := !axs.any (suspiciousAxioms.contains ·)
           depCount := (transitiveDeps env n).size }

/-- Emit ledger evidence as JSON, for composition by the trust-ledger renderer. -/
elab "#audit_ledger " ids:ident+ : command => do
  let mut out : Array Json := #[]
  for i in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload i
    let e ← evidenceFor n
    out := out.push <| Json.mkObj
      [ ("name",     Json.str e.name.toString)
      , ("axioms",   Json.arr (e.axioms.map (Json.str ·.toString)).toArray)
      , ("clean",    Json.bool e.clean)
      , ("depCount", Json.num e.depCount) ]
  logInfo (Json.arr out).pretty

end Autoform.Audit
