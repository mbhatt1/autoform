# Fuel, termination, and proofs at a fixed budget

The Core interpreter is **fuel-indexed**: every evaluation function takes a `Nat` budget
that strictly decreases on each recursive call. This makes it total, and Lean accepts it
without `partial`. Every result therefore carries a third possibility alongside "a value"
and "an exception": the budget ran out.

```lean
inductive EResult where
  | val      : Val → EResult
  | exn      : Val → EResult
  | hole     : String → EResult
  | outOfFuel : EResult
```

| outcome | meaning |
|---|---|
| `val` / `exn` | the program did this |
| `hole l` | the program contains a construct we did not translate — *ignorance*, counted in the ledger |
| `outOfFuel` | we did not look far enough — also ignorance, but ours, not the transpiler's |

`hole` and `outOfFuel` are kept apart. A hole is a permanent gap in the semantics; running
out of fuel is a budget we chose. Collapsing them would let "we did not look" be reported as
"the code is untranslated", or the reverse.

## What fuel is not

Fuel is not a termination argument. `outOfFuel` does not mean the program diverges, and a
program that terminates in CPython can still exhaust any budget. Fuel bounds execution of the formal model. It does not itself prove source-to-model
fidelity or establish that the returned value meets an independent specification.
Total correctness — this function terminates on this domain — is a separate claim requiring
a decreasing measure, which `execStmt_loop_rule` in `Autoform/Refine.lean` takes as an
explicit argument.

## The resulting problem

A specification proved at one fuel budget states what the model computes with that
budget. Transporting it to every larger budget requires a monotonicity theorem and
evidence that the recorded execution did not run out of fuel.

Since the laws are `Bool`-valued and `outOfFuel` is a distinct constructor, a law could in
principle hold at `FUEL` for the wrong reason.

## Fuel monotonicity

`Autoform/FuelMono.lean` closes the obligation. The statement, for each of the seven
mutually recursive interpreter functions:

> raising the budget cannot change a result that did not run out of fuel.

```lean
theorem applyFunc_fuel_mono_all {ctx} {k k'} … (hk : k ≤ k')
    (he : applyFunc ctx k h ρ … = (h', r)) (hne : r ≠ .outOfFuel) :
    applyFunc ctx k' h ρ … = (h', r)
```

Proved by a single induction on fuel over a seven-way conjunction covering
`evalExpr`, `evalList`, `evalPairs`, `execStmt`, `execFor`, `applyFunc` and
`applyClosure` — every recursive call is at `k`, so one induction hypothesis serves all
seven. Each function has a `_fuel_succ_all` form (`k` to `k+1`) and a `_fuel_mono_all` corollary
(`k ≤ k'`). The out-of-fuel spelling differs per function and is documented at each:
`EResult.outOfFuel` for `evalExpr`/`applyFunc`/`applyClosure`, `Sum.inl .outOfFuel` for
`evalList`/`evalPairs`, and a `Ctl` constructor for `execStmt`/`execFor`.

Axiom basis: `[propext, Classical.choice, Quot.sound]`. No `sorry`, no `native_decide`.

## Finalizers and incomplete execution

A language-level return, exception, break or continue carries the local environment
at its exit point. Handlers and finalizers use that environment. If a finalizer
completes normally, its updated locals accompany the pending exit; the already
computed return value or exception payload is preserved. If it exits abnormally,
its new exit replaces the pending one.

Interpreter holes and exhausted fuel are different: the body was not fully
interpreted, so its finalizer is not run. A `finally: return 1` cannot erase a
translation gap or turn an unfinished loop into an apparent result.

The regression theorem `tryFinally_preserves_incomplete` checks that an insufficient
budget reports `outOfFuel` instead of the partial value previously returned by the
finalizer. With sufficient fuel it returns the complete result. This correction
allows the unrestricted monotonicity proof to cover every statement constructor;
`fuelMonoExclusions` is now `[]`.

The legacy predicates `tfFreeS` and `TFFreeCtx` still mean that a statement or context
contains no finalizer. Older theorem entry points accept these premises for existing
generated modules. New `_all` entry points do not require them. Historical generated
comments that describe a finalizer counterexample refer to the previous semantics.

## Discharging the obligations

With monotonicity available, every `…_at_FUEL` theorem lifts to its ∀-fuel form:

```lean
theorem X : ∀ fuel, FUEL ≤ fuel → ((dom_X).all (lawY C fuel f_…)) = true
```

The route, in `Autoform/SpecsGen/Basis.lean`: `runCase_fuel_mono_all` reduces a `Case`
to `applyFunc_fuel_mono_all`; `all_transfer` lifts a per-element guard-and-law
implication over the domain list. The per-law `_fuel_mono_all` lemmas include
finalizers and require the same evaluated guards as other functions. The generator
uses these unrestricted entry points.

Run `./assure.sh examples/python_control ControlFlow` to regenerate native
comparisons, conformance proofs, mutation checks and independent replay for the
control-flow examples. Current proved and open counts are recorded in its reports.

## Vacuity in `lawCommutes`

`EResult.beq r₁ r₂` is `true` when both sides are `outOfFuel`. A commutation law could
therefore hold vacuously, with both orders equally failing to compute. The guard `gComm`
checks both argument orders, and it is evaluated over each law's own domain before emission,
for all 83 live laws.

Result: 0 cases reached `outOfFuel` at `FUEL`. It never mattered on this corpus. The guard
remains on the emission path, because "it does not happen to bite here" and "it cannot bite"
are different claims.

## Regenerating

```bash
lake build Autoform.FuelMono           # the monotonicity theorems
lake env lean Autoform/FuelMono.lean   # re-elaborate from source, print axioms
scripts/synth_specs.py <Module> …      # re-derive the specs and their fuel forms
```

Re-derive any figure here before relying on it: a stale `.olean` produced ten fictitious
divergences on this project once already (`STRATEGY.md` §19).
