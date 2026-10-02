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
program that terminates in CPython can still exhaust any budget. The interpreter therefore
establishes *partial* correctness: whenever it produces an answer, that answer is right.
Total correctness — this function terminates on this domain — is a separate claim requiring
a decreasing measure, which `execStmt_loop_rule` in `Autoform/Refine.lean` takes as an
explicit argument.

## The resulting problem

A specification proved at one fuel budget is a weak statement. `∀ x ∈ dom, law(x) at
FUEL = true` says the law holds when evaluated with 400 units of fuel. It does not rule out
the law failing at 401. Every synthesized specification in `Autoform/SpecsGen/` was of this
shape, and each carried an open obligation reading *"proved at FUEL only; fuel-independence
unproved"* — one per law. (The count was 71 at one point and 72 later; the population moves
when the generated module is re-exported, so any figure below is a snapshot of the tree at
the commit named in the "Where it stands" section, to be re-derived.)

Since the laws are `Bool`-valued and `outOfFuel` is a distinct constructor, a law could in
principle hold at `FUEL` for the wrong reason.

## Fuel monotonicity

`Autoform/FuelMono.lean` closes the obligation. The statement, for each of the seven
mutually recursive interpreter functions:

> raising the budget cannot change a result that did not run out of fuel.

```lean
theorem applyFunc_fuel_mono {ctx} (hctx : TFFreeCtx ctx) {k k'} … (hk : k ≤ k')
    (he : applyFunc ctx k h ρ … = (h', r)) (hne : r ≠ .outOfFuel) :
    applyFunc ctx k' h ρ … = (h', r)
```

Proved by a single induction on fuel over a seven-way conjunction covering
`evalExpr`, `evalList`, `evalPairs`, `execStmt`, `execFor`, `applyFunc` and
`applyClosure` — every recursive call is at `k`, so one induction hypothesis serves all
seven. Each function has a `_fuel_succ` form (`k` to `k+1`) and a `_fuel_mono` corollary
(`k ≤ k'`). The out-of-fuel spelling differs per function and is documented at each:
`EResult.outOfFuel` for `evalExpr`/`applyFunc`/`applyClosure`, `Sum.inl .outOfFuel` for
`evalList`/`evalPairs`, and a `Ctl` constructor for `execStmt`/`execFor`.

Axiom basis: `[propext, Classical.choice, Quot.sound]`. No `sorry`, no `native_decide`.

## The general statement is false

`Stmt.tryFinally` is the one construct that does not propagate an out-of-fuel sub-result.
If the body exhausts fuel and the finalizer exits abnormally, Python's rule makes the
finalizer's outcome discard the body's, so the statement returns an ordinary result computed
from a partially-mutated heap, and more fuel mutates that heap further.

```python
try:
    x = 1
    x = 2
finally:
    return x
```

returns **1 at fuel 4** and **2 at fuel 5**. This is a theorem:

```lean
theorem tryFinally_breaks_fuel_mono :
    (execStmt cexCtx 4 cexHeap [] cexStmt).2 = .ret (.int 1) ∧
    (execStmt cexCtx 5 cexHeap [] cexStmt).2 = .ret (.int 2) ∧
    tfFreeS cexStmt = false := ⟨rfl, rfl, rfl⟩
```

The function table is empty, so call resolution is not involved; the construct itself is the
cause.

The theorems therefore carry a side condition rather than a weakened conclusion:

* `tfFreeS : Stmt → Bool` — this statement contains no `tryFinally`;
* `TFFreeCtx ctx` — no reachable function body contains one;
* `tfFree_of_table` — discharges `TFFreeCtx` from a table-wide check;
* `fuelMonoExclusions : List String := ["Stmt.tryFinally"]` — the exclusion as a
  `#print`-able value, not a comment.

If you extend the interpreter and a construct breaks monotonicity, add it here with a
counterexample rather than weakening the statement.

## Discharging the obligations

With monotonicity available, a `…_at_FUEL` theorem lifts to its ∀-fuel form:

```lean
theorem X : ∀ fuel, FUEL ≤ fuel → ((dom_X).all (lawY C fuel f_…)) = true
```

The route, in `Autoform/SpecsGen/Basis.lean`: `runCase_fuel_mono` reduces a `Case` to
`applyFunc_fuel_mono`; `all_transfer` lifts a per-element guard-and-law implication over
the domain list; per-law `law*_fuel_mono` transport lemmas handle the law families. A
module that uses it proves `C_tfFree : TFFreeCtx C` by computation (`tfFree_of_table` over
`C.table.all`, by `rfl`), and each theorem additionally discharges `tfFreeS f_X.body = true`
per subject, so the exclusion is checked per function rather than assumed globally.

### Where it stands (tree at 9639df0)

The route is closed for the modules whose context really is `tryFinally`-free:
`SpecsGen/LinuxLib.lean`, `V8Exp.lean` and `V8Base/Base.lean` each state
`theorem C_tfFree : TFFreeCtx C`. (I did not re-derive how many of their laws are transported
rather than stated at one fuel; that is per-module, in each file's `obligations`.)

**It is NOT closed for `cachetools`, and the hypothesis is refuted.** The exporter learned to
translate `try/finally` after `SpecsGen/Cachetools.lean` was generated; 8 of the rendered
bodies (the `_cachedmethod`/`_cached` lock wrappers) now contain `Stmt.tryFinally`, the one
construct `FuelMono` excludes. `Autoform.SpecsGen.Cachetools.C_not_tfFree : ¬ TFFreeCtx C`
(proved, axioms `propext`/`Classical.choice`/`Quot.sound`) states this, and every
`∀ fuel ≥ FUEL` law that rested on `C_tfFree` has been turned into a `Prop`-valued `def`
(an open obligation, asserting nothing) with its content at `FUEL` kept as a theorem. In the
current file: 144 `…_at_FUEL` theorems (72 laws and 72 `…_guard_at_FUEL` guards, checked by
kernel computation), 72 fuel-transport obligations open, and 11 further obligations the
proof portfolio never closed (not fuel-related): `Cachetools.obligations.length = 83`
(`#eval`). Closing the 72 needs a reachability-restricted fuel-monotonicity lemma (one that
only requires the `tryFinally`-free property of bodies actually reachable from the subject)
or a corpus whose reachable bodies are `tryFinally`-free. The earlier claim here, "72 of 72
fuel obligations closed", was true of the previous export and is false now.

## Vacuity in `lawCommutes`

`EResult.beq r₁ r₂` is `true` when both sides are `outOfFuel`. A commutation law could
therefore hold vacuously, with both orders equally failing to compute. The guard `gComm`
checks both argument orders, and it is evaluated over each law's own domain before emission;
each law family carries such a guard, and in `SpecsGen/Cachetools.lean` every law has its
`…_guard_at_FUEL` theorem (7 `commutes_*` guards among the 72), kernel-checked.

When this was first measured (an earlier export, 83 live laws), 0 cases reached `outOfFuel`
at `FUEL`: it never mattered on that corpus. The guard remains on the emission path,
because "it does not happen to bite here" and "it cannot bite" are different claims.

## Regenerating

```bash
lake build Autoform.FuelMono           # the monotonicity theorems
lake env lean Autoform/FuelMono.lean   # re-elaborate from source, print axioms
scripts/synth_specs.py <Module> …      # re-derive the specs and their fuel forms
```

Re-derive any figure here before relying on it: a stale `.olean` produced ten fictitious
divergences on this project once already (`STRATEGY.md` §19).
