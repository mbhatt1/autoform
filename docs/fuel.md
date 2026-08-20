# Fuel, termination, and why a proof at one budget is not a proof

The Core interpreter is **fuel-indexed**: every evaluation function takes a `Nat` budget
that strictly decreases on each recursive call. This is what makes it total, and Lean
accepts it without `partial`. The cost is that every result carries a third possibility
alongside "a value" and "an exception": the budget ran out.

```lean
inductive EResult where
  | val      : Val → EResult
  | exn      : Val → EResult
  | hole     : String → EResult
  | outOfFuel : EResult
```

Four outcomes, and they mean genuinely different things:

| outcome | meaning |
|---|---|
| `val` / `exn` | the program did this |
| `hole l` | the program contains a construct we did not translate — *ignorance*, counted in the ledger |
| `outOfFuel` | we did not look far enough — *also* ignorance, but ours, not the transpiler's |

Keeping `hole` and `outOfFuel` apart matters. A hole is a permanent gap in the semantics;
running out of fuel is a budget we chose. Collapsing them would let "we didn't look" be
reported as "the code is untranslated", or worse, the reverse.

## What fuel is not

Fuel is **not** a termination argument. `outOfFuel` does not mean the program diverges,
and a program that terminates in CPython can still exhaust any budget you pick. So the
interpreter establishes *partial* correctness: whenever it produces an answer, that answer
is right. Total correctness — this function terminates on this domain — is a separate
claim requiring a decreasing measure, which is what `execStmt_loop_rule` in
`Autoform/Refine.lean` takes as an explicit argument.

## The problem this created

A specification proved at one fuel budget is a weak statement. `∀ x ∈ dom, law(x) at
FUEL = true` says the law holds *when evaluated with 400 units of fuel*. Nothing about it
rules out the law failing at 401. For a while every synthesized specification in
`Autoform/SpecsGen/` was of this shape, and each carried an open obligation reading
*"proved at FUEL only; fuel-independence unproved"* — one per law. (The count was 71 at
one point and 72 later; the population moves when the generated module is re-exported,
which is why this document quotes the *ratio* closed rather than a snapshot.)

That obligation is not a formality. Since the laws are `Bool`-valued and `outOfFuel` is a
distinct constructor, a law could in principle hold at `FUEL` for the wrong reason.

## Fuel monotonicity

`Autoform/FuelMono.lean` closes it. The statement, for each of the seven mutually
recursive interpreter functions:

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

`Stmt.tryFinally` is the one construct that does **not** propagate an out-of-fuel
sub-result. If the body exhausts fuel and the finalizer exits abnormally, Python's rule
makes the finalizer's outcome *discard* the body's — so the statement returns an ordinary
result computed from a partially-mutated heap, and more fuel mutates that heap further.

```python
try:
    x = 1
    x = 2
finally:
    return x
```

returns **1 at fuel 4** and **2 at fuel 5**. This is a theorem, not a caveat:

```lean
theorem tryFinally_breaks_fuel_mono :
    (execStmt cexCtx 4 cexHeap [] cexStmt).2 = .ret (.int 1) ∧
    (execStmt cexCtx 5 cexHeap [] cexStmt).2 = .ret (.int 2) ∧
    tfFreeS cexStmt = false := ⟨rfl, rfl, rfl⟩
```

The function table is empty, so it has nothing to do with call resolution — the construct
itself is the cause.

So the theorems carry a side condition rather than a weakened conclusion:

* `tfFreeS : Stmt → Bool` — this statement contains no `tryFinally`;
* `TFFreeCtx ctx` — no reachable function body contains one;
* `tfFree_of_table` — discharges `TFFreeCtx` from a table-wide check;
* `fuelMonoExclusions : List String := ["Stmt.tryFinally"]` — the exclusion as a
  `#print`-able value, not a comment.

**An honest exclusion with a proof beats a total theorem that quietly assumes.** If you
extend the interpreter and a construct breaks monotonicity, add it here with a
counterexample; do not weaken the statement to make it compile.

## Discharging the obligations

With monotonicity available, every `…_at_FUEL` theorem lifts to its ∀-fuel form:

```lean
theorem X : ∀ fuel, FUEL ≤ fuel → ((dom_X).all (lawY C fuel f_…)) = true
```

The route, in `Autoform/SpecsGen/Basis.lean`: `runCase_fuel_mono` reduces a `Case` to
`applyFunc_fuel_mono`; `all_transfer` lifts a per-element guard-and-law implication over
the domain list; twelve per-law transport lemmas and five guards handle the law families.
`C_tfFree : TFFreeCtx C` is proved **by computation** (`tfFree_of_table` over
`C.table.all`, by `rfl`), and each theorem additionally discharges
`tfFreeS f_X.body = true` per subject — so the exclusion is checked per function rather
than assumed globally.

Result: **72 of 72 fuel obligations closed, zero `def ob_*` stubs left.** The 11 remaining
obligations are not fuel-related; they are statements the proof portfolio cannot close at
all, so there was no `_at_FUEL` theorem to lift.

## The vacuity trap in `lawCommutes`

`EResult.beq r₁ r₂` is `true` when **both** sides are `outOfFuel`. A commutation law could
therefore hold vacuously — both orders equally failing to compute. The guard `gComm`
checks both argument orders, and it is evaluated over each law's own domain before
emission, for all 83 live laws.

**Result: 0 cases reached `outOfFuel` at `FUEL`.** It never mattered on this corpus. It is
still on the emission path, because "it does not happen to bite here" and "it cannot bite"
are different claims, and only the second is worth relying on.

## Regenerating

```bash
lake build Autoform.FuelMono           # the monotonicity theorems
lake env lean Autoform/FuelMono.lean   # re-elaborate from source, print axioms
scripts/synth_specs.py <Module> …      # re-derive the specs and their fuel forms
```

Never read a figure here without re-deriving it: a stale `.olean` produced ten fictitious
divergences on this project once already (`STRATEGY.md` §19).
