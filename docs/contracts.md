# Contracts at holes

`Autoform/Contracts.lean`

## Why this exists

`STRATEGY.md` §5 lists, among the honest failure modes, *"Proof burden grows
superlinearly with program size. Hence: **verified core + contracts**, never
whole-repo."* `Autoform/Refine.lean` built the verified-core half. This file is the
other half, and until now it did not exist.

The cost of not having it is measurable. On `cachetools`, 165 of 238 functions are
hole-free and 74 are call-closed. A single untranslated construct anywhere in a function
makes the whole function unanalysable, because `Expr.hole l` evaluates to
`EResult.hole l`, `Refine.Outcome` has no `hole` constructor, and `refines_not_hole`
turns that into a theorem: *a refined function never reaches a hole.* That default is
correct and is not weakened here. What was missing is the opt-in — a way to say "assume
the hole labelled `op:starredUnpack` returns a value" and then prove the surrounding
function correct **relative to** that assumption, with the assumption surfaced rather
than discharged silently.

## The mechanism in one paragraph

A `Contract` names a hole label and asserts a property `post` of what the interpreter
produces there, within a declared `fuel` budget. An `Impl` is a witness: a map from hole
label to an ordinary `Expr` that replaces it. `Consistent Γ p σ` says the witness `σ`
meets the contracts `Γ` — in every heap, every environment, at every budget at or above
the declared one — and fills *only* labels `Γ` speaks about. Then

```lean
RefinesUnder Γ p name N dom spec :=
  ∀ σ, Consistent Γ p σ → Total Γ σ → Refines (σ.onProgram p) name N dom spec
```

That is: **for every** way of filling the contracted holes consistently with `Γ`, the
resulting program refines `spec` in the ordinary sense. There is no second interpreter
and no new evaluation rule; holes are filled with terms of the same language, so the
semantics being trusted is exactly the semantics the differential oracle tests.

## Why it is not `Refines`, and cannot be mistaken for it

* `Γ` is a parameter of the statement. A theorem is unconditional **iff** its `Γ` is
  literally `[]`, and in that case `refinesUnder_nil_iff` proves the two relations are
  equivalent. There is no other overlap.
* The `←` direction of that theorem needs the clause of `Consistent` that forbids `σ`
  from filling labels `Γ` does not mention. Without it, a "contract-relative" theorem
  could silently repair holes nobody declared. With it, `Γ` is an exact inventory of what
  was assumed.
* `RefinesUnder.discharge` is the only route back to `Refines`, and what it yields is
  `Refines (σ.onProgram p)` — a claim about the *repaired* program. Nothing in this file
  ever produces a claim about `p` itself from a non-empty `Γ`.

## The failure mode, and what is built in against it

A contract mechanism is a machine for assuming your conclusion. Four theorems make that
visible instead of latent:

| theorem | what it says |
|---|---|
| `refinesUnder_of_unsatisfiable` | if **no** implementation meets `Γ`, then `RefinesUnder Γ` holds for *every* spec |
| `unsatisfiable_of_false_post` | a contract with an unsatisfiable `post` makes `Γ` unsatisfiable, in any program — contradiction is detectable |
| `refinesUnder_unique` | if `Γ` **is** satisfiable, two specs proved under the same `Γ` agree on the domain |
| `methodkey_not_refinable_under_top` | an *unconstrained* contract proves nothing at all, on a real function |

The first is the whole problem stated as a theorem. Its consequence is that
`Satisfiable Γ p` is a **proof obligation**, not a comment — this file's demonstrations
prove it constructively, by exhibiting a witness implementation, before stating anything
relative to the contract.

The last is the counterweight to the obvious over-reaction. Satisfiability is necessary
and *not sufficient*: `topContract` ("this hole may do anything") is always satisfiable
(`satisfiable_top`) and provably useless, because leaving the hole exactly where it is is
one of the things "anything" includes, and `refines_not_hole` then bites. So the two
degenerate ends — a contract that assumes too much and one that assumes nothing — are
both detectable, and by different theorems.

## What a reader must check before believing a contract-relative theorem

In order. A theorem that fails any of these is not weak evidence, it is no evidence.

1. **Read `Γ`.** It is in the statement. If it is `[]` the theorem is unconditional and
   the rest of this list does not apply.
2. **Demand `Satisfiable Γ p`, with a proof.** By `refinesUnder_of_unsatisfiable`, a
   theorem whose contracts cannot be met carries zero information — it is true of every
   specification simultaneously, including contradictory ones. The
   `assumptionsJson` record carries a `satisfiable` flag and the name of the
   satisfiability proof precisely so this cannot be skipped. `false` there is a
   disqualification, not a caveat.
3. **Read each `post`, not each `stmt`.** `Contract.stmt` is unchecked prose for the
   assurance case; it is never used in a proof. A wrong `stmt` misleads a human and
   cannot mislead the kernel, which is exactly why a human has to check it.
4. **Ask whether the `post` is true of the real construct.** This is the only step no
   tool here performs, and it is where all the risk lives. `pureValueContract` asserts
   that a hole terminates, returns a value, raises nothing and does not mutate the heap.
   For `op:starredUnpack` in CPython that is *false in general*: `f(*x)` raises
   `TypeError` when `x` is not iterable. So a theorem using it is implicitly conditional
   on the unpacked argument being iterable, and that condition is real, unstated in `Γ`,
   and the reader's job to notice. Contracts move an assumption from invisible to
   visible; they do not make it true.
5. **Check the fuel budget.** `Contract.fuel` is the cost assumed for the untranslated
   construct. It is what keeps the `N` in a `RefinesUnder` theorem from being a lie.
6. **Check the name-resolution lemmas.** `resolve_methodkey`, `resolve_hashkey`,
   `resolve_kwargs` and `resolveMethod_hashedTuple_init` are stated separately rather than
   buried in an evaluation proof, because they are the facts that make the demonstration's
   program slice equivalent to the whole corpus, and they are the ones a reader should
   check against the real `cachetools`.
7. **Check the program the theorem is about.** The demonstrations here are stated over a
   two-function slice of the translated `cachetools`, using the generated `Func` values
   verbatim. The only thing a slice can change is name resolution, since `Ctx.resolve`
   falls back to a unique-suffix match over the function table. `#eval`s at the end of the
   demonstration section run the *full* 238-function program and confirm it agrees. That
   is evidence, not proof, and it is listed here as a reader obligation rather than
   claimed as one.

## What was proved on a real function

`cachetools/keys.py:methodkey` —

```python
def methodkey(self, *args, **kwargs):
    return hashkey(*args, **kwargs)
```

— translates to a body containing exactly one hole, `op:starredUnpack`, which is the most
common hole label in the corpus (33 occurrences). That one node is the entire reason the
function is outside the verifiable core.

* `methodkey_holes` — untouched, it reports `hole "op:starredUnpack"` at any adequate
  fuel. This is the status quo.
* `satisfiable_pureValue` — the contract can be met; witness exhibited.
* `methodkey_refinesUnder_value` — under that one contract, `methodkey` refines a total
  Lean function at fuel bound 14 on the unrestricted domain: it terminates, never raises,
  never reaches any other hole, and returns a freshly allocated `_HashedTuple`. Nothing is
  assumed about *which* value the hole produces; the conclusion is uniform over all
  implementations meeting the contract. (That uniformity is available only because the
  translated `_HashedTuple` has no `__init__`, so the unpacked arguments are not
  observable in the result — a fact about the translation that the proof discovered.)
* `methodkey_refinesUnder_raise` — under a *different* contract, the same function refines
  `raise payload` instead. The contract is load-bearing: it determines the conclusion, it
  does not merely permit a fixed one.
* `methodkey_raise_result` — the raising theorem paired with the one payload whose
  satisfiability is proved.
* `satisfiable_raises_zeroDiv` — and satisfiability of a raising contract is not free.
  Core can raise `ZeroDivisionError` (witness: `1 / 0`), so that payload is meetable; an
  assumption that the hole raises some arbitrary payload is *not* automatically meetable,
  and the obligation surfaces at the witness rather than being smuggled in.
* `methodkey_not_refinable_under_top` — under the unconstrained contract, no spec refines
  it, at any fuel bound, on any non-empty domain.

Read together: the mechanism admits a real function that was previously unspeakable, the
admission is exactly as strong as the stated assumption, and both degenerate contracts are
rejected by theorems rather than by discipline.

## Statement holes are deliberately out of scope

`substS` does **not** fill `Stmt.hole`. A statement-level hole is an untranslated
*effect*, and replacing it with an expression is a category error; the honest contract for
one would have to be a relation on control outcomes (`Ctl`), including `brk`/`cont`/`ret`
escaping from inside it. Doing that properly is a separate piece of work. Until then
`control:TRY-finally-escaping` (31 occurrences) and `scope:nonlocal-write` (8) remain
outside the mechanism, which is the conservative direction: they stay unspeakable rather
than becoming speakable on a shaky footing.

## The API for assumption extraction

`Ledger.lean` and `scripts/sacm.py` already turn every hole label into a named SACM
`Assumption` node of the **module**. A contract-relative theorem needs finer granularity:
its contracts are assumptions of *that theorem*, and discharging them is different work
from discharging the module's other holes.

```lean
structure Assumption where
  label     : String   -- the CPG hole label, matching Ledger.tally's keys
  statement : String   -- unchecked prose from Contract.stmt
  fuelBound : Nat      -- the budget assumed for the construct

def ContractEnv.assumptions : ContractEnv → List Assumption

def assumptionsJson (theoremName : String) (Γ : ContractEnv)
    (satisfiabilityProof : Option String) : Lean.Json
```

`assumptionsJson` emits, per contract-relative theorem:

```json
{ "theorem": "Autoform.Contracts.Demo.methodkey_refinesUnder_value",
  "relativeTo": [ { "label": "op:starredUnpack",
                    "statement": "…",
                    "fuelBound": 1 } ],
  "satisfiable": true,
  "satisfiabilityProof": "Autoform.Contracts.Demo.satisfiable_pureValue" }
```

What `scripts/sacm.py` should do with it:

1. Attach each `relativeTo` entry as an `Assumption` node **of the goal supported by that
   theorem**, not of the module — the label matches the module-level assumption node the
   ledger already emits, so the two can be cross-referenced rather than duplicated.
2. Treat `"satisfiable": false` as a **disqualification** of the supporting evidence, at
   least as severe as the unattributed-evidence cap it already applies. By
   `refinesUnder_of_unsatisfiable` such a theorem supports every claim equally, which is
   to say none.
3. Record `fuelBound`, so the assumed cost of the untranslated construct appears in the
   case rather than only in the Lean source.
