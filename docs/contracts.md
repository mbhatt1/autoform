# Contracts at holes

`Autoform/Contracts.lean`

## Why this exists

`STRATEGY.md` §5 lists, among the honest failure modes, *"Proof burden grows
superlinearly with program size. Hence: **verified core + contracts**, never
whole-repo."* `Autoform/Refine.lean` built the verified-core half. This file is the
other half.

On `cachetools`, 207 of 209 functions are
hole-free and 107 are call-closed. A single untranslated construct anywhere in a function
makes the whole function unanalysable, because `Expr.hole l` evaluates to
`EResult.hole l`, `Refine.Outcome` has no `hole` constructor, and `refines_not_hole`
turns that into a theorem: *a refined function never reaches a hole.* That default is
not weakened here. What this file adds is the opt-in: a way to say "assume the hole
labelled `op:starredUnpack` returns a value" and then prove the surrounding function
correct **relative to** that assumption, with the assumption surfaced rather than
discharged silently.

## The mechanism

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

## How it differs from `Refines`

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

## The failure mode, and the guards against it

A contract mechanism can be used to assume its conclusion. Four theorems make that visible
rather than latent:

| theorem | what it says |
|---|---|
| `refinesUnder_of_unsatisfiable` | if **no** implementation meets `Γ`, then `RefinesUnder Γ` holds for *every* spec |
| `unsatisfiable_of_false_post` | a contract with an unsatisfiable `post` makes `Γ` unsatisfiable, in any program — contradiction is detectable |
| `refinesUnder_unique` | if `Γ` **is** satisfiable, two specs proved under the same `Γ` agree on the domain |
| `methodkey_not_refinable_under_top` | an *unconstrained* contract proves nothing at all, on a real function |

By the first, `Satisfiable Γ p` is a **proof obligation**, not a comment. This file's
demonstrations prove it constructively, by exhibiting a witness implementation, before
stating anything relative to the contract.

Satisfiability is necessary and *not sufficient*. `topContract` ("this hole may do
anything") is always satisfiable (`satisfiable_top`) and useless, because leaving the hole
where it is is one of the things "anything" includes, and `refines_not_hole` then applies.
The two degenerate ends — a contract that assumes too much and one that assumes nothing —
are detectable by different theorems.

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
4. **Ask whether the `post` is true of the real construct.** No tool here performs this
   step. `pureValueContract` asserts
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
   demonstration section run the *full* 208-function program and confirm it agrees. That
   is evidence, not proof, and it is listed here as a reader obligation rather than
   claimed as one.

## What was proved on a real function

`cachetools/keys.py:methodkey` —

```python
def methodkey(self, *args, **kwargs):
    return hashkey(*args, **kwargs)
```

— **used** to translate to a body containing exactly one hole, `op:starredUnpack`, the most
common hole label in the corpus (36 occurrences on the committed AST). That one node was
the entire reason the function was outside the verifiable core.

It no longer is. STRATEGY.md §35 added the calling convention, so `methodkey` is hole-free
and `Autoform/Contracts.lean` proves **`methodkey_refines` unconditionally** — an ordinary
`Refine.Refines`, `Γ = []`. The contract-relative theorems below are kept and re-pointed
at `keysProgramHoled`, which is `methodkey` **as the transpiler used to emit it**. Read
them as a worked example of the mechanism on a historical program, not as the current
state of `cachetools`.

* `methodkey_holes` — on `keysProgramHoled`, it reports `hole "op:starredUnpack"` at any
  adequate fuel. This is what the status quo used to be.
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

Together: the mechanism admits a function that was previously outside the core, the
admission is exactly as strong as the stated assumption, and both degenerate contracts are
rejected by theorems rather than by convention.

## Statement holes are deliberately out of scope

`substS` does **not** fill `Stmt.hole`. A statement-level hole is an untranslated
*effect*; replacing it with an expression is a category error. The contract for one would
have to be a relation on control outcomes (`Ctl`), including `brk`/`cont`/`ret` escaping
from inside it. That is separate work. Until then
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

> **Figures for `cachetools` are regenerated, not typed.** The authoritative source is
> `ledger-Cachetools.json`; `scripts/check_docs.py` compares this document against it and
> fails on a mismatch. Current: 209 functions, 207 hole-free, 107 call-closed, 3 holes.
> (97, not the 108 reported until 2026-09-21: the ledger's call analysis had a wildcard
> arm and did not look inside `tryFinally` -- Python `with` -- so eleven functions whose
> only open callee sat inside one were counted as closed. `Ledger.lean`'s analyses are
> now exhaustive over every constructor; see "Which callees to contract next".)
> Historical figures elsewhere in this repository (238 functions, 208 functions, cores of
> 45, 69, 74) are superseded snapshots taken before the exporter changes that removed
> `<metaClassCallHandler>` synthetics and closed `op:starredUnpack`.

## Which callees to contract next — measured

The verifiable core is *hole-free and call-closed*. The gap between the two counts is the
functions whose body translates but whose callees leave the program, and those callees are
mostly the standard library. Milestone 3 of
[the goal statement](GOAL-arbitrary-codebases.md) closes that gap with **contracts**:
an explicit assumption about what an external call does, carried by the theorem that
depends on it, never folded into the unconditional core.

Which callees are worth a contract is a frequency question, so it is answered by a table
rather than a guess. `scripts/external_callees.py` mirrors `Ctx.resolvable` — unique
dotted-suffix for free calls, any suffix for method calls, modelled Python builtins
resolvable — and reports, per callee, how many call sites it has and how many
**hole-free functions it alone keeps out of the core** (`blocks`). The second number is
what a contract for it is worth.

Snapshot taken 2026-09-21 on the tracked corpora; re-measure before quoting:

```sh
python3 scripts/external_callees.py ast-Cachetools.json ast-LangJava.json ast-LangGo.json \
    ast-LangJS.json ast-LangTS.json ast-LangC.json ast-Sample.json ast-Stress.json --json out.json
```

| corpus | dialect | functions | hole-free but call-open | distinct external callees |
|---|---|--:|--:|--:|
| `ast-Cachetools.json` | python | 209 | 92 | 55 |
| `ast-LangJava.json` | cLike | 669 | 159 | 315 |
| `ast-LangGo.json` | cLike | 83 | 15 | 65 |
| `ast-LangJS.json` | javascript | 14 | 4 | 18 |
| `ast-LangTS.json` | javascript | 86 | 26 | 72 |
| `ast-LangC.json` | cLike | 59 | 9 | 24 |
| `ast-Sample.json` | python | 5 | 2 | 6 |
| `ast-Stress.json` | python | 6 | 0 | 0 |

The table is honest about what it finds: many of the top entries are not the standard
library at all but **closure-local names** (`info`, `wrapper`, `cache_clear`,
`this.delegate`, `value`) — calls to a variable holding a function, which is the
value-callee gap of milestone 2, not a contract. The library calls that do appear
(`strlen`, `requireNonNull`, `Sprintf`, `functools.update_wrapper`, `startsWith`,
`equals`, `Math.max`) are the initial contracted set in `Ledger.lean`'s
`contractedCallees`, each annotated *modelled* (executed by `Stdlib.lean`) or *assumed*
(a boundary assumption, pure and total on its documented domain — nothing proves it).

| # | external callee | sites | blocks | corpora |
|--:|---|--:|--:|---|
| 1 | `this.delegate` | 19 | 19 | LangJava(cLike) |
| 2 | `value` | 39 | 8 | LangJava(cLike) |
| 3 | `info` | 7 | 7 | Cachetools(python) |
| 4 | `cache_delitem` | 9 | 6 | Cachetools(python) |
| 5 | `super` | 9 | 6 | Cachetools(python), LangTS(javascript) |
| 6 | `getName` | 16 | 4 | LangJava(cLike) |
| 7 | `cache_getitem` | 6 | 4 | Cachetools(python) |
| 8 | `_CacheInfo` | 5 | 4 | Cachetools(python) |
| 9 | `.RECORD_HELPER` | 4 | 4 | LangJava(cLike) |
| 10 | `set` | 14 | 3 | Cachetools(python), LangJava(cLike) |
| 11 | `strlen` | 6 | 3 | LangC(cLike) |
| 12 | `tmp0.move_to_end` | 4 | 3 | Cachetools(python) |
| 13 | `.gson` | 3 | 3 | LangJava(cLike) |
| 14 | `cache_clear` | 3 | 3 | Cachetools(python) |
| 15 | `this.outerClass` | 20 | 2 | LangJava(cLike) |
| 16 | `equals` | 19 | 2 | LangJava(cLike) |
| 17 | `add` | 14 | 2 | Cachetools(python), LangJava(cLike) |
| 18 | `requireNonNull` | 14 | 2 | LangJava(cLike) |
| 19 | `isAssignableFrom` | 10 | 2 | LangJava(cLike) |
| 20 | `func` | 8 | 2 | Cachetools(python) |
| 21 | `getAnnotation` | 8 | 2 | LangJava(cLike) |
| 22 | `startsWith` | 8 | 2 | LangJava(cLike) |
| 23 | `lock` | 7 | 2 | Cachetools(python) |
| 24 | `max` | 5 | 2 | LangJava(cLike) |
| 25 | `this.#scheduleRateLimitUpdate` | 5 | 2 | LangTS(javascript) |
| 26 | `this.appendable` | 5 | 2 | LangJava(cLike) |
| 27 | `this.on` | 4 | 2 | LangTS(javascript) |
| 28 | `this.value` | 4 | 2 | LangJava(cLike) |
| 29 | `Sprintf` | 3 | 2 | LangGo(cLike) |
| 30 | `functools.update_wrapper` | 3 | 2 | Cachetools(python) |
| 31 | `this.componentType` | 3 | 2 | LangJava(cLike) |
| 32 | `v.Tags` | 3 | 2 | LangGo(cLike) |
| 33 | `nextNode` | 2 | 2 | LangJava(cLike) |
| 34 | `self._Timer__timer` | 2 | 2 | Cachetools(python) |
| 35 | `warnings.warn` | 2 | 2 | Cachetools(python) |
| 36 | `<init>` | 58 | 1 | LangJava(cLike) |
| 37 | `nullValue` | 21 | 1 | LangJava(cLike) |
| 38 | `this.stack` | 16 | 1 | LangJava(cLike) |
| 39 | `Implements` | 8 | 1 | LangGo(cLike) |
| 40 | `__ecma.Array.factory` | 7 | 1 | LangJS(javascript), LangTS(javascript) |
| 41 | `type` | 7 | 1 | Cachetools(python) |
| 42 | `cache_setitem` | 6 | 1 | Cachetools(python) |
| 43 | `iter` | 6 | 1 | Cachetools(python) |
| 44 | `string` | 6 | 1 | LangGo(cLike) |
| 45 | `assert` | 4 | 1 | LangJava(cLike), LangC(cLike) |
| 46 | `reject` | 4 | 1 | LangTS(javascript) |
| 47 | `this.#tryToStartAnother` | 4 | 1 | LangTS(javascript) |
| 48 | `this.constructor` | 4 | 1 | LangJava(cLike) |
| 49 | `LFUCache._Link` | 3 | 1 | Cachetools(python) |
| 50 | `getTimeZone` | 3 | 1 | LangJava(cLike) |
| 51 | `skipValue` | 3 | 1 | LangJava(cLike) |
| 52 | `this.#getActiveTicksCount` | 3 | 1 | LangTS(javascript) |
| 53 | `this.#processQueue` | 3 | 1 | LangTS(javascript) |
| 54 | `this.adapterFactoryMap` | 3 | 1 | LangJava(cLike) |
| 55 | `.typeAdapter` | 2 | 1 | LangJava(cLike) |
| 56 | `ParseBool` | 2 | 1 | LangGo(cLike) |
| 57 | `Symbol` | 2 | 1 | LangJS(javascript), LangTS(javascript) |
| 58 | `TTLCache._Link` | 2 | 1 | Cachetools(python) |
| 59 | `getSimpleName` | 2 | 1 | LangJava(cLike) |
| 60 | `kwargs.items` | 2 | 1 | Cachetools(python) |
| 61 | `memset` | 2 | 1 | LangC(cLike) |
| 62 | `queueMicrotask` | 2 | 1 | LangTS(javascript) |
| 63 | `signal.removeEventListener` | 2 | 1 | LangJS(javascript), LangTS(javascript) |
| 64 | `this.#onInterval` | 2 | 1 | LangTS(javascript) |
| 65 | `this.#updateRateLimitState` | 2 | 1 | LangTS(javascript) |
| 66 | `this.clazz` | 2 | 1 | LangJava(cLike) |
| 67 | `this.dateTypeAdapter` | 2 | 1 | LangJava(cLike) |
| 68 | `this.type` | 2 | 1 | LangJava(cLike) |
| 69 | `AccessChecker.INSTANCE` | 1 | 1 | LangJava(cLike) |
| 70 | `EnumSet.class` | 1 | 1 | LangJava(cLike) |
| 71 | `Execute` | 1 | 1 | LangGo(cLike) |
| 72 | `JsonElementTypeAdapter.ADAPTER` | 1 | 1 | LangJava(cLike) |
| 73 | `_TimedCache._Timer` | 1 | 1 | Cachetools(python) |
| 74 | `cache_len` | 1 | 1 | Cachetools(python) |
| 75 | `cache_repr` | 1 | 1 | Cachetools(python) |
| 76 | `clearInterval` | 1 | 1 | LangTS(javascript) |
| 77 | `clearTimeout` | 1 | 1 | LangTS(javascript) |
| 78 | `collections.namedtuple` | 1 | 1 | Cachetools(python) |
| 79 | `compile` | 1 | 1 | LangJava(cLike) |
| 80 | `construct` | 1 | 1 | LangJava(cLike) |
| 81 | `getProperty` | 1 | 1 | LangJava(cLike) |
| 82 | `hash` | 1 | 1 | Cachetools(python) |
| 83 | `hashCode` | 1 | 1 | LangJava(cLike) |
| 84 | `isMemberClass` | 1 | 1 | LangJava(cLike) |
| 85 | `memcmp` | 1 | 1 | LangC(cLike) |
| 86 | `newFactory` | 1 | 1 | LangJava(cLike) |
| 87 | `ofEpochSecond` | 1 | 1 | LangJava(cLike) |
| 88 | `ofSeconds` | 1 | 1 | LangJava(cLike) |
| 89 | `out.append` | 1 | 1 | Sample(python) |
| 90 | `panic` | 1 | 1 | LangGo(cLike) |
| 91 | `parseDouble` | 1 | 1 | LangJava(cLike) |
| 92 | `parseFloat` | 1 | 1 | LangJava(cLike) |
| 93 | `reject_` | 1 | 1 | LangJS(javascript) |
| 94 | `resolve_` | 1 | 1 | LangJS(javascript) |
| 95 | `self._DeprecatedDescriptorBase__cache_clear` | 1 | 1 | Cachetools(python) |
| 96 | `self._WrapperBase__cache` | 1 | 1 | Cachetools(python) |
| 97 | `self._WrapperBase__cond` | 1 | 1 | Cachetools(python) |
| 98 | `self._WrapperBase__lock` | 1 | 1 | Cachetools(python) |
| 99 | `setTimeout` | 1 | 1 | LangTS(javascript) |
| 100 | `this.#next` | 1 | 1 | LangTS(javascript) |

**How the ledger reports it.** `ledger-<Module>.json` carries `closedByTranslation` (the
unconditional core, identical to `verifiableCore`) and, separately, `closedByContract`:
hole-free functions that are *not* call-closed but become closed once the dialect's
`contractedCallees` are assumed, with `contractsUsed` naming which. The printed ledger
shows the second as `closed by contract : +N … NOT in the core above`, and the SACM case
must attach those N to a claim that carries the assumption, never to `G3.1`.
