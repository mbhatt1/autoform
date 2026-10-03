# Contracts at holes

`Autoform/Contracts.lean` (expression holes), `Autoform/HoleContracts.lean`
(statement holes, site-scoped), `Autoform/Ledger.lean` (conditional counts, named
hole assumptions), `scripts/emit_contracts.py` → `scripts/sacm.py` (assurance case).

## Why this exists

`STRATEGY.md` §5 lists, among the honest failure modes, *"Proof burden grows
superlinearly with program size. Hence: **verified core + contracts**, never
whole-repo."* `Autoform/Refine.lean` built the verified-core half. This file is the
other half.

On `cachetools`, 168 of 209 functions are
hole-free and 98 are call-closed. A single untranslated construct anywhere in a function
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
   demonstration section run the *full* translated `cachetools` (209 functions today; the
   `Contracts.lean` comment still says 208) program and confirm it agrees. That
   is evidence, not proof, and it is listed here as a reader obligation rather than
   claimed as one.

## What was proved on a real function

`cachetools/keys.py:methodkey` —

```python
def methodkey(self, *args, **kwargs):
    return hashkey(*args, **kwargs)
```

— **used** to translate to a body containing exactly one hole, `op:starredUnpack`, the most
common hole label in the corpus (36 occurrences in the AST of that time; the label no longer occurs in `ast-Cachetools.json`). That one node was
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

## Statement holes: site-scoped contracts on effects

`Autoform/HoleContracts.lean`. `substS` above still does **not** fill `Stmt.hole`; a
separate substitution, `fillS`, does, and nothing else. The two are disjoint, so neither
can silently repair the other's holes.

A statement hole is an untranslated *effect*, so its contract is a relation on how
control leaves it:

```lean
structure SContract where
  site  : String   -- the function containing the hole
  label : String   -- the CPG hole label
  stmt  : String   -- unchecked prose for the assurance case
  fuel  : Nat      -- budget the implementation is assumed to need
  post  : Heap → Env → Heap × Ctl → Prop   -- footprint + result relation
```

* **Per site, not per label.** Contracts and implementations are keyed by
  `(function, label)`. When `del x[k]` was still a hole, `del self.__data[key]` in
  `Cache.__delitem__` touched no attribute while `del self[key]` in `Cache.pop` dispatched
  to `__delitem__` and wrote `_Cache__currsize`; a label-wide contract would have been
  false at one of them.
* **Footprint and result relation live in `post`.** `AttrFrame h h'` is the standard
  footprint (every pre-existing object keeps its class, attributes, captured bindings
  and *kind* — a builtin container stays one, an ordinary instance stays one; container
  contents may change). The kind clause was added when boxed containers entered Core:
  attribute access on an object with a `list`/`dict` payload now holes
  (`field:…:builtin-container`), so a footprint that let a hole turn `self` into a container
  would not protect the attributes it claims to protect. `completesOrRaisesFramed` is the standard contract:
  normal completion with the environment unchanged, or a raise, plus `AttrFrame`.
* **The wrapper is a hypothesis, not an axiom.**
  `UnderS Γ p Q := ∀ τ, ConsistentS Γ p τ → TotalS Γ τ → Q (τ.onProgram p)`. `Q` is any
  property of the instantiated program — `Refines` (`RefinesUnderS`) or a heap-level
  post-condition of a method, which is what a footprint is for. `#print axioms` on every
  theorem in the file reports only `propext`, `Classical.choice`, `Quot.sound`, so the
  audit tells a conditional result from an unconditional one by its *statement* (a
  non-empty `Γ`), exactly as before. `tests/test_contracts.py` fails if either contracts
  file ever declares an `axiom`, uses `sorry` or `native_decide`.
* **The same guards, re-proved.** `underS_nil_iff` (empty `Γ` is no assumption),
  `underS_of_unsatisfiable` (an unmeetable `Γ` proves everything — so `SatisfiableS` is an
  obligation), `not_underS_false` (a satisfiable `Γ` does not prove `False`),
  `unsatisfiableS_of_false_post`.
* **The hole-aware evaluation lemma** is `filled_hole`: at a contracted site the
  instantiated body contains *some* statement `s`, and running `s` at any fuel above the
  budget, in any heap and environment, satisfies `post`. A proof never learns `s`.
  `resolve_onProgram` / `resolveMethod_onProgram` say filling changes no name resolution,
  and `resolveMethod_of_unique` resolves a method on a 209-entry table by evaluation
  (`decide +kernel`) instead of unfolding the table in `simp`.

### Worked examples on the regenerated `cachetools`

Both are about `Autoform.Generated.Cachetools.program` itself — all 209 functions,
imported, not a slice — rendered from the committed `ast-Cachetools.json` as regenerated
with the merged exporter (items G, H, L). Re-running the exporter can again move a hole;
when it does, these proofs stop elaborating rather than silently describing a different
program.

**1. `Cache.__delitem__` — the contract retired, the theorem unconditional.** The first
version of this file proved `__delitem__` *relative to* a contract on
`del self.__data[key]` (`op:delete-index`). Item G translates that statement to
`Stmt.delIndex`, so the contract is gone and `delitem_refines` states the method's exact
heap effect and result with no assumption (`delitem_unconditional` is the same statement
through `UnderS []`):

```python
def __delitem__(self, key):
    size = self.__size.pop(key)
    del self.__data[key]
    self.__currsize -= size
```

For an ordinary `Cache` object whose size table is a `_DefaultSize` instance and whose data
is a boxed `dict` at another address, at every fuel ≥ 12: an unhashable key raises
`TypeError`; an absent key raises `KeyError` with the heap untouched; a present key is
removed from the dict (`Stdlib.dictDel`) and `_Cache__currsize` becomes `c - 1`. Stated as
an equation on the resulting heap, so a mutant that drops the deletion or the decrement
refutes it. `#eval` on `delHeap`: key present → `val unit`, size 5 → 4, dict emptied; key
absent → `exn "KeyError"`, size 5.

**2. `RRCache.clear` — a statement hole that survives.**

```python
def clear(self):
    Cache.clear(self)
    self.__index.clear()
    del self.__index[:]          # Stmt.hole "op:delete-slice"
```

* `rrclear_reaches_hole` — on the generated program, on every admissible receiver, the
  method reaches `hole "op:delete-slice"`. No unconditional statement exists.
* `satisfiable_sliceContract` — the one assumption, `sliceContract` (site
  `RRCache.clear`, `completesOrRaisesFramed`), can be met; witness `skip`.
* `rrclear_under : UnderS Γslice P RRPost` — at every fuel ≥ 30, `clear` either returns
  `None` or raises, and **in both cases `_Cache__currsize = 0`**, for every implementation
  of the hole meeting the contract. The footprint is load-bearing: `Cache.clear` writes
  `_Cache__currsize = 0` *before* the hole runs, so only `AttrFrame` stops the hole from
  undoing it.
* `rrclear_not_provable_under_top` — under `topSContract` the property is false, because
  leaving the hole in place is an admitted implementation.
* `rrclear_not_vacuous` — `False` does not follow from `Γslice`; `rrHeap_shape` shows the
  domain is inhabited.
* `#eval` cross-checks on the full program: filled with `skip` → `val unit`, size 3 → 0;
  filled with `raise` → `exn`, size 0; unfilled → `hole "op:delete-slice"`.

The proof goes through `Cache.clear(self)`, which names the class through its value
`cachetools/__init__.py:<module>.Cache<meta>`; `className_Cache` proves the interpreter
recovers `Cache` from it by unfolding `String.splitOn` step by step (it is well-founded
recursion, which neither `rfl` nor `decide +kernel` reduces).

**Reader obligations specific to these examples** (none is in `Γ`): `del x[:]` on a CPython
`list` has no attribute side effect; the `RRShape` domain states the globals-frame binding
of `Cache` (address `0`, as `initGlobals` allocates it) instead of running the module
initialisers; both domains fix `_Cache__size` as a `_DefaultSize` *instance attribute*,
whereas real `cachetools` reaches `_DefaultSize` through a class attribute the translation
does not model; and both require the receiver and the size table to be ordinary objects
(`payload = .none`), because the semantics dispatches on payload.

**Next candidates.** The statement holes left in the current ledger
(`ledger-Cachetools.json`, `holeAssumptions`) are: `op:delete-slice` in `RRCache.clear`
(done above) and `TLRUCache.clear` (the same shape behind a timer context manager),
`gen:generator`/`gen:yield` in `TTLCache.__iter__` and `TLRUCache.__iter__` (a generator
needs suspension in Core, so a footprint contract would have to describe an iterator rather
than a completion), and `control:TRY-multiCatch` in `_DescriptorBase.__get__` (the one statement
hole the ledger does not count as conditionally verifiable). The expression holes are
`call:computed-callee` (six: `_cache.decorator` and the five `cachetools/func.py`
decorators), `expr:genExp` (two, in `typedkey`) and `op:stringExpressionList` (one, in
`_DescriptorBase.__set_name__`), a candidate set for `Contracts.lean`. The 30
`param:default-nonliteral` holes sit in parameter *defaults*, which neither substitution
fills yet — a contract for them would have to be stated on `Func.defaults`.

## Conditionally verifiable and conditionally verified — separate numbers

The ledger (`Autoform/Ledger.lean`, `ledger-<Module>.json`) and the assurance case
(`scripts/sacm.py`, `sacm-<Module>.json`) now report, **apart from the verifiable core and
never added to it**:

| figure | meaning | source |
|---|---|---|
| `conditionallyVerifiable` | functions with ≥ 1 hole whose calls all resolve: a statement about them is expressible relative to contracts on their holes. An upper bound, like hole-free. | `Program.conditionallyVerifiable` |
| `conditionalAssumptions` | hole occurrences in those functions, i.e. the named assumptions such statements would rest on | ledger |
| `holeAssumptions` | **every** hole occurrence, named `H:<function>#<i>:<label>`, with kind `stmt`/`expr`. Complete by `Func.holeSites_labels` (the inventory's labels *are* `Func.holes`, body and parameter defaults). | `Program.holeAssumptionsJson` |
| `conditionallyVerified` | functions *of this module's generated program* with a contract-relative theorem whose contracts are proved satisfiable | `contracts-<Module>.json` |

On `cachetools` (`lake env lean` on `scripts/ledger.lean.tmpl` instantiated for
`Cachetools`, then `scripts/emit_contracts.py Cachetools` and
`scripts/sacm.py --module Cachetools`): 32 of 209 functions are conditionally
verifiable, resting on 36 named hole assumptions; 1 is conditionally verified
(`RRCache.clear`); 46 hole occurrences are named in all (30 of them in parameter
defaults, which `Func.holeSites` includes so that `Func.holeSites_labels` — the inventory's
labels *are* `Func.holes` — holds). The `methodkey` theorems are
about the historical slice `keysProgramHoled`, so their registry records carry
`program: Autoform.Contracts.Demo.keysProgramHoled` and sacm.py labels them "NOT about the
current module" and does not count them.

In the SACM case: claim `G3.3` carries the conditional number (STATIC evidence `E8`); it is
linked to `G3` as `CONTEXT`, never `SUPPORTS`, and nothing conditional supports `G1`. Each
`H:` occurrence is an `Assumption` refining its label's `A.<label>` node; each contract of
a theorem is an `Assumption` of that theorem's own claim, and names the `H:` occurrence(s)
it assumes, so the other occurrences of the same label visibly remain unassumed.

## What remains

* **Mixed environments.** A function with both an expression hole and a statement hole
  needs `Contracts.Consistent` and `ConsistentS` at once; the two substitutions commute
  (they touch disjoint constructors) but no combined wrapper is stated yet.
* **Callee holes.** `conditionallyVerifiable` mirrors `callClosed`: it checks that calls
  *resolve*, not that callees are hole-free. A result about a function whose callee has a
  hole must contract that hole too; `UnderS` accepts any site in `Γ`, so this is
  expressible, but the ledger does not compute the transitive assumption set.
* **`Analysis.sCalls` does not descend into `breakBlock`, `tryFinally`, `setGlobal` or
  `setDerefIref`**, so both `callClosed` and `conditionallyVerifiable` can over-count on
  functions whose only unresolved calls sit there (pre-existing; not changed here).
* **Contracts are hand-written.** The ledger names every hole; it does not propose a
  `post` for any. Inferring candidate footprints per label (e.g. `AttrFrame` for
  `op:delete-slice` on a `list`) and checking them against the differential oracle is the
  next step. SQLite has no worked example yet.

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

> **Figures for `cachetools` are regenerated, not typed** (the figures below are for
> cachetools v7.1.7 at `01af8e5`, as of the exporter at this commit). The authoritative source is
> `ledger-Cachetools.json`; `scripts/check_docs.py` compares this document against it and
> fails on a mismatch. Current: 209 functions, 168 hole-free, 98 call-closed, 46 holes,
> 32 conditionally verifiable.
> The re-export with the class table (STRATEGY.md §62) moved two of these: a bare call name
> is now a variable, so the ledger counts it resolvable when it is one of the caller's own
> locals (`cache_getitem(self, key)` with `cache_getitem` a parameter: 13 more
> conditionally verifiable functions, 19 → 32, the defaulted-parameter methods of the
> cache classes and `_HashedTuple`), and not when it is only a captured name
> (`_unlocked.cache_clear` calls the enclosing function's `cache`: core 99 → 98).
> Historical figures elsewhere in this repository (238 functions, 208 functions, cores of
> 45, 69, 74) are superseded snapshots taken before the exporter changes that removed
> `<metaClassCallHandler>` synthetics and closed `op:starredUnpack`.
