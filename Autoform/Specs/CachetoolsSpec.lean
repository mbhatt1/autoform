import Autoform.Specs.CachetoolsSpec.Base
import Autoform.Specs.CachetoolsSpec.Part1
import Autoform.Specs.CachetoolsSpec.Part2
import Autoform.Specs.CachetoolsSpec.Part3
import Autoform.Specs.CachetoolsSpec.Part4
import Autoform.Specs.CachetoolsSpec.Part5
import Autoform.Specs.CachetoolsSpec.Part6

import Autoform.Refine
import Autoform.Generated.Cachetools

/-!
# Specifications about *translated* code — `cachetools`

`Autoform/Refine.lean` proves refinement theorems about deep terms that were **copied**
into it. That is fine for demonstrating the technique, but it means the mutation gate
(`scripts/mutate.py`) has never been pointed at a machine-generated module: G4 of the
SACM case ("the specifications are non-vacuous") could only ever cite
`Autoform.Lang.Imp.Semantics`, a hand-written toy.

This file states theorems about `Autoform/Generated/Cachetools.lean` **by import**, so
every deep term named below is the literal output of `cartographer/render_lean.py` and a
mutation of that file is a mutation of the subject of these theorems. That is the whole
point: `scripts/mutate.py --spec-module` mutates `Generated/Cachetools.lean` and rebuilds
*this* module, so a specification that does not notice the bug is exposed as vacuous.

## What is (and is not) claimed

Each theorem is a `Refines`/`MRefines` statement, i.e. it fixes the *entire* observable
behaviour — result value **and** resulting heap — of one entry point, for every fuel
budget at or above a stated bound, on a stated domain. `Refine.lean`'s non-vacuity
theorems apply verbatim: `Outcome` has no `hole` and no `outOfFuel` constructor, so none
of these can be satisfied by a function that fails to translate or fails to terminate
(`refines_not_hole`, `refines_terminates`).

The functions are drawn from the 45-function call-closed core (`Program.callClosed`).
They are small: accessors, a comparison, two constructors, a decrement, a membership
test. That is honest — the call-closed core of a real Python library *is* mostly small
methods, and the large ones are exactly the ones that still carry holes. Section 4
records what could not be proved, as stated obligations rather than `sorry`.
-/

/-! ## Build shape (2026-10-10): `Base` + 6 parts

This file is the umbrella: it imports `CachetoolsSpec/Base.lean` (the subject, `MRefines`,
the field model and the class-lookup facts) and `CachetoolsSpec/Part1.lean` ..
`Part6.lean` (the theorems, moved verbatim and still in `Autoform.Specs.Cachetools`).
One Lean process retains every proof term it elaborates, so the single-file module held
13.6 GB; the parts hold what the comment in `.github/workflows/ci.yml` records. Nothing was
restated. `scripts/mutate.py --spec-file Autoform/Specs/CachetoolsSpec.lean` reads every
part through `generated_module.spec_files`. -/

namespace Autoform.Specs.Cachetools

open Autoform.Core Autoform.Refine Autoform.Generated.Cachetools

/-! ## 4. What the mutation gate actually said

Run (2026-10-09, after the re-land on the final exporter and semantics):
`scripts/mutate.py Autoform/Generated/Cachetools.lean Autoform.Generated.Cachetools
--spec-file Autoform/Specs/CachetoolsSpec.lean --spec-module Autoform.Specs.CachetoolsSpec
--generated --max-mutants 60 --seed 20260819 --decls <the 12 subject functions of the map>
--subject <theorem→function map>`. 51 mutants of the *generated* module, 51 run,
0 rejected as not type-correct, 0 inconclusive, 0 coarse attributions.

**On-subject score: 68 / 73 = 93.2%.** Twelve of the seventeen theorems are `HAS TEETH`
(100%). Every one of the five survivors was examined; none is a case of a theorem failing
to notice a behavioural change:

* **4 × `ast-seq-delete` of a docstring** (`maxsize` and `currsize`, each once under its
  own `_mrefines` and once more under `Cache_size_fields_distinct`). The deleted statement
  is `Stmt.expr (Expr.lit (Lit.str "..."))` — Python's docstring, translated as
  evaluate-and-discard. Deleting a discarded pure literal is a **provably equivalent
  mutant**; no specification of observable behaviour can, or should, kill it. These three
  theorems are therefore reported `WEAK` (3/4, 3/4, 6/8), and that verdict is correct
  about the gate's operator set, not about the theorems.
* **1 × `ast-ret->expr` in `_cachedmethod._none`.** The body is `.ret (.lit .unit)`;
  under `.expr` the body falls through to `Ctl.normal`, which `applyFunc` maps to
  `EResult.val Val.unit` — the same observable. Equivalent mutant, and a real property of
  the semantics: a Python function that falls off the end returns `None`. With one mutant
  and one survivor the theorem is reported `VACUOUS` (0/1); it is not.
* **2 theorems with no mutants at all**: `_DefaultSize.__setitem__` has body `.skip`, and
  `_TimedCache.expire`'s body offers the operator set nothing it rewrites (the gate prints
  `no mutant generated for declaration` for both). `DefaultSize_setitem_mrefines` and
  `TimedCache_expire_raises` are reported `UNTESTED` rather than given a score. That is
  the honest verdict, not a pass.

Two findings the gate produced about *this file*, both recorded because they generalise:

1. **Witness corollaries proved by rewriting their parent theorem are invisible to the
   gate.** `Cache_size_fields_distinct`, `Cache_contains_discriminates`,
   `Timer_exit_decrements` and `Timer_init_sets_both` were restated on 2026-10-09 as
   `∀ fuel ≥ N` consequences of their parents and scored **0 / 23** that way: when a mutant
   breaks the parent, Lean reports the error at the parent and still admits its
   *statement* downstream, so the corollary re-derives from an unchanged statement and
   never fails. They now evaluate the interpreter directly (`rfl` on the concrete heap —
   `Val` has no `DecidableEq`, so `decide` is not available) and score 25 / 27. This is the
   same shape as STRATEGY.md 14: a theorem stated in terms of the thing being mutated
   moves with it.
2. **An inequality between two functions tests neither.** `Cache_size_fields_distinct`
   originally claimed only `maxsize ≠ currsize` and scored **0/8** — mutating one
   accessor leaves the other alone, so the two still differ. Pinning both values is what
   gives it its 6/8 (the remaining two being the docstring-deletion equivalents).

The score over the *whole* mutant population is 2%–16% per theorem. That number is not
a vacuity measurement, it is a **coverage** measurement: these theorems describe 12 of
209 translated functions, so most mutants are in code they never mention. The two must
not be conflated, which is why `mutate.py --subject` reports them separately.

## 5. Open obligations

Stated, never admitted. Nothing above is `sorry`, `partial`, `unsafe`, or
`native_decide`.

1. **The specified functions are small.** Ten entry points out of a 45-function
   call-closed core, and out of 233 translated. The large call-closed functions
   (`Cache.__setitem__`, `LRUCache.popitem`, the `_Link` splice/unlink pair) mutate
   containers through `Stmt.setIndex`, which is still an honest hole, or need a
   representation predicate relating a heap region to a shallow record — obligation (4)
   of `Refine.lean` §5, still open.

2. **No loop is refined here.** `Refine.lean` obligation (3) (loop-invariant rule) blocks
   `_Link.unlink` and the eviction loops, which are the functions whose specifications
   would actually be interesting to a `cachetools` user.

3. **Exception arguments are unmodelled.** `TimedCache_expire_raises` names the class —
   the `py:exception:<Name>` constructor evaluates to the represented class name, and
   `ExcSafe.lean` proves every Python exception Core raises is one — but an exception is
   only its class here: `KeyError(key)` and `KeyError()` are the same value, so no
   statement in this file can speak about what an exception *carries*.

4. **`Cache.get` is not specified.** Its body is `if key in self: return self[key]`, and
   `Expr.inOp`/`Expr.index` applied to a `ref` receiver hole out (`in:non-container`)
   rather than dispatching to `__contains__`/`__getitem__`. That is a genuine fidelity
   gap in the semantics — Python's `in` on an object *is* a method call — and it means
   `Cache.get` currently joins the not-refinable set for a reason the ledger does not
   record as a hole, because the hole is dynamic rather than static.
-/

end Autoform.Specs.Cachetools
