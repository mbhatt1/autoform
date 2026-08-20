# Boxed containers for Core

**Status:** design, not implementation. Written to be read before `Syntax.lean` and
`Semantics.lean` are changed.

**Problem.** `Val.list`, `Val.tuple` and `Val.dict` are *values*. Python's are *objects*.
The consequences are all currently visible in the ledger and the oracle:

| symptom | where | size |
|---|---|---|
| `Stmt.setIndex` is an unconditional hole | `Semantics.lean:608` | `setIndex:immutable-containers` |
| `del d[k]` / `del xs[a:b]` are holes | transpiler | `op:delete-index`, `op:delete-slice` |
| `list.append` / `dict.pop` implemented but unwireable | `Stdlib.lean:376` | `MethodResult.mutating` |
| `dict`/`tuple`-subclass receivers refused by the oracle | `differential.py` | `skip_self_not_object` 1,361 |
| `==` cannot distinguish "equal" from "the same object" | `Val.beq` | see §5 |

All five are one defect. This document specifies the fix, what it costs, and what it does
*not* fix.

---

## 1. The representation

Containers move into the existing heap. No new heap, no new address space, no `Ref`
namespace split — `Val.ref` already means "a mutable thing with identity", which is
exactly what a Python list is.

The change is to `Obj`, not to `Val`:

```lean
/-- The mutable container payload an object carries, if any. -/
inductive Payload where
  | none                              -- an ordinary instance
  | list  : List Val → Payload        -- `list`, and `list` subclasses
  | dict  : List (Val × Val) → Payload -- `dict`, and `dict` subclasses
  | tuple : List Val → Payload        -- `tuple` *subclass* instances only (see §2)
  deriving Repr, Inhabited

structure Obj where
  cls      : String
  fields   : List (String × Val)
  captured : List (String × Val) := []
  payload  : Payload := .none
  /-- Bumped by every mutation. Iterators record it; a change during iteration is
  CPython's `RuntimeError: dictionary changed size during iteration`. See §6. -/
  version  : Nat := 0
  deriving Repr, Inhabited
```

`[1, 2]` evaluates to `Val.ref r` where the heap cell at `r` is
`⟨"list", [], [], .list [.int 1, .int 2], 0⟩`. `{}` likewise with `cls := "dict"`.

### Why a payload on `Obj`, and not a new `Val.box` constructor

Because **it closes `skip_self_not_object` for free**, which a separate box does not.
`cachetools.Cache` is a `dict` subclass; `_HashedTuple` is a `tuple` subclass. Under a
separate `Val.box`, such an instance is *both* an object (it has `__dict__` fields and a
class) and a container, so it has to be encoded as one or the other — which is exactly
why the oracle refuses 1,361 cases today. With the payload on `Obj`, it is **one heap
cell**: `cls := "Cache"`, its own `fields`, and `payload := .dict [...]`. Method dispatch
resolves in Python's own order:

1. `Ctx.resolveMethod obj.cls name` — the user class wins (`Cache.__getitem__`);
2. otherwise `Stdlib.method` on the payload — the builtin behaviour;
3. otherwise the existing `mcall:<name>` hole.

That is the MRO for a one-level subclass, which is all Core can represent anyway, and it
is the same precedence `Stdlib.lean` already documents ("must be consulted **only after**
the interpreter's own class dispatch fails").

### Tuples stay values

`Val.tuple` is **not** boxed. Tuples are immutable and hashable; no method can change one,
so value semantics is observationally equivalent to boxing *except* for `is` and `id`.
Rather than pay allocation on every dict key and lose structural key comparison, the
immutability is preserved by construction — there is nowhere to write — and the one
observable difference is made a hole:

* `a is b` where either side is an unboxed value (`int`, `str`, `bool`, `float`, `tuple`)
  → `Expr.hole "is:unboxed-value-identity"`. CPython interns small ints, some strings and
  no tuples, all of it implementation-defined; this is the same refusal `Stdlib.lean`
  already makes for `id()` and `hash()`.

`Payload.tuple` exists only for *subclass* instances, which do have identity and a class,
and it admits no mutating methods.

### `Heap` operations added

```lean
def Heap.payload   (h : Heap) (r : Ref) : Payload
def Heap.setPayload (h : Heap) (r : Ref) (p : Payload) : Heap   -- also bumps `version`
```

`setPayload` **replaces**, unlike `Heap.setField`, which prepends and shadows. Shadowing a
payload would make the object's size grow without bound under `xs.append` in a loop.

---

## 2. What the operations then mean

### The rule that makes all of this correct

> **After the receiver expression has been evaluated to a `Val.ref`, the expression is
> never looked at again.** Mutation is `Heap.setPayload r …`. No mutation path may
> mention `Expr`.

This is the whole design in one sentence, and it is what avoids the trap the stdlib work
measured. The CPG desugars

```python
self.__data.pop(k)
```

into

```
tmp0 = self._Cache__data
tmp0.pop(k)
```

Under **value** semantics the only place to write the updated container back is the
receiver *expression* `tmp0` — a temporary — so the object is untouched and the mutation
is silently lost. That is why `MethodResult.mutating` could not be wired, and any design
that writes back through the receiver expression reproduces the bug.

Under **boxed** semantics `tmp0` binds the *same reference value* as
`self._Cache__data`. `tmp0.pop(k)` evaluates `tmp0` to `.ref r` and calls
`Heap.setPayload r`. `self._Cache__data` still holds `.ref r`, so it observes the change.
Nothing is written back anywhere. The temporary is harmless because copying a `Val.ref`
is what Python's assignment does.

A mechanical check for this rule: after the change, `grep -n 'Expr' ` over the mutation
path in `Semantics.lean` should find the receiver being *evaluated* and nothing else.

### `Stmt.setIndex e i v` — `e[i] = v`

```
eval e ↝ .ref r        ; anything else is not a hole any more:
                         .tuple/.str/.int ↝ .exn (.str "TypeError")
                                              (Python: "'tuple' object does not support
                                               item assignment") — a *value*, not ignorance
if the class defines __setitem__ → call it (user code wins)
else match Heap.payload r with
  | .list vs  => match seqIndex vs.length i with
                 | some k => setPayload r (.list (vs.set k v))
                 | none   => .exn (.str "IndexError")
  | .dict kvs => setPayload r (.dict (Stdlib.dictSet kvs i v))      -- insertion order
  | .tuple _  => .exn (.str "TypeError")
  | .none     => .exn (.str "TypeError")   -- unless __setitem__ resolved above
```
with `i` a slice → `Expr.hole "setIndex:slice"` (§8, item 3).

`Stdlib.dictSet` already implements CPython's replace-in-place / append-at-end rule, so
key order stays observable and correct.

### `del d[k]` / `del xs[i]`

Needs a new statement — the current holes `op:delete-index` exist because there is no
constructor to translate to:

```lean
| delIndex : Expr → Expr → Stmt      -- `del e[i]`
```

Semantics mirror `setIndex`: `.dict` → `dictDel`, missing key → `KeyError`; `.list` →
`dropAt`, out of range → `IndexError`; `.tuple`/non-container → `TypeError`. Both helpers
already exist in `Stdlib.lean`.

`del xs[a:b]` (`op:delete-slice`) stays a hole. See §8.

### `list.append`, `dict.pop`, and the rest of `MethodResult.mutating`

**`Stdlib.lean` does not change at all.** It already returns `.mutating result newRecv`.
The wiring in `evalExpr`'s `.mcall` case becomes:

```
eval receiver ↝ (h₁, .val recvV)
match recvV with
| .ref r =>
    -- 1. user class method first
    match ctx.resolveMethod (h₁.get r).cls name with
    | some f => applyFunc … (self? := some (.ref r)) …
    | none   =>
      -- 2. builtin, on the payload
      match Stdlib.method ctx.dialect h₁ (payloadToVal (h₁.payload r)) name args with
      | some (h₂, .pure res)        => (h₂, res)
      | some (h₂, .mutating res nv) => (h₂.setPayload r (valToPayload nv), res)
      | none                        => (h₁, .hole s!"mcall:{name}")
| _ => (h₁, .hole s!"mcall:{name}:unboxed-receiver")
```

`payloadToVal`/`valToPayload` are the only adapters needed, because `Stdlib.method` speaks
`Val.list`/`Val.dict`. Keeping that interface (rather than rewriting `Stdlib` against
`Payload`) is deliberate: `Stdlib.lean` is 700 lines with its own `#eval` evidence and
proofs, and none of it is about aliasing.

The `unboxed-receiver` hole is reachable — `dict.keys()` returns a `Val.list` view — and
must stay a hole rather than silently mutating a copy. That is the §22 "writes by copying
values back would appear to work on simple cases and be silently wrong on aliased ones"
rule, applied here.

---

## 3. Aliasing, worked

```python
a = []
b = a
b.append(1)
```

| step | heap | env |
|---|---|---|
| `a = []` | `0: ⟨"list", [], [], .list [], 0⟩` | `a ↦ ref 0` |
| `b = a` | unchanged | `a ↦ ref 0`, `b ↦ ref 0` |
| `b.append(1)` | `0: ⟨"list", [], [], .list [1], 1⟩` | unchanged |

`a` is now `[1]`, because `a` and `b` are the same `Val.ref 0`. Today `b = a` copies the
list and `a` stays `[]` — a silent wrong answer that no test in the corpus currently
reaches only because `append` is unwired.

The non-aliasing case is equally load-bearing:

```python
a = []; b = []; b.append(1)     # a stays [], because `[]` allocates twice
def f(xs): xs.append(1)         # f(a) mutates the caller's list, since args pass refs
```

Both fall out of the design without a special case, which is the test of whether the
design is right.

---

## 4. Iteration

`for x in xs` currently reads `Val.iterable : Val → Option (List Val)` and iterates a
*snapshot*. After boxing there is a choice, and the faithful one is not the cheap one:

* **CPython's `list_iterator` holds the list object and an index.** Appending during
  iteration extends the loop; deleting shortens it. Modelling this means `execFor` carries
  `(Ref, Nat)` rather than `List Val` and re-reads the payload each step.
* **CPython's `dict` iterator raises** `RuntimeError: dictionary changed size during
  iteration`. This is what `Obj.version` is for: the iterator records the version at
  creation and the loop head compares. Cheap, and it turns a currently-invisible wrong
  answer into a modelled exception.

Snapshot iteration should **not** be kept "for now": it is currently harmless because
nothing can mutate a container mid-loop, and boxing is precisely what makes it reachable.
Landing boxing and snapshot iteration together would introduce a silent wrong answer in
the same commit that removes one.

For an unboxed `Val.tuple` or `Val.str`, snapshot iteration remains exactly right.

---

## 5. `==` versus `is`

This is the subtlest part of the change and the one most likely to produce false
divergences if done casually.

Today `Val.beq` is structural and total: `Val → Val → Bool`. It serves `==`, `!=`, `in`,
dict lookup, `list.index`, `list.count`, `list.remove`. `Expr.isOp` compares `.ref`s.

After boxing, two distinct list objects with equal contents have **different refs**, so a
structural `Val.beq` answers `False` for `[1] == [1]` — the exact opposite of Python. The
relation has to split in two:

### `is` — identity

```lean
def Val.identical : Val → Val → Option Bool
  | .ref a, .ref b => some (a == b)
  | .unit,  .unit  => some true
  | _, _           => none          -- ↦ hole "is:unboxed-value-identity"
```

Total, decidable, heap-free, and *more* correct than today: `[] is []` becomes `False`
(two allocations) rather than `True`.

### `==` — value equality, and it needs the heap

```lean
/-- Python `==`. Fuel-indexed because containers can be cyclic
(`a = []; a.append(a)`), heap-indexed because contents live in the heap. -/
def Val.eqPy (h : Heap) : Nat → Val → Val → Option Bool
```

Three properties it must have:

1. **Reference identity short-circuits to `true` first.** This is not an optimisation, it
   is CPython's own behaviour (`PyObject_RichCompare`'s identity fast path for
   containers) and it is what makes `a == a` terminate for the cyclic list above.
2. **Out of fuel is `none`, not `false`.** `none` becomes `EResult.outOfFuel`, keeping the
   project's "ignorance ≠ behaviour" rule. A `false` here would be a manufactured
   divergence on deeply nested structures.
3. **It does not call user `__eq__`.** See §8 item 1.

### The cost of the split

`Val.beq`'s signature change is the single largest mechanical cost of this design, larger
than `setIndex` itself:

* `Semantics.lean`: ~12 call sites (`applyBinop` `==`/`!=`, `valIn`, `Expr.index` dict
  lookup, `evalExpr`'s `.dictE`, `isOp`).
* `Stdlib.lean`: `dictGet`, `dictHas`, `dictSet`, `dictDel`, `listRemove`, `listIndex`,
  `listCount` — 7 helpers, each of which gains `(h : Heap) (fuel : Nat)` and an `Option`
  result. Their `#eval` evidence block (lines ~600–700) needs the extra arguments.
* Anything proved by `simp [Val.beq]` or `decide` over container values needs re-proving.

A cheaper variant was considered and rejected: keep `Val.beq` structural and make `==` on
two `.ref`s dispatch to a *separate* container comparison. Rejected because `Val.beq` is
also what compares dict *keys*, and a key can be a tuple containing a ref — so the heap
has to reach every level of the comparison anyway, and a two-relation design would differ
from itself at depth 2.

### Dict keys become correct in one respect

`d[[1]] = 1` currently "works". After boxing, a `.ref` to a `list`-payload object as a key
is `TypeError: unhashable type: 'list'` — checkable from the payload, and a value rather
than a hole. Keys that are objects with user `__eq__` remain refused (§8).

---

## 6. Heap growth, and a lemma the refinement layer wants anyway

Every container literal allocates, and `Heap` is an append-only `List Obj` that is never
collected. Two consequences:

* **Performance.** `Heap.setField`/`setPayload` are `mapIdx` — O(n) per write, so a loop
  doing `xs.append` n times is O(n²). Acceptable: the oracle runs small cases and the
  interpreter is a specification, not a runtime. Worth stating in the ledger rather than
  discovering.
* **Proofs.** Refinement theorems currently pin the exact final heap. Once a loop
  allocates, that is fragile. The right shape is a monotonicity lemma:

```lean
/-- Evaluation only ever extends the heap: `h` is a prefix of the result heap. -/
theorem evalExpr_heap_mono (ctx) (k h ρ e) : h <:+: (evalExpr ctx k h ρ e).1
```

with refinement statements quantified over "any heap extending `h₀`". This is a lemma the
layer wants independently of boxing — `Expr.alloc` already extends the heap — so it is
migration cost that buys something.

---

## 7. Migration cost, measured

Counts taken from this repository, not estimated:

### `Autoform/Refine.lean` — 2,067 lines, 115 theorems

| | count | why |
|---|--:|---|
| theorems whose statement or proof mentions a container constructor or iteration | **3** | `execStmt_forIn_val`, `total_run`, `total_refines` |
| theorems in the `PureE` fragment (fuel independence, heap inertness) | 3 | **unaffected** |
| `evalSimp` mechanical lemmas (`evalExpr_*`, `execStmt_*`, `evalList_*`, `applyFunc_*`) | ~40 | **unaffected** |

The headline "~74 theorems" overstates it, and the reason is a design decision already
taken: `PureE` (`Refine.lean:487`) is `lit | name | fnref | unop | binop | cond` — it
never admitted `listE`, `dictE` or `index`. So `evalExpr_pure_fuel_indep`,
`evalExpr_pure_fuel_mono` and `evalExpr_pure_heap_inert` — the three load-bearing
structural theorems, and the expensive ones — are about a fragment that does not allocate,
and survive verbatim. Likewise every `evalSimp` lemma: none of them covers a container
constructor, so none of them asserts "the heap is unchanged" about an expression that
would start allocating.

The real work is concentrated:

* **`total_run` (lines 1895–1993).** A ~100-line explicit evaluation that mentions
  `Val.list (ys.map Val.int)` in 12 places. It must be rewritten to allocate the list into
  the heap and thread `Val.ref`. This is the single largest proof rewrite, and it is one
  proof.
* **`total_refines`** (its corollary) and **`execStmt_forIn_val`** — statement changes
  following §4's iterator change.
* **~25 call sites** across `Semantics.lean` and `Stdlib.lean` for the `Val.beq` split
  (§5), most of them mechanical.

Compare with `STRATEGY.md` §22's estimate for `nonlocal` writes ("would require
re-repairing the 74-theorem refinement layer"): boxing containers is materially cheaper,
because `Env` is untouched. Every scope stays a value; only the heap grows.

### `Autoform/Generated/*.lean`

35 sites mention `setIndex`/`listE`/`dictE`. **None need regeneration.** The AST is
unchanged; only its meaning changes. This is the deep-embedding payoff and worth stating
in the ledger: a semantics change that re-verifies six corpora without re-running Joern.

### `Autoform/Ledger.lean`, `Demo.lean`

New hole labels to register: `setIndex:slice`, `op:delete-slice`,
`mcall:<name>:unboxed-receiver`, `is:unboxed-value-identity`. Removed:
`setIndex:immutable-containers`, `op:delete-index`. The verifiable-core numbers will move
in both directions and should be reported as a before/after pair, not a single number
(§17).

---

## 8. What breaks in `scripts/differential.py`

The encoder is where boxing costs the most, because it currently encodes containers
*by value* and that is now wrong in a way that would show up as divergences.

1. **`Encoder.enc` must route `list`/`dict` through `alloc`** (`differential.py:96–113`),
   returning `("ref", …)` and memoised on `id`. The memo already exists for objects. This
   is not optional: today `f(x, x)` with a shared Python list encodes two structurally
   equal copies, and after boxing Core will see two *different* refs and disagree with
   itself. **Python-side aliasing must be reproduced ref-for-ref.**
2. **`lean_heap` changes shape** (`differential.py:186`). Every emitted `Obj` literal gains
   `payload` and `version` fields, so every heap literal in every generated case changes.
3. **`same()` must dereference** (`differential.py:275`). It compares list/tuple/dict
   structurally by position today. Comparing *ref numbers* would be comparing an allocator
   artefact, so the comparison must expand both sides into a canonical value tree, with a
   cycle guard, and compare *identity-sharing patterns* rather than numbers: "the value at
   argument 0 and the value at argument 1 are the same object" is the observable fact,
   `ref 3` is not.
   This requires the runner to print `(heap, result)` rather than just an `EResult`, and
   the `Repr` parser (`differential.py:230–270`) to learn `Obj`. That is the largest
   harness change in this document.
4. **`base` arithmetic gets more load-bearing** (`differential.py:720`, §25). Every
   container literal in a case now consumes a heap slot, so the receiver base offset must
   count containers as well as objects. §25's fault-injection test — running with
   `base - 1` and checking the harness reports `harness:receiver-alias` rather than a false
   agreement — must be re-run after this change, not assumed to still hold.
5. **`enc_result`'s `result-allocates-fresh-object` refusal will over-fire.** Today a
   function returning a fresh *list* encodes by value and compares fine; after boxing a
   fresh list is a fresh object and the case is refused. Left alone this is a **coverage
   regression**, and it will land in the same commit that fixes `skip_self_not_object`, so
   the two must be reported separately or the net number will hide both. The fix is to
   relax the refusal for freshly allocated *containers* whose contents are all comparable,
   and keep it for fresh class instances, whose identity genuinely has no counterpart on
   the Core side.
6. **`skip_self_not_object` (1,361) largely goes away**: a `dict`/`tuple`-subclass receiver
   is now one `Obj` with a class *and* a payload, which is what §1 was designed for.
7. Floats are independent of this document — see `Autoform/Lang/Core/Float.lean` for the
   encoder change there (`Val.float (Fl.ofBits …)`, no decimal formatting anywhere).

---

## 9. Where faithfulness is impossible — these stay holes

Stated explicitly so they are not rediscovered as divergences.

1. **`==` on objects with a user-defined `__eq__`/`__hash__`.** §27's boundary, and boxing
   does *not* move it. `Val.eqPy` compares structurally; CPython dispatches to user code.
   The 27 cases `differential.py` refuses under `unencodable_reasons` stay refused.
   It *becomes possible* to fix — `eqPy` could re-enter `evalExpr` to call `__eq__` — but
   that makes equality mutually recursive with evaluation (equality can raise, can loop,
   can mutate the heap), which is a second design of comparable size. Not in scope, and
   guessing in the meantime is worse than refusing.
2. **`is` / `id` on unboxed values** (`int`, `str`, `bool`, `float`, `tuple`). CPython
   interns small integers and some strings; none of it is specified. Hole
   `is:unboxed-value-identity`.
3. **Slice assignment and slice deletion** (`xs[a:b] = …`, `del xs[a:b]`). Needs a slice
   *value* with tri-state `start`/`stop`/`step`, plus CPython's extended-slice length
   rules (`xs[::2] = [...]` requires matching lengths, `xs[a:b] = ...` does not). Holes
   `setIndex:slice`, `op:delete-slice` until Core has a slice value. Boxing is a
   prerequisite for that work, not a substitute.
4. **Anything observing deallocation**: `weakref`, `__del__`, refcount-driven finalisation.
   The heap is append-only and never collects. `cachetools` uses `functools` machinery
   that touches weakrefs; those functions must remain holes rather than being modelled
   against a heap that never frees.
5. **`sys.getsizeof`, `id()` as a number, memory addresses.** Allocator artefacts.
6. **Concurrent mutation / thread safety.** Core has one thread; `cachetools`' locks
   already encode as unrepresentable and should stay that way.
7. **Dict *iteration order* after delete-then-reinsert is faithful, not a hole** — worth
   recording, because it looks like it should be a problem. CPython 3.7+ guarantees
   insertion order, a deleted key reinserted goes to the end, and `Stdlib.dictSet`'s
   replace-in-place/append-at-end rule plus `dictDel` reproduce exactly that. What is
   *not* faithful is `popitem` on a dict that has had deletions in a specific pattern
   where CPython's compact-array layout leaks through — no known case in the corpus, but
   it is an assumption, not a theorem.

---

## 10. Suggested landing order

Each step is independently checkable, which matters because the oracle numbers move at
step 4 and must not be attributed to step 1.

1. `Payload`/`version` on `Obj`, `Heap.payload`/`setPayload`, no behaviour change yet
   (nothing constructs a payload). Refine.lean untouched; all corpora re-verify.
2. `Val.beq` → `Val.identical` + `Val.eqPy` (§5), still on unboxed containers. This is the
   mechanical `Option`/heap/fuel plumbing, and it is separable from boxing. Corpora
   re-verify; oracle numbers unchanged.
3. Container literals allocate; `Expr.index`, `valIn`, iteration read through refs (§4).
   `total_run` rewritten. **Oracle numbers change here for reasons 8.1–8.5.**
4. `setIndex`, `delIndex`, and the `MethodResult.mutating` wiring (§2). The holes close.
5. `differential.py` encoder and comparison (§8), including re-running §25's
   `base - 1` fault injection.

Step 3 is the one that can regress the conformance number while being correct. Report
before/after per step rather than a single delta, as §17 requires.
