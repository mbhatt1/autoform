# Boxed containers for Core

**Status: steps 1-4 landed for Python (the 2026-10 section directly below says how, where
it departs from this design, and why); step 5 -- the oracle's encoder -- is not done.**
Read this before changing `Syntax.lean` or `Semantics.lean`.

## Steps 3-4 as landed (Python)

### What changed

* **A display is an object.** The exporter wraps every Python list display and `{}` in
  `Expr.boxContainer` (`.py` files only). It evaluates the inner `listE`/`dictE` and
  allocates an `Obj` of class `list`/`dict` whose `Payload` holds the contents. Joern
  lowers a non-empty dict display and every comprehension to an empty display followed by
  `d[k] = v` / `.append`, so all of them are boxed. Results of `list(x)`, `dict(x)`,
  `sorted(x)` and `xs.copy()` are boxed too (fresh objects in CPython).
* **`Stmt.setIndex`** (evaluates `v`, `e`, `i`: CPython's order) writes a boxed container
  with `Heap.setPayload` on the reference. **`Stmt.delIndex`** is new and replaces the
  exporter's `op:delete-index` for Python. Both run a plain object's OWN
  `__setitem__`/`__delitem__`; a tuple/str/scalar is `TypeError`; an unboxed list/dict
  value keeps the original hole. Non-Python dialects are untouched (the old hole,
  unevaluated).
* **Mutating methods** (`append`, `pop`, `insert`, `extend`, `clear`, `remove`,
  `setdefault`, `update`, `popitem`) on a boxed receiver go through `Stdlib.method`
  unchanged and the new receiver value is written back with `setPayload` -- to the
  reference, never to the receiver expression, so `t = self.d; t.pop(k)` reaches `self.d`.
* **Readers see through the heap one level** (`Heap.view`): `index`, `in`, truthiness in
  `if`/`while`/`and`/`or`/`not`/`cond`, `for`, `*xs`, `**d`, `xs + ys`, builtin-base
  construction, and the builtins in `Boxed.viewedBuiltins`.
* **`==` is `Val.eqPy` on every container**, not only on references (`(xs,) == ([1],)`
  compares a boxed list at depth 1), boxed-vs-unboxed compares contents, and dict equality
  is now order-insensitive (it was positional, which CPython's is not). `in` on a list or
  tuple uses `Val.eqPy` per element.
* **Negative indices** count from the end under Python. Before this change `Int.toNat`
  clamped them, so `(7, 8, 9)[-1]` read `7` -- a silent wrong answer on every Python corpus.
  Outside Python a negative index is the hole `index:negative`.

### Where this departs from the design above, and why

1. **A wrapper constructor, not a change to `listE`/`dictE`** (§1). C aggregate
   initializers and JS/Java literals also translate to `listE`/`dictE`, and C copies
   structs by value; re-meaning the shared constructors would have changed every C corpus.
   The exporter knows the source language; the semantics does not need to guess it.
2. **Snapshot iteration is kept, but guarded** (§4 says it must not be retained). Iterating
   a snapshot is exact as long as nothing writes to the object during the loop, and
   `Obj.version` detects the write: a loop whose container's version moved ends in
   `forIn:container-mutated-during-iteration` instead of an answer. This is sound and
   conservative (a loop that writes and then returns before the next element would have
   agreed with CPython and is still refused), and it avoids a new mutually recursive
   iterator in `execFor` -- and with it a new arm of the fuel-monotonicity proof.
3. **Dict views are refused** (§2 treated `keys()`/`values()`/`items()` as reads). A
   snapshot list is right until the next write and silently stale after it; boxing is
   exactly what makes "after it" reachable. `mcall:dict.<m>:live-view-not-modelled`.
4. **`Val.beq` is NOT split; heap-free consumers are guarded instead** (§5's cost table).
   `Stdlib` keeps comparing with `Val.beq`; a method or builtin that would compare a boxed
   reference by address (`count`, `index`, `remove`, `dict(pairs)`) holes
   (`mcall:<m>:boxed-element-equality`, `call:<f>:boxed-key`), and a dict key that is
   unhashable (a list or dict, boxed or not, or a tuple holding one) is CPython's
   `TypeError` before `Val.beq` ever sees it. Hashable keys contain no boxed reference, so
   `Val.beq` on keys stays exact.
5. **The fuel-monotonicity proof needed one new arm per statement**, and `Refine.lean`'s
   truthiness lemmas now state `(h.view v).truthy`; no theorem lost its content. Three
   generated cachetools accessor theorems and four hand-written `CachetoolsSpec` theorems
   gained a precondition CPython imposes too (the receiver is a plain object; a membership
   probe is hashable); the `Basis` accessor lemmas take it as an auto-param discharged for
   every non-Python program, so no C/C++ theorem changed.

Also found on the way and fixed separately (commit "export_ast: do not box Python
class-typed locals as C structs"): the C boxed-aggregate prologue was running on Python
methods, rebinding a class-typed local such as `LFUCache` (inside
`LFUCache.__setitem__`) to a fresh `<local>` box. 43 of the 209 cachetools 7.1.7 methods
carried such a prologue with the exporter at 46c65fc.

### Evidence

* `Autoform/BoxedContainers.lean`: 30 kernel-checked evaluations of hand-written Core
  programs (aliasing, append/pop through aliases and temporaries, dict set/get/del,
  insertion order, `==`/`is`/`in`, negative and out-of-range indices, unhashable keys,
  truthiness, and each refusal).
* `tests/test_boxed_containers.py`: 34 Python functions run through the REAL exporter
  (pinned Joern 4.0.606 + pysrc2cpg) and renderer and compared with CPython 3.11: 31 agree,
  the 3 unmodelled shapes are pinned as holes, 0 diverge.
* cachetools 7.1.7 (GitHub tag `v7.1.7`, commit `01af8e5`), ledger
  (`scripts/ledger.lean.tmpl`), exporter at 46c65fc vs this change:

  | | before | after |
  |---|--:|--:|
  | holes | 26 | 20 |
  | `op:delete-index` | 6 | 0 |
  | hole-free | 184 / 209 | 190 / 209 |
  | verifiable core | 105 / 209 | 107 / 209 |
  | dynamic-hole risk | 890 | 896 |

  The other hole causes are unchanged (`scope:nonlocal-write` 8, `call:computed-callee` 6,
  `expr:genExp` 2, `op:delete-slice` 2, `op:stringExpressionList` 1,
  `control:TRY-multiCatch` 1). `setIndex` was never a STATIC hole -- it held at run time --
  so the ledger understates the change.
* `scripts/differential.py` on the same tree (CPython 3.11, the suite's own tests), AST
  without boxing vs with boxing, both under the new semantics: 246/248 agree in both,
  the same 2 divergences in both (`TLRUCache.__getitem__` reaching a test-file subclass's
  `__missing__`, which Core resolves to `Cache.__missing__`: not introduced here),
  functions exercised 106 -> 111, INCONCLUSIVE 290 -> 315 (the 5 functions that became
  hole-free when `del d[k]` was translated now run and stop at other, pre-existing holes).

### What remains

* **Step 5, the encoder.** `differential.py` and `core_oracle.py` still encode a receiver's
  list/dict fields as VALUES, so `self._Cache__data[k] = v` on an encoded receiver is still
  `setIndex:immutable-containers`, and `skip_self_not_object` is unchanged. §8 is the
  plan; the receiver `base` arithmetic and the `base - 1` fault injection must be redone
  with it. (`core_oracle.py` does not run at 46c65fc at all: its probe opens
  `Autoform.Generated` rather than the per-corpus namespace.)
* Live dict views; `list.sort`/`reverse`; slice reads, writes and deletes; `__setitem__`
  inherited through a translated base class (needs an MRO); `list`/`dict` SUBCLASS
  receivers (`Val.bobj`, still value semantics); `**kwargs` dicts and `*args` tuples are
  unboxed values (mutating a `kwargs` dict holes).
* `True == 1` is `False` in Core (`Val.beq` has no bool/int case), so `d[True]` misses a
  key `1`. Pre-existing and not introduced here, but boxing makes dict writes reachable.

Step 2 landed WITHOUT re-typing `applyBinop`, which this document proposed and which is the
wrong trade: 155 call sites, and it destroys the reducible scalar path that `Refine.lean`'s
`evalSimp` lemmas and every `decide`-based generated theorem depend on. `Val.eqPy` is instead
diverted to at the ONE `evalExpr` call site where a ref can appear, behind a named guard
`binopNeedsHeap`. Twelve proofs needed repair rather than a hundred, and `applyBinop` keeps
its heap-free signature. Section 5 below should be read with that substitution in mind.

One correction to section 5 that matters for step 3: the comparison's fuel must NOT come from
the evaluator's fuel. Threading `evalExpr`'s fuel into `Val.eqPy` makes a `binop`'s value
depend on the fuel budget, which breaks `evalExpr_pure_fuel_indep` outright -- the pure
fragment includes `binop`. `Val.eqFuel h = h.length + 64` is derived from the heap, which is
equal across two runs differing only in evaluator fuel because the pure fragment is
heap-inert.

Step 2 splits into two halves that are NOT equally separable. `Val.identical` (the `is` half,
section 5) is landed: it is total, heap-free, and touches one call site, and it made `is`
strictly more honest at no cost to the oracle (35 compared / 169-174 agree, unchanged). The
`Val.eqPy` half was at first judged unsliceable -- `Val.beq` is structurally recursive and
reducible by `rfl`/`decide`, which `Refine.lean` depends on, so re-typing it to take a heap
and fuel could not be done without breaking the corpora. It landed anyway (step 2b,
`de8db00`, 2026-08-22) by *not* re-typing `Val.beq`: `Val.eqPy` is a separate heap-aware
relation, reached only through the `binopNeedsHeap` guard described at the top of this
section.

Step 1 (`Payload`/`version` on `Obj`, `Heap.payload`/`setPayload`) is in the tree and is
INERT: nothing constructs a payload other than `.none`. It cost zero proof changes and zero
corpus regeneration, and the oracle is unchanged at 35 compared / 169-174 agree, which is
the check that it is really inert. It is landed separately for the reason section 10 gives --
the numbers move at step 3, and a number that moves two steps after the field appeared cannot
be blamed on the field.

**Problem.** `Val.list`, `Val.tuple` and `Val.dict` are *values*. Python's are *objects*.
The consequences are all currently visible in the ledger and the oracle:

| symptom | where | size |
|---|---|---|
| `Stmt.setIndex` is an unconditional hole | `execStmt`'s `.setIndex` case, `Semantics.lean` | `setIndex:immutable-containers` |
| `del d[k]` / `del xs[a:b]` are holes | transpiler | `op:delete-index`, `op:delete-slice` |
| `list.append` / `dict.pop` implemented but unwireable | `MethodResult`, `Stdlib.lean` | `MethodResult.mutating` |
| `dict`/`tuple`-subclass receivers refused by the oracle | `differential.py` | `skip_self_not_object` 1,361 |
| `==` cannot distinguish "equal" from "the same object" | `Val.beq` | see §5 |

All five are one defect. This document specifies the proposed fix, what it would cost, and
what it would not fix.

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

A payload on `Obj` closes `skip_self_not_object`; a separate box does not.
`cachetools.Cache` is a `dict` subclass; `_HashedTuple` is a `tuple` subclass. Under a
separate `Val.box`, such an instance is *both* an object (it has `__dict__` fields and a
class) and a container, so it has to be encoded as one or the other — which is why the
oracle refuses 1,361 cases today. With the payload on `Obj`, it is one heap cell:
`cls := "Cache"`, its own `fields`, and `payload := .dict [...]`. Method dispatch resolves
in Python's order:

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

### The rule the design depends on

> **After the receiver expression has been evaluated to a `Val.ref`, the expression is
> never looked at again.** Mutation is `Heap.setPayload r …`. No mutation path may
> mention `Expr`.

This is what avoids the trap the stdlib work measured. The CPG desugars

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

Both fall out of the design without a special case.

---

## 4. Iteration

`for x in xs` currently reads `Val.iterable : Val → Option (List Val)` and iterates a
*snapshot*. After boxing there is a choice:

* **CPython's `list_iterator` holds the list object and an index.** Appending during
  iteration extends the loop; deleting shortens it. Modelling this means `execFor` carries
  `(Ref, Nat)` rather than `List Val` and re-reads the payload each step.
* **CPython's `dict` iterator raises** `RuntimeError: dictionary changed size during
  iteration`. This is what `Obj.version` is for: the iterator records the version at
  creation and the loop head compares. Cheap, and it turns a currently-invisible wrong
  answer into a modelled exception.

Snapshot iteration must not be retained past this change. It is currently harmless because
nothing can mutate a container mid-loop; boxing is what makes the case reachable. Landing
boxing and snapshot iteration together would introduce a silent wrong answer in the same
commit that removes one.

For an unboxed `Val.tuple` or `Val.str`, snapshot iteration remains exactly right.

---

## 5. `==` versus `is`

This part of the change is the most likely to produce false divergences.

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

1. **Reference identity short-circuits to `true` first.** This is CPython's behaviour
   (`PyObject_RichCompare`'s identity fast path for containers), and it is what makes
   `a == a` terminate for the cyclic list above.
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
  interpreter is a specification, not a runtime. To be stated in the ledger.
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

The "~74 theorems" figure overstates the cost, because of a design decision already taken:
`PureE` (`Refine.lean`) is `lit | name | fnref | unop | binop | cond` — it
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
unchanged; only its meaning changes. This is the deep-embedding payoff: a semantics change
that re-verifies six corpora without re-running Joern.

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
   Boxing makes a fix possible — `eqPy` could re-enter `evalExpr` to call `__eq__` — but
   that makes equality mutually recursive with evaluation (equality can raise, can loop,
   can mutate the heap), which is a second design of comparable size. Out of scope; until
   then the cases stay refused.
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
7. **Dict *iteration order* after delete-then-reinsert is faithful, not a hole.**
   CPython 3.7+ guarantees
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
