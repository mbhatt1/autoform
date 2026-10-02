# Conformance from the corpus's own test suite

`scripts/differential.py` is the only oracle that compares the Lean semantics to a real
runtime. For Python it does not invent inputs. It runs the corpus's own pytest suite
under `sys.settrace`, records each call into a translated function, and replays the
recorded call through the Lean interpreter. The recording covers the arguments, the
receiver, every object reachable from them (as a `Heap` snapshot) and the CPython
outcome. Random integers and synthesized calls are only a supplement, and each case is
tagged `origin: test-suite | random | constructed`.

This is the "drive the harness from the repository's own test suite" item from
STRATEGY.md §3/§13. It has been the harness's primary input source since STRATEGY.md §19.
This document describes the recorder as it stands after a round of fixes to it. The
measurements below are from that round, and so are the findings, which are about the
exporter and Core.

## Running it

```sh
git clone https://github.com/tkem/cachetools ~/src/cachetools
git -C ~/src/cachetools checkout 01af8e5          # the commit ast-Cachetools.json is from (CI pins it)
lake build Autoform.Generated.Cachetools
python3.11 scripts/differential.py ast-Cachetools.json ~/src/cachetools Cachetools 5
```

Run it from a scratch directory, because it writes `conformance.json` to the current
directory. A run takes about 15 minutes on a loaded 4-core box. Tracing the suite takes
under 10 seconds; almost all of the time is the Lean interpreter evaluating the cases in
chunks of 20.

**Python version.** cachetools at `01af8e5` declares `requires-python >= 3.10`. On the
measurement box `python3` is 3.11.15, and that is the only interpreter there with
`pytest` installed. 3.10, 3.12 and 3.13 are present but have no `pytest`. Under 3.11.15
the suite passes: 312 tests, rc 0, both standalone and under the tracer. The harness
prints a `WARNING` and records `test_runs[].rc` whenever the suite does not pass under
tracing, because a failing suite only yields the calls made before each failure.
`exit_kind` was checked on CPython 3.10–3.13.

## What a recorded case is, and how it can be wrong

A recorded case is only as good as the recorder. Before this round, every fault listed
below either produced a comparison CPython never made or silently threw away reach. Each
one now has a test in `tests/test_recorder.py`.

| fault | effect before | now |
|---|---|---|
| an outcome counted as "raised" if any exception passed through the frame and the result was `None` | `try: d[k] except KeyError: pass` was recorded as raising `KeyError`. Old and new recordings of the same cachetools calls differ in 8 cases (`LRUCache.__touch` ×2, `TTLCache.__setitem__` ×1, `TLRUCache.__setitem__` ×5). All 8 happened to hole in Lean, so no false verdict was issued; each would have become a false divergence once its hole closed | the exit kind comes from the opcode the frame stops at (`exit_kind`) |
| generators | a generator's `return` trace event fires at every `yield`, so each yielded element was recorded as the call's result | refused, and counted as `generator` |
| the index was keyed by `(file, first line)` | the module's own code object (`<module>`, line 1) was recorded as a zero-argument call to whatever `def` sits on line 1 | keyed by `(file, first line, co_name)` |
| same-named `def`s in one scope | every call was attributed to the **last** body. Recorded `make_info` outcomes differed in 4 cases, because its three bodies differ | numbered `f<redefined>0, 1, …` in source order, which is the exporter's convention, checked against `cached.decorator.make_info` |
| `self` was always treated as the receiver | nested functions the exporter keeps `self` on (`keys.methodkey`, `_locked.wrapper`, …) were refused as parameter mismatches | the receiver is whatever the AST stripped |
| closures replayed by name | free variables were unbound in Core | plain closures are replayed through `applyClosure` with their captured cells, and an instance of a function-local class carries `Obj.captured`. A capture that cannot be encoded refuses the call |
| floats refused as a "value-model gap" | Core has had `Val.float` (an IEEE bit pattern, `Core/Float.lean`) since before this; every `time.monotonic` timer receiver was refused | encoded by bit pattern and compared bit-exactly (any NaN matches any NaN) |
| `inspect.isroutine` true for any object whose class defines `__get__` | user descriptor instances were refused as "callable" | encoded as objects |
| `Cls[int, int](...)` stores `__orig_class__` | `vars()` on the alias forwards to the class namespace, so every `TLRUCache[int,int,int](...)` receiver was refused | encoded as a type reference |
| a recorded call's result was unencodable | it still used up one of the function's `n` slots | the slot is given back |
| first `n` calls only | the suite's first `n` calls are usually one test, one receiver class, one state | records up to `40·n` calls, then keeps `n` per function round-robin across call shapes (`diversify`) |
| `MAX_TOTAL_CASES` shuffle-and-cut | could drop every case of a function, uncounted | round-robin across functions; each cut is counted in `truncated_cases` |
| refusals were global counters | `skip_unencodable_args: 12002933` said nothing about any function | per-function `trace_ledger` (calls, recorded, over quota, refusals by reason) feeds `coverage.by_status` |
| an exception inside the tracer | propagates into the traced program and fails a cachetools test | counted as `recorder-error` against the function |
| `live` instances keyed by `__name__` | the six distinct nested classes cachetools calls `Wrapper` were conflated | keyed by `module:qualname` |

Three things remain refused, each with a counted reason:

* **Value-model gaps:** `set`, `frozenset`, `functools.partial`, a builtin-subclass
  receiver (`_HashedTuple`), an opaque C object, a container wider than 512, and an
  object or float used as a dict key.
* **Lambdas and module initializers.** These have no call site that can be matched to a
  traced frame.
* **Non-empty `**kwargs`.** The harness has no keyword channel.

`coverage.by_status` names the reason for every function that was not compared.

## Measurement

The same AST, the same corpus commit (`01af8e5`), the same Python (3.11.15) and the same
command were used for both runs. `build_stable: true` held in both. Both runs used
`python3.11 scripts/differential.py ast-Cachetools.json <cachetools> Cachetools 5`.

| | harness at `46c65fc` | this round (merged with item I) |
|---|--:|--:|
| functions in `ast-Cachetools.json` | 209 | 209 |
| hole-free | 184 | 184 |
| exercised (≥ 1 case built) | 106 | 128 |
| **compared** (≥ 1 case adjudicated) | **48** | **60** |
| cases agreeing | 246 / 248 | 233 / 247 |
| divergences | 2 | **14** |
| INCONCLUSIVE cases | 290 | 353 |
| cases cut by the 600-case budget (counted) | 0 | 64, from 17 functions |
| by status: compared / blocked by semantics or transpiler / AST holes / value model / unexercised | 48 / 57 / 25 / 22 / 57 | 60 / 67 / 25 / 33 / 24 |

The "this round" column was re-run on the merged branch (items C and I: the class-aware
`_HashedTuple` encoding adds three compared functions). The README's earlier "30 of 208" was stale. At `46c65fc` the harness compares 48 of 209
(208 entries carry a `.py` file; the 209th is `<module-objects>`).

Compared, gained: `LRUCache.__setitem__`, `TTLCache.__contains__`, `TTLCache.ttl`,
`_UnboundTTLCache.maxsize` (all reached through floats), `_DescriptorBase.__init__`
(descriptor instances), and the `_cachedmethod.py` closures `_locked.wrapper`,
`_unlocked.wrapper`, `_condition/_locked/_unlocked.cache_clear` (which reached the oracle
through the receiver fix and captures, and which all diverge — see below). `_cached.py`'s
`_unlocked.wrapper` also agrees now.

Compared, lost:

* `TLRUCache.__iter__`. Its agreement was **false**: see finding 1.
* `_TimedCache._Timer.__call__`. The 5 calls `diversify` keeps all hole on
  `mcall:_Timer._Timer__timer`, which is a call through an instance attribute holding a
  callable object. It is a sample effect, not a verdict.

## Findings

Every divergence was traced to its cause. None is "fixed" here by exclusion.

### 1. The exporter translates `yield` as `return`, which produced a false agreement

`TLRUCache.__iter__` and `TTLCache.__iter__` are generators. In `ast-Cachetools.json`
both are hole-free, and the `yield curr.key` in each body is a `{"k": "ret"}`. Joern's
`pysrc2cpg` lowers `yield` to a `Return` node, and `cartographer/export_ast.sc`'s
`case r: Return` emits `ret` for it. The translation is therefore "return the first live
key", which is wrong. The old recorder made the same mistake in the same direction: it
recorded the first yielded element as the call's result. So `TLRUCache.__iter__` was
**compared and agreeing** at `46c65fc`, two wrong models agreeing with each other. The
recorder now refuses generator calls, so the false agreement is gone.

**Fixed in the exporter (item L).** A `Return` whose code is a `yield`/`yield from` is the
hole `gen:yield` (statement or value position), and a function whose own body contains
one starts with `gen:generator`: calling a generator runs none of its body, and Core has
no suspension. Both `__iter__`s are no longer hole-free (`ast-Cachetools.json` re-exported
at `01af8e5`; `tests/test_cachetools_ast_scoping.py` pins it). Eager materialisation into a
list was considered and rejected: it is wrong for an infinite generator, a consumer that
stops early, and these two bodies, which read the timer and the linked list between
yields.

### 2. The exporter binds a call through a closure variable to an unrelated method (11 divergences)

In `_cachedmethod.py`, `_locked`, `_unlocked` and `_condition` take a parameter named
`cache`, and their inner `wrapper` and `cache_clear` call `cache(self)`. The AST binds
that call to `cachetools/_cachedmethod.py:<module>._WrapperBase.cache`, which is a
*property of another class*. Core then calls a method with no receiver and raises
`TypeError`, while CPython calls the captured lambda. This accounts for all 11 closure
divergences (`_unlocked.wrapper` ×5, `_locked.wrapper` ×3, `*.cache_clear` ×3). A scan of
the AST for calls bound to a qualified function whose short name is a local or captured
name of the caller (`misbind`-style: parameters, assignments and enclosing functions'
parameters) finds these 6 call sites. It finds one more:

* `cached.decorator` does `from ._cached import _wrapper`, but the AST binds both of its
  `_wrapper(...)` calls to **`_cachedmethod.py`'s** `_wrapper`, which is the wrong module.
  It is INCONCLUSIVE today (`functools.update_wrapper` holes first), so no verdict has
  been issued. It is a latent wrong translation.

Both are name-based call resolution in the front end. The fix belongs in the exporter:
prefer a local or captured binding over a global method of the same short name, and honour
the import.

**Fixed in the exporter (item L), and the 11 divergences remain, now with a Core cause.**
A Python call whose bare callee is bound in a function scope (the caller's or an enclosing
`def`'s parameter, assignment or import) is now emitted *by the variable's name*
(`Expr.call "cache"`, `Expr.call "_wrapper"`); Joern's target is kept only when it is the
one function that scope binds the name to (a nested `def`, or `x = lambda`). The scan
above now finds 0 sites in the re-exported AST (`tests/test_cachetools_ast_scoping.py`).
The pyscoping fixture re-exports byte-identically under the same rule.

The differential verdicts did not move, because Core's `Expr.call` consults the function
table **before** a non-closure local: `Ctx.resolve "cache"` is a unique suffix match for
`_WrapperBase.cache`, and the lambda the harness supplies for `cache` is a `.fn`, not a
`.clos` (checked with `#eval` on the rendered program: `resolve "cache"` = `some
…_WrapperBase.cache`; `resolve "_wrapper"` = `none`, ambiguous, so `cached.decorator`'s call
now reaches the imported `_cached.py` `_wrapper` through the environment). So the remaining
11 are finding 3's suffix fallback applied to a bare call name. Python scoping for bare
names in Core (in progress elsewhere) resolves them; the exporter now hands Core the name
Python would look up rather than a wrong qualified one.

### 3. Core's method dispatch has no class hierarchy (3 divergences)

The cachetools suite subclasses its caches (`class DefaultCache(self.Cache)`) and
overrides `__missing__`. When `Cache.__getitem__` or `TLRUCache.__getitem__` runs on such
an instance, CPython calls the override. Core's `Ctx.resolveMethod cls m` looks for
`.<cls>.<m>` and otherwise falls back to `Ctx.resolve m`, which takes **any** unique
function with that suffix. It finds `Cache.__missing__`, which raises `KeyError`. That
gives `Cache.__getitem__` ×1 and `TLRUCache.__getitem__` ×2. The same fallback answers an
unbound name (`Expr.name`) with a same-suffix function or `unit` instead of `NameError`.
That fallback is how finding 2's misbinding would also have surfaced, had the harness not
supplied captures. Inside a corpus these fallbacks are right only when names are unique.
For a receiver class Core does not know, the honest answer is a hole.

## Re-export (item L)

`ast-Cachetools.json` was re-exported from cachetools `01af8e5` with the merged exporter
(items H, G and L) and now has a provenance record
(`provenance/ast-Cachetools.json.prov.json`). Static figures, each from `stats`-style
counting over the AST and checked against `ledger-Cachetools.json`:

| AST | holes | hole-free |
|---|--:|--:|
| committed at `46c65fc` | 26 | 184 |
| fresh export, exporter at `86a161b` (H: cells, defaults) | 48 | 167 |
| + G (boxed containers) | 42 | 170 |
| + L (this change: `gen:*`, local-name calls) — committed | 46 | 168 |

L's own static delta is exactly 10 functions: the two `__iter__`s gain `gen:generator` +
`gen:yield`, and 8 call sites change callee name (`_locked/_unlocked/_condition` ×
`wrapper/cache_clear`, `cached/cachedmethod.decorator`).

Differential, `python3.11 scripts/differential.py ast-Cachetools.json <cachetools@01af8e5>
Cachetools 5`, each run against its own rendered module:

| | committed AST, `86a161b` | H+G export, merged | H+G+L (committed) |
|---|--:|--:|--:|
| hole-free | 184 | 170 | 168 |
| compared | 60 | 48 | 48 |
| cases agreeing | 233 / 247 | 225 / 237 | 225 / 237 |
| divergences | 14 | 12 | 12 |
| by status: compared / blocked (sem.) / AST holes / value model / unexercised | 60 / 67 / 25 / 33 / 24 | 48 / 65 / 39 / 33 / 24 | 48 / 65 / 41 / 31 / 24 |

* L moves no verdict: the two generators move from "value model" (the recorder refuses
  generator calls) to "AST holes", and the 11 closure divergences now have a Core cause
  (above).
* The 12 compared functions lost between the first two columns all carry exactly one hole,
  `param:default-nonliteral` (H: `cache_getitem=Cache.__getitem__`, `key=keys.hashkey`, …).
  That hole fires only on a call that *omits* the argument, but the harness treats any
  static hole as "untestable until translated". `TLRUCache.__getitem__` is among them, so
  its 2 finding-3 divergences are no longer *observed*; they are not fixed.
* Remaining 12 divergences: 11 × finding 2 via Core's bare-name suffix rule, 1 ×
  `Cache.__getitem__` (finding 3).

## What remains

* Finding 3 in Core: method resolution along `classBases`, or a hole for an unknown
  receiver class; and Python scoping for a bare call name, which retires the last 11 of
  finding 2. Each changes what translated functions compute, so specs bound to the AST
  hash move with it.
* The harness could compare a function whose only static hole is a parameter default on
  every recorded call that supplies that argument; today it skips the function.
* Lambdas (9 functions) need the exporter's per-file lambda numbering reproduced from the
  source. The numbering is plausible but unverified, so the recorder does not guess it.
* `functools.partial` (the `key=` of every `cachedmethod` wrapper) and `set` (all of
  `LFUCache`) are the two largest value-model blocks. Each needs a Core value, not harness
  work.
* The 600-case budget now cuts 49 cases, mostly the 4th and 5th case of a function and
  random-origin cases. Raising it costs Lean time linearly.
