# Evidence — V8Base (C++, `v8/src/base`)

First ledger + assurance case + execution oracle for one of the five large corpora.
Before this, all three existed only for `cachetools` (238 Python functions) and the toy
modules, so 12,700 of the 12,946 translated functions had no coverage claim at all.

`ledger-V8Base.json` and `sacm-V8Base.json` are gitignored (`ledger-*.json`,
`sacm-*.json`), so their numbers are recorded here. The two artifacts that are *not*
ignored are committed: `ast-V8Base.json` (the neutral AST the module is rendered from)
and `core-oracle-V8Base.json` (the full execution record: every refuted function, its
hole labels, and the inputs that reached them).

Regenerate:

```
sed s/@MODULE@/V8Base/g scripts/ledger.lean.tmpl > /tmp/L.lean && lake env lean --run /tmp/L.lean
python3 scripts/core_oracle.py ast-V8Base.json V8Base -n 12 --no-tests --chunk 120 \
        --out core-oracle-V8Base.json
python3 scripts/sacm.py --module V8Base            # with core-oracle-V8Base.json as core-oracle.json
```

## 1. Trust ledger

| | V8Base | cachetools (for scale) |
|---|---|---|
| functions translated | 1920 | 238 |
| AST nodes | 24,755 | — |
| holes | 1513 (6% of nodes) | — |
| hole-free (static upper bound) | 1290 / 1920 (67%) | 165 / 238 |
| **verifiable core** (hole-free AND call-closed) | **807 / 1920 (42%)** | 74 / 238 |
| dynamic-hole risk | 6240 constructs may hole at runtime | 971 |

Wall clock: **4.3 s**, not the quadratic blow-up seen on Django's 10k functions (363 s).
`Ctx.resolve` is still O(n) per lookup; 1920 functions is simply small enough.

Top hole causes (79 distinct labels in all):

| cause | count |
|---|---|
| `expr:CONTROL_STRUCTURE:DO` | 137 |
| `op:cast:opaque-type` | 98 |
| `assign:lhs:indirection` | 94 |
| `op:cast:pointer` | 84 |
| `op:alloc:ctor-unresolved-class` | 80 |
| `op:indirection:pointer` | 75 |
| `op:addressOf:local:opaque-type` | 70 |
| `op:and` | 59 |
| `op:arithmeticShiftRight` | 58 |
| `op:sizeOf` | 57 |
| `control:FOR` | 56 |

The bit-twiddling operators (`op:and`, `op:arithmeticShiftRight`, `op:shiftLeft`,
`op:or`) are the cheapest remaining work: they are ordinary total operations on
fixed-width integers, unlike the pointer and cast families around them.

## 2. Assurance case (`scripts/sacm.py --module V8Base`)

Top claim **G1: UNDEVELOPED** — 1513 unresolved holes carried as assumptions, and
faithfulness not established over the module.

| goal | status | why |
|---|---|---|
| G2 translation faithfulness | UNDEVELOPED | `conformance.json` absent — no differential run exists for V8Base. The differential harness traces a *Python* test suite; C++ has no equivalent path, so this is not a missed run but an unbuilt capability. |
| G3 every function translated without holes | **UNSUPPORTED** | 630/1920 functions carry at least one hole; 1513 occurrences over 79 causes. |
| G3.1 the 807-function core is statically hole-free and call-closed | SUPPORTED, then **countered** | evidence E6 (ledger); defeater D3.1 below. |
| G3.2 the core is hole-free at RUNTIME | **DEFEATED** (coverage 84.5%) | settled by execution, not estimated: 682 of 807 never holed, 125 did. |
| G4 specifications non-vacuous | UNDEVELOPED | `mutation.json` absent; no source-level mutation gate for this module, and no specifications about V8Base exist to mutate against. |
| G5 no unsound axiom | WEAK | `audit.json` is repo-wide: 2741 declarations on `Classical.choice, Quot.sound, propext`, kernel-replayed fresh by `leanchecker`. **No theorem about V8Base exists**, so nothing here is attributable to this module — the WEAK cap is the honest reading, not a defect in the sweep. |

Nothing was tuned to make a goal green. G3/G3.2 are red because execution says so.

## 3. Execution oracle — the number this exercise existed to produce

`scripts/core_oracle.py` runs the claimed core instead of describing it: 807 functions ×
12 synthetic inputs = 9684 cases, fuel 5000, every case answered by the interpreter.

| | V8Base (C++) | cachetools (Python) |
|---|---|---|
| claimed verifiable core | 807 | 74 |
| exercised at all | 807 (100%) | 74 |
| **never holed on any input tried** | **682 (84%)** | 30 (41%) |
| holed on some input | **125** | 44 |
| holed on an input from the project's own test suite | **0 — see denominator below** | 21 |
| inconclusive (never exercised) | 0 | — |
| **static-over-runtime overstatement** | **1.18×** | ~2.5× |

The cachetools column is the committed `core-oracle.json`, which describes an earlier
revision of that module (238 functions, core 74); the module in the tree today has 208
functions and a 100-function core. It is quoted for order of magnitude, not as a
same-revision comparison.

**C++ overstates by 1.18×, not the 2.5× measured on Python.** The direction is the same
but the magnitude is far smaller, and the reason is visible in the labels: cachetools'
core is full of dict/attribute polymorphism that only a value can settle, while V8Base's
core is dominated by small arithmetic functions whose static hole-freedom really does
survive execution. Holes are *denser* in C++ overall (1513 over 1920 functions) but they
are concentrated in functions the ledger already excludes from the core.

### The denominator, stated

`holed_on_a_real_input = 0` is **not** evidence that no real input holes. It is
`0 / 0`: **zero functions were exercised with a recorded input**, because
`differential.py`'s tracer imports a Python test suite and V8's C++ tests have no such
path. Every one of the 9684 cases is synthetic. So:

* the 125 refutations are sound — the interpreter *did* hole, on inputs it was handed;
* the 682 survivors are "never holed over 12 synthetic inputs each", which is weaker
  than cachetools' survivors, some of which faced arguments the real suite produced.

### How much of the refutation is the harness?

Reported rather than buried: of the 125 refuted functions, 55 hole *only* with
`field:<name>:non-object` labels, and 10 of those name what look like receiver fields
(V8's trailing-underscore convention: `initialized_`, `timer_`, `address_`, `vmar_`).
Those 10 are the ones where a synthetic receiver of the wrong shape could be at fault.
The other 45 name namespace-level or static lookups — `nullopt`, `FromLittleEndian`,
`bit_cast`, `kExitWithSuccessAndIgnoreDcheckFailures` — which the transpiler models as
field access on a non-object and which no receiver shape would fix. So the harness-risk
band is **10 of 125 refutations at most**, and the corrected core is between 682 and 692.

Runtime hole labels, most frequent first: `field:nullopt:non-object` (144),
`field:FromLittleEndian:non-object` (144), `call:DCHECK` (84), `binop:+` (68),
`index:unsupported` (64), `op:sizeOf` (60), `field:initialized_:non-object` (48),
`unop:cast:u64` (47), `call:IsNull` (36), `field:bit_cast:non-object` (36).

89 of the 125 hole on *every* input tried, i.e. they are unconditionally broken rather
than input-dependent — a static analysis of the interpreter, not just of the AST, would
have found them.

## 4. Three harness bugs found on the way (all in `scripts/core_oracle.py`)

Each one made the oracle quieter than the truth, which is the failure this repo keeps
re-learning.

1. **The driver did not type-check at all.** `applyFunc` gained a sixth explicit
   parameter (keyword arguments); the driver still called it with five, so `.2` was a
   projection on a function and *every* case failed to elaborate. The driver then read
   back no answers, bisected to singletons, and would have classified all 807 functions
   INCONCLUSIVE — a run that reads as "nothing refuted". Fixed, and an explicit abort
   now fires when zero cases out of a non-empty run get an answer.
2. **Receiver fields were harvested only from Python names.** `class_fields` matched
   `file.py:<module>.Class.method` and returned `{}` for every C++ class, so every
   synthetic receiver was fieldless and every `self.f` access holed — charging the module
   for holes the harness manufactured (STRATEGY.md §27). The class-name derivation is now
   shared with `synth_cases`, and it cuts the C++ signature off before splitting, which
   also fixes classes being read out of a parameter list (`Get:optional(v8.base.X*)`).
3. **The freshness gate compared only function-name sets.** `/tmp/final-V8Base.json`, the
   AST this task was pointed at, was one transpiler commit behind the module — 2055 holes
   against the module's 1513 — and the gate passed in silence because the names matched.
   It now also compares a body-derived fingerprint (total hole count, `hole` + `holeS`)
   and says DISAGREE loudly; the result is recorded in the output as
   `ast_body_staleness`. The AST committed here is a fresh export from
   `v8run/base.cpg` and agrees with the module exactly: 1513 = 1513.
