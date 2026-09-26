# Language support — measured

The current end-to-end regression fixtures cover Python, C, C++, Java, Go,
JavaScript, TypeScript and Kotlin. Run `AUTOFORM_TEST_JOERN=1 python -m pytest
tests/test_source_pipeline.py -q` to translate them through Joern, compare with the
real runtimes and compile the resulting conformance theorems. This validates the
fixture operations; it is not whole-language or arbitrary-repository equivalence.

This is a historical source-frontend measurement. Some recorded defects have since
been fixed (including the JavaScript dialect and JSX/TSX recognition); it is not a
current capability registry. The binary/assembly path, its tested architectures,
and its outstanding limitations are documented in [machine-code.md](machine-code.md).
The current Joern numeric changes and their native-runtime checks are documented
in [typed-numerics.md](typed-numerics.md); the historical measurements below have
not been rerun against whole repositories.

The README claims the CPG is "already a universal AST … *one* semantics and *one*
exporter cover all of them". Until this run, everything measured was Python (`cachetools`)
plus a five-function hand-written C file. This document records what the unmodified
pipeline (`./autoform.sh`) did when pointed at real code in the other languages.

Nothing was tuned. No pipeline file was modified. Figures move with every change to the
pipeline; where a document and an artifact disagree, the artifact wins.

## Corpora

| Language | Corpus | Files | Why |
|---|---|---|---|
| C | `antirez/sds` (`sds.c`, `sds.h`, `sdsalloc.h`) | 3 | real C, string library, heavy pointer use |
| Java | `google/gson` `com/google/gson/internal/**` | 14 | real utility library, generics, inner classes |
| Go | `kelseyhightower/envconfig` (all `.go`) | 7 | small real package incl. tests |
| TypeScript | `sindresorhus/p-queue` `source/*.ts` | 5 | real async library |
| JavaScript | `sindresorhus/p-map` `index.js` | 1 | real library, 285 lines |
| JavaScript (scale) | `lodash/lodash.js` | 1 | 17k lines, 693 functions |
| Kotlin | `Kotlin/kotlinx-datetime` `core/common/src` | 20 | real Kotlin, 7.4k lines |
| Kotlin (toy) | hand-written `gcd`/`addAll` | 1 | control experiment |
| Python (baseline) | `cachetools` | — | the previously measured corpus |

Joern 4.0.606, `joern-cli/frontends/` has `c2cpg`, `javasrc2cpg`, `jimple2cpg`,
`jssrc2cpg`, `gosrc2cpg`, `kotlin2cpg`, `pysrc2cpg`, `ghidra2cpg`, and others.
Binaries (`ghidra2cpg`), C#, PHP, Ruby, Rust and Swift were **not tested**.

## Support matrix

| Language | Parses | Translates | Lean compiles | Dialect inferred | Functions | Hole-free | Verifiable core | Holes / nodes | Differential oracle |
|---|---|---|---|---|---|---|---|---|---|
| Python | yes | yes | yes | `.python` ✅ | 209 | 99% | 107 (51%) | 0.05% | **yes** (CPython) |
| C | yes | yes | yes | `.cLike` ✅ | 59 | 17 (29%) | 8 (13%) | 11% | crashed (see below) |
| Java | yes | yes | yes | `.java` ✅ (`#guard`) | 669 | 350 (52%) | 191 (28%) | 6% | JVM backend present; ran end to end on the in-repo fixture (`tests/test_differential_backends.py`, `AUTOFORM_TEST_ORACLES=1`), **not yet on this corpus** -- its sources are not in the repository |
| Go | yes | yes | yes | `.go` ✅ (`#guard`) | 83 | 21 (25%) | 6 (7%) | 4% | `go test` backend present; ran end to end on the in-repo fixture (`tests/test_differential_backends.py`, `AUTOFORM_TEST_ORACLES=1`), **not yet on this corpus** -- its sources are not in the repository |
| TypeScript | yes | yes | yes | `.javascript` ✅ | 86 | 44 (51%) | 18 (20%) | 4% | Node (`--experimental-strip-types`) backend present; the fixture run covers `.js` only, **not yet run on `.ts` or on this corpus** |
| JavaScript | yes | yes | yes | `.javascript` ✅ | 14 | 5 (35%) | 1 (7%) | 5% | Node backend present; ran end to end on the in-repo fixture (`tests/test_differential_backends.py`, `AUTOFORM_TEST_ORACLES=1`), **not yet on this corpus** -- its sources are not in the repository |
| JavaScript (lodash) | yes | **no** | n/a | `.cLike` ⚠️ | 693 | 419 (60%) | — | 1.8% | Node backend present; nothing to compare until it translates |
| Kotlin (real repo) | **no** | n/a | n/a | n/a | — | — | — | — | **none** |
| Kotlin (toy) | yes | yes | yes | `.java` ⚠️ | 3 | 2 (66%) | 2 (66%) | 4% | **none** |
| `.tsx` / `.jsx` | yes | yes | yes | `.javascript` ✅ (was `.python` ❌, §2) | — | — | — | — | none |

**On the "Differential oracle" column.** `scripts/differential.py` now carries a runtime
backend for Node (JS/TS), the JVM (Java, and Kotlin through a `@JvmStatic` thunk) and Go,
each with its own recorded `measurement_basis` (`node-numeric-pool-v1`,
`jvm-primitive-static-v1`, `go-package-func-v1`) and `runtime_version`, selectable with
`--language`. "Backend present; ran on the fixture" means exactly that: the oracle was
executed end to end -- runtime, `lake build`, Lean evaluation, comparison -- on a
three-function fixture per language and agreed with Core with 0 divergences. It is NOT a
statement about the corpora in this table, whose sources are not in the repository; the
day one is re-exported with `scripts/reland_corpus.sh` its conformance row goes here with
the counts, and until then the column says "not yet on this corpus".

Percentages are from the ledger the pipeline printed (`ledger-Lang*.json`);
`scripts/lang_matrix.py` recomputes them from the exported AST independently and agrees
to within the ledger's slightly different node-counting.

⚠️ = the dialect *is* in `render_lean.py`'s `DIALECT` map, but the language rides another
language's constructor: Kotlin/JVM runs as `.java` (same integer model and boolean
operators; its structural string `==` lands on Java's `str:reference-equality` hole).
✅ (`#guard`) = the language has its own `Dialect` constructor and the numeric claims in
§5 are `#guard`s in `Semantics.lean`/`Numeric.lean`, checked on every build — which is
NOT a differential oracle: the last column is still **none** for both. See below.

### Failures observed, verbatim

* **Kotlin, real repo — does not parse.** `joern-parse` exits `1`:
  `ReachingDefPass failed … java.util.NoSuchElementException: key not found: MethodRef`.
  `autoform.sh` runs under `set -e` with joern's output redirected to `/dev/null`, so the
  run stops after `==> [1/6] parsing` printing **no error at all**. A CPG file is still
  written; running `export_ast.sc` on it crashes with the same exception. A hand-written
  two-function Kotlin file goes end to end, so this is the frontend on real Kotlin, not
  the corpus.
* **JavaScript at scale — does not render.** lodash exports 693 functions (25 MB of AST)
  and then `render_lean.py` dies:
  `RecursionError: maximum recursion depth exceeded while decoding a JSON object`.
  `json.load` in CPython recurses on nesting depth, and jssrc2cpg produces deeply nested
  expression trees. The exporter completes; the renderer is the wall.
  `scripts/lang_matrix.py` raises the limit and walks iteratively, which is how the
  lodash row above was measured.
* **C differential oracle — segfaults.** `python3 scripts/differential.py` on `sds`
  terminated with `Segmentation fault: 11`. The C path `ctypes`-loads the compiled object
  and calls hole-free functions with random *integers*; `sds` functions take `char *`, so
  the harness dereferences small integers as pointers. `autoform.sh` swallows this
  (`|| true`) and continues to the ledger.
* **Java/Go/TS/JS differential oracle — does not exist.** `scripts/differential.py`
  chooses its runtime with one line: `runtime = "cc" if is_c else "cpython"`, where
  `is_c` tests for a `.c`/`.h` suffix. Everything that is not C is handed to CPython,
  which cannot import Java or Go, so the harness reports
  `no comparable cases in this corpus` and the run is scored with **zero** conformance
  evidence. The oracle that found every dialect bug in the project's history is wired for
  two of the seven languages.

## Node kinds the exporter does not map

Holes by cause, per language — CPG vocabulary items that exist but have no Core
translation. They are not the same set across languages, which is direct evidence against
"one node vocabulary".

| Language | Top hole causes |
|---|---|
| C | `op:indirection` 28, `op:cast` 18, `control:SWITCH` 14, `assign:lhs:indirectIndexAccess` 12, `op:indirectIndexAccess` 12, `assign:lhs:indirection` 12, `cstr:address-equality` 11, `op:postIncrement` 11, `op:postDecrement` 8, `control:FOR` 7, `control:GOTO` 5, `op:sizeOf` 5 |
| Java | `op:alloc` 166, `control:THROW` 125, `op:cast` 123, `op:instanceOf` 90, `op:arrayInitializer` 43, `control:FOR` 30, `expr:BLOCK-impure` 20, `control:SWITCH` 15, `op:postIncrement` 15, `op:sizeOf` 13, `control:TRY-multiCatch` 4 |
| Go | `op:addressOf` 44, `stmt:IMPORT` 39, `lit:unquoted` 17, `stmt:TYPE_DECL` 13, `op:indirection` 12, `assign:arity` 7 (multi-return `a, b := f()`), `control:FOR` 6 |
| TypeScript | `op:assignment` 26, `op:notNullAssert` 11, `control:THROW` 10, `stmt:TYPE_DECL` 9, `op:alloc` 7, `op:await` 7, `op:instanceOf` 5, `op:spread` 2 |
| JavaScript (lodash) | `op:assignment` 111, `op:instanceOf` 100, `op:preIncrement` 91, `expr:BLOCK-impure` 44, `op:postIncrement` 44, `op:alloc` 27, `op:and` 23, `control:THROW` 16, `op:iterator` 6 |
| Kotlin (toy) | `stmt:METHOD` 2 |

Language-specific constructs that hole *everywhere they appear*: Go's `:=` multi-return
(`assign:arity`), Go pointers (`op:addressOf`, `op:indirection`), Java `instanceof` and
casts, TypeScript's `!` non-null assertion and `await`, JS iterators and spread, C's
`goto` and pointer indirection. `control:FOR` is a hole in **every** C-family language —
Joern models the C-style three-clause `for` differently from Python's `for … in`, and the
exporter only handles the latter (plus `while`). That costs a large fraction of the
coverage in C, Java and Go.

`op:alloc` (166 holes in Java) covers constructor calls, i.e. essentially all idiomatic
Java object creation, which is untranslated.

## Silent mistranslations found

These are the §12 failure mode: a construct that looks the same across languages and means
something different, producing a **wrong answer rather than a hole**. Each was measured —
Lean output from the generated module, real output from the real runtime.

### 1. `and` / `or` return an operand, not a boolean (Python, JS, TS) — NEW, and it hits the flagship corpus

`Semantics.applyBinop` returns `.val (.bool (x.truthy && y.truthy))`, and the
short-circuit path in `evalExpr` returns `.bool false` / `.bool true`. In C, Java and Go
that is correct. In Python and JavaScript `a || b` evaluates to **`b` itself**, and
`a && b` to an operand — the default-value idiom.

| input | real runtime | Core |
|---|---|---|
| JS `pick(a,b){return a\|\|b}` at `(0, 5)` | `5` | `Val.bool true` |
| JS `both(a,b){return a&&b}` at `(2, 3)` | `3` | `Val.bool true` |
| Python `def pick(a,b): return a or b` at `(0, 5)` | `5` | `Val.bool true` |
| Python `def both(a,b): return a and b` at `(2, 3)` | `3` | `Val.bool true` |

This is wrong for the language the project has measured most. It survived because
`cachetools` only uses `and`/`or` in conditions (7 `&&`, 1 `||`), where truthiness is all
that is observed; lodash uses 355 `&&` and 196 `||`, mostly as values. Verdict: **wrong**,
not a hole.

### 2. `.tsx` / `.jsx` sources got the **Python** dialect — FIXED; the record stands

**Fixed.** `render_lean.py`'s `DIALECT` table now maps `.js .ts .tsx .jsx .mjs .cjs` to
`.javascript` and `.cc .cxx .hh .hpp` to `.cLike`, and an extension it does not know is a
**refusal** (`infer_dialect` raises), not a Python default.
`tests/test_render_lean.py` (`test_dialect_inference`, `test_unknown_extension_is_refused_not_defaulted`) pins the table
entry by entry and the refusal. The measurement below is kept as the record of what the
bug looked like. Still open for JavaScript: `await` (a suspended frame Core has no
representation for) stays a counted `op:await` hole; `throw`, single-`catch (e)`,
`void`, TS `x!` and object-literal properties (`{a: 1}.a`, `o.b = 2`) lower under the
`.javascript` dialect (`jsLikeFile` in the exporter, `jsContainerField` in
`Semantics.lean`).


`render_lean.py`'s `DIALECT` map keys off the file extension and lists
`.py .c .h .cpp .java .js .ts .kt .go`. Anything else casts no vote, and `infer_dialect`
returns `".python"` when there are no votes. A React/TypeScript project (`.tsx`), a
`.jsx` project, `.mjs`/`.cjs`, `.cc`/`.cxx`/`.hpp` C++, C#, Ruby, PHP, Rust, Swift — all
silently receive **floored division, Python remainder, and unbounded integers**.

Measured on a two-function `C.tsx` put through the unmodified pipeline; the generated
module says `Source dialect: .python`:

| input | TypeScript | Core |
|---|---|---|
| `md(-7, 3)` (`a % b`) | `-1` | **`2`** |
| `half(-7, 2)` (`a / b`) | `-3.5` | **`-4`** |

This is the `fmod(6, -9)` bug the README records catching, re-entering through the
extension table. Verdict: **wrong**. The default should be a refusal, not Python.

### 3. JavaScript numbers are IEEE doubles; Core gives them 32-bit C integers

`.js`/`.ts` → `.cLike` → `NumConfig.c32Wrapv`. JavaScript has no integers at all.

| input | Node | Core |
|---|---|---|
| `2147483647 + 1` | `2147483648` | **`-2147483648`** |
| `7 / 2` | `3.5` | **`3`** |
| `5 / 0` | `Infinity` | **raises `ZeroDivisionError`** |
| `-7 % 3` | `-1` | `-1` ✅ (truncated remainder happens to match) |

Three wrong answers, one accidental agreement. Verdict: **wrong**.

### 4. JavaScript `==` and `===` are the *same* Core operator

Both compile to `<operator>.equals` in jssrc2cpg and to Core `binop "=="`, evaluated by
`Val.beq` (structural). Verified by exporting a file containing both: identical Lean.

| input | Node | Core |
|---|---|---|
| `1 == "1"` | `true` | **`false`** |
| `0 == false` | `true` | **`false`** |
| `1 === "1"` | `false` | `false` ✅ |

`===` agrees by coincidence and `==` is wrong; Core cannot tell them apart even in
principle, because the distinction is erased before Core sees it. Verdict: **wrong**, and
not fixable inside the semantics; it needs an exporter change.

### 5. Java `long` and Go `int` are 64-bit; Core modelled them as 32-bit — FIXED for Go, named for Java

**Now:** `Dialect.java` and `Dialect.go` are constructors (`Syntax.lean`), and
`Dialect.toNumConfig` sends the **untagged** path to `NumConfig.java32` (Java `int`:
32-bit, wraps, masked shifts) and `NumConfig.go64` (Go `int`: 64-bit, wraps, zero-divide
panics). The Go rows in the table below are therefore right today, by `#guard` in
`Numeric.lean` (`Dialect.go.toNumConfig.add 9223372036854775807 1 == .ok
(-9223372036854775808)`). The Java rows are about `long`, and `long` is NOT what the
untagged path models: an untagged Java operation is `int`, so `long a = 2147483647L; a+1`
still reads `-2147483648` **when the exporter could not type it**. That is a named width
choice — one width per language on the fallback — not a claim; the fix for `long` is the
tag. `Lang.numConfig` now agrees with the evaluator for every language but C
(`Lang.numConfig_agrees_with_dialect`, the C exception being standard-vs-compiler).

**Before (retained as the record):** `.java`/`.go` → `.cLike` → `c32Wrapv` on the
untagged path. `Numeric.lean` defined `java32`, `java64` and `go64`, and `Dialect` had no
`.java`/`.go` constructor to select them (its three were `python`, `cLike`, `javascript`).

These configs are no longer dead code: the exporter now tags each operation with its
resolved operand type (`num:java:i64:+`), and `TypedNumeric.parse` turns that tag into a
width-correct config, so a *tagged* Java `long` really is 64-bit and division by zero
raises `ArithmeticException` rather than holing. The row below is therefore the
behaviour of the **untagged fallback**, which is what an operation gets when the
exporter could not resolve its operand type. Untypable operations are emitted as
`numeric:unknown-type:<op>` holes rather than guessed — on a live Apache Spark export
that was 66 holes out of 5099.

`Lang.numConfig` (`Numeric.lean`) maps `.java` to `java64`, which contradicts the
untagged path; it has no callers and is marked non-normative in its docstring.

| input | real runtime | Core, untagged, before | Core, untagged, now |
|---|---|---|---|
| Java `long a=2147483647L; a+1` | `2147483648` | **`-2147483648`** | **`-2147483648`** (`int` width; `long` needs the `num:java:i64` tag) |
| Java `long m=100000L; m*m` | `10000000000` | **`1410065408`** | **`1410065408`** (same) |
| Go `a:=2147483647; a+1` | `2147483648` | **`-2147483648`** | `2147483648` ✅ `#guard` |
| Go `m:=100000; m*m` | `10000000000` | **`1410065408`** | `10000000000` ✅ (`go64`) |

This is the *same* mistranslation §16 records finding for C (`mulbig(100000,100000)`
giving `1410065408` against `cc`) — except here `1410065408` is the wrong one, because
Java `long` and Go `int` are 64-bit. Core has no types, so on the untagged path it cannot
distinguish Java `int` from Java `long`; whichever width it picks is wrong for the other,
and `.java` picks `int`. Verdict: Go **fixed** (`#guard`, no oracle yet); Java **named**
— right for `int`, wrong for an untyped `long`, exact for a tagged one.

### 6. Java string `+`, `==`: right answer, wrong reason — FIXED

**Now:** under `.java`, `Dialect.stringsAreValues` is `true`, so `"a" + "b"` is `"ab"`
and `<`/`>` compare contents; `==`/`!=` on two strings is the hole
`str:reference-equality` via the new predicate `Dialect.stringEqIsReference` — Java
compares references there, and Core's single `Val.str` cannot say whether two equal
contents are one object. Under `.go`, `==` compares contents. All three are `#guard`s in
`Semantics.lean`. JavaScript/TypeScript were fixed earlier by `.javascript`.

**Before (retained as the record):** under `.cLike`, `applyBinop` made `"a" + "b"` a hole
labelled `str:pointer-arithmetic-not-modelled`, and `s == t` a hole labelled
`str:pointer-equality-not-modelled`. For C those labels are correct. For Java:

* `s == t` is reference equality, so holing is conservative and defensible — though the
  label says "pointer", which is the right idea by accident.
* `s + t` is concatenation and is ordinary Java. Holing it is a coverage loss, not a wrong
  answer.
* The same rules are applied to JavaScript and TypeScript, where `+` on strings is
  concatenation and `==`/`===` on strings compare *contents*. Measured: JS `"a"+"b"` →
  `hole "str:pointer-arithmetic-not-modelled"` instead of `"ab"`; JS `1 + "1"` →
  `hole "binop:+"` instead of `"11"`.

Verdict then: **hole** (safe) but wrong for three of the four `.cLike` languages — the
inverse of the C case, and the evidence that `.cLike` was not one dialect. Verdict now:
Java and Go have their own; C is the only `.cLike` language left among those measured
(Kotlin rides `.java`).

### 7. Division by zero and shifts: holes and near-misses (checked, not wrong)

* Java `5 / 0` → Core `exn (.str "ZeroDivisionError")`. Java throws
  `ArithmeticException: / by zero`. The *shape* is right (an exception) but the identity
  is wrong; Core has no exception types, so a `catch (ArithmeticException e)` cannot be
  matched. Not a wrong value, not a faithful one.
* Go `5 / 0` → same `ZeroDivisionError`. Go *panics*, which is not a catchable exception
  in the same sense (`recover` only in a deferred call). Approximate.
* `Integer.MIN_VALUE / -1` → Core `-2147483648`. Java agrees. **Correct** ✅ (measured).
* Java `a << 32` and `a >>> k` → holes (`op:shiftLeft`, `op:arithmeticShiftRight` are not
  in the exporter's operator map). Java masks the shift count to 5 bits and `>>>` is a
  logical shift; `NumConfig.java32` models both correctly but is unreachable. As shipped
  these are holes, which is safe. **hole**.
* Go integer overflow is *defined* to wrap; Core wraps, but at the wrong width (item 5).
* JS `<<` coerces to int32 first; Core holes it. **hole**.

### 8. A call on a static field loses the method name — the AST is *wrong*, not merely incomplete

Measured on a live Apache Spark export. `common/unsafe/.../Platform.java:198` reads:

```java
public static long allocateMemory(long size) {
  return _UNSAFE.allocateMemory(size);
}
```

`_UNSAFE` is a `private static final Unsafe` field. The exported AST is:

```json
{"k":"mcall","recv":{"k":"fnref","v":"org.apache.spark.unsafe.Platform"},
 "m":"_UNSAFE","args":[{"k":"name","v":"size"}]}
```

The receiver is the *class*, the method slot holds the *field* name, and the method
actually being called — `allocateMemory` — is gone. Joern gives the call a field-access
callee (`Platform._UNSAFE`) whose name the exporter takes as the method
(`cartographer/export_ast.sc`, the `callee.flatMap(asField)` branch of the `mcall`
lowering); for Python `obj.method(x)` the field name and the call name coincide, which
is why the shape survived. When they differ — a method invoked on a field — the call
name is the one that matters and it is discarded.

This is a different and worse category than the rest of this file: every other entry is
a hole or a documented approximation, whereas here the AST **states something false**
about the program. It is currently masked, because `Semantics.lean` cannot find a class
method named `_UNSAFE` and emits `mcall:Platform._UNSAFE:not-a-class-method`, so the
wrong name fails closed rather than calling the wrong thing. It would stop being masked
the moment a class did define a member with the field's name.

Blast radius on Spark: **183 of 5020 hole-free functions** perform an `mcall` on an
`fnref`. Related and separate: **280** read a static field (`field` over `fnref`), which
holes as `field:<name>:non-object` because Java static initializers (`static { }`
blocks, static field initializers) are never exported — `render_lean.py` builds
`moduleInits` only from `:<module>`/`:<global>` suffixes, the Python and C conventions,
and a Spark export contains zero of either and zero `<clinit>`.

Not fixed here: correcting the lowering changes every Java AST, and the ASTs are the
tracked source of truth that renders, recorded hashes and generated specs are all
pinned to, so it needs a re-export and re-record of the Java corpora together with the
change. Recorded as a known defect rather than silently carried.

### 9. Predicted, unverified

* Java boxed `Integer` comparison: `Integer a=1000, b=1000; a==b` is `false` in Java
  (reference equality) but Core's `Val.beq` on two `.int`s gives `true`. Core has no
  boxing, so this is a wrong answer waiting for a corpus that boxes. Not measured because
  `op:alloc` holes most boxing paths first.
* Java `char` arithmetic (16-bit unsigned) under a 32-bit signed config.
* Go `&^` (and-not) and unsigned `uint` arithmetic under a signed config.

### 10. Python attribute and exception semantics

Five findings from the production-readiness pass (STRATEGY.md §57), consolidated because
they are one story: Core represents an exception as the *name* of its class and an object
as a bag of fields, and every item below is a place where Python's attribute or exception
model is richer than that. Each "done" names the `#guard`, theorem or test that makes it
so; `tests/test_documentation_claims.py` checks those names still exist.

#### 10.1 `except` dispatch holes on an exception it cannot name — and every producer is pinned

`cartographer/export_ast.sc` lowers `try`/`except` into a dispatch that compares the
pending exception against `Stdlib.excNames` **as a string**, and holes
(`control:TRY-exception-representation`) when it is not one of them. On a fresh
`cachetools` export that is the largest remaining Python hole class (34 at last count —
up from 29, because whole-function holes stopped masking it).

The guard looked redundant — "obviously every exception Core makes is one of those
names" — and checking that claim found it false in one place (10.2). Every producer of an
exception value in Core is now a theorem rather than an assumption:

* `makeException_excSafe` (`Stdlib.lean`) — holes on any name outside `excNames`, and
  otherwise yields that name, or a `TypeError` from argument validation;
* `raiseValue_excSafe` (`Stdlib.lean`) — raising a string is a `TypeError` as in CPython,
  an object holes, a builtin class reference routes through `makeException`;
* `python_shiftCount_trap` (`Numeric.lean`) — the one exit that was not safe; see 10.2.

`test_every_exception_producer_in_core_is_pinned_by_a_theorem` asserts all three exist and
that `ExcSafe` is stated over `excNames` itself, not a restatement that could drift from
the list the exporter's dispatch actually compares to.

**The guard is gone.** What blocked removing it was `Stmt.raise`: `execStmt` raised its
operand's evaluated value directly, so nothing in the semantics prevented an arbitrary
`Val` from becoming an exception, and the exporter's guard stood in for the missing
proof. Two changes close that:

* `Stmt.raise` under `.python` now classifies its operand through `pythonRaise`
  (`Semantics.lean`). A value that already IS an exception in Core's encoding — a `.str`
  naming a represented class, which is what the `py:exception:<Name>` constructor
  produces and what a re-raised caught exception holds — is raised as-is. Anything else
  goes through `Stdlib.raiseValue`: a class reference instantiates, a non-exception string
  is a `TypeError` as in CPython, an object holes. Other dialects are untouched; Java and
  C++ throw arbitrary objects and Core has no representation to check them against.
* Typed numeric operators (`num:<family>:...`) are refused under `.python`
  (`numeric:typed-op-in-python`). Their traps name themselves in the family's own terms
  — `panic:negative shift amount`, `ArithmeticException` — which are not Python classes,
  and the exporter never emits one for a Python file anyway. The JavaScript operators
  (`js:+` … `js:%`) are gated the same way, on `.javascript`: outside it they could only
  reach the typed fallthrough, and no source program of another language spells them.

With those, `Autoform/Lang/Core/ExcSafe.lean` states the invariant the guard was
checking and proves it by simultaneous induction over the interpreter's eight mutually
recursive functions, the same shape as `FuelMono.lean`: `evalExpr_exn_excSafe` and
`execStmt_exn_excSafe` say that under `.python`, every `.exn v` the interpreter produces
has `v` a represented class name. The leaves are `makeException_excSafe`,
`raiseValue_excSafe`, `pythonRaise_excSafe`, `python_shiftCount_trap`, per-operator
lemmas showing the unbounded Python `NumConfig` never traps except on a shift count,
the `Float.lean` lemmas pinning float arithmetic to `ZeroDivisionError`/`OverflowError`
(`div_exn`, `fmod_exn`, `pyMod_exn`, `ofInt_exn`), and `Stdlib`'s scans of the builtin
and container-method tables (`builtin_excSafe`, `method_pure_excSafe`,
`method_mutating_not_exn`).

`cartographer/export_ast.sc`'s typed-handler dispatch is now `ifte (pending ∈ accepted)
selected rest` with no outer guard: the 29–34 `control:TRY-exception-representation` holes
on a cachetools export come off, and what stands behind that is a theorem rather than a
belief that every exception is obviously a name.

#### 10.2 A Python trap named itself in prose

`numToE` turns a numeric trap into `.exn (.str r)`, and `r` is read downstream as the
exception's class name. `NumConfig.python` traps on shift count and the trap carried
`"negative shift count"`:

| | `1 << -1` |
|---|---|
| CPython | `ValueError: negative shift count` |
| Core, before | `.exn (.str "negative shift count")` |
| Core, now | `.exn (.str "ValueError")` |

So `except ValueError:` around a negative shift silently stopped catching. The dialect
table at the top of `Numeric.lean` said `ValueError` the whole time; the implementation
did not deliver it, and nothing compared the two. **Done**: `NumConfig.shiftCountFault :
Option String`, `none` by default so no other dialect changes and C's negative shift stays
UB. `python_shiftCount_trap` is the theorem; `test_python_negative_shift_raises_valueerror_by_name`
guards the config.

#### 10.3 `nonlocal` — an exporter gap, not a semantics gap, and now closed

`scope:nonlocal-write` holed every `nonlocal` write; on cachetools all 8 were the
`hits += 1` counters in `_cached.py`. The exporter comment said `Expr.closure` captures
by value, so a write cannot reach the frame owning the variable, and an `assign` would be
silently wrong. Right about `assign`, wrong about Core: capturing a `Val.ref` by value
still shares the object behind it, which is precisely a closure cell. `Semantics.lean`
carries the worked program as a `#guard_msgs` (`cellProg`: two calls through a closure,
owning frame observes both writes, `2`), checked on every build.

**Done.** The exporter boxes the name in the scope that defines it and lets the closure
share the cell, reusing `boxedLocals`, the machinery that existed for C address-taken
locals. Two sets per function: the enclosing scope's names get the box and the allocation
prologue; the closure's (`capturedBoxes`) get the same `field`/`setField` treatment and
explicitly **no** prologue — allocating there would rebind the name to a fresh box and
destroy the alias.

The safety condition is the whole content, and it is checked rather than assumed: the box
must exist when the closure captures it, so the enclosing function must bind the name by
a plain assignment at the top level of its body **before the first nested `def`**. A
binding inside an `if`, or after the `def`, does not dominate the capture; the parent
leaves the name a plain value, and telling the closure it is boxed would read a field off
an integer. Those keep the hole, as do chains deeper than one level. End to end:
`counter()` with a `nonlocal hits` increment called twice returns `2`, as in CPython; the
`if`-bound variant still holes. `TestNonlocalBoxing` pins both directions.

Two bugs recorded because they were silent. The first draft translated the unsafe case,
because the child's set came from its declaration alone instead of being intersected with
what the parent actually boxed. And `globalDeclNames` strips the literal prefix
`global`, so on `nonlocal x` it returned the name `"nonlocal x"`; the membership test
failed and the hole stayed — harmless that time, one edit from wrong. It has its own
parser, `nonlocalDeclNames`.

#### 10.4 A `@property` read was a silent wrong answer; it is a hole, and the general case is priced

`c.currsize` calls a getter in Python. Core has no descriptor protocol, so the exporter
lowered it to a field read — and `Cache.__init__` stores the name-mangled
`_Cache__currsize`, so a field called `currsize` does not exist. `evalExpr` answers a
missing field on an ordinary object with `unit`, **silently**, with no hole:

| | `c.currsize` |
|---|---|
| CPython | `1` |
| Core | `unit` |

Both by execution. This is the failure class the whole project is organised against —
well-typed, hole-free, and wrong — and it was inside the tracked corpus, where
`make_info` reads `cache.currsize` and `cache.maxsize` and the ledger counted those
functions as translated.

**Done, in the conservative direction**: the exporter holes any attribute read whose name
is a `@property` anywhere in the same file (`call:python-property-access`). By name rather
than by receiver type, because Python attribute access is not statically resolvable in
general and over-holing is the safe side. On cachetools this *raised* the hole count, 108
to 126 across 18 sites — the coverage was never real. `TestPropertyAccessHoles` asserts
**both** lowering paths refuse it: patching `callExpr` alone changed nothing, because a
plain `return c.prop` goes through `exprV`.

**The tracked corpus still has the defect.** `ast-Cachetools.json` predates the change, so
its `make_info` still computes with `unit`. One more reason a tracked AST is evidence
about the exporter that produced it (`docs/integrity.md`).

*The general case was priced here and is now done — see §16.A.* A missing attribute on
an ordinary object raises `AttributeError` under `.python` once class metadata makes
the hierarchy complete, as the Language Reference specifies (§3.2.11, §3.3.2), and is
a named gap on a legacy model, instead of answering `unit`. What the pricing predicted was
right in shape and wrong in size: the accessor lemma `applyFunc_ret_field_self` in
`SpecsGen/Basis.lean` did have to be restricted, but to a receiver that HAS the field
(`hfld`), which made its `@property` and class-attribute premises unnecessary rather than
adding to them, and no generated spec broke because a hit is found before any of those
arms. The oracle, not a refactor, settled which answer is right: click 8.2.1 diverged from
CPython three times on exactly this (§10.9).

#### 10.5 Property dispatch: implemented, proved fuel-monotone, blocked on provability

Making `c.prop` *run* its getter — what Python does — was built end to end, twice, and
reverted both times. The semantics were never the hard part.

**What worked.** On a field miss, `evalExpr` resolves the getter and applies it to the
receiver. `FuelMono`'s `.field` case, previously `exact hy` because the case was
fuel-free, extended to the explicit nested proof a recursive branch needs, and goes
through.

**Design one: a `Ctx.properties` field.** 289 broken declarations — every `Ctx` literal in
`Contracts.lean` disagreed with `ctxOf` and `runFunc` about a field it did not mention.
Not a semantics problem; a handful of construction sites that stopped agreeing.

**Design two: a marker name in the existing table**, `<property>currsize`, which no source
language can spell. No new field anywhere, every `Ctx` term byte-identical, and the same
dialect gate that turned the switchover's 163 into 3 collapses all 120 `V8Base` accessor
uses, leaving three in `Cachetools`. Those three **cannot discharge their side
condition**. It is `ctx.resolve (propertyGetter fld) = none` — a proof that a name is
*absent* from the table — and `Ctx.resolve` suffix-matches with `String` operations the
kernel will not reduce cheaply. `rfl` fails at 209 entries; so does `simp` with
`Ctx.resolve`, `Ctx.resolve.go` and the table unfolded. Finding a name is cheap because it
short-circuits; proving one is not there is a full scan.

So the recommendation is design one after all. Absence is then `[] = []`, decidable with
no `String` reduction, and the 289 are the cost of aligning `ctxOf`, `runFunc` and the
`Ctx` literals in `Contracts.lean` on one more defaulted field — a job of the same shape as
`builtinBases`, which already threads through exactly those sites. The lesson is the one
this file keeps recording in other forms: a design that is cheaper to *write* can be far
more expensive to *prove*, and which one matters is not visible until the proof is
attempted.

#### 10.6 Comprehensions, generator expressions and `with`

**Comprehensions lower.** pysrc2cpg spells `[e for x in xs if p]` as a block of three
statements — `tmp0 = []`, the ordinary `for` lowering with the body `if p: tmp0.append(e)`,
and a read of `tmp0` — and every piece of that is a Core construct already: under `.python`
the list literal allocates, `append` writes through the payload, `forIn`/`ifte` are the
loop. The exporter's `comprehensionLowering` recognises exactly that shape (one assignment
to a temporary from an empty `listLiteral`/`dictLiteral`/`setLiteral`/`genExp`, one loop,
one read of the same temporary) and emits it as a prelude plus a read. A dict
comprehension is the same with `tmp0[k] = v`; a set comprehension stays `expr:setComp`,
because Core has no set value.

**The loop variable does not leak.** Python 3 gives a comprehension its own scope —
`x = 1; ys = [x for x in xs]; x` is still `1` — while Core's `forIn` binds into the
enclosing environment. Left alone, a later read of `x` would have seen the last element:
a silent wrong answer, the kind this document exists to catch. Every `forIn` the lowering
produces is therefore rebound to `$comp$x`, a name no source language can spell, and its
body renamed to match; the names the frontend binds *from* the loop variable (the
destructuring `k = tmp[0]; v = tmp[1]` of `for k, v in pairs`) follow it. The first
loop's iterable is left alone, because Python evaluates it in the enclosing scope.
`compNoLeak` in `tests/test_source_numeric.py` reads the outer `x` afterwards and is
compared against CPython.

**Generator expressions retain their suspension.** The exporter records a `genExpr`
node with lexical-scope metadata; the renderer compiles it to an auxiliary generator
factory. The first iterable and its iterator are prepared at creation. Resumption uses
that same iterator without repeating `__iter__`, and evaluates the body and subsequent
clauses lazily. The factory does not add a source function to the coverage denominator;
the body remains in its owner's `analysisBody`.

The old consumer-name shortcut has been removed. Core drives `list`, `tuple`, integer
`sum`, `any` and `all` through ordinary iteration when given generator objects. Truth
tests and accumulation happen between yielded items, and `any`/`all` stop when their
answer is known. `len(generator)` raises `TypeError`. Custom length hints, non-integer
accumulation, and captured free-variable cells remain explicit gaps. Other consumers
retain their existing runtime gaps; a matching callee name never makes evaluation
eager. Historical ASTs containing eager list lowering require a full source re-export.
The source and kernel regressions are `tests/test_source_generator_expressions.py`.

**`with` was already translating; the approximation is now named.** The frontend lowers
`with cm as x: body` to `__enter__`/`try`–`finally`/`__exit__()` itself, and the exporter
rejoins the bound-method temporaries into `mcall`s (`boundMethodCall`), so the 49
`tryFinally` bodies in the cachetools render include every `with self.__timer`. What is
approximate is the finaliser: Python passes `(type, value, traceback)` to `__exit__` and
lets a truthy return SUPPRESS the exception; the lowered call passes nothing and never
suppresses. For a context manager whose `__exit__` ignores its arguments and returns a
falsy value — every one in cachetools — this is exact. A suppressing `__exit__` would
observe the difference; it is recorded here as `control:WITH-exit-args` and is the next
thing to close if a corpus has one.

#### 10.7 The container protocol on user instances (`__contains__`, `__getitem__`, `__setitem__`, `__delitem__`)

`key in self`, `self[key]`, `self[key] = v` and `del self[key]` on an ordinary instance
are method calls in Python, and Core answered them structurally: an instance is not a
list, so `Cache.get`'s `if key in self` was the dynamic hole `in:non-container` and the
function INCONCLUSIVE against CPython. **Done** for the four container dunders:
`Ctx.dunderOn` (`Semantics.lean`) answers `some (r, fn)` exactly when the receiver is a
reference to an ordinary instance — payload `.none`, so boxed containers keep their path
— whose class *defines* the method (`classDefines`, not `resolveMethod` alone: a free
function called `__getitem__` is not the class's), under `.python`; `evalExpr`/`execStmt`
then call it with the receiver bound, and `not in` negates the result's truthiness as
CPython does. A class without the method keeps the hole it had — nothing is guessed.

Checked: `dunderProg` in `Semantics.lean` (eleven `#guard`s: hit/miss/`not in`,
`__getitem__` doubling, `__setitem__` and `__delitem__` writing the instance, the four
`Plain` holes unchanged, `in` on a boxed list still structural). `FuelMono` gained the
four recursive branches (`Ctx.dunderOn_resolves` connects a dispatched method to the
`resolveMethod` hypothesis the transport is stated over) and `ExcSafe` closes them with
the existing `ihF` closers. `tests/test_production_gaps.py::TestDunderDispatch` pins the
text. Not yet: `__eq__`/`__lt__`/`__len__`/`__iter__`/`__bool__`/`__hash__`/`__str__`
(Milestone 1's remaining protocols, `docs/GOAL-arbitrary-codebases.md`).

#### 10.8 Value dunders: `==`, `<`, `len()`, `bool()` on an instance run the class's method

A Python class redefines what a *value* means for its instances: `a == b` is
`a.__eq__(b)`, `a < b` is `a.__lt__(b)`, `len(a)` is `a.__len__()`, `bool(a)` is
`a.__bool__()` or, failing that, `a.__len__() != 0`; `hash`, `str`, `repr` likewise. Core
answered all of these structurally — identity for `==` (`Val.eqPy`), a hole for `<`
(`binop:<`), a hole for `len` (`call:len`). For a class that defines the dunder that is a
**silent wrong answer**, the §12 kind: `_HashedTuple.__eq__`, `TLRUCache._Item.__lt__`
(the heap ordering `cachetools` sorts expiries by) were compared as objects.

**Done.** `cmpDunderTarget` / `builtinDunderTarget` (`Semantics.lean`) decide whether a
dunder applies — `.python` only, receiver an ordinary instance (no container payload, not a
module frame) whose class **defines** the method itself (`Ctx.classDefines`, so a free
function named `__eq__` is not mistaken for every class's method) — and the interpreter
makes the call through `applyFunc`, so fuel monotonicity (`FuelMono.lean`, two new
non-tail `applyFunc` sites) and exception safety (`ExcSafe.lean`,
`builtinDunderResult_excSafe`) go through the ordinary induction. `!=` uses `__ne__` when
defined and otherwise negates `__eq__`, as CPython's default `__ne__` does. The answer of
`len`/`hash`/`str`/`repr`/`bool` is type-checked as CPython does (`__len__` must return a
non-negative `int`, …), raising `TypeError`/`ValueError` by name.

The order operators join `==`/`!=` in `binopNeedsHeap`, so a comparison whose left
operand is a reference goes through the heap; a scalar comparison never does, and
`Refine.lean`'s `evalExpr_binop_val` is untouched. The cost is honest and stated: the
**pure fragment** (`PureE`) now excludes comparisons syntactically (`isCmpOp op = false`),
because a comparison can call — `evalExpr_pure_fuel_indep` and
`evalExpr_pure_heap_inert` would otherwise be false.

Checked against CPython 3.11 by twelve `#guard`s over `dunderProg`: `P(1) == P(1)` is
`True` through `__eq__` where identity said `False`; `P(1) != P(1)` is `False`; `P(1) <
P(2)`; `len(C())` is 3; `bool(C())`/`bool(Z())` through `__len__`; `hash`/`str`; and the
two negatives — a class without `__eq__` keeps identity, and `>=` on a class without
`__ge__` stays the hole it was rather than a guess. `tests/test_production_gaps.py::
TestValueDunders` pins the shape.

**Not done, and named.** Only the LEFT operand dispatches: CPython's reflected fallback
(`b.__gt__(a)` when `a.__lt__(b)` returns `NotImplemented`) is not modelled, and
`NotImplemented` has no value in Core. Stateful iteration is described in §16.F;
`in`, `[]`, `[]=` and `del []` are the container half of the protocol.

### 15. Three small exporter labels, dispositioned

* **`op:delete-index` — closed for Python.** `del xs[i]` / `del d[k]` lower to
  `Stmt.delIndex` now that containers box (see `docs/boxed-containers.md` for why it was
  held back). C aggregates keep the hole: no identity to delete from.
* **`op:stringExpressionList` — safe subset.** `"a" "b"`, Python's implicit concatenation
  of adjacent literals, folds to one `.str` when every part is a plain string literal. An
  f-string arrives through the same operator with interpolated parts, and folding it would
  need `str()` conversion semantics per part; it keeps a hole, now labelled
  `op:stringExpressionList:non-literal-part` so the count says which shape it was.
* **`call:computed-callee` — closed.** This is `f(x)(y)`: the callee is itself the
  result of a call. `Expr.call` is by NAME; `Expr.callValue : Expr → List Expr → Expr`
  (`Syntax.lean`) applies what the callee EVALUATES to -- a `.fn` (with the same
  unbound-method and `@classmethod` rules as a name bound to one), a `.clos` with its
  captures, a boxed function object -- and holes `call:value:not-callable` on anything
  else, so `5(1)` is a named hole where CPython raises `TypeError`. `#guard`s in
  `Semantics.lean` (`valueCallProg`) pin `mk(10)(2)` and `d["k"](3)` to CPython's
  answers; `FuelMono` and `ExcSafe` cover the new clause. The exporter emits it only when
  the callee node is itself a `Call`; an unnamed callee of any other shape stays
  `call:no-callee-name`. Emitting `call ""` was tried once and was worse than the hole --
  it typechecked, counted as translated, and resolved to nothing at run time.
* **`mcall:<m>:unboxed-container` — documented, not closed.** After the switchover the one
  remaining source of an unboxed `Val.dict` in a Python program is `bindParams` itself:
  `**kwargs` is built as a value at the kwarg binding in `Semantics.lean`, not allocated.
  A mutating method on `kwargs` (`kwargs.pop(...)`) therefore still holes. Making
  `bindParams` allocate would give it a heap argument -- the `applyBinop` re-typing
  problem -- so it is recorded here rather than done.

#### 10.9 What the oracle found on `click` 8.2.1 (2026-09-21)

The first scale corpus run with the differential oracle after the object-protocol work:
**189/196 agree, 7 divergences, 404 inconclusive**
(`.autoform-work/reland/Click/conformance.json`; reproduce with
`scripts/differential.py ast-Click.json <click-src-root> Click 5`). The seven are three
distinct gaps, none of them oracle noise:

1. **A missing instance attribute answers `unit`; CPython raises `AttributeError`**
   (`ShellComplete.source_vars`, 3 cases). This is §13's documented choice — a `.field`
   miss after the instance, its captures, its properties and its class attributes is
   `Val.unit` — and the oracle now prices it: it is a silent wrong answer on any code
   that relies on the exception. Closing it means the final arm of the `.field` chain
   raising `AttributeError` (represented in `excNames`; `ExcSafe` extends) and the
   accessor lemmas in `SpecsGen/Basis.lean` carrying "the field exists" as a premise
   instead of returning `unit` on a miss.
2. **A callable held in an instance field is not callable through the attribute**
   (`FuncParamType.convert`: `self.func(value)`, 3 cases). `Expr.mcall` on a `ref`
   dispatches by CLASS method; when the class has no such method but the instance has a
   field of that name holding a function or closure, Python calls the field. Closing it is
   one more arm in `.mcall`'s `ref` case, routed through the value-call machinery
   `Expr.callValue` already has.
3. **A module-level variable read through a global returns `unit`**
   (`get_completion_class`: `_available_shells.get(shell)`, 1 case) — the same family as
   the `import:member-not-found` label that dominates `requests` (66 of 148 holes): a
   module object carries functions and classes but not its module-level VARIABLES, so a
   dict built at import time is invisible. This is the largest single lever left on the
   scale corpora and needs module objects to carry their globals frame.

Until (1)–(3) land, `scripts/synth_specs.py --conformance-only` refuses the click
observations (it will not state a conformance theorem next to a recorded divergence), so
`SpecsGen/Click` does not exist yet; that is the gate working as designed.

## Verdict

**"Universal" is aspirational, not currently true.** Precisely:

1. **The front end generalizes.** Five languages parsed, exported and type-checked without
   a change to the exporter or the semantics, and Java — the biggest corpus at 669
   functions — produced the highest hole-free rate of any language measured, 52%. One node
   vocabulary absorbed four new frontends.
2. **The back end does not.** There are two dialects for six languages. `.cLike` means
   "32-bit truncating C" and is applied unchanged to Java `long`, Go `int64`, and
   JavaScript doubles. Every arithmetic answer Core gives for Java `long`, Go `int` or
   any JS number of magnitude ≥ 2³¹ is wrong, silently, with no hole. `Numeric.lean`
   already contains the right configs; `Dialect` has no constructors to reach them.
3. **The safety net is Python-only.** The differential oracle — the mechanism that found
   every dialect bug the project documents — runs CPython or `cc` and nothing else. For
   Java, Go, JS, TS and Kotlin it produces zero cases and says so quietly. The four new
   languages are the ones with *no* check that the semantics matches their runtime, which
   is why the mistranslations above were found by hand.
4. **Two languages fail outright on real code**: Kotlin (frontend crash, reported as
   silence) and JavaScript at scale (renderer `RecursionError`).
5. **A file-extension typo is a semantics change.** `.tsx` gets Python's floored modulo.
   The dialect is inferred from a lookup table with a silent default; a language not in
   the table does not fail, it gets Python.

The accurate claim today: *"Python is supported and checked. C is supported and partially
checked. Java, Go, JavaScript and TypeScript parse, translate and type-check — their
arithmetic is known-wrong at 64-bit widths and for JS numbers, and nothing verifies them
against their runtimes. Kotlin does not work on real code."*

The cheapest change to the verdict is not more front ends. It is
(a) more `Dialect` constructors wired to the `NumConfig`s that already exist,
(b) making `infer_dialect` refuse instead of defaulting to Python, and
(c) a `java`/`node`/`go run` backend for `differential.py` — after which the oracle can
find the rest of this list without a human predicting it.

## Reproducing

```sh
export JOERN_HOME=$HOME/joern PATH="$HOME/.elan/bin:$PATH"
./autoform.sh <corpus> LangJava            # etc.
python3 scripts/lang_matrix.py             # every ast-*.json in the repo root
python3 scripts/lang_matrix.py ast-LangGo.json   # or specific ones
```

`scripts/lang_matrix.py` measures corpora the ledger cannot reach, because it does not
depend on the corpus having rendered.

> **On the function count.** This table uses the ledger's population (209 for `cachetools`), which is regenerated by `scripts/ledger.lean.tmpl` and checked by `scripts/check_docs.py`. Earlier revisions of these documents quote 238 and 208; both are superseded. Percentages must state which population they are over, since the ledger counts module-level synthesized functions the neutral AST does not list separately.

## 16. Interpreter faithfulness pass (2026-09-21, one agent per slice)

Each block below is one slice, grounded in the language's official specification, with
the section cited next to the rule in `Semantics.lean`.

#### 16.A Missing attributes raise `AttributeError` (Python)

**Specification.** Python Language Reference §3.2.11 "Class instances": attribute
lookup searches the instance dictionary, then the class attributes (with descriptors),
then `__getattr__` if the class defines one. §3.3.2 "Customizing attribute access":
`object.__getattribute__` "should either return the (computed) attribute value or raise
an `AttributeError` exception". Library Reference, Built-in Exceptions: `AttributeError`
is "raised when an attribute reference or assignment fails".

**Rule.** `Expr.field` under `.python`, after the instance fields, the closure captures,
a `@property` getter and the class-attribute fallback have all missed, evaluates to
`.exn (.str "AttributeError")` when the program carries recovered class metadata
(`Program.classDecls`), so the miss was searched through a complete MRO
(`Semantics.lean`, the `.field` clause; the arm cites the sections above). Core has no
`__getattr__`, so there is no further fallback to model. On a legacy model with no
class metadata Core cannot see the bases, and a miss is the named gap
`field:<attr>:unresolved-inheritance` rather than a claim that CPython raises: on the
tracked cachetools corpus, `self.getsizeof` on an `LRUCache` instance is the inherited
`Cache.getsizeof`, and the exception answer was 154 of the 157 divergences the runtime
oracle found there.
Every other dialect keeps its previous answer: in JavaScript a missing property is
`undefined` by ECMA-262 §10.1.8.1 OrdinaryGet ("If desc is undefined, return
undefined"), which Core spells `.unit`.

**Checked.** `attrMissMetaProg` in `Semantics.lean` (the class declared): `C().x` is
`AttributeError`; `try/except` binds the class name; an instance attribute still reads;
a `@property` still runs; `attrMissProg` (no metadata): the same reads are the named gap;
`jsMissProg`: `({}).x` is `unit` under `.javascript`. `ExcSafe` closes the new leaf
(`AttributeError ∈ excNames`); `FuelMono` is unchanged in shape (the arm is not
recursive).

**Specs.** `SpecsGen/Basis.lean`'s accessor lemmas `applyFunc_ret_field_self` /
`applyFunc_doc_ret_field_self` now take `hfld` — "under Python the receiver has the field
or captures it" — in place of `hprop`/`hcls`, both of which described arms a receiver
that has the field never reaches. The 74 generated `.cLike` V8 callers pass nothing new
(the default discharges it); `scripts/synth_specs.py`'s projection templates carry the
conjunct in the domain and pass `hfld`.

**Priced by.** §10.9 item 1 (`ShellComplete.source_vars`, three divergences on click).

#### 16.B Module-level variables

**Done.** A Python module object now carries its module-level variables, not only its
functions, classes and submodules. The rule follows the Language Reference:

* §3.2.9 *Modules*: "A module object has a namespace implemented by a dictionary object
  ... Attribute references are translated to lookups in this dictionary, e.g. `m.x` is
  equivalent to `m.__dict__["x"]`. ... Attribute assignment updates the module's
  namespace dictionary."
* §5.4.1 *Loaders*: the loader executes "the module's code in the module's global name
  space (`module.__dict__`)"; §5.4 *Loading*: the module is in `sys.modules` before its
  code runs; §5.3.1 *The module cache*: a module already there satisfies a later import
  without running again.
* §7.11 *The `import` statement*: the `from` form "check[s] if the imported module has an
  attribute by that name ... if the attribute is not found, `ImportError` is raised.
  otherwise, a reference to that value is stored in the current namespace".

What that becomes in the pipeline (`cartographer/export_ast.sc`, `bindName`,
`importValue`, `inits`):

* A module-level binding `X = e` (and a `global X; X = e` inside a function) lowers to the
  globals-frame write it always was **plus** `setField <module>file X X` -- the module
  object's field holds the value the body computed, written when the statement runs.
* `from a import X` for a member that is not a function, class, alias or submodule -- the
  cases that were `import:member-not-found` -- lowers to `setGlobal X (field <module>a X)`:
  a read of the module object at import time, the value copied once. `import a; a.X` is
  the `.field` read at use time it already was.
* Module initializers run in import-dependency order (depth-first over the `from`/`import`
  edges recorded during translation; a cycle keeps name order), so `a`'s body has bound
  `X` before `b` reads it -- the once-each approximation of §5.4/§5.3.1.
* A name the module never bound stays Core's `module-attr:<name>` hole at the read
  (CPython raises `ImportError`/`AttributeError`; Core refuses rather than raises).

Core itself did not change shape: `Stmt.setField`, `Expr.field` and the `<module>` marker
class already existed. `Semantics.lean`'s `modVarProg` block pins `f() = 4`, `a.LIMIT = 3`,
`from a import LIMIT as L` and the two refusals (a missing member; a misordered run) as
`#guard_msgs` checked on every build. Re-measure with `scripts/lang_matrix.py
ast-Requests.json` after a re-export: the 66 `import:member-not-found` holes were also
aborting the importing module's initializer, so the functions they unblock are more than
66.

#### 16.I Go and C: pointers, aggregates, control flow (2026-09-21)

Measured on the tracked corpora before this pass (`scripts/lang_matrix.py ast-LangGo.json
ast-LangC.json`): Go 83 functions, 21 hole-free, 149 holes; C 59 functions, 17 hole-free,
171 holes. The Go corpus is `kelseyhightower/envconfig` with its tests. Neither artifact
could be re-exported here (no Joern in this pass), so the counts below are what the rules
address, not a re-measurement — re-measure with the command above after the next export.

**Lowered, each grounded in the Go specification (quoted at the rule in
`cartographer/export_ast.sc`):**

* `stmt:IMPORT` (39) — an `Import` node is a dependency declaration, not behaviour
  ("An import declaration states that the source file containing the declaration depends
  on functionality of the imported package and enables access to exported identifiers of
  that package" — *Import declarations*). It is `skip`, for every language that has one.
  The imported package's own `init` and package-level variables are outside the exported
  program either way.
* `lit:unquoted` (17, part) — Go **raw string literals**: "the value of a raw string
  literal is the string composed of the uninterpreted [...] characters between the quotes;
  [...] Carriage return characters ('\r') inside raw string literals are discarded"
  (*String literals*). Back quotes stripped, `\r` dropped, nothing else interpreted. The
  remaining `lit:unquoted` on Go are not raw strings (typed constants such as `iota`
  expressions) and stay holes.
* `assign:arity` (7) — **tuple assignment**, `goTupleAssign`: "The assignment proceeds
  in two phases. First, the operands of index expressions and pointer indirections [...]
  on the left and the expressions on the right are all evaluated in the usual order.
  Second, the assignments are carried out in left-to-right order" (*Assignment
  statements*). Every right-hand value is stored in a fresh temporary before any target is
  written, so `a, b = b, a` swaps; a single multi-valued right-hand side (a tuple-typed
  call, `v.(T)`, `m[k]`) is indexed as the `Val.tuple` Core returns for it. Identifier
  targets only; a field/index target is `assign:arity:target-shape` because its own
  operands belong to phase one. Checked in Core: `goProg` (`Semantics.lean`), `swap` = 21
  and `destructure` = 34 as `go1.20.6` prints them.
* `control:FOR` (6, part) — the two Go forms the four-clause lowering did not cover: "The
  iteration may be controlled by a single condition, a "for" clause, or a "range"
  clause" (*For statements*). `for cond { }` lowers to Core's `loop` **only when the first
  child's static type is `bool`** — a range clause also arrives with two children and
  must not be misread as a condition; `for { }` is `loop true` ("If the condition is
  absent, it is equivalent to the boolean value true"). `range` stays `control:FOR:range`:
  its map order "is not specified and is not guaranteed to be the same from one iteration
  to the next", so a program observing that order is out of contract even once the
  clause's CPG shape is known. Checked: `cond` = 3, `forever` = 6.

**Not lowered, and why — Go:** `op:addressOf` (44) and `op:indirection` (12). Go's
`&T{...}` is the dominant shape in this corpus (test fixtures); with `Dialect.go`
boxing containers, the pointer to a fresh struct literal IS the boxed value's reference,
and `&x` of a local is the C boxing path (`boxableName`) — but the Go frontend's spelling
of composite literals (`op:arrayInitializer`, 3) and of `&` over them was not visible
without a CPG, and guessing the shape is the mistranslation this document exists to
refuse. `control:SWITCH` (2): Go's `switch` does not fall through ("unless [...] a
'fallthrough' statement") while `switchStmt` is the C/Java/JS fallthrough-by-threading
lowering keyed on C's `CASTCaseStatement` labels; Go's own labels are unknown here.

**Not lowered, and why — C:** `op:indirection` (28), `op:indirectIndexAccess` (12),
`assign:lhs:indirectIndexAccess` (12), `assign:lhs:indirection` (12): a dereference of a
pointer whose provenance is not one of the shapes Core can track (`ptrIrefNames`,
`ptrAliases`, `closedOutParams`, `strCursorParams`) needs a memory model Core does not
have; `op:cast` (18): casts to pointer types (`castTargetIsPointer`) — the scalar casts
already go through `IntType.wrap`; `control:SWITCH` (14): `switchStmt` handles the
standard shape (C: "The break statement, when encountered anywhere in statement, exits
the switch statement" — fallthrough otherwise, cppreference *switch statement*), so the
14 are shapes it refuses (`consumeLabels`' "defensive only" arm), which cannot be
identified without the CPG. All of these are counted, not hidden.

#### 16.J Assignment expressions, decorators, TS/Kotlin leftovers

Measured on the tracked ASTs before this change: TS `op:assignment` 26 and
`op:notNullAssert` 11 (`ast-LangTS.json`), Kotlin `stmt:METHOD` 2 (`ast-LangKt.json`),
Python `call:python-decorator-binding` 19, `call:python-defaults` 10 and
`function:python-default-evaluation` 3 (`ast-Click.json`). Each is resolved against the
language's own specification, cited beside the rule in `cartographer/export_ast.sc`:

* **`@overload` stubs are a raise, not a hole.** `typing.overload` at run time binds
  the name to a dummy that raises `NotImplementedError` for any call, and the following
  un-decorated definition rebinds the name
  ([typing.overload](https://docs.python.org/3/library/typing.html#typing.overload)).
  The stub therefore translates completely: permissive collectors (no arity `TypeError`
  can answer first) and a body of `raise NotImplementedError` through the
  `py:exception:` constructor. Its `...` defaults are no gap: the dummy never binds them.
  17 of click's 19 decorator holes and 8 of its 10 default holes are these stubs
  (`command`, `group`, `Context.lookup_default`, `Command.main`, `Parameter.get_default`,
  `get_current_context`); re-measure with `scripts/lang_matrix.py` after re-export.
* **External decorators are named.** Language Reference §8.7: `@f def g` is `g = f(g)`,
  evaluated when the definition executes. A decorator the program defines still holes as
  `call:python-decorator-binding` (applying it at definition time is the next step); one
  from outside the program (`contextlib.contextmanager` on `augment_usage_errors`,
  `functools.wraps(f)`) is `decorator:external:<dotted name>` — a different gap with its
  own count. A decorated method is this gap, not `call:python-receiver-signature`.
* **Negative numeric defaults are literals.** `def read(self, n=-1)`: §8.7 evaluates the
  default once when the `def` executes, so `-1` is the constant −1 and binds like any
  literal. `-True` is deliberately not one.
* **Kotlin local functions.** The Kotlin specification ("Local function declaration")
  says a local function may capture the enclosing scope and sees a captured `var`'s later
  reassignment — capture is by reference. Core's `Expr.closure` captures by VALUE at the
  definition, so the lowering (`name = closure(body)`, the body exported as its own
  function) is emitted only when every captured name is assigned at most once in the
  enclosing function and never by the local function; otherwise
  `kotlin:local-fn-capture-mutated`. Top-level functions in the `.kt` file initialiser
  were already `skip` (separate exports); the tracked `ast-LangKt.json` predates that.
* **TS `x!`** was already `x` in both `expr` and `exprV` (ECMA-262 has no such operator;
  TypeScript erases it); the tracked AST predates the rule.
* **TS `op:assignment` (26) is NOT closed here.** `if`/`while` conditions and `return`
  already splice `exprV`'s prelude, and `assignAsValue` handles a name, field or index
  target with ECMA-262 §13.15.2's value (the assigned value) — so the 26 come from a
  target shape or an `expr`-only position this pass could not see without the CPG.
  Logical assignment (`??=`, `||=`, `&&=`; §13.15.2: the right side is evaluated only
  when the left does not decide, and the expression's value is then the left operand) is
  likewise unmodelled until the frontend's operator names for them are confirmed on a
  real export. Both need a Joern run, which this pass did not have.

#### 16.F Iteration protocol and generators

Python `iter` and `next` now use heap-backed iterator objects. Lists, tuples,
strings and dictionaries retain their source and position. List changes remain visible;
exhaustion is permanent. Dictionary value replacement is allowed, size changes raise a
sticky `RuntimeError`, and same-size key-layout changes remain
`iterator:dict-keys-changed` because Core does not represent CPython's dictionary slots.

Ordinary source instances dispatch through `__iter__` and `__next__`, with sequence
fallback through `__getitem__`. An `__iter__` result must itself provide `__next__`;
returning a list now raises `TypeError`. Sequence iterators stop on `IndexError` or
`StopIteration`. `next(iterator, default)` handles exhaustion. Callable/sentinel
iteration invokes its callback lazily, compares the sentinel first, preserves identity
shortcuts and retains exhaustion across reentrant callbacks. These rules follow the
[Python iterator protocol](https://docs.python.org/3/library/stdtypes.html#iterator-types)
and [CPython iterator implementation](https://github.com/python/cpython/blob/3.14/Objects/iterobject.c).

The synthetic protocol methods run through ordinary Core calls. Each loop uses a
binding specific to its iterator reference, keeping nested loops independent. Fuel
monotonicity and exception safety cover the new paths. Source comparisons and kernel
proofs are in `tests/test_source_iterators.py`; a small nested-loop kernel regression
also runs without Joern. Unknown exception ancestry and relevant unknown identity
remain explicit holes. Taking a builtin iterator's synthetic method as a value is
`field:runtime-method`; direct calls are supported. An object result with unresolved
inherited or metaclass iterator behavior is `iterator:result-protocol`. General class-level rebinding of
special methods and inherited dispatch still need the broader object-model work.

Ordinary generator functions now compile to suspended heap frames through
`cartographer/generator_lowering.py`. Creation leaves the body unexecuted, and
`__next__`/`send` resume saved locals and control state, including exception handlers
and `finally` continuations. The implementation shares protocol helpers without adding
them to source-function coverage. `tests/test_source_generators.py` compares actual
Joern exports with CPython and proves the observations by kernel reduction.

`yield from`, `close`, `throw`, return payloads, shared free-variable cells, closure
frames and async generators retain named gaps. Generator expressions use the suspended
frame lowering described in §10.6. Implicit iteration uses reserved protocol operations,
so user bindings named `iter` or `next` cannot replace the machinery of a `for` loop.
See the
[recovery record](interpreter-recovery.md) for implementation details and validation
scope; these additions do not establish arbitrary-codebase completion.

#### 16.C `except ... as e` binding and corpus-defined exception classes

Two labels that dominated the scale corpora's `try` statements are closed, each against
the Python language reference rather than against an intuition.

**`except E as e:` binds (`control:TRY-handler-binding`: click 11, requests 2).** The
reference (§8.4.1, "except clause") says the target is bound to the exception object and
"cleared at the end of the `except` clause". Core's exception value is the class name —
there is no payload — so the exporter binds `e` to the pending value exactly when every
use of `e` in the handler is one the class name answers or one the exporter can refuse
precisely (`binding_ok` in the decoder): re-raising it or `raise ... from e`;
`isinstance(e, T)`, which is lowered to the same membership test the dispatch uses
(`inOp e (T's closure)`); `type(e)`; passing `e` to an exception constructor, whose payload
Core drops anyway; an attribute read `e.args`/`e.errno`, which becomes the hole
`exception:payload:<attr>` (library reference: `BaseException.args` is "the tuple of
arguments given to the exception constructor", which Core does not carry); and `str(e)`/
`repr(e)`/`format(e)`, which become `exception:payload:str`. Any other use — `return e`,
`x = e`, `e == y`, `f(e)` — would let a string stand in for an object, so the whole handler
keeps its `control:TRY-handler-binding` hole. The end-of-clause deletion is not modelled:
a read of `e` after the clause is a `NameError` in CPython and reads the class name here;
it is recorded rather than fixed because no scale corpus does it.

**Corpus exception classes are catchable and raisable (`control:TRY-handler-type`:
requests 15, click 8).** The reference matches a raised exception against a handler
naming "the class or a non-virtual base class of the exception object, or a tuple that
contains such a class"; the library reference has user code "derive new exceptions from
the `Exception` class or one of its subclasses". So a class the corpus defines whose base
chain reaches a builtin exception (`class RequestException(IOError)`) is an exception class
like any other. The exporter now reads every Python class's single base from the CPG
(`pyClassBases`), closes each handler's accepted set over both hierarchies —
`acceptedFor`: the decoder's builtin closure plus every corpus class deriving from a named
type — and lowers `raise MyErr(args)` to "evaluate the arguments for their effects, raise
the name `MyErr`". Core accepts the name because the renderer lists every such class in
`Program.excClasses` and `pythonRaise ctx.excClasses` treats it as represented
(`Semantics.lean`); `ExcSafe.lean` is restated over `Stdlib.ExcSafeIn ctx.excClasses` —
every exception Core raises under `.python` names a builtin or one of the program's own
classes. Tuples of types flatten; an attribute path (`socket.error`), an alias Core cannot
see, or a name that is not a corpus exception class stays `control:TRY-handler-type`;
multiple inheritance and a short name bound to two different bases are not guessed at.

Checked on every build by the `excClassProg` `#guard`s in `Semantics.lean`, against
CPython: catch by own class, by base `Exception` (whose closure contains the corpus class),
no match on `KeyError` propagates, `except (KeyError, MyErr) as e: return e` yields the
class name, `raise e` re-raises it, and raising a non-exception name is CPython's
`TypeError` ("exceptions must derive from BaseException").

#### 16.G JavaScript objects, classes, equality (2026-09-21)

Slice G of the "interpreter for every language" pass. Every rule names the ECMA-262
clause it implements (2027 draft numbering; the clause NAMES are stable across editions).

* **`new C(args)`** (§13.3.5 `new MemberExpression Arguments` → EvaluateNew → Construct).
  jssrc2cpg lowers it to the same three-sibling block C++ uses -- `_tmp = <operator>.alloc;
  <operator>.new(C, args…); _tmp` -- with the class as the receiver of `<operator>.new`.
  `ctorAlloc` folds a corpus class to `Expr.alloc C args`, whose constructor is now a
  dialect fact: `Dialect.ctorName .javascript = "<init>"` (jssrc2cpg's name for
  `constructor(...)`), `"__init__"` everywhere else. `new Map()` with no arguments is an
  empty boxed dict -- keys to values with identity is what a Map is to Core. Any other
  constructor is a hole that names it (`op:new:Promise`, `op:new:computed-constructor`);
  a `<operator>.new` outside the block shape is `op:new:unfolded` instead of the former
  silent `call "<operator>.new"`, which only failed at run time.
* **`this`.** jssrc2cpg keeps `this` as parameter 0 of every function. It now leaves the
  parameter list and is spelled `self` in bodies, exactly as C++'s `this` already was,
  because `applyFunc` binds the receiver itself; a NAMED call no longer threads argument 0
  back in (§10.2.1.2 OrdinaryCallBindThis: no receiver, `this` is `undefined`/the global
  object -- Core's `applyFunc … none`). `#guard newPt`: `new Pt(3).getX()` is `3`.
* **`typeof e`** (§13.5.3, the "typeof Operator Results" table) is `jsTypeof`. jssrc2cpg
  spells the operator `<operator>.instanceOf` with ONE child; the two-child form is the
  real `instanceof` (§13.10.2 InstanceofOperator), which needs the class hierarchy Core
  does not carry and stays `op:instanceof:class-hierarchy`.
* **`===` / `!==`** are IsStrictlyEqual (§7.2.14); **`==` / `!=`** are IsLooselyEqual
  (§7.2.13). Both spell `<operator>.equals` in the CPG; the exporter reads the source
  text (`binopFor`) and emits `js:===`/`js:==`. `jsLooseEq` decides steps 1-10 (same
  type; null/undefined; Boolean → ToNumber; Number against an integer-literal String) and
  answers `none` for ToPrimitive on objects and non-integer numeric strings, which the
  interpreter reports as `js:loose-eq:<kind>-<kind>` rather than guessing. `#guard eqs`:
  `[1 === "1", 1 == "1", 0 == false, null == undefined, "" == 0, 1 === 1.0, 2 != "2"]` is
  Node's `[false, true, true, true, true, true, false]`.
* **`null` and `undefined` are one `Val.unit`.** They agree under `==`; they differ under
  `===` and `typeof`. Core answers as if the value were `undefined`, so two idioms are
  silently wrong when the value is actually `null`: `x === null` (Core: `true` for an
  `undefined` `x`, Node: `false`) and `typeof x` (Core `"undefined"`, Node `"object"`).
  Splitting them is a `Val` constructor, which touches every exhaustive match in Core,
  the ledger and the renderer; it is recorded here as the next JS semantics change rather
  than done in this slice.

Not done in this slice, with the label each keeps: `a instanceof B`
(`op:instanceof:class-hierarchy`), `await` (`op:await`), TS assignment in receiver
position (`op:assignment` -- jssrc2cpg's `_tmp = this.#f` lowering, not yet unpicked),
builtins other than `Map` (`op:new:<Name>`). The tracked `ast-LangJS.json`/`ast-LangTS.json`
predate this exporter and today's `throw`/`catch`/`void`/`x!`/`++` lowerings; their counts
are re-measured by a re-export, not by this document.

#### 16.D `assert`, sets, `bytes`, `and`/`or` chains, impure blocks (2026-09-21)

Measured on click 8.2.1 and requests 2.32.5 (`scripts/lang_matrix.py ast-Click.json
ast-Requests.json`); each rule cites the Python Language Reference it implements and
is checked against CPython by the `sliceDProg` `#guard`s in `Semantics.lean`.

* **`op:logicalAnd` / `op:logicalOr` (23+3 / 8+1) -- closed.** pysrc2cpg flattens
  `a and b and c` into ONE call with three operands, and the exporter only lowered the
  two-operand shape. §6.11: `x and y` "first evaluates x; if x is false, its value is
  returned; otherwise, y is evaluated and the resulting value is returned" -- the
  operators "return the last evaluated argument". The chain folds left (the grammar is
  `and_test: and_test "and" not_test`) onto Core's short-circuit value operator.
* **`op:assert` (13+6) -- closed.** §7.3: `assert e` "is equivalent to
  `if __debug__: if not e: raise AssertionError`", `assert e, m` to
  `... raise AssertionError(m)`. Lowered to exactly that with the existing `ifte` and
  `raise` of the `py:exception:AssertionError` constructor; the message is in the
  else-branch, so it is evaluated only on failure, as in CPython. `__debug__` is taken
  as `True` -- the oracle's CPython runs without `-O`.
* **`op:setLiteral` (7) -- closed, by a stated model.** §6.2.7: a set display's
  "elements are evaluated from left to right and added to the set object"; a set is "an
  unordered collection of distinct hashable objects" (library reference, Set Types).
  Core has no set value; a set display is a boxed dict whose values are all `unit`.
  `in`, `len` and iteration are the dict's own on its keys; `add`, `discard` and
  `remove` (KeyError when absent) are `Stdlib.method` arms; distinctness comes from
  `dictE` deduplicating keys. What the model does NOT give: set operators (`|`, `&`,
  `-`, `^` still hole at the operator), `==` between a set and a dict of `unit`s (a dict
  literal of `unit` values is indistinguishable -- no corpus does this), and
  `set()`/`frozenset()` calls.
* **Dict displays deduplicate (§6.2.8).** Found while modelling sets: "you can specify
  the same key multiple times in the dict item list, and the final dictionary's value
  for that key will be the last one given". `dictE` now folds its pairs through
  `Stdlib.dictSet` (first position, last value); it used to keep both entries and
  answer `len` 2 for `{1: "a", 1: "c"}`.
* **`len`/`sum`/`min`/`max`/`bool`/`any`/`all` see through a boxed container.** Found
  by the set guards: `len(xs)` on a list that allocates was the hole `call:len`, because
  `Stdlib.builtin` matched the raw `Val.ref`. Read-only, scalar-returning builtins now
  unbox their arguments first (`Stdlib.unboxesArgs`); container-returning ones do not,
  because their result would have to allocate.
* **`expr:BLOCK-impure` (31+12) / `expr:BLOCK-prelude` (2+2) -- closed where a prelude
  exists.** In a prelude-aware position (`exprV`: an argument, an assigned value) the
  frontend's `tmpN = e` bindings are hoisted into the prelude in order instead of being
  substituted, so an impure binding is evaluated once and in order relative to the rest
  of its block. In plain `expr` position there is still no slot and the labels stay.
  The caveat is `exprV`'s own: a hoisted prelude runs before sibling arguments to its
  left are read, which Python (§6.16, evaluation order: "operands are evaluated from
  left to right") would evaluate first.
* **`lit:bytes` (7+5) -- kept as a hole.** §2.5.5: bytes literals "produce an instance
  of the bytes type instead of the str type". Encoding one as a `Val.str` would be a
  wrong type (`b'a' == 'a'` is `False`); a `Val.bytes` touches every exhaustive match
  over `Val` in `FuelMono`, `ExcSafe`, `Ledger` and `Basis`, and is not done here.

#### 16.H Java objects, exceptions, casts, arrays, `for` (2026-09-21)

Grounded in the Java Language Specification (SE 21), section cited at each rule in the
code. Measured on `ast-LangJava.json` (gson, 669 functions) before the change: `op:alloc`
166, `control:THROW` 125, `op:cast` 123, `op:instanceOf` 90, `op:arrayInitializer` 43,
`control:FOR` 30. What this pass changed, and what it deliberately did not:

* **`this` was unbound.** The Java frontend spells the receiver `this` (JLS §15.8.3) and
  Core binds it as `self`; only C++ was being renamed, so every `this.x` in a Java method
  read `unit` from an unbound name -- 559 sites in gson, all silently wrong, none a hole.
  `localName` now renames it for `.java` files. This is the single largest fidelity fix
  here and it moves no hole count at all, which is the point of the differential oracle.
* **Constructors and method names.** javasrc2cpg names methods with their erased
  signature (`pkg.Cls.<init>:void(int)`, JLS §8.4.9/§8.8), so Core's dotted-suffix
  `resolveMethod` never matched a Java method. `stripSig` drops the signature before the
  suffix test (structurally, kernel-reducible) and `Ctx.resolveCtor` tries `__init__` then
  `<init>`: `new Box(7)` now runs the constructor with `this` bound (§15.9.4). `#guard`
  `javaProg` in `Semantics.lean`.
* **Casts (§5.1.2, §5.1.3).** To `byte`/`short`/`char`/`int`/`long`: Core's `cast:*`
  operators. Integral→integral discards all but the low-order bits (`IntType.wrap`).
  Floating→integral is `javaFloatToIntegral`: NaN → 0, round toward zero, saturate to
  `int`/`long`, then narrow again for `byte`/`short`/`char` -- `(int) 3.9 == 3`,
  `(int) NaN == 0`, `(int) 1e30 == Integer.MAX_VALUE`, `(byte) 300.9 == 44`, each a
  `#guard`. Under `.cLike` the same float cast stays a hole: C17 §6.3.1.4 makes it
  undefined out of range. Casts to `float`/`double` (`op:cast:java-floating`) and
  reference casts (`op:cast:java-reference`, §5.5.1 may throw `ClassCastException`) keep
  named holes.
* **`throw` (§14.18).** Lowered to `Stmt.raise`; under `.java` Core raises the value
  as-is. Handler dispatch for typed `catch` (§14.20.1, by class ancestry) is NOT done: the
  `try` lowering still holes a Java `catch (T e)` as `control:TRY-handler-language`, so
  the 125 `control:THROW` holes become raises whose catching is a separate, named gap.
* **Array initializers (§10.6, §4.3.1).** `{a, b, c}` is a new array object with
  left-to-right initializers: the boxed list literal under `.java`. `new int[n]`
  (§15.10.2, default values §4.12.5) is not lowered yet.
* **Collections.** `knowsMethod .java` now answers `java.util.List`/`Map` on the boxed
  list/dict: `add` (returns `true`), `get` (`IndexOutOfBoundsException` on any
  out-of-range index -- no negative indexing), `size`, `isEmpty`, `contains`, `put`
  (previous value or `null`), `containsKey`; `knowsMethod_java_complete` proves each name
  is answered. `new ArrayList<>()` itself is still the frontend's alloc-block shape and is
  not lowered here.
* **Not done, on purpose:** `instanceof` (§15.20.2 needs a run-time class test against
  the corpus's class hierarchy -- no Core expression reads an object's class yet), classic
  `for` (§14.14.1 already lowers via `forStmt` where the CPG has four clauses; the 30
  bare `control:FOR` holes are a different child shape not yet examined), `new C(args)`
  for corpus classes in the exporter (the frontend's three-statement alloc block is not
  yet folded for Java, so `op:alloc` stays 166 until it is). Every one of these is a
  hole, never a guess.

#### 16.E `str()`, `repr()` and f-strings

**Done for every value whose spelling is a function of the value; a hole, by kind, for
the rest.** `Stdlib.pyRepr`/`pyStr` print `int`, `bool`, `None`, `str`, `list`, `tuple`
and `dict` exactly as CPython does (`[1, 'a', None, True, (2,), {'k': [3]}]`), following
the language definition rather than an approximation:

* `repr()` — "a string that would yield an object with the same value when passed to
  `eval()`" (Built-in Functions § `repr`); the escaping of a `str` follows CPython's
  `unicode_repr`: single quotes unless the text contains `'` and no `"`, then `\\`, the
  quote, `\n`, `\r`, `\t`, and `\xNN` for other control characters and DEL. Whether a
  non-ASCII character prints as itself is a Unicode-printability property Core does not
  carry, so a string containing one is the hole `format:unprintable:str-non-ascii`.
* `str()` — "the default implementation defined by the built-in type `object` calls
  `object.__repr__()`" (Data model § `object.__str__`); `str` of a `str` is the string.
  On an instance, `builtinDunderTarget` runs `__str__`, falling back to `__repr__` as the
  data model says, and an instance with neither is `format:unprintable:instance` — its
  CPython spelling is an address.
* `format(value, spec)` — an empty spec "usually gives the same effect as calling
  `str(value)`" (Built-in Functions § `format`) and is exactly that here. A non-empty
  spec is the Format Specification Mini-Language (Library § `string`): implemented are
  `[[fill]align]["0"][width]["." precision][type]` with `type` ∈ {`s`, `d`, none} — the
  documented defaults (`<` for strings, `>` for numbers; `0` before the width means fill
  `0` and sign-aware `=` for numbers, and since 3.10 does not change a string's
  alignment), the documented refusals (`=` or a sign on a string, a precision on an
  integer, `s` for an int or `d` for a str: `ValueError`; any non-empty spec on `None`,
  a list, a tuple or a dict: `TypeError`, per Data model § `object.__format__`), and a
  `bool` under a non-empty spec formats as the int it is. Everything else — sign, `z`,
  `#`, grouping, nested fields, `b`/`x`/`o`/`e`/`f`/`g`/`%`/`n`/`c` — is the hole
  `format:spec:<spec>`, which quotes the spec so the count says what is missing.
* Floats. `repr`/`str` of a float is the shortest round-tripping decimal, which
  `Float.lean` deliberately does not model; every float print is
  `format:unprintable:float`.

The exporter reads the conversion and the spec off the field text (Lexical analysis
§ f-strings, `fstring_replacement_field`): `{x}` → `str(x)`, `{x!r}` → `repr(x)`,
`{x:>5}` → `format(x, '>5')`, `{x!r:>5}` → `format(repr(x), '>5')` — the conversion
before the spec, as the Format String Syntax says. Literal segments decode their escapes
as the lexer does and `{{`/`}}` become single braces; `!a`, the debug specifier `{x=}`,
a nested spec `{x:{w}}` and `\N{name}` are refused at export with a label that says
which. Plain string literals now decode their escapes too (a raw `r'…'` keeps them), which
closes a silent wrong value (`'a\nb'` was a backslash and an `n`) that predates this
section. Adjacent literals with an f-string part (`"a" f"{x}"`) concatenate.

Checked against CPython 3.11 by the `#guard` table in `Stdlib.lean`; the former residue in
`Semantics.lean` (`f'v{x}!'` with a string `x` was the hole `call:str`) now pins CPython's
`'vx!'`. Exception safety is a theorem (`strBuiltin_excSafe`: only `ValueError` and
`TypeError`, both represented), and the builtins still leave the heap unchanged
(`builtin_heap_unchanged`).

#### 17.R4 Statement effects in expression operands

Recovered from the interrupted interpreter work and validated against real Joern
output. `exprV` now carries intermediate statements through computed callees, method
receivers, positional and keyword arguments, constructor arguments, list/tuple displays,
membership/identity operands and slice bounds. Earlier operands are evaluated into
fresh temporaries before later operands' statements run. Nested frontend blocks retain
their final expression's statements too. For `make_function()(argument)`, the
computed function runs before the argument's statements; a callee or earlier argument
that raises prevents later effects. The source comparisons cover both exception paths
and selecting a function from a container that a later argument reassigns.

The contract is Python's [evaluation order](https://docs.python.org/3/reference/expressions.html#evaluation-order).
This includes effects and exceptions from earlier operands, not just their final
values. A preceding `*args` or `**kwargs` expansion still refuses a later hoisted
effect: saving the iterable or mapping would not save the expansion. This change does
not extend the existing eager-generator consumer set to method calls. Suspended
generators remain required for the arbitrary-codebase goal.

`assert` keeps its message's statements inside the failure branch; conditions run
before the test. Loop iterables run once before iteration. `del` receivers and indexes
and non-Python raise operands also carry statements in source order. Conditional
expression branches and short-circuit operands keep their conditional execution.

The runtime comparison exposed two further defects. Python type recovery can name an
unnamed context-manager call `Held..__init__`; an empty callee name must not turn into
an allocation. The exporter now lets its existing bound-method recovery handle that
shape. `tuple` can now read a boxed container without losing references to its nested
mutable elements. This does not establish general context-manager exception
suppression or lazy-generator correctness.

Validation commands:

```sh
AUTOFORM_TEST_JOERN=1 .venv/bin/python -m pytest tests/test_source_numeric.py -k 'joern_native_numeric and python' -q
.venv/bin/python -m pytest tests/test_source_numeric.py -k tuple_from_boxed -q
```

The source test compares the results with CPython and proves every Python observation
in Lean's kernel, including receiver reassignment, keyword ordering, constructor
arguments, display ordering, slicing, deletion, assertion messages, short-circuiting,
loop iterables and the normal context-manager path. Re-export a corpus with
`scripts/reland_corpus.sh` before claiming updated corpus conformance or coverage.

#### 17.R8 Go and C pointers with the CPG shapes (2026-09-21)

**What the measurement actually was.** The tracked `ast-LangGo.json` / `ast-LangC.json`
carry the OLD bare labels (`op:addressOf`, `op:indirection`, `op:cast` -- 44/12, 28/18)
with no `:shape:kind` suffix: they were exported before the exporter's interior-pointer
machinery (`boxedLocals`, `ptrAliases`, `ptrIrefNames`, `irefField`/`irefIndex`/
`derefIref`/`setDerefIref`, `castTargetIsPointer`, the labelled `op:addressOf:<shape>:<kind>`
holes) existed. Those counts therefore measure a different exporter, and this pass did not
run Joern; the honest statement is what is now IN PLACE for a re-export, not a delta.

**Go, done.** The boxing/alias/iref path is language-agnostic except for one fact it asks
of every type: `isPointerType`. Go spells a pointer type with the star first (spec "Pointer
types": `PointerType = "*" BaseType`, so `*main.T`, `*int`), where C/C++/Java spell it last;
until now every Go pointer read as `opaque-type` and no pointer rule could fire on a Go
file. Fixed in `cartographer/export_ast.sc` (`isPointerType`). With it, `x := 1; p := &x`
boxes `x` at its binding (the dominance rule the C path and Python's `nonlocal` already
apply), `*p` resolves through the alias, `&s.f` / `&a[i]` are `irefField` / `irefIndex`,
`*p = v` is `setDerefIref`. Core needed no new clause: `goPtrProg` in `Semantics.lean`
runs those clauses under `.go` and pins `go1.20.6`'s answers (`ptrLocal` 5, `ptrField` 11,
`ptrIndex` 14, `ptrAlias` 3), with the spec sentences ("Address operators", "Selectors")
quoted beside them.

**Go, not done, and why.** `&T{...}` (a pointer to a composite literal) and `for range`
depend on gosrc2cpg's spelling of the composite literal and of the range clause, which is
not derivable from the Go spec and was not observed in this pass; both keep their holes
(`op:addressOf:call:*`, `control:FOR:range`). Map iteration order, when `range` lands, is
out of contract by the spec's own sentence ("is not specified and is not guaranteed to be
the same from one iteration to the next").

**C, unchanged.** The 28/18/14 `sds` holes are bare labels from the old export; the current
exporter's `op:indirection:<kind>`, `castTargetIsPointer` and `switchStmt` paths cover
much of `sds` already and the residue (pointer arithmetic on `char *` cursors beyond the
`strCursorParams` shapes, pointer casts between distinct pointer types, `switch` bodies
whose labels are not `CASTCaseStatement`/`CASTDefaultStatement`) needs the CPG to name.
C17 §6.5.6 (pointer arithmetic) and §6.8.4.2 (fallthrough) are the contracts a future pass
must meet; none of them is guessed here.
