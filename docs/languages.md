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
| Python | yes | yes | yes | `.python` ✅ | 209 | 86% | 101 (48%) | 0.8% | **yes** (CPython) |
| C | yes | yes | yes | `.cLike` ✅ | 59 | 17 (29%) | 8 (13%) | 11% | crashed (see below) |
| Java | yes | yes | yes | `.cLike` ⚠️ | 669 | 350 (52%) | 191 (28%) | 6% | **none** |
| Go | yes | yes | yes | `.cLike` ⚠️ | 83 | 21 (25%) | 6 (7%) | 4% | **none** |
| TypeScript | yes | yes | yes | `.cLike` ⚠️ | 86 | 44 (51%) | 18 (21%) | 4% | **none** |
| JavaScript | yes | yes | yes | `.cLike` ⚠️ | 14 | 5 (35%) | 1 (7%) | 5% | **none** |
| JavaScript (lodash) | yes | **no** | n/a | `.cLike` ⚠️ | 693 | 419 (60%) | — | 1.8% | **none** |
| Kotlin (real repo) | **no** | n/a | n/a | n/a | — | — | — | — | **none** |
| Kotlin (toy) | yes | yes | yes | `.cLike` ⚠️ | 3 | 2 (66%) | 2 (66%) | 4% | **none** |
| `.tsx` / `.jsx` | yes | yes | yes | **`.python` ❌ WRONG** | — | — | — | — | none |

Percentages are from the ledger the pipeline printed (`ledger-Lang*.json`);
`scripts/lang_matrix.py` recomputes them from the exported AST independently and agrees
to within the ledger's slightly different node-counting.

⚠️ = the dialect *is* in `render_lean.py`'s `DIALECT` map, but every non-Python language
maps to the single `.cLike` constructor, which is 32-bit truncating C. See below.

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

### 2. `.tsx` / `.jsx` sources get the **Python** dialect — NEW, and it is the original §12 bug reappearing

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

### 5. Java `long` and Go `int` are 64-bit; Core models them as 32-bit

`.java`/`.go` → `.cLike` → `c32Wrapv` on the **untagged** path. `Numeric.lean` defines
`java32`, `java64` and `go64`, and `Dialect` still has no `.java`/`.go` constructor to
select them (its three are `python`, `cLike`, `javascript`).

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

| input | real runtime | Core |
|---|---|---|
| Java `long a=2147483647L; a+1` | `2147483648` | **`-2147483648`** |
| Java `long m=100000L; m*m` | `10000000000` | **`1410065408`** |
| Go `a:=2147483647; a+1` | `2147483648` | **`-2147483648`** |
| Go `m:=100000; m*m` | `10000000000` | **`1410065408`** |

This is the *same* mistranslation §16 records finding for C (`mulbig(100000,100000)`
giving `1410065408` against `cc`) — except here `1410065408` is the wrong one, because
Java `long` and Go `int` are 64-bit. Core has no types, so it cannot distinguish Java
`int` from Java `long`; whichever width it picks is wrong for the other. Verdict:
**wrong**.

### 6. Java string `+`, `==`: right answer, wrong reason

Under `.cLike`, `applyBinop` makes `"a" + "b"` a hole labelled
`str:pointer-arithmetic-not-modelled`, and `s == t` a hole labelled
`str:pointer-equality-not-modelled`. For C those labels are correct. For Java:

* `s == t` is reference equality, so holing is conservative and defensible — though the
  label says "pointer", which is the right idea by accident.
* `s + t` is concatenation and is ordinary Java. Holing it is a coverage loss, not a wrong
  answer.
* The same rules are applied to JavaScript and TypeScript, where `+` on strings is
  concatenation and `==`/`===` on strings compare *contents*. Measured: JS `"a"+"b"` →
  `hole "str:pointer-arithmetic-not-modelled"` instead of `"ab"`; JS `1 + "1"` →
  `hole "binop:+"` instead of `"11"`.

Verdict: **hole** (safe) but wrong for three of the four `.cLike` languages. This is the
inverse of the C case, and it shows that `.cLike` is not one dialect.

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

### 10. Python `except` dispatch: the representation guard, and its removal

`cartographer/export_ast.sc` lowers Python `try`/`except` into a dispatch that compares
the pending exception against `Stdlib.excNames` **as a string**, and holes
(`control:TRY-exception-representation`) when it is not one of them. That is 29 holes on
a fresh `cachetools` export — the largest single Python hole class after literal defaults.

The guard looks redundant, and establishing whether it is was worth doing properly,
because "obviously every exception is one of those names" is exactly the sort of claim
this project keeps finding to be false. Every producer of an exception value in
`Autoform/Lang/Core/Stdlib.lean` is now pinned by a theorem:

* `makeException_excSafe` — holes on any name outside `excNames`, and otherwise yields
  that name (or a `TypeError` from argument validation).
* `raiseValue_excSafe` — raising a string is a `TypeError` as in CPython, an object
  holes, and a builtin class reference is routed through `makeException`.
* `python_shiftCount_trap` (`Numeric.lean`) — the one exit that was **not** safe. A
  numeric trap becomes `.exn (.str r)`, and the Python shift-count trap carried the prose
  `"negative shift count"`, so `except ValueError:` could not match it. Fixed; the
  theorem is what keeps it fixed.

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

### 11. `nonlocal` is an exporter gap, not a semantics gap

`scope:nonlocal-write` holes every `nonlocal` write — 8 on a cachetools export, all of
them the `hits += 1` counters in `_cached.py`. The exporter comment explains that
`Expr.closure` captures by value, so a write cannot reach the frame owning the variable,
and emitting an `assign` would compute the wrong answer silently.

That is right about `assign` and wrong about what Core can express. Capturing a `Val.ref`
by value still shares the object behind it, which is precisely a closure cell: `boxNew`
allocates, `field`/`setField` read and write. `Autoform/Lang/Core/Semantics.lean` carries
the worked program as a `#guard_msgs` — two calls through a closure, owning frame observes
both writes, `2`. It is checked on every build rather than asserted here, because "the
semantics can already do this" is the kind of claim that rots.

**Done.** The exporter now boxes the name in the scope that defines it and lets the
closure share the cell, reusing the `boxedLocals` machinery that already existed for C
address-taken locals. Two sets per function: the enclosing scope's names get the box and
the allocation prologue, the closure's get the same `field`/`setField` treatment and
explicitly NO prologue — allocating there would rebind the name to a fresh box and
destroy the alias.

The safety condition is the whole content, and it is checked rather than assumed. The box
must exist when the closure captures it, so the enclosing function must bind the name by a
plain assignment at the top level of its body **before the first nested `def`**. A binding
inside an `if`, or after the `def`, does not dominate the capture: the parent leaves the
name a plain value, and telling the closure it is boxed would read a field off an integer.
Those keep the hole. One level of nesting; deeper chains keep it too.

On cachetools this closes all 8 sites — every one is the decorator idiom, `hits = misses =
0` before `def wrapper`. Checked end to end: `counter()` with a `nonlocal hits` increment
called twice returns `2`, as in CPython, and the `if`-bound variant still holes.

One bug worth recording, because it was silent in the first pass: `globalDeclNames` strips
the literal prefix `global`, so on `nonlocal x` it returns the name `"nonlocal x"`. The
membership test then failed and the hole stayed — the harmless direction that time, but
the same parser was one edit away from deciding a name WAS boxed when it was not.

### 12. A `@property` read was a silent wrong answer, and is now a hole

`c.currsize` calls a getter in Python. Core has no descriptor protocol, so the exporter
lowered it to a plain field read — and `Cache.__init__` stores the name-mangled
`_Cache__currsize`, so a field called `currsize` does not exist. `evalExpr` answers a
missing field on an ordinary object with `unit`, **silently**, with no hole:

| | `c.currsize` |
|---|---|
| CPython | `1` |
| Core | `unit` |

Both confirmed by execution, not by reading. This is the failure class the whole project
is organised against — well-typed, hole-free, and wrong — and it was inside the tracked
corpus, where `make_info` reads `cache.currsize` and `cache.maxsize`, and the ledger
counted the enclosing functions as translated.

The exporter now holes any attribute read whose name is a `@property` anywhere in the same
file (`call:python-property-access`). Conservative by name rather than by receiver type,
because Python attribute access is not statically resolvable in general and over-holing is
the safe direction. On cachetools this *raises* the hole count, 108 to 126 across 18 read
sites — which is the point: the coverage was never real, and a number that drops when a
silent wrong answer is corrected was measuring the wrong thing.

Two consequences worth stating plainly:

* **The tracked corpus still has the defect.** `ast-Cachetools.json` was exported before
  this change, so its `make_info` still reads `currsize` as a field and still computes with
  `unit`. The fix lands in future exports only, which is one more entry on the list of
  reasons the tracked ASTs are evidence about the exporter that produced them.
* Closing the hole properly — making `c.prop` call the getter — is descriptor dispatch in
  `evalExpr`'s field case, and it needs the receiver's class. That is a Core change on the
  hottest path in the interpreter, and it is not what this entry did.

### 13. The `@property` bug is an instance; the general case is priced

Item 12 is one symptom of a rule in `evalExpr`: a missing field on an **ordinary** object
evaluates to `unit`. Python does not do that.

| | `c.missing` where `c` has no such attribute |
|---|---|
| CPython | `AttributeError: 'C' object has no attribute 'missing'` |
| Core | `unit` |

Module objects already hole here (`module-attr:<f>`), and the comment beside that case
says ordinary objects keep `unit` "so no existing corpus changes" — which is exactly the
reason to check what changing it costs rather than leave it at a comment.

**Measured.** Making an ordinary missing field hole (`attr:<f>`) breaks **171 declarations
across 36 files, 136 of them in generated `SpecsGen` specs** (every `V8Base` part plus
`Cachetools`). The direct cause is `applyFunc_ret_field_self` and its documented twin in
`SpecsGen/Basis.lean`: they state "an accessor returns the field it names" for *every*
heap, including receivers that do not have the field, where the claim today is that the
accessor returns `unit`. Restricting them to receivers that actually have the field — two
lines, and a better theorem — is not the expensive part; re-stating the 136 generated
specs that depend on the unrestricted form is, and that means changing `synth_specs.py`
and regenerating them.

So the general case is **not** closed here, and the cost is on record rather than guessed
at. Two notes for whoever takes it:

* Holing is the conservative option, not the faithful one. If Core's object model is
  complete for a translated program then `AttributeError` is the *correct* answer and a
  hole understates what is known; if it is not complete, a hole is right and
  `AttributeError` would be a fresh wrong answer. Deciding that is the real work, and it
  is a decision about what the project claims, not a refactor.
* The instance that was actually observed — `@property` — is fixed at the exporter (§12),
  which needed no Core change and no spec regeneration.

### 14. Property dispatch: implemented, proved fuel-monotone, blocked on one lemma

§12 holes a `@property` read rather than computing `unit`. Making it *work* — running the
getter, which is what Python does — was implemented end to end and reverted. The semantics
are not the hard part, and it is worth recording what is.

**What worked.** On a field miss, `evalExpr` resolves the getter and applies it to the
receiver. `FuelMono`'s `.field` case, previously `exact hy` because the case was
fuel-free, was extended to the explicit nested proof a recursive branch needs, and it
goes through.

**Two designs, and the second is the one to keep.** A `Ctx.properties : List (String ×
String)` field cost **289 broken declarations**, because every `Ctx` literal in
`Contracts.lean` then disagreed with `ctxOf` about a field it did not mention. Registering
the getter in the *existing* function table under a marker name no source language can
spell — `<property>currsize` — needs no new field anywhere, so every `Ctx` term and every
proof that reduces one stays byte-identical. That is the version that should be built.

**What blocks it.** `applyFunc_ret_field_self` and its twin claim "an accessor returns the
field it names" for every receiver, and a class with a property of that name now answers a
call instead. Excluding it needs a side condition of the shape
`ctx.resolveMethod o.cls (propertyGetter fld) = none`, and that cannot be discharged by
`rfl`: `o.cls` is universally quantified, and `resolveMethod` falls back to `Ctx.resolve`,
which suffix-matches over the whole table. Without a discharge the obligation lands on 284
declarations across the generated specs.

The missing piece is small and identified: a characterisation lemma saying `Ctx.resolve`
returns `none` when no table entry's name ends with the sought suffix.
`FuelMono.resolve_go_mem` — "the suffix scanner only ever returns a function drawn from the
list it scanned, or the accumulator it started with" — is exactly the building block, and
it already exists. With that lemma the side condition becomes a statement about the
concrete table, decidable by `rfl` for every corpus, and the 284 collapse the same way the
switchover's 163 collapsed to 3.

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
