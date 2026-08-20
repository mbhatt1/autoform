# Language support — measured

The README claims the CPG is "already a universal AST … *one* semantics and *one*
exporter cover all of them". Until this run, everything measured was Python (`cachetools`)
plus a five-function hand-written C file. This document is what happened when the
unmodified pipeline (`./autoform.sh`) was pointed at real code in the other languages.

Nothing here was tuned. No pipeline file was modified. Where a number is bad, it is
printed as measured.

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
| Python | yes | yes | yes | `.python` ✅ | 208 | 76% | 45 (19%) | 1.1% | **yes** (CPython) |
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
  two-function Kotlin file goes end to end fine, so this is the frontend on real Kotlin,
  not the corpus being exotic.
* **JavaScript at scale — does not render.** lodash exports 693 functions (25 MB of AST)
  and then `render_lean.py` dies:
  `RecursionError: maximum recursion depth exceeded while decoding a JSON object`.
  `json.load` in CPython recurses on nesting depth, and jssrc2cpg produces deeply nested
  expression trees. The exporter is fine; the renderer is the wall.
  `scripts/lang_matrix.py` raises the limit and walks iteratively, which is how the
  lodash row above was measured at all.
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
  evidence. This is the load-bearing fact of this document: the oracle that found every
  dialect bug in the project's history is only wired for two of the seven languages.

## Node kinds the exporter does not map

Holes by cause, per language — these are the CPG vocabulary items that exist but have no
Core translation. They are *not* the same set across languages, which is the first direct
evidence against "one node vocabulary".

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
exporter only handles the latter (plus `while`). That alone costs a large fraction of the
coverage in C, Java and Go.

`op:alloc` (166 holes in Java) is worth naming: constructor calls, i.e. essentially all
idiomatic Java object creation, are untranslated.

## Silent mistranslations found

These are the §12 failure mode: a construct that *looks* the same across languages and
means something different, producing a **wrong answer rather than a hole**. Each was
measured — Lean output from the generated module, real output from the real runtime.

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

This is exactly the `fmod(6, -9)` bug the README celebrates catching, re-entering through
the extension table. Verdict: **wrong**. The default should be a refusal, not Python.

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

So `===` is right by luck and `==` is wrong, and Core cannot tell them apart even in
principle — the distinction is erased before Core sees it. Verdict: **wrong**, and not
fixable inside the semantics; it needs an exporter change.

### 5. Java `long` and Go `int` are 64-bit; Core models them as 32-bit

`.java`/`.go` → `.cLike` → `c32Wrapv`. `Numeric.lean` *already defines* `java32`,
`java64` and `go64` configs — but `Dialect` has only two constructors (`python`,
`cLike`), so nothing can ever select them. They are dead code.

| input | real runtime | Core |
|---|---|---|
| Java `long a=2147483647L; a+1` | `2147483648` | **`-2147483648`** |
| Java `long m=100000L; m*m` | `10000000000` | **`1410065408`** |
| Go `a:=2147483647; a+1` | `2147483648` | **`-2147483648`** |
| Go `m:=100000; m*m` | `10000000000` | **`1410065408`** |

Note this is the *same* mistranslation §16 records finding for C (`mulbig(100000,100000)`
giving `1410065408` against `cc`) — except this time `1410065408` is the wrong one,
because Java `long` and Go `int` are 64-bit. Core has no types, so it cannot distinguish
Java `int` from Java `long` at all; whichever width it picks is wrong for the other.
Verdict: **wrong**.

### 6. Java string `+`, `==`: right answer, wrong reason

Under `.cLike`, `applyBinop` makes `"a" + "b"` a hole labelled
`str:pointer-arithmetic-not-modelled`, and `s == t` a hole labelled
`str:pointer-equality-not-modelled`. For C those labels are correct. For Java:

* `s == t` really *is* reference equality, so holing is conservative and defensible —
  though the label says "pointer", which is the right idea by accident.
* `s + t` really *is* concatenation and is completely ordinary Java. Holing it is a
  coverage loss, not a wrong answer.
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
  matched. Not a wrong value, but not a faithful one either.
* Go `5 / 0` → same `ZeroDivisionError`. Go *panics*, which is not a catchable exception
  in the same sense (`recover` only in a deferred call). Approximate.
* `Integer.MIN_VALUE / -1` → Core `-2147483648`. Java agrees. **Correct** ✅ (measured).
* Java `a << 32` and `a >>> k` → holes (`op:shiftLeft`, `op:arithmeticShiftRight` are not
  in the exporter's operator map). Java masks the shift count to 5 bits and `>>>` is a
  logical shift; `NumConfig.java32` models both correctly but is unreachable. As shipped
  these are holes, which is safe. **hole**.
* Go integer overflow is *defined* to wrap; Core wraps, but at the wrong width (item 5).
* JS `<<` coerces to int32 first; Core holes it. **hole**.

### 8. Predicted, unverified

* Java boxed `Integer` comparison: `Integer a=1000, b=1000; a==b` is `false` in Java
  (reference equality) but Core's `Val.beq` on two `.int`s gives `true`. Core has no
  boxing, so this is a wrong answer waiting for a corpus that boxes. Not measured because
  `op:alloc` holes most boxing paths first.
* Java `char` arithmetic (16-bit unsigned) under a 32-bit signed config.
* Go `&^` (and-not) and unsigned `uint` arithmetic under a signed config.

## Verdict

**"Universal" is aspirational, not currently true.** Precisely:

1. **The front end genuinely does generalize.** Five languages parsed, exported and
   type-checked without a single change to the exporter or the semantics, and Java —
   the biggest corpus at 669 functions — produced the *highest* hole-free rate of any
   language measured, 52%. That is real, and it is the strongest evidence the bet is
   sound. One node vocabulary really did absorb four new frontends.
2. **The back end does not.** There are two dialects for six languages. `.cLike` means
   "32-bit truncating C" and is applied unchanged to Java `long`, Go `int64`, and
   JavaScript doubles. Every arithmetic answer Core gives for Java `long`, Go `int` or
   any JS number of magnitude ≥ 2³¹ is wrong, silently, with no hole. `Numeric.lean`
   already contains the right configs; `Dialect` has no constructors to reach them.
3. **The safety net is Python-only.** The differential oracle — the single mechanism that
   found every dialect bug the project documents — runs CPython or `cc` and nothing else.
   For Java, Go, JS, TS and Kotlin it produces zero cases and says so quietly. So the
   four new languages are exactly the ones with *no* check that the semantics matches
   their runtime, which is why the mistranslations above had to be found by hand.
4. **Two languages fail outright on real code**: Kotlin (frontend crash, reported as
   silence) and JavaScript at scale (renderer `RecursionError`).
5. **A file-extension typo is a semantics change.** `.tsx` gets Python's floored modulo.
   The dialect is inferred from a lookup table with a silent default; a language not in
   the table does not fail, it gets Python.

An honest claim today would be: *"Python is supported and checked. C is supported and
partially checked. Java, Go, JavaScript and TypeScript parse, translate and type-check —
their arithmetic is known-wrong at 64-bit widths and for JS numbers, and nothing verifies
them against their runtimes. Kotlin does not work on real code."*

The cheapest thing that would change the verdict is not more front ends. It is
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
