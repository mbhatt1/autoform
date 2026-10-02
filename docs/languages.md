# Language support — measured

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
| TypeScript | `sindresorhus/p-queue` `source/*.ts` @ `9efde42` | 5 | real async library (re-exported 2026-10-02 from this revision, `provenance/ast-LangTS.json.prov.json`) |
| JavaScript | `sindresorhus/p-map` `index.js` @ `3f153f1` | 1 | real library, 285 lines (re-exported 2026-10-02 from this revision, `provenance/ast-LangJS.json.prov.json`) |
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
| Python | yes | yes | yes | `.python` ✅ | 209 | 80% | 99 (47%) | 0.8% | **yes** (CPython) |
| C | yes | yes | yes | `.cLike` ✅ | 59 | 17 (29%) | 8 (13%) | 11% | crashed (see below) |
| Java | yes | yes | yes | `.cLike` ⚠️ | 669 | 350 (52%) | 191 (28%) | 6% | **none** |
| Go | yes | yes | yes | `.cLike` ⚠️ | 83 | 21 (25%) | 6 (7%) | 4% | **none** |
| TypeScript | yes | yes | yes | `.javascript` ✅ | 82 | 46 (56%) | not re-measured | 3.1% | **Node, 55 cases** (`tests/test_jsnode_node.py`; not this corpus) |
| JavaScript | yes | yes | yes | `.javascript` ✅ | 14 | 6 (43%) | not re-measured | 2.9% | **Node, 55 cases** (as above) |
| JavaScript (lodash) | yes | **no** | n/a | `.cLike` ⚠️ | 693 | 419 (60%) | — | 1.8% | **none** |
| Kotlin (real repo) | **no** | n/a | n/a | n/a | — | — | — | — | **none** |
| Kotlin (toy) | yes | yes | yes | `.cLike` ⚠️ | 3 | 2 (66%) | 2 (66%) | 4% | **none** |
| `.tsx` / `.jsx` | yes | yes | yes | **`.python` ❌ WRONG** | — | — | — | — | none |

> **Dated correction (2026-10-02, item R, STRATEGY.md section 64).** The TypeScript and
> JavaScript rows were re-measured: both artifacts were re-exported with a real
> `jssrc2cpg` 4.0.606 (the old ones came from an unrecorded frontend: 86 and 14 functions,
> TS overload signatures exported as functions, `const f = () => ...` named `f`). Functions,
> hole-free and holes/nodes come from `python3 scripts/lang_matrix.py ast-LangJS.json
> ast-LangTS.json` (JS 14 functions, 6 hole-free, 31 holes over 1,061 nodes; TS 82, 46,
> 82 over 2,625); "Lean compiles" from `scripts/check_render.py --typecheck LangJS LangTS`.
> "Verifiable core" was not re-measured (it needs the ledger run). The dialect column is
> `.javascript` because `render_lean.py` has said so since `46c65fc`; the old `.cLike ⚠️`
> was stale.

Percentages are from the ledger the pipeline printed (`ledger-Lang*.json`);
`scripts/lang_matrix.py` recomputes them from the exported AST independently and agrees
to within the ledger's slightly different node-counting.

⚠️ = the dialect *is* in `render_lean.py`'s `DIALECT` map, but every non-Python language
maps to the single `.cLike` constructor, which is 32-bit truncating C. See below.

> **Dated correction (2026-10-02, at `46c65fc`).** The non-Python rows were measured at or
> before `16f7c88` (2026-08-20) and have not been re-run. The *Dialect inferred* column no
> longer describes the renderer for JS/TS: `Dialect` now has a third constructor,
> `.javascript`, and `render_lean.py` maps `.js .ts .tsx .jsx .mjs .cjs` to it. `.java`,
> `.kt` and `.go` still map to `.cLike`. An unknown extension is now a hard error
> (`infer_dialect` raises), not a silent `.python`. The Python row was regenerated from
> `ast-Cachetools.json` + `Autoform/Generated/Cachetools.lean` with
> `scripts/ledger.lean.tmpl` (26 holes over 5,574 nodes at `46c65fc`; 46 over 5,661 after
> the item-L re-export of `ast-Cachetools.json`, which is what the row now shows). Note that
> `scripts/lang_matrix.py` carries its own copy of the extension table, which still says
> `.js`/`.ts` → `cLike` and does not know `.cc`, so its *dialect* column is stale even
> though its counts are recomputed.

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

**Current status (2026-10-02, at `46c65fc`).** The items below are the original
measurements and are kept as recorded. Since then the semantics changed under several of
them. Each "Core now" entry is `#eval applyBinop <dialect> …` against the built
`Autoform.Lang.Core.Semantics` at that commit; the runtime column is copied from the
original measurement, not re-run.

| item | input | runtime | Core now | status |
|---|---|---|---|---|
| 1 | Python `0 or 5` | `5` | `int 5` | **fixed** (`Dialect.boolOpsAreValues`) |
| 1 | JS `2 && 3` | `3` | `int 3` | **fixed** |
| 2 | `.tsx`/`.jsx` dialect | — | `.javascript`; unknown extension is an error | **fixed** |
| 3 | JS `2147483647 + 1` | `2147483648` | `int 2147483648` | **fixed** (`.javascript` uses `NumConfig.python`) |
| 3 | JS `7 / 2` | `3.5` | `float 3.5` | **fixed** (`jsIntDiv`: inexact quotients go to IEEE binary64) |
| 3 | JS `5 / 0` | `Infinity` | `float +inf` | **fixed** (`jsIntDiv`; `5 % 0` is `NaN`) |
| 3 | JS `-7 % 3` | `-1` | `int (-1)` | **fixed** (`jsIntMod` truncates) |
| 3 | JS `-5.5 % 2.0` | `-1.5` (JS `%` truncates) | `-1.5` | **fixed** under `.javascript` (truncated `fmod`); `.cLike` float `%` still uses Python's floored `pyMod` |
| 4 | JS `1 == "1"` | `true` | `hole "js:==:cross-type-coercion"` | **hole** (was `bool false`): JS `==` is now loose equality, exact on same-type operands, a hole across types except `null`/`undefined` |
| 4 | JS `1 === "1"` | `false` | `bool false` | **fixed** — `===`/`!==` are Core operators of their own, recovered by the exporter from source text (jssrc2cpg erases them) |
| 4 | JS `null == 0` | `false` | `bool false` | **fixed** (was `true` by reading the exporter, not measured on a JS CPG: `pointerNullTest` keys on `cLikeFile`, which includes `.js`/`.ts`, and rewrote `x == null` to `x in (None, 0)`). **Measured on a real JS CPG in item R:** the old exporter already emitted `==` for `x == null`, so `0 == null`, `"" == null`, `false == null` were `false` (`tests/fixtures/jsnode`, 4 cases) |
| 4 | JS `null === undefined` | `false` | `bool false` | **fixed** in item R: `null` is `Val.jsnull`, `undefined` is `Val.unit` (was the hole `js:===:null-vs-undefined`) |
| 4 | JS `0 ?? 5`, `"" ?? "d"`, `false ?? 5` | `0`, `""`, `false` | same | **fixed** in item R (was `5`, `"d"`, `5`: jssrc2cpg lowers `??` to `<operator>.logicalOr`, so it exported as `\|\|`; silent wrong answer). Lowered by the exporter to `a == null ? b : a` |
| 4 | JS `x === 'a'` (single-quoted literal) | — | `bool` | **fixed** in item R: the old token recovery returned `op:js-token-unrecovered` for every comparison with a single-quoted string, found only by running on a real CPG |
| 7 | JS `1 << 32`, `-1 >>> 0`, `~2147483648` | `1`, `4294967295`, `2147483647` | same | **fixed** (`jsBitwise`/`jsBitNot`: ToInt32/ToUint32; operands beyond 2^53 are a hole). Was `4294967296`, a `ub` hole, `-2147483649` |
| 5 | Java `long` / Go `int` | 64-bit | 32-bit `.cLike` | **still wrong** — `.java`/`.go` still map to `.cLike` |
| 6 | JS `"a" + "b"` | `"ab"` | `str "ab"` | **fixed** (`Dialect.stringsAreValues`) |

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

**Status (2026-10-02): fixed or holed, in both halves.** jssrc2cpg v4.0.606 still maps
`==`/`===` to `<operator>.equals` and `!=`/`!==` to `<operator>.notEquals` (and, worse,
`>>`/`>>>` both to `<operator>.arithmeticShiftRight`; read from
`AstForExpressionsCreator.astForBinaryExpression` at tag `v4.0.606`). The exporter now
recovers the token from the call's source span (`jsAmbiguousBinop` in
`cartographer/export_ast.sc`) and emits `"==="`/`"!=="`/`"=="`/`"!="`/`">>"`/`">>>"`; a
span it cannot parse is the hole `op:js-token-unrecovered:<op>`. In Core (`jsEqE` in
`Semantics.lean`), under `.javascript`:

| input | Node | Core |
|---|---|---|
| `1 === "1"` / `1 !== "1"` | `false` / `true` | `false` / `true` ✅ |
| `1 == "1"`, `0 == false`, `[1] == 1` | `true` | hole `js:==:cross-type-coercion` |
| `null == undefined`, `null == 0` | `true`, `false` | `true`, `false` ✅ (`null` is `Val.jsnull`, `undefined` is `Val.unit`; item R) |
| `null === undefined`, `null === null` | `false`, `true` | `false`, `true` ✅ (was the hole `js:===:null-vs-undefined`; item R) |
| `NaN === NaN`, `-0 === 0`, `1 === 1.0` | `false`, `true`, `true` | same ✅ |
| `o == o`, `[1] == [1]` (heap objects) | `true`, `false` | same ✅ (identity, not Python's `__eq__`) |

Every row is an `example … := rfl` or `#eval` in `Semantics.lean`; the Node column is
from `node -e` (v22). **Verified end to end in item R (2026-10-02), see "4b" below.** The paragraph that stood
here said jssrc2cpg was not installed, that the exporter change had only been run on 15
synthetic spans, and that `ast-LangJS.json` was not re-exported. All three are no longer
true: jssrc2cpg 4.0.606 was fetched, a real JS CPG was exported, and both JS/TS artifacts
were regenerated.

### 4b. Running the JS exporter on a real jssrc2cpg CPG (item R)

**Obtaining the frontend.** `io.joern:jssrc2cpg_3:4.0.606` is on Maven Central (a 700 KB
jar; the other jars it needs are already in the Joern distribution). It shells out to
`astgen`, whose pinned version is in the jar (`application.conf`: `astgen_version:
"3.47.0"`). `joernio/astgen` has moved to `joernio/astgen-monorepo`; the binary is the
release asset `astgen-linux` of tag `javascript-astgen/v3.47.0`, selected with
`ASTGEN_BIN`. `JoernParse --language jssrc` also wants a `js2cpg.sh` in the installation
root; a two-line wrapper that strips the `-J` flags and runs `io.joern.jssrc2cpg.Main`
does it. `provenance/ast-LangJS.json.prov.json` records the exact command and the
astgen digest.

**What the real runs found** (a purpose-written fixture, `tests/fixtures/jsnode/
jsnode_cases.js`, 55 functions each run under Node `v22.22.2` and under Core on the
exporter's real output; `Autoform/JsNode.lean`, `tests/test_jsnode_node.py`):

| finding | measured |
|---|---|
| the token recovery works on real CPGs | `===`, `!==`, `==`, `!=`, `>>`, `>>>` all recovered from the real call spans; p-map has 21 `===` and no `==`, p-queue 34 `===` and 9 `!==` (counts of the re-exported ASTs). The committed `ast-LangJS.json` had 21 `"=="` for those 21 `===`: read as loose equality, which was exact on same-type operands, so no wrong answer, but the strictness was lost |
| it did **not** work for single-quoted strings | jssrc2cpg re-quotes every string literal as `"..."`, so the operand text no longer occurs in the expression text and `typeof x === 'string'` was `op:js-token-unrecovered:equals`. p-queue had 4 such holes (`typeof options.intervalCap === 'number'` ...), the fixture 3. Fixed: the span comparison folds the quote character |
| `??` is erased | `0 ?? 5` is exported as `0 \|\| 5`. On the fixture, the 4dc1f19 exporter against Node: 15 of 55 cases differ, 11 silent wrong answers (7 are `??`) and 4 holes. The other 4 "wrong" ones only differ because Core now answers `===` on two `unit`s; under the old Core they were holes |
| `undefined`, `NaN`, `Infinity` are unbound names | the exporter emitted `name "undefined"`, and Core reads any unbound name as `Val.unit` outside Python (`Ctx.unboundName`), so `NaN` was `undefined`/`null`. jssrc2cpg gives every undeclared identifier a synthetic `Local`, so "has a `Local`" says nothing about shadowing. Now `undefined` is `unit`, `NaN`/`Infinity` are the IEEE values, unless some parameter or assignment in the CPG rebinds the name |
| `a ??= b` | exported as the hole `op:notNullAssert` (jssrc2cpg maps it to the TS non-null operator); `a \|\|= b` as an unmodelled call. Both are holes, not wrong answers; unchanged |
| sibling calls | `f(x)` where `f` is another top-level function is the hole `call:f`: `Ctx.resolve` matches the suffix `.f`, and jssrc2cpg names functions `file.js::program:f`. Not changed here; it is why the fixture's cases are zero-argument and inline |

**`??`.** Not a new Core operator (that would put a third arm into `evalExpr`'s short-circuit
`if`, which `Refine.lean`, `FuelMono.lean` and `Overflow.lean` each case-split on): the
exporter recovers the token (`jsLogicalOr`) and lowers `a ?? b` to `cond (a == null) b a`.
`==` against the null literal is true exactly for `null` and `undefined` and false for
`0`, `""`, `false` and objects, which is the definition of `??`. `a` is evaluated once
(a temp when it is impure), `b` only when `a` is nullish. A `logicalOr` whose text contains
`??` and whose token cannot be recovered is the hole `op:js-token-unrecovered:logicalOr`
(p-queue has one: `options.id ?? (this.#idAssigner++).toString()`).

**`null` versus `undefined`.** Done: `Val.jsnull` and `Lit.jsnull`. Under `.javascript`,
`.unit` is `undefined` (what a missing return, a missing property and an unassigned
variable already evaluated to) and the source literal `null` is `.jsnull`. `jsEqE`: both are
loosely equal to each other and strictly equal only to themselves. The ripple was small:
`Val.kind`, `Val.identical`, `Val.beq`, `Val.truthy`, `Lit.toVal`, `evalExpr`'s literal
arm and one case split in `FuelMono.lean` (`| jsnull => exact hy`); `Refine`, `Overflow`
and every importer built unchanged. No theorem statement changed.

### 5. Java `long` and Go `int` are 64-bit; Core models them as 32-bit

`.java`/`.go` → `.cLike` → `c32Wrapv`. `Numeric.lean` *already defines* `java32`,
`java64` and `go64` configs — but `Dialect` has only two constructors (`python`,
`cLike`), so nothing can select them. They are dead code.

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
* JS `<<` coerces to int32 first. *Correction (2026-10-02):* this line said Core holes
  it; it did not — `.javascript` used `NumConfig.python`, so `1 << 32` was `4294967296`
  (Node: `1`) and `-1 >>> 0` a `ub` hole (Node: `4294967295`). Now `jsBitwise`
  applies ToInt32/ToUint32 and masks the count to 5 bits; `~` likewise (`jsBitNot`).
  Float operands (`1.5 | 0`) and integers beyond 2^53 are holes. **fixed**.

### 8. Predicted, unverified

* Java boxed `Integer` comparison: `Integer a=1000, b=1000; a==b` is `false` in Java
  (reference equality) but Core's `Val.beq` on two `.int`s gives `true`. Core has no
  boxing, so this is a wrong answer waiting for a corpus that boxes. Not measured because
  `op:alloc` holes most boxing paths first.
* Java `char` arithmetic (16-bit unsigned) under a 32-bit signed config.
* Go `&^` (and-not) and unsigned `uint` arithmetic under a signed config.

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
   the table does not fail, it gets Python. *(Fixed since: see the status table above.
   Item 2 of this verdict now applies to Java and Go, and JS integer `/` and `%` are wrong
   in a different way; items 3 and 4 have not been re-measured.)*

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
