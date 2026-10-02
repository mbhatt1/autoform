# Language support — measured

The README claims the CPG is "already a universal AST … *one* semantics and *one*
exporter cover all of them". This document records what the pipeline (`./autoform.sh`)
did when pointed at real code in the other languages.

**How to read this page.** Part 1 is the **current state**, checked on 2026-10-02 at
`9639df0`: every figure and status in it was re-derived that day from the code, the
committed ASTs, or a command (each says which), or is marked *not re-measured*. Part 2 is
the **historical record**: the measurements as first taken (2026-08-20, at `16f7c88`), kept
as recorded so the trail is auditable, with every section marked *superseded* and
pointing at the section of `STRATEGY.md` that changed it. Do not quote a figure from Part 2
as current. Where a document and an artifact disagree, the artifact wins.

# Part 1 — Current state (2026-10-02, at `9639df0`)

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

Joern 4.0.606 (`joern-version`). `jssrc2cpg`, `gosrc2cpg`, `javasrc2cpg` and `kotlin2cpg`
4.0.606 are all usable: the JS/TS (§65), Go and Kotlin (§66) and Java (§63) frontends were
each run for real in this project (the JS/TS, Go and Kotlin ASTs carry provenance in
`provenance/`). `ast-LangJava.json` and `ast-LangC.json` are in `provenance/unattributed.json`:
their frontend, revision and exporter are not recorded, and they predate the typed integer
operators (no typed operator tags in them; see the matrix). Binaries (`ghidra2cpg`), C#, PHP,
Ruby, Rust and Swift were **not tested**.

## Support matrix (current)

Functions, hole-free and holes/nodes are `python3 scripts/lang_matrix.py ast-Lang*.json`
on the committed ASTs, run 2026-10-02 (Python: the ledger, see below). "Verifiable core" is
*not re-measured* for every non-Python row except where a value is quoted as recorded: it
needs a ledger run (`ledger-Lang*.json` are not committed), which was not repeated.
"Dialect" is `render_lean.py`'s `DIALECT` map (read from the file; `tests/test_lang_matrix.py`
checks `lang_matrix.py`'s copy against it). "Integer ops" says how the exporter names integer
`+ - * / % << >>`.

| Language | Dialect | Functions | Hole-free | Verifiable core | Holes / nodes | Integer ops | Differential oracle |
|---|---|---|---|---|---|---|---|
| Python (`cachetools`) | `.python` | 209 | 80% (168) | 98 (47%) | 0.8% (46 / 5,677) | Python semantics: `/` is true division, `//` floors, `bool` is an `int` (§64) | **CPython**: 42 functions compared, 220/220 agree, 0 divergences (STRATEGY §57, not re-run here) |
| C (`sds`) | `.cLike` | 59 | 29% (17) | 13% (8), as recorded 2026-08-20, not re-measured | 8.8% (171 / 1,948) | **untyped** in this AST (32-bit wrapping): the committed AST predates §63. A re-export would carry `*:i64`-style tags | `cc` fixtures: `cintwidth` 23 cases (§63), `cboolint`, `c_address`. The `sds` corpus-level run is not re-run (see "Open items") |
| Java (`gson/internal`) | `.cLike` | 669 | 52% (350) | 28% (191), as recorded, not re-measured | 5.5% (678 / 12,330) | **untyped** in this AST (predates §63); the exporter now emits `+:j32`/`*:j64` | `java`: `javaintwidth` fixture, 22 cases agree (§63; `tests/test_javaintwidth_java.py` passed 2026-10-02) |
| Go (`envconfig`) | `.cLike` | 82 | 24% (20) | not re-measured | 4.1% (232 / 5,653) | typed (`*:g64`, `-:w08`; 5 tagged operators in the AST, 2 `op:int:unresolved-type` holes) | `go` 1.24: `gointwidth` 56 cases, 55 agree + 1 hole (§66; test passed 2026-10-02) |
| TypeScript (`p-queue`) | `.javascript` | 82 | 56% (46) | not re-measured | 3.1% (82 / 2,625) | JS Number semantics (`jsIntDiv`, `jsBitwise`) | **Node**: `jsnode` fixture, 55 cases (`tests/test_jsnode_node.py`, passed 2026-10-02; not this corpus) |
| JavaScript (`p-map`) | `.javascript` | 14 | 43% (6) | not re-measured | 2.9% (31 / 1,061) | as TypeScript | Node, as above |
| Kotlin (toy) | `.cLike` | 3 | 67% (2) | not re-measured | 3.4% (2 / 58) | typed (`*:k64`, `-:q32`; 3 tagged operators in the AST) | Kotlin compiler 2.3.21: `kotlinintwidth` 61/61 (§66; the pytest is **skipped** here, no Kotlin compiler on PATH, so not re-run by this edit) |
| JavaScript (lodash) | `.javascript` (by extension) | 693, as recorded | 60% (419), as recorded | — | 1.8%, as recorded | — | none. Not re-measured: no lodash AST is committed |
| Kotlin (real repo) | n/a | — | — | — | — | — | none: the pipeline does not complete (see "Open items") |
| `.tsx` / `.jsx` | `.javascript` | — | — | — | — | — | covered by the JS fixture's dialect only |

The Python row is the ledger's population (`ledger-Cachetools.json`, regenerated and checked
by `scripts/check_docs.py`): 209 functions, 168 hole-free, 98 verifiable core, 46 holes over
5,677 nodes. `lang_matrix.py` on `ast-Cachetools.json` counts a different population
(209 functions, 196 hole-free = 94%, 16 holes over 7,538 nodes): the 30-hole difference was
**not** investigated here (the neutral AST evidently does not contain every hole the ledger
counts). Likewise the C figure moved from 11% recorded (ledger) to 8.8% (`lang_matrix.py`)
and Java from 6% to 5.5%; the two tools are not guaranteed to agree, and the old statement
that they agree "to within node-counting" is withdrawn.

**Dialects.** `Dialect` has three constructors: `.python`, `.cLike`, `.javascript`
(`Autoform/Lang/Core/Syntax.lean`). `render_lean.py` maps `.py` to `.python`;
`.js .ts .tsx .jsx .mjs .cjs` to `.javascript`; `.c .h .cpp .cc .cxx .hh .hpp .java .kt .go`
to `.cLike`. An unknown extension is a hard error (`infer_dialect` raises `SystemExit`), not a
silent Python default. Java, Go and Kotlin share the `.cLike` dialect for everything the
typed integer operators do not cover: e.g. `"a" + "b"` is the hole
`str:pointer-arithmetic-not-modelled` and string `==` the hole
`str:pointer-equality-not-modelled` (both evaluated 2026-10-02), correct for C's pointers, a
coverage loss for Java/Go/Kotlin strings.

**Typed integer operators** (`Autoform/Lang/Core/TypedInt.lean`; STRATEGY §63 C and Java,
§66 Go and Kotlin). The exporter names the operand type inside the operator (C `*:i64`,
`>>:u32`; Java `+:j32`/`*:j64`; Go `g08..g64` signed and `w08..w64` unsigned; Kotlin
`k32/k64` and `q32/q64`); a type it cannot resolve is the hole `op:int:unresolved-type`.
An **untyped** `.cLike` operator still means 32-bit wrapping C. Evaluated 2026-10-02
(`#eval applyBinop .cLike ...`): `"*:j64" 100000 100000` = 10000000000, `"*:g64"` and
`"*:k64"` the same, `"+:j64" 2147483647 1` = 2147483648, `"&^:w08" 255 15` = 240,
`"/:j32" 5 0` raises `ArithmeticException`, `"/:g64" 5 0` raises
`panic: integer divide by zero`, `"/:j32" MIN (-1)` = MIN, `">>:j32" (-16) 1` = -8,
`"<<:j32" 1 32` = 1, `">>>:j32" (-16) 28` = 15; the untyped `"*" 100000 100000` is still
1410065408.

### Holes by cause (current)

`lang_matrix.py` on the committed ASTs, 2026-10-02: the top causes per corpus (the tool
prints the top 15; those are listed).

| Language | Top hole causes |
|---|---|
| C (old AST) | `op:indirection` 28, `op:cast` 18, `control:SWITCH` 14, `assign:lhs:indirectIndexAccess` 12, `op:indirectIndexAccess` 12, `assign:lhs:indirection` 12, `cstr:address-equality` 11, `op:postIncrement` 11, `op:postDecrement` 8, `control:FOR` 7, `op:sizeOf` 5, `control:GOTO` 5, `op:arrayInitializer` 5 |
| Java (old AST) | `op:alloc` 166, `control:THROW` 125, `op:cast` 123, `op:instanceOf` 90, `op:arrayInitializer` 43, `control:FOR` 30, `expr:BLOCK-impure` 20, `control:SWITCH` 15, `op:postIncrement` 15, `op:sizeOf` 13, `op:assignmentPlus` 7, `control:TRY-multiCatch` 4 |
| Go | `stmt:empty-ast-children` 134, `stmt:IMPORT` 39, `assign:arity` 16 (multi-return `a, b := f()`), `lit:unquoted` 15, `op:indirection:opaque-type` 12, `expr:empty-block` 4, `control:SWITCH` 2, `call:no-callee-name` 2, `op:int:unresolved-type` 2 |
| TypeScript (`p-queue`) | `op:assignment` 22, `op:notNullAssert` 12, `control:THROW` 10, `op:alloc:ctor-unresolved-class` 7, `op:await` 7, `expr:BLOCK-prelude` 6, `op:instanceOf` 5, `op:iterator` 3, `expr:BLOCK-impure` 2, `op:spread` 2, `op:void` 2 |
| JavaScript (`p-map`) | `op:await` 9, `control:THROW` 8, `op:void` 6, `op:alloc:ctor-unresolved-class` 2, `op:instanceOf` 2 |
| Kotlin (toy) | `stmt:METHOD` 2 |
| JavaScript (lodash), as recorded 2026-08-20 on an AST no longer committed | `op:assignment` 111, `op:instanceOf` 100, `op:preIncrement` 91, `expr:BLOCK-impure` 44, `op:postIncrement` 44, `op:alloc` 27, `op:and` 23, `control:THROW` 16, `op:iterator` 6 |

The sets differ across languages, which remains direct evidence against "one node
vocabulary". `control:FOR` is a hole in the old C and Java ASTs (7 and 30); the current Go AST
has one `control:FOR:elided-clause`. The exporter was not re-run on C or Java for this table,
so whether `control:FOR` is still a hole on a fresh C/Java export is **not re-measured**.

## Silent mistranslations: current status

These are the §12 failure mode: a construct that looks the same across languages and means
something different, producing a **wrong answer rather than a hole**. Each "Core now" entry
was re-evaluated on 2026-10-02 with `#eval applyBinop <dialect> ...` against the built
`Autoform.Lang.Core.Semantics` at `9639df0`; the runtime column is copied from the original
measurements (Part 2) except where a fixture test is named. The numbered sections in Part 2
give the original measurements.

| item | input | runtime | Core now | status |
|---|---|---|---|---|
| 1 | Python `0 or 5` | `5` | `int 5` (as `\|\|` under `.python`; `applyBinop .python "or"` is itself the hole `binop:or`, the short-circuit lives in `evalExpr`) | **fixed** (`Dialect.boolOpsAreValues`) |
| 1 | JS `2 && 3`, `0 \|\| 5` | `3`, `5` | `int 3`, `int 5` | **fixed** |
| 2 | `.tsx`/`.jsx` dialect | — | `.javascript`; unknown extension is an error | **fixed** |
| 3 | JS `2147483647 + 1` | `2147483648` | `int 2147483648` | **fixed** (`.javascript` uses `NumConfig.python`) |
| 3 | JS `7 / 2` | `3.5` | `float 3.5` | **fixed** (`jsIntDiv`: inexact quotients go to IEEE binary64) |
| 3 | JS `5 / 0` | `Infinity` | `float +inf` | **fixed** (`jsIntDiv`; `5 % 0` is `NaN`) |
| 3 | JS `-7 % 3` | `-1` | `int (-1)` | **fixed** (`jsIntMod` truncates) |
| 3 | JS `-5.5 % 2.0` | `-1.5` (JS `%` truncates) | `-1.5` | **fixed** under `.javascript` and, since the `.cLike` arm changed to `fmod`, under `.cLike` too (both give `-1.5`; `.python` gives `0.5`, correct for Python) |
| 4 | JS `1 == "1"` | `true` | `hole "js:==:cross-type-coercion"` | **hole** (was `bool false`): JS `==` is now loose equality, exact on same-type operands, a hole across types except `null`/`undefined` |
| 4 | JS `1 === "1"` | `false` | `bool false` | **fixed** — `===`/`!==` are Core operators of their own, recovered by the exporter from source text (jssrc2cpg erases them) |
| 4 | JS `null == 0` | `false` | `bool false` | **fixed** (`null == 0` is `false`, `null == undefined` is `true`). History: the old `true` was inferred from reading the exporter, not measured on a JS CPG; item R measured the old exporter on a real CPG and it already emitted `==` for `x == null` (`tests/fixtures/jsnode`, 4 cases) |
| 4 | JS `null === undefined` | `false` | `bool false` | **fixed** in item R: `null` is `Val.jsnull`, `undefined` is `Val.unit` (was the hole `js:===:null-vs-undefined`) |
| 4 | JS `0 ?? 5`, `"" ?? "d"`, `false ?? 5` | `0`, `""`, `false` | same | **fixed** in item R (was `5`, `"d"`, `5`: jssrc2cpg lowers `??` to `<operator>.logicalOr`, so it exported as `\|\|`; silent wrong answer). Lowered by the exporter to `a == null ? b : a` |
| 4 | JS `x === 'a'` (single-quoted literal) | — | `bool` | **fixed** in item R: the old token recovery returned `op:js-token-unrecovered` for every comparison with a single-quoted string, found only by running on a real CPG |
| 7 | JS `1 << 32`, `-1 >>> 0`, `~2147483648` | `1`, `4294967295`, `2147483647` | same | **fixed** (`jsBitwise`/`jsBitNot`: ToInt32/ToUint32; operands beyond 2^53 are a hole). Was `4294967296`, a `ub` hole, `-2147483649` |
| 5 | Java `long` / Go `int` / Kotlin `Long` | 64-bit | `10000000000` for `100000 * 100000` through `*:j64`, `*:g64`, `*:k64` | **fixed** — Java in §63, Go and Kotlin in §66: the exporter names the operand type in the operator; the dialect is still `.cLike`. The committed `ast-LangJava.json` / `ast-LangC.json` predate this and still hold untyped operators; fixtures `javaintwidth` (22), `gointwidth` (56), `kotlinintwidth` (61) are checked against the real runtimes |
| 6 | JS `"a" + "b"` | `"ab"` | `str "ab"` | **fixed** (`Dialect.stringsAreValues`); `1 + "1"` is still the hole `binop:+` (safe, not `"11"`) |
| 6 | Java/Go/Kotlin `"a" + "b"`, `s == t` | `"ab"`; contents/reference | hole `str:pointer-arithmetic-not-modelled`, hole `str:pointer-equality-not-modelled` | **hole, unchanged** (safe, not wrong; a coverage loss for Java/Go/Kotlin strings) |
| 7 | Java `5 / 0`, `MIN / -1`, `1 << 32`, `-16 >>> 28` | `ArithmeticException`, `MIN`, `1`, `15` | `exn ArithmeticException` (`/:j32`), `MIN`, `1` (`<<:j32`), `15` (`>>>:j32`) | **fixed** under typed operators (was `ZeroDivisionError` and shift holes); an untyped `/` by zero is still `ZeroDivisionError` |
| 7 | Go `5 / 0` | panic | `exn "panic: integer divide by zero"` (`/:g64`) | **modelled as an exception**; `recover` semantics are not modelled |
| 8 | Go `&^`, unsigned arithmetic | AND NOT, wraps at width | `"&^:w08" 255 15` = 240; `w08..w64` tags | **fixed** (§66) |
| 8 | Java `char` arithmetic | promotes to `int`; compound assignment and `++` narrow to 16-bit unsigned | exporter: `char` unboxes to `int`, and `x += e`, `x++` narrow via `castObj((false, 16))` (read from `export_ast.sc`); fixture case `case_char_increment` (`char c = 65535; c++`) is one of the 22 `javaintwidth` cases that agree with `java` | **fixed for arithmetic and compound stores**. An explicit `(char)` cast still holes (`op:cast:char-signedness` in the shared cast arm, `export_ast.sc` line 9845; STRATEGY §63 "Not done"): **not re-run** on a fresh Java export |
| 8 | Java boxed `Integer a=1000, b=1000; a==b` | `false` (reference equality) | `Val.beq` on two `int`s would be `true` | **still predicted, never measured**: Core has no boxing, and `op:alloc` holes most boxing paths first |

Items 2 and 5 of the original list (the `.tsx` dialect, 64-bit widths) are the ones the
original verdict called the most serious; both are closed. The JS rows are additionally
checked against Node by `tests/fixtures/jsnode` (55 cases, `tests/test_jsnode_node.py`).

## Open items (current)

* **Kotlin on real code does not complete.** `kotlin2cpg` 4.0.606 parses `kotlinx-datetime`
  `core/common/src` and writes a CPG, but Joern's default `ReachingDefPass` crashes
  (`key not found: MethodRef`) before the exporter runs (STRATEGY §66 (a)); the Kotlin width
  fix is exercised on fixtures only. `autoform.sh` line 76 still redirects joern-parse output
  to `/dev/null` under `set -euo pipefail`, so a failed parse stops the run with no message
  (read from the script; not re-run here).
* **Go**: package-level constants (`field:mask:non-object`), named integer types from other
  packages, `1 << n` with an untyped constant (`op:int:untyped-constant-shift`), Go `int`
  under `ilp32` not exercised (§66 "Not done").
* **Kotlin**: `typealias` and `Char` arithmetic are holes (§66 (c)).
* **Java**: explicit `(char)` casts hole (above). Boxed `Integer ==` unmeasured.
* **Float arithmetic** is untouched by the typed operators for Java, Go and Kotlin
  (§66 (d)).
* **Committed C and Java ASTs are stale relative to the exporter** (untyped operators, no
  provenance). Their rows above are old exports; a re-export would change function and
  hole counts (SQLite lost 211 hole-free functions to `op:int:unresolved-type` in §63).
* **Differential oracle.** `scripts/differential.py` now chooses its runtime from the
  corpus language (`LANG_BY_EXT`, `TOOLCHAIN`; an unknown language is refused, not defaulted
  to CPython) and has `java_backend`, `go_backend` and `node_backend`; Kotlin reports
  `UNSUPPORTED: no kotlinc`. These corpus-level backends were **not run** on the `gson`,
  `envconfig`, `p-queue` or `p-map` corpora for this edit, so no corpus-level agreement
  figure exists for them; the evidence for those languages is the fixtures in the matrix.
* **C `sds` differential run.** The 2026-08-20 run segfaulted (the harness called `char *`
  functions with small integers). `c_runtime` now takes the extracted signatures and
  `call_in_child` forks each call; whether the `sds` run still crashes was not re-run (the
  `sds` sources are not in this checkout).
* **JavaScript at scale (lodash).** The 2026-08-20 `RecursionError` was in `json.load` inside
  `render_lean.py`. `render_lean.py` now raises the recursion limit to 300,000 and renders on
  a thread with a large stack (`main`, line 768). That this fixes lodash was **not
  re-measured** (no lodash AST here); `lang_matrix.py` still reads it iteratively.
* **Verifiable core** for every non-Python row: not re-measured.

## Verdict (current, 2026-10-02)

**"Universal" is still aspirational, but the specific failures the original verdict named
are closed.** Precisely:

1. **The front end generalizes.** Python, C, Java, Go, JavaScript, TypeScript and a Kotlin
   toy have committed ASTs from five Joern frontends (Java: 669 functions, 52% hole-free,
   the highest hole-free rate among the non-Python rows). Real Kotlin does not complete
   (Open items).
2. **The back end has three dialects and typed integer operators.** `.cLike` is no longer
   applied unchanged to Java `long`, Go `int` or JavaScript numbers: JS has its own
   `.javascript` dialect (own division, remainder, bitwise, equality and `null`/`undefined`
   rules, §61/§65), and C, Java, Go and Kotlin integer operators carry their operand type
   (§63, §66). What is still approximate is everything outside integer arithmetic under
   `.cLike` for Java/Go/Kotlin: strings (holes), floats (not typed), and the language
   features in the hole table.
3. **The safety net is no longer Python-only, but it is fixture-sized.** Integer
   semantics for C, Java, Go, Kotlin and JavaScript are each pinned against the real
   runtime (`cc`, `java`, `go`, the Kotlin compiler, Node) on 23, 22, 56, 61 and 55 cases.
   Corpus-level differential agreement is recorded for Python only (`cachetools`, 42
   functions compared). The other languages' real-code rows have no corpus-level runtime
   comparison.
4. **Real-code failures that remain:** Kotlin (frontend overlay crash, reported as
   silence); JavaScript at scale is not re-measured.
5. **A file-extension typo is an error**, not a semantics change (`infer_dialect`).

The accurate claim today: *Python is supported and checked against CPython at corpus
scale. C, Java, Go, Kotlin and JavaScript/TypeScript parse and translate; their integer
arithmetic is checked against their real runtimes on fixtures (not on the corpora in the
matrix), and the committed C and Java corpus ASTs predate the typed operators. Kotlin does
not work on real code.*

# Part 2 — Historical record (measured 2026-08-20 at `16f7c88`; **superseded**, kept as recorded)

> **Superseded.** Everything below was measured at or before `16f7c88` (2026-08-20), with the
> dated corrections inserted later. Where a section's text conflicts with Part 1 or with
> `STRATEGY.md` §57-66, Part 1 is right. Each section carries its own marker.

## Original support matrix (as recorded; **superseded** by Part 1, "Support matrix (current)")

| Language | Parses | Translates | Lean compiles | Dialect inferred | Functions | Hole-free | Verifiable core | Holes / nodes | Differential oracle |
|---|---|---|---|---|---|---|---|---|---|
| Python | yes | yes | yes | `.python` ✅ | 209 | 80% | 99 (47%; the ledger now says 98) | 0.8% | **yes** (CPython) |
| C | yes | yes | yes | `.cLike` ✅ | 59 | 17 (29%) | 8 (13%) | 11% (8.8% by `lang_matrix.py` now) | crashed (see below; not re-run) |
| Java | yes | yes | yes | `.cLike` ⚠️ (as recorded) | 669 | 350 (52%) | 191 (28%) | 6% | **none** as recorded (a `java`-checked integer fixture exists since §63) |
| Go | yes | yes | yes | `.cLike` ⚠️ (as recorded) | 82 | 20 (24%) | not re-measured | 4.1% | **none** as recorded (a `go`-checked integer fixture exists since §66) |
| TypeScript | yes | yes | yes | `.javascript` ✅ | 82 | 46 (56%) | not re-measured | 3.1% | **Node, 55 cases** (`tests/test_jsnode_node.py`; not this corpus) |
| JavaScript | yes | yes | yes | `.javascript` ✅ | 14 | 6 (43%) | not re-measured | 2.9% | **Node, 55 cases** (as above) |
| JavaScript (lodash) | yes | **no** | n/a | `.cLike` ⚠️ (as recorded; `.javascript` by extension now) | 693 | 419 (60%) | — | 1.8% | **none** |
| Kotlin (real repo) | **no** | n/a | n/a | n/a | — | — | — | — | **none** |
| Kotlin (toy) | yes | yes | yes | `.cLike` ⚠️ (as recorded) | 3 | 2 (67%) | not re-measured | 3.4% | **none** as recorded (a Kotlin-compiler-checked integer fixture exists since §66) |
| `.tsx` / `.jsx` | yes | yes | yes | **`.python` ❌ WRONG** (as recorded; now `.javascript`, §61) | — | — | — | — | none |

> **Dated correction (2026-10-02, item R, STRATEGY.md section 65).** The TypeScript and
> JavaScript rows were re-measured: both artifacts were re-exported with a real
> `jssrc2cpg` 4.0.606 (the old ones came from an unrecorded frontend: 86 and 14 functions,
> TS overload signatures exported as functions, `const f = () => ...` named `f`). Functions,
> hole-free and holes/nodes come from `python3 scripts/lang_matrix.py ast-LangJS.json
> ast-LangTS.json` (JS 14 functions, 6 hole-free, 31 holes over 1,061 nodes; TS 82, 46,
> 82 over 2,625); "Lean compiles" from `scripts/check_render.py --typecheck LangJS LangTS`.
> "Verifiable core" was not re-measured (it needs the ledger run). The dialect column is
> `.javascript` because `render_lean.py` has said so since `46c65fc`; the old `.cLike ⚠️`
> was stale.

**Go and Kotlin rows re-exported (item S, STRATEGY.md §66).** `ast-LangGo.json` and
`ast-LangKt.json` were re-exported with provenance (`provenance/ast-LangGo.json.prov.json`,
`ast-LangKt.json.prov.json`): Go from `kelseyhightower/envconfig` at `7834011` (82
functions; the earlier artifact, 83 functions, came from an unrecorded revision), the Kotlin
toy from `tests/fixtures/langkt/T.kt`. Their Functions / Hole-free / Holes-per-node cells
are `scripts/lang_matrix.py ast-LangGo.json ast-LangKt.json` on the new files; the
*Verifiable core* cells were not re-measured (they need the ledger, which was not re-run),
and the Go hole-cause row below is that tool's count for the new file.

Percentages are from the ledger the pipeline printed (`ledger-Lang*.json`);
`scripts/lang_matrix.py` recomputes them from the exported AST independently and agrees
to within the ledger's slightly different node-counting.

⚠️ = the dialect *is* in `render_lean.py`'s `DIALECT` map, but every non-Python language
mapped (as recorded, 2026-08-20) to the single `.cLike` constructor, which was 32-bit truncating C. **Superseded:** there are now three dialects and typed integer operators; see Part 1.

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

### Failures observed, verbatim (as recorded 2026-08-20; **superseded in part**, current status in Part 1 "Open items")

* **Kotlin, real repo — does not parse.** `joern-parse` exits `1`:
  `ReachingDefPass failed … java.util.NoSuchElementException: key not found: MethodRef`.
  `autoform.sh` runs under `set -e` with joern's output redirected to `/dev/null`, so the
  run stops after `==> [1/6] parsing` printing **no error at all**. A CPG file is still
  written; running `export_ast.sc` on it crashes with the same exception. A hand-written
  two-function Kotlin file goes end to end, so this is the frontend on real Kotlin, not
  the corpus. (Item S, 2026-10-02: kotlin2cpg 4.0.606 itself *does* parse
  `kotlinx-datetime` `core/common/src` — 66 files, `c73ca37` — and writes a CPG; the crash is
  in Joern's `ReachingDefPass`, one of the default overlays `joern --script` applies
  before `export_ast.sc` runs, so the exporter is not involved: the unmodified exporter and
  the item-S exporter fail identically on it. Real Kotlin therefore still cannot be
  exported end to end, and the Kotlin width fix is exercised on fixtures only.)
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
* **Java/Go/TS/JS differential oracle — did not exist at the time (superseded: `differential.py` now has Java, Go and Node backends and refuses unknown languages; see Part 1).** `scripts/differential.py`
  chooses its runtime with one line: `runtime = "cc" if is_c else "cpython"`, where
  `is_c` tests for a `.c`/`.h` suffix. Everything that is not C is handed to CPython,
  which cannot import Java or Go, so the harness reports
  `no comparable cases in this corpus` and the run is scored with **zero** conformance
  evidence. The oracle that found every dialect bug in the project's history is wired for
  two of the seven languages. *(As recorded 2026-08-20.)*

## Node kinds the exporter does not map (as recorded 2026-08-20; **superseded** by Part 1, "Holes by cause (current)")

Holes by cause, per language — CPG vocabulary items that exist but have no Core
translation. They are not the same set across languages, which is direct evidence against
"one node vocabulary".

| Language | Top hole causes |
|---|---|
| C | `op:indirection` 28, `op:cast` 18, `control:SWITCH` 14, `assign:lhs:indirectIndexAccess` 12, `op:indirectIndexAccess` 12, `assign:lhs:indirection` 12, `cstr:address-equality` 11, `op:postIncrement` 11, `op:postDecrement` 8, `control:FOR` 7, `control:GOTO` 5, `op:sizeOf` 5 |
| Java | `op:alloc` 166, `control:THROW` 125, `op:cast` 123, `op:instanceOf` 90, `op:arrayInitializer` 43, `control:FOR` 30, `expr:BLOCK-impure` 20, `control:SWITCH` 15, `op:postIncrement` 15, `op:sizeOf` 13, `control:TRY-multiCatch` 4 |
| Go | `stmt:empty-ast-children` 134, `stmt:IMPORT` 39, `assign:arity` 16 (multi-return `a, b := f()`), `lit:unquoted` 15, `op:indirection:opaque-type` 12, `expr:empty-block` 4 |
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

## Silent mistranslations found (as recorded; the numbered sections below are **superseded**)

These are the §12 failure mode: a construct that looks the same across languages and means
something different, producing a **wrong answer rather than a hole**. Each was measured —
Lean output from the generated module, real output from the real runtime.

**Status table as of 2026-10-02 at `46c65fc` — superseded by Part 1, which has the current table.** The items below are the original
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
| 5 | Java `long` / Go `int` / Kotlin `Long` | 64-bit | typed operators (`*:j64`, `*:g64`, `*:k64`) | **fixed** — Java in §63, Go and Kotlin in §66: the exporter names the operand type in the operator; the dialect is still `.cLike` |
| 6 | JS `"a" + "b"` | `"ab"` | `str "ab"` | **fixed** (`Dialect.stringsAreValues`) |

### 1. `and` / `or` return an operand, not a boolean (Python, JS, TS) — NEW, and it hits the flagship corpus  *(superseded: fixed, `Dialect.boolOpsAreValues`)*

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

### 2. `.tsx` / `.jsx` sources get the **Python** dialect — NEW, and it is the original §12 bug reappearing  *(superseded: fixed, `.javascript`; unknown extensions are an error)*

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

### 3. *(Superseded 2026-10-02, fixed by `.javascript`: §61/§65. Original heading: "JavaScript numbers are IEEE doubles; Core gives them 32-bit C integers".)* As measured 2026-08-20

`.js`/`.ts` → `.cLike` → `NumConfig.c32Wrapv`. JavaScript has no integers at all.

| input | Node | Core |
|---|---|---|
| `2147483647 + 1` | `2147483648` | **`-2147483648`** |
| `7 / 2` | `3.5` | **`3`** |
| `5 / 0` | `Infinity` | **raises `ZeroDivisionError`** |
| `-7 % 3` | `-1` | `-1` ✅ (truncated remainder happens to match) |

Three wrong answers, one accidental agreement. Verdict: **wrong**.

### 4. *(Superseded: fixed or holed, see the status below.)* JavaScript `==` and `===` were the *same* Core operator

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

### 5. *(Superseded 2026-10-02, fixed for integer arithmetic: §63 Java, §66 Go and Kotlin. Original heading: "Java `long` and Go `int` are 64-bit; Core models them as 32-bit".)* As measured 2026-08-20

> **Fixed for integer arithmetic** — Java by STRATEGY.md §63, Go and Kotlin by §66. The
> exporter names the type each integer operation is performed at inside the operator
> (`"*:j64"`, Go `"*:g64"` / `"-:w08"`, Kotlin `"*:k64"` / `"-:q32"`); `TypedInt.lean` gives
> each language its own overflow, shift and division rules (Go: a shift count at or above
> the width gives 0/-1, division by zero panics; Kotlin: masked counts,
> `ArithmeticException`); a type that does not resolve is the hole
> `op:int:unresolved-type`. Measured against the real runtimes on 56 Go cases (`go`
> 1.24.7) and 61 Kotlin cases (Kotlin compiler 2.3.21): before, Go 15 agree / 20 wrong /
> 21 holes and Kotlin 20 / 20 / 21; after, Go 55 agree + 1 hole (`1 << n` with an untyped
> constant, whose type comes from a context the exporter cannot see) and Kotlin 61/61. The
> section below is the original measurement, kept as recorded.

`.java`/`.go` → `.cLike` → `c32Wrapv`. `Numeric.lean` *already defines* `java32`,
`java64` and `go64` configs — but `Dialect` had only two constructors (`python`,
`cLike`), so nothing could select them. They were dead code. *(As recorded. The typed tags in `TypedInt.lean` now select `java32`/`java64`/`go64`; `Dialect` has three constructors, none of them Java or Go.)*

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

### 6. Java string `+`, `==`: right answer, wrong reason  *(JS part superseded: fixed by `Dialect.stringsAreValues`; the Java/Go/Kotlin hole is unchanged)*

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

### 7. Division by zero and shifts: holes and near-misses (checked, not wrong)  *(as recorded; superseded for Java/Go typed operators, see the Part 1 status table)*

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
* Go integer overflow is *defined* to wrap; Core wrapped, but at the wrong width (item 5; fixed in §66).
* JS `<<` coerces to int32 first. *Correction (2026-10-02):* this line said Core holes
  it; it did not — `.javascript` used `NumConfig.python`, so `1 << 32` was `4294967296`
  (Node: `1`) and `-1 >>> 0` a `ub` hole (Node: `4294967295`). Now `jsBitwise`
  applies ToInt32/ToUint32 and masks the count to 5 bits; `~` likewise (`jsBitNot`).
  Float operands (`1.5 | 0`) and integers beyond 2^53 are holes. **fixed**.

### 8. Predicted, unverified  *(as recorded; Go `&^`/unsigned and Java `char` arithmetic since handled, boxed `Integer ==` still unmeasured: Part 1)*

* Java boxed `Integer` comparison: `Integer a=1000, b=1000; a==b` is `false` in Java
  (reference equality) but Core's `Val.beq` on two `.int`s gives `true`. Core has no
  boxing, so this is a wrong answer waiting for a corpus that boxes. Not measured because
  `op:alloc` holes most boxing paths first.
* Java `char` arithmetic (16-bit unsigned) under a 32-bit signed config. *(Since handled for arithmetic and compound stores; `(char)` casts still hole.)*
* Go `&^` (and-not) and unsigned `uint` arithmetic under a signed config. *(Since handled, §66.)*


## Verdict, as recorded 2026-08-20 — **SUPERSEDED; the current verdict is in Part 1** (STRATEGY §61-66)

> **Do not read this as current.** Its items 2 and 3 (two dialects; `.cLike` applied unchanged to
> Java `long`, Go `int64` and JS doubles; no differential oracle beyond Python and `cc`) are
> false at `9639df0`: there are three dialects, typed integer operators for C/Java/Go/Kotlin,
> a JS dialect, and fixture oracles for each. Item 4's Kotlin half still holds; item 5 was fixed.

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

# Reproducing (applies to both parts)

```sh
export JOERN_HOME=$HOME/joern PATH="$HOME/.elan/bin:$PATH"
./autoform.sh <corpus> LangJava            # etc.
python3 scripts/lang_matrix.py             # every ast-*.json in the repo root
python3 scripts/lang_matrix.py ast-LangGo.json   # or specific ones
```

`scripts/lang_matrix.py` measures corpora the ledger cannot reach, because it does not
depend on the corpus having rendered.

> **On the function count.** This table uses the ledger's population (209 for `cachetools`), which is regenerated by `scripts/ledger.lean.tmpl` and checked by `scripts/check_docs.py`. Earlier revisions of these documents quote 238 and 208; both are superseded. Percentages must state which population they are over, since the ledger counts module-level synthesized functions the neutral AST does not list separately.
