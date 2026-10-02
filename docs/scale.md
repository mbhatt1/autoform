# Scale: behaviour on a large codebase

When this was written, every number in `README.md` and `STRATEGY.md` came from one corpus:
`cachetools`, 1,637 lines, 238 functions at the time (now 209). (The README has since
added a SQLite hole census, and `docs/evidence-*.md` cover V8, Linux and Ansible.) "Point it at an arbitrary codebase"
was never tested. This document records that test, on seven open-source Python
repositories from 8.8k to 165k lines. Figures move with every change to the pipeline;
where a document and an artifact disagree, the artifact wins.

Reproduce with `scripts/scale_test.py`, which runs the same stages as `autoform.sh` but
times, memory-profiles and error-captures each one separately, and writes nothing into
the repository except the generated module `lake build` requires.

```sh
scripts/scale_test.py --scratch /tmp/scale --out scale-results.json \
  --target ScaleRequests /path/to/requests
```

## Summary

**Largest codebase that works end to end on the pipeline as committed: `requests`,
12,032 lines / 751 functions.** Everything larger fails, and the first thing that breaks
is not Joern, not memory and not Lean — it is `cartographer/render_lean.py` hitting
Python's default 1,000-frame recursion limit.

**With two limits raised (and no pipeline code changed), Django's `django/` package —
165,118 lines, 10,623 functions — completes end to end**: Joern parses it, the exporter
produces a 54 MB neutral AST, the renderer emits 503,485 lines of Lean, Lean elaborates
it in 110 s at 10.3 GB peak RSS, and the ledger reports 5,574 call-closed functions.

The architecture scales. The *implementation* has three fixed-size limits that were never
parameterized, and one superlinear stage.

"Arbitrary codebase" is therefore **aspirational as shipped and plausible as designed**:
the two blocking failures are one-line configuration changes, the third (the ledger) is a
data-structure change, and none of them are in the semantics.

## Measurements

Wall-clock seconds per stage, peak RSS of the whole stage process tree (`/usr/bin/time`).
`build` is `lean` elaborating the generated module; `ledger` is `lake env lean` on
`scripts/ledger.lean.tmpl`.

| repo | src lines | files | funcs | AST MB | Lean MB | Lean lines | parse | graph | export | render | build | ledger | peak RSS |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| `sqlparse`  | 8,798   | 41  | 700    | 7.0  | 5.6  | 34,527  | 7  | 10 | 9  | 4  | 5   | 2   | 1.7 GB |
| `requests`  | 12,032  | 37  | 847    | 4.2  | 2.7  | 36,112  | 6  | 7  | 8  | 2  | 6   | 3   | 1.8 GB |
| `flask`     | 18,345  | 83  | 1,731  | 5.5  | 3.6  | 53,379  | 7  | 8  | 9  | 2  | 8   | 5   | 2.1 GB |
| `jinja`     | 22,875  | 60  | 1,941  | 7.3  | 4.9  | 64,653  | 7  | 8  | 11 | 3  | 10  | 7   | 2.3 GB |
| `click`     | 28,547  | 78  | 2,128  | 9.7  | 6.5  | 72,857  | 8  | 10 | 12 | 4  | 12  | 7   | 2.4 GB |
| `rich`      | 51,866  | 213 | 2,087  | 18.7 | 11.9 | 134,832 | 24 | 21 | 26 | 12 | 38  | 11  | 3.7 GB |
| `django/`   | 165,118 | 906 | 10,623 | 54.5 | 34.8 | 503,485 | 44 | 53 | 79 | 40 | 110 | 363 | 10.3 GB |

Every row except `requests` needed `--recursion-limit`; `django` additionally needed
`-DmaxRecDepth=60000` (all rows above `requests` ran with 8,000, which is why `django`'s
`build` column is the 60,000 rerun). Neither workaround edits the pipeline: the first
runs `render_lean.py` unmodified on a big-stack thread, the second passes an option to
`lean`.

**These timings are noisy.** Several agents were building the same Lean project
concurrently throughout. The control row: `requests` measured 6/7/8/2/6/3 s in one run and
15/22/28/9/33/11 s in another, on identical input — a 4-5x spread from machine load alone.
Treat the *shape* of the growth as the result and the absolute seconds as an upper bound.
The one number too large to be explained by contention is the Django ledger at 363 s (see
below).

### Coverage, from the ledger

The `cachetools` row was regenerated on 2026-10-02 on the item-L branch (after merging `8d3a970`),
from a fresh re-export of `ast-Cachetools.json` at cachetools `01af8e5` (`scripts/ledger.lean.tmpl`
over the tracked AST; provenance in `provenance/ast-Cachetools.json.prov.json`); `scripts/check_docs.py` checks it. The other rows
predate the exporter changes described below and were not re-run.

| repo | functions | hole-free | call-closed (verifiable core) | holes | AST nodes | dynamic-hole risk |
|---|--:|--:|--:|--:|--:|--:|
| `cachetools` (published) | 209 | 168 (80%) | 99 (47%) | 46 | 5,661 | 915 |
| `sqlparse` | 700    | 295 (42%) | 163 (23%) | 1,163  | 25,072  | 4,387 |
| `requests` | 847    | 342 (40%) | 117 (14%) | 1,512  | 27,039  | 4,658 |
| `flask`    | 1,731  | 1,005 (58%) | 624 (36%) | 2,200 | 39,284 | 6,557 |
| `jinja`    | 1,941  | 968 (50%) | 509 (26%) | 2,270  | 48,118  | 9,119 |
| `click`    | 2,128  | 1,093 (51%) | 690 (32%) | 2,932 | 53,890 | 8,904 |
| `rich`     | 2,087  | 914 (44%) | 675 (32%) | 3,361  | 119,630 | 13,045 |
| `django/`  | 10,623 | 6,926 (65%) | **5,574 (52%)** | 12,010 | 397,571 | 76,694 |

**Coverage does not collapse at scale.** The call-closed fraction on Django is 52%.

The `cachetools` figure this was originally compared against was 19%, and the comparison
was read as evidence that call closure is largely an artifact of corpus *size*: a small
library calls mostly outward into an unmodelled stdlib, while a large framework calls
mostly inward and its callees resolve inside the translated program.

**That reading no longer follows from these two numbers.** `cachetools` was 105/209 =
50% at `46c65fc` (99/209 = 47% after the re-export that made generators, defaults and
local-name calls honest), against Django's 52%. The change came from exporter work — emitting Joern's resolved
`fullName` so `Ctx.resolve`'s exact match fires, closing `op:starredUnpack`, and dropping
`<metaClassCallHandler>` synthetics — not from the corpus getting larger. So most of the
original gap was a resolution defect in the exporter, not a property of corpus size.

The size effect may still exist; it is simply not measurable from a 50%-versus-52%
comparison. Establishing it would require re-running Django with the current exporter,
which has not been done — every Django figure in this table predates that work.

Hole *density* was stable — 2.4%-3.0% of AST nodes across every corpus including Django's
397,571 nodes — so translation quality was size-independent at the time these rows were
measured. `cachetools` has since dropped to 0.5% (26 / 5,574) through exporter work, which
the other rows have not been re-run against. The hole causes shift:
Django's top cause is `import:unresolved` (5,122), which barely registers on `cachetools`.

## Where it breaks, in the order it breaks

### 1. The renderer overflows Python's stack at 246 consecutive top-level statements

`cartographer/render_lean.py` renders each function with mutually recursive
`flat`/`flat_child`/`render`, about four Python frames per AST level, against the default
1,000-frame limit. `Stmt.seq` is right-nested, so a module body of *n* top-level
statements is an AST of depth *n*.

Bisected, with a synthetic module of *n* consecutive assignments:

> **the stock renderer handles 246 top-level statements in a single file and fails at 247**
> with `RecursionError: maximum recursion depth exceeded`.

Observed depths (the deepest `<module>` initializer per repo):

| repo | deepest module | depth | stock renderer |
|---|---|--:|---|
| `cachetools` | `cachetools/__init__.py` | 76 | ok |
| `requests` | `src/requests/utils.py` | 242 | ok |
| `flask` | `tests/test_basic.py` | 278 | **RecursionError** |
| `jinja` | `src/jinja2/filters.py` | 285 | **RecursionError** |
| `rich` | `tests/test_console.py` | 292 | **RecursionError** |
| `django/` | — | 316 | **RecursionError** |
| `click` | `tests/test_options.py` | 675 | **RecursionError** |
| `sqlparse` | `sqlparse/keywords.py` | 576 | **RecursionError** |

This is why the ceiling is 12k lines. It is **not** a function of repository size:
`sqlparse` at 8.8k lines fails and `requests` at 12k lines passes, because the trigger is
one file's top-level statement count. `sqlparse/keywords.py` is a long list of
regex/keyword bindings; that one file, in a repo a fifth of Django's size, defeats the
pipeline. Any repo with a generated table, a long `__all__`-style block, or a big
constants module hits this.

**Fix:** either raise the limit and the thread stack in `render_lean.py`, or make the
printer iterative over the `seq` spine (a module body is a *list* of statements masquerading
as a right-nested tree, so an explicit worklist is the structurally honest version). The
second is better: raising the limit moves the cliff.

### 2. Lean's `maxRecDepth` overflows on the `program` function list

Once the renderer is past its own limit, `lean` hits its default `maxRecDepth`. Two
distinct sites, in this order:

* the deep single term for a `<module>` initializer — this is what fails on `sqlparse`
  under `lake build`, at `ScaleSqlparse.lean:24326`, inside the depth-576 term;
* `def program : Program := { funcs := [ … ] }`, a list literal with one element per
  translated function. On Django this is the failure at `ScaleDjango.lean:492859`, and it
  needs `maxRecDepth` above roughly the function count: 8,000 was enough for 2,128
  functions and not for 10,623; 60,000 elaborates Django.

The generated module emits no `set_option maxRecDepth`, so a user gets an error that
names a Lean option rather than anything about their code.

**Fix:** have `render_lean.py` emit `set_option maxRecDepth <k·len(funcs)>` at the top of
the generated module — it already knows the function count. It is a one-line change to a
deterministic printer and does not affect what is proved.

### 3. The ledger goes superlinear — the `List` function table, measured

The ledger is the only stage whose cost grows faster than its input:

| repo | functions | ledger seconds | s / function |
|---|--:|--:|--:|
| `sqlparse` | 700 | 2.4 | 0.0034 |
| `flask` | 1,731 | 4.9 | 0.0028 |
| `click` | 2,128 | 6.6 | 0.0031 |
| `rich` | 2,087 | 10.9 | 0.0052 |
| `django/` | 10,623 | **363** | **0.034** |

Five times the functions cost **55 times** the wall-clock, and unlike the other stages
this cannot be attributed to contention — it is a single-threaded `lean` process, and the
per-function cost rises by an order of magnitude across the range.

The cause is in the source. `Program.table` is an association `List`:

```lean
def Program.table (p : Program) : FuncTable := p.funcs.map (fun f => (f.name, f))
def Ctx.resolve (ctx : Ctx) (n : String) : Option Func :=
  match ctx.table.find? (·.1 == n) with
  | some (_, f) => some f
  | none        => match ctx.table.filter (fun p => p.1.endsWith ("." ++ n)) with …
```

`find?` is a linear scan and the fallback `filter` traverses the *entire* table, so a
miss is unconditionally O(F) with a string-suffix test per entry. `Program.callClosed`
runs `f.calls.all ctx.resolvable` over every hole-free function, making the ledger
O(F × calls-per-function × F). At F = 10,623 that is the 363 seconds.

**Fixed, for the ledger only.** The prescribed fix — make `Program.table` a
`Std.HashMap String Func` — turned out not to be available: `Autoform/Contracts.lean`,
`Autoform/Refine.lean` and `Autoform/CallingConvention.lean` `simp` through
`Ctx.resolve.go` on the association list, so the list shape is load-bearing for the
proofs and changing it breaks them.

What was done instead is a `ResolveIndex` that lives in `Autoform/Ledger.lean`, is built
once per program, and answers exactly what `Ctx.resolvable` answers (exact keys, plus a
count of table entries per dotted tail, so the *unique*-suffix rule and the first-match
method rule stay distinct). `Ctx.resolve` itself is untouched. The quadratic definition is
kept as `Program.callClosedRef`, and `Program.callClosureAgrees` re-derives the answer
both ways: `scripts/ledger.lean.tmpl` aborts if they differ, so the faster number can
never be reported unchecked.

Measured in one process per corpus, `callClosedRef` vs `callClosed`, identical results
(a timing snapshot, not re-run; the Cachetools verifiable core is 105 today, see the
coverage table above):

| corpus | functions | verifiable core | before | after |
|---|---|---|---|---|
| Cachetools | 209 | 101 | 65 ms | 2 ms |
| V8Numbers | 157 | 78 | 50 ms | 1 ms |
| V8Base | 1,920 | 830 | 670 ms | 11 ms |
| LinuxCrypto | 1,955 | 347 | 1,150 ms | 14 ms |
| LinuxLib | 3,368 | 920 | 1,789 ms | 21 ms |
| Ansible | 5,547 | 2,205 | 10,806 ms | 72 ms |

**Still open:** `Ctx.resolve` is also on the interpreter's hot path (`evalExpr`'s `.call`,
`.mcall` and `.alloc` cases all go through it), so every evaluation and every conformance
run still pays O(F) per call on a large program. The index above does nothing for that,
and the assoc-list constraint from the proofs applies there too.

### 4. Memory grows with the generated module

Peak RSS is dominated by `lean` elaborating the generated module, and it grows faster
than the module does: 6.5 MB of Lean → 2.4 GB, 11.9 MB → 3.7 GB, 34.8 MB → 10.3 GB. That
is roughly 300 MB of RSS per MB of generated Lean, near-linear in file size but with a
large constant, and it is the constraint that binds first on a machine with less than
16 GB. Nothing OOM'd here; Django at 10.3 GB is the largest observed and it completed.

Joern is the other memory consumer and is better behaved: 5.2 GB parsing Django's
165k lines, 4.8 GB exporting it, both well inside default JVM settings. **Joern never
failed, never OOM'd and never timed out on any target.**

## SQLite (C, full tree): generated header and a conformance sample

Everything above is Python. This section is the one C corpus run at scale through the
static census *and* the runtime oracle. Numbers are from the commands below, run on
2026-10-02 against `sqlite/sqlite` 3.54.0 (`manifest.uuid` `52f84cfc…`), Joern 4.0.606.

### Reproduce

```sh
scripts/sqlite_corpus.sh /opt/corpus/sqlite-src /opt/corpus/D/full all
#   gen:    copy the tree, build autosetup/jimsh0.c and tool/mksourceid.c, run
#           tool/mksqlite3h.tcl -> tree/src/sqlite3.h (no system tclsh needed)
#   parse:  c2cpg with SQLITE_OS_UNIX, SQLITE_TEST and the linkage macros
#   export: cartographer/export_ast.sc with the same cppDefines -> ast.json + metrics
# amalgamation of the SAME checkout, for the C side of the sample:
(cp -r <sqlite-src> amal && cd amal && ./configure && make sqlite3.c)
scripts/sqlite_sample.py /opt/corpus/D/full/ast.json /opt/corpus/D/full/tree \
    amal/sqlite3.c /opt/corpus/D/sample
python3 cartographer/render_lean.py /opt/corpus/D/sample/ast-SqliteSample.json \
    Autoform/Generated/SqliteSample.lean SqliteSample
lake build Autoform.Generated.SqliteSample
(cd /opt/corpus/D/sample && python3 <repo>/scripts/differential.py \
    ast-SqliteSample.json csrc SqliteSample 20)
```

`tclsh` is not installed on the measurement box. Instead of substituting the
amalgamation's header (the corpus copy at `/opt/corpus/sqlite/sqlite3.h` is 3.47.0, the
tree is 3.54.0, so it would be the wrong header), `gen` runs SQLite's own generator
under the Tcl interpreter SQLite ships for exactly this case. `make sqlite3.c` in a
configured copy produced a byte-identical `sqlite3.h` (`cmp`).

A bare `--define NAME` makes `NAME` defined but EMPTY in c2cpg: on a two-branch fixture
`#if FOO` took the false branch under `--define FOO` and the true one under
`--define FOO=1`. `SQLITE_OS_UNIX` and `SQLITE_TEST` are passed bare to match the
published configuration, not because that is right.

### Census

| Run | Functions | Hole-free | Holes | `op:cast*` | `op:sizeOf*` |
|---|--:|--:|--:|--:|--:|
| checkout as is (`/opt/corpus/final/full`, exporter at `46c65fc`) | 7,772 | 5,054 (65.0%) | 11,759 | 1,511 | 1,083 |
| generated `sqlite3.h` + linkage macros, same exporter | 8,105 | 5,736 (70.8%) | 10,451 | 404 | 652 |
| plus the `<operators>.` normalization | 8,105 | 5,724 (70.6%) | 10,497 | 404 | 652 |

Per function (keyed by file and name), between the first and last rows: 7,738 functions
are in both; 441 became hole-free and 43 lost it. The 367 functions only in the new run
(283 hole-free) are mostly `src/test*.c`, whose bodies c2cpg could not parse without the
header. The 34 only in the old run are `<duplicate>N` names that were renumbered. Every
loss checked is a more precise refusal: `sqlite3DbstatRegister`'s `sqlite3_module`
initializer had been exported as a positional `listE` because the type was unknown and is
now `op:arrayDecl:static-initializer`; `sqlite3_status`'s `*pCurrent = (int)iCur` had
been a `cast:i32` of an unknown type and is now `assign:lhs:indirection`.

The hole-free figure was more inflated than the census showed. Without the header,
`SQLITE_OK`, `SQLITE_BUSY`, ... are not expanded, and a function that reads one is
"hole-free" but reads an undefined name at run time. 1,597 hole-free functions did so
before; 291 after. The rest are `TK_*` (156 functions) and `OP_*` (112), defined in
`parse.h` and `opcodes.h`, which are also generated and still absent, and 49 `SQLITE_*`
names. Generating those headers too is the next step.

### Exporter fix: `<operators>.`

Joern names six compound assignments with a plural prefix: `x |= 1` has
`METHOD_FULL_NAME` `<operators>.assignmentOr` (also `.assignmentAnd`, `.assignmentXor`,
`.assignmentShiftLeft`, `.assignmentArithmeticShiftRight`, `.assignmentModulo`), while
`x += 1` is `<operator>.assignmentPlus`. Every operator test in `export_ast.sc` is a
`<operator>.` key or `startsWith("<operator>")`, which `"<operators>.…"` fails, so these
were exported as calls to a function of that name with the target passed by value. The
function stayed hole-free and the write was lost. 157 hole-free SQLite functions had one.
The exporter now renames them to the singular spelling on C CPGs, so they take the
existing `augOps` / `>>=` path (the translation `x = x | m` already gets, with its
single-evaluation guards). Of the 157, 145 now translate and 12 hole
(`assign:aug-impure-target` 7, `op:shiftRight:64-bit-operand` 4, one `>>=` of unknown
signedness). On a fixture of `|= &= ^= <<= %= >>=` the result agreed with `cc` on 40/40
random cases. Python is deliberately left alone: there `a |= b` mutates a set in place,
which `a = a | b` does not.

### Conformance sample

`scripts/sqlite_sample.py` keeps only what the C leg of `differential.py` can run with
nothing invented. The AST carries no C types, so a candidate must be hole-free,
call-closed through other candidates, have integer parameter and return types, and contain
no preprocessor line in its body, no free names, and no objects. Its file must be compiled
by the default amalgamation of the same checkout. The C side is SQLite's own code:
`csrc/sample.c` renames each function by macro, `#include`s the amalgamation unchanged,
and exports a wrapper under the original name with the function's own signature.
`csrc/ctypes.json` records each parameter's and the result's width and signedness, read
from a program compiled against the same amalgamation (`probe_types`), so `LogEst` is
16-bit signed and `sqlite3_int64` 64-bit because the compiler says so. Selection is by
sha256 of the name, so it is deterministic.

Of 5,724 hole-free functions, 3,269 are in files the default amalgamation does not
compile (`autosetup/jimsh0.c`, `tool/`, `ext/fts5`, `ext/jni`, `src/test*.c`, ...),
1,135 return a non-integer type (849 `void`), 1,125 have a non-integer parameter
(pointer, struct, float, ...), 133 have a definition the signature reader could not
match, and the remaining filters remove 53 more (no parameters, preprocessor lines,
non-candidate callees, ...). **9 qualify**, the same 9 as before the typed leg:
admitting `_Bool`, `Bitmask`, `<stdint.h>` names and `SQLITE_OPT_INLINE u64` moved 8
functions from "return type" to "parameter" (every one also takes a pointer), and no
function in the population was refused for an integer *width* alone. The binding
constraint is pointers, not integer types.

**Typed C leg.** `differential.py` reads `ctypes.json` when it is present: values are
passed and read at their real C width and signedness (`char`/`short`/`int`/`long`/`long
long`, `unsigned`, `_Bool`) through ctypes, and each argument is drawn over its whole type
(a boundary of the type with probability 0.35: min, max, their neighbours, the
power-of-two edges), so a `sqlite3_int64` parameter now receives values a 32-bit model
cannot hold. The basis is `c-typed-v1`; it is not comparable with the int-only basis.
`tests/test_cboolint_cc.py` checks that every typed argument is representable in its
type and that both boundaries are drawn.

Commands, 2026-10-02, Core at this branch (`Dialect.promotesBool`):

```sh
python3 scripts/sqlite_sample.py /opt/corpus/D/full/ast.json /opt/corpus/D/amal \
    /opt/corpus/D/amal/sqlite3.c <out>
python3 cartographer/render_lean.py <out>/ast-SqliteSample.json \
    Autoform/Generated/SqliteSample.lean SqliteSample
lake build Autoform.Generated.SqliteSample
(cd <out> && python3 <repo>/scripts/differential.py ast-SqliteSample.json csrc SqliteSample 20)
# int-only basis: the same command on a copy of round 1's /opt/corpus/D/sample (no ctypes.json)
```

| Basis | Functions compared | Agree | Diverge | Inconclusive |
|---|--:|--:|--:|--:|
| int-only (`varargs-attempted-v2`), before the fix | 9/9 | 140/170 | 30 | 10 |
| int-only, after | 9/9 | **170/170** | 0 | 10 |
| typed (`c-typed-v1`), after | 9/9 | **168/168** | 0 | 12 |

**The 30 round-1 divergences** (`isFatalError` 20, `validJulianDay` 10) had one root
cause: C's relational, equality, `!`, `&&`, `||` results are `int` 0/1 (C11 6.5.8-6.5.14,
6.5.3.3), and Core's were `Val.bool`, which `==` against an `int` compared false
(`Val.beq`) and arithmetic holed. In the sample they all surfaced at the RETURN (`return
rc!=0 && rc!=5 && rc!=6` gave `bool true`, `cc` 1); the same root cause is a silent wrong
answer one step inside a function: `int t = (a < b); if (t == 1) return 7; return 3;`
returned 3 where `cc` returns 7.

The fix is in Core, not the exporter, and it is a promotion rather than a change of
result type, because `.cLike` also serves Java, Go, Kotlin and C++. There `a < b` is a
`boolean`/`bool`: Java's `boolean` must stay a `bool` (Java's `&` on two of them is a
`boolean`), C++ integral-promotes `bool` to `int` 0/1 in arithmetic and comparison
([conv.prom]/6), and in Java/Go/Kotlin mixing a boolean with a number is a compile error,
so no well-typed program of theirs reaches the promoted cases. So comparisons still yield
`Val.bool`, and under `.cLike` (`Dialect.promotesBool`) a `bool` meeting an integer or a
float in `applyBinop` (`binopFallback`), or under unary `-`/`~`, is promoted to 0/1 --
the C++ rule, which for C is its own arithmetic. `(a<b) == 1` is now true, `(a<b) +
(b<a)` is 1, `(a<b) & (b>0)` stays a `bool` (Java) that a later integer context reads as
1 (C). `cIntBinop_eq` proves the promoted arms compute exactly what the integer arms
compute. No proof needed changing: the integer arms are untouched, and `simp` lemmas for
the split-out fallback (`binopFallback_int_int`, `binopTail_eq`, ...) keep
`Specs/V8Spec.lean`'s `simp [applyBinop, ...]` working as it was.

The one integer context Core does not see is the return conversion to the function's
declared type: `int f(void) { return a < b; }` returns `Val.bool`. The harness applies
that conversion (`c_return_conversion`: `bool` compares as exactly 0/1, nothing looser),
and so does `tests/test_cboolint_cc.py`. Of the 30, all 30 agree through it; the Core
promotion is what fixes the in-function form, which the sample happens not to contain and
the fixture does. Emitting a `cast:<T>` on `return` from the exporter would move the
conversion into the translation; it needs the declared return type at each `Return`
and a re-export, and is not done.

`tests/fixtures/cboolint/cboolint_cases.c` (15 cases, including the fixture above,
`(a<b)+(b<a)`, `-(a<b)`, `~(a>b)`, `(a<b)<<3`, a loop counting `i % 3 == 0`, and `(a<b) +
0.5 > 1.0`) is exported by Joern, rendered to `Autoform/CBoolIntProgram.lean`, pinned in
`Autoform/CBoolInt.lean` with `#guard_msgs`, and compared with `cc` by
`tests/test_cboolint_cc.py`: 15/15 agree, none holes.

**Float `%`.** `.cLike` `%` on a double used CPython's floored `pyMod`. The only
`.cLike` languages that accept a floating `%` are Java and Kotlin (C, C++ and Go reject
it at compile time), and both truncate: `-5.5 % 2.0` is `-1.5` (JLS 15.17.3; `javac`/
`java` on this box print `-1.5`, and `1.5` for `5.5 % -2`). `.cLike` now uses `fmod`, pinned
by `#guard`s in `Semantics.lean` (with Python's `0.5` pinned alongside).

**The inconclusive cases.** 11 (typed) / 10 (int-only) are `validJulianDay(iJD)` on
`iJD >= 0`: `INT_464269060799999` is `((i64)0x1a640 << 32) | 0x1072fdff`, and Core's
`.cLike` integers are 32-bit, so `<< 32` is `ub:shift count out of range`, a hole. The
typed leg adds one: `vdbeSorterTreeDepth(nPMA)` keeps an `i64 nDiv` and multiplies it by
16 until it exceeds `nPMA`. At 32 bits `16^8 = 2^32` wraps to 0, the loop never ends, and
Core answers `outOfFuel` (checked directly: `runFunc` gives 6 for `nPMA = 2^28`, which
`cc` agrees with, and `outOfFuel` for `2^28 + 1` and `INT_MAX`, where `cc` gives 7). Not
a wrong answer here, but the same gap: **64-bit C arithmetic is computed at 32 bits**
(`Dialect.toNumConfig .cLike = c32Wrapv` for every C integer type), and a function whose
`i64`/`u64`/`unsigned` arithmetic leaves the `int` range without hitting a hole or a
loop would be a wrong answer. The int-only leg could not reach it (`randint(-20, 20)`);
the typed leg reaches it, and on this sample it lands on a hole and `outOfFuel` only.
Per-type widths in Core (the exporter already resolves them for `>>`) are the fix.

## What was *not* measured

* **`Heap` as a `List` with `mapIdx` writes.** `Heap.setField` is `h.mapIdx …`, i.e. O(heap)
  per field write, and `Heap.alloc` is `h ++ [o]`, also O(heap). This is a *runtime*
  cost, so it is exercised by `scripts/differential.py`, not by translation or
  elaboration, and no differential run was made on these corpora — running one requires
  each repo's test suite as the specimen source. The quadratic is legible in the source
  and consistent with the `Program.table` finding, but it is **unmeasured**.
* **`assure.sh`** end to end (axiom sweep, mutation gate, SACM) on a large corpus. Only
  the `autoform.sh` stages were run.
* **Conformance percentages at scale.** The 100% figures in `README.md` remain
  `cachetools`-only for Python. The one large-corpus run, SQLite (above), compared 9
  functions, found a real semantic divergence (C comparison results as `int`), and after
  its fix agrees on every conclusive case.

## Caveats on these runs

* Repositories were measured **whole**, including their `tests/` directories, because
  that is what `./autoform.sh <repo>` does. Several of the deepest modules are test files.
* `cartographer/export_ast.sc` was being edited by another agent during the run window.
  One `rich` export failed to compile the script outright (`Not found: escapes`) and one
  `render` failure did not reproduce; both were rerun, and the function counts shifted
  slightly between runs (`requests` 847 → 751, `rich` 2,359 → 2,087) because the exporter
  changed underneath. Rows are internally consistent — each row's ledger comes from the
  same AST as its timings — but rows from different runs are not strictly comparable.
* `django/` means the `django/` package inside the repository, not the repository root
  (which adds ~200k lines of tests).
* Nothing in the pipeline was tuned, patched or otherwise altered to improve any number
  in this document.
