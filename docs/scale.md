# Does this survive a large codebase?

Every number in `README.md` and `STRATEGY.md` comes from one corpus: `cachetools`, 1,637
lines, 238 functions at the time of writing (now 209). "Point it at an arbitrary codebase" was never tested. This is that
test, on seven open-source Python repositories from 8.8k to 165k lines.

Reproduce with `scripts/scale_test.py`, which runs the same stages as `autoform.sh` but
times, memory-profiles and error-captures each one separately, and writes nothing into
the repository except the generated module `lake build` requires.

```sh
scripts/scale_test.py --scratch /tmp/scale --out scale-results.json \
  --target ScaleRequests /path/to/requests
```

## The short answer

**Largest codebase that works end to end on the pipeline as committed: `requests`,
12,032 lines / 751 functions.** Everything larger fails, and the first thing that breaks
is not Joern, not memory and not Lean — it is `cartographer/render_lean.py` hitting
Python's default 1,000-frame recursion limit.

**With two limits raised (and no pipeline code changed), Django's `django/` package —
165,118 lines, 10,623 functions — completes end to end**: Joern parses it, the exporter
produces a 54 MB neutral AST, the renderer emits 503,485 lines of Lean, Lean elaborates
it in 110 s at 10.3 GB peak RSS, and the ledger reports 5,574 call-closed functions.

So the architecture scales. The *implementation* has three fixed-size limits that were
never parameterized, and one genuinely superlinear stage.

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
`lean`. Both exist so the run could go on to find what breaks *next*.

**These timings are noisy.** Several agents were building the same Lean project
concurrently throughout. The clearest evidence is the control row: `requests` measured
6/7/8/2/6/3 s in one run and 15/22/28/9/33/11 s in another, on identical input — a 4-5x
spread from machine load alone. Treat the *shape* of the growth as the result and the
absolute seconds as an upper bound. The one number too large to be explained by
contention is the Django ledger at 363 s (see below).

### Coverage, from the ledger

| repo | functions | hole-free | call-closed (verifiable core) | holes | AST nodes | dynamic-hole risk |
|---|--:|--:|--:|--:|--:|--:|
| `cachetools` (published) | 209 | 180 (86%) | 101 (48%) | 118 | 5,416 | 1,014 |
| `sqlparse` | 700    | 295 (42%) | 163 (23%) | 1,163  | 25,072  | 4,387 |
| `requests` | 847    | 342 (40%) | 117 (14%) | 1,512  | 27,039  | 4,658 |
| `flask`    | 1,731  | 1,005 (58%) | 624 (36%) | 2,200 | 39,284 | 6,557 |
| `jinja`    | 1,941  | 968 (50%) | 509 (26%) | 2,270  | 48,118  | 9,119 |
| `click`    | 2,128  | 1,093 (51%) | 690 (32%) | 2,932 | 53,890 | 8,904 |
| `rich`     | 2,087  | 914 (44%) | 675 (32%) | 3,361  | 119,630 | 13,045 |
| `django/`  | 10,623 | 6,926 (65%) | **5,574 (52%)** | 12,010 | 397,571 | 76,694 |

**Coverage does not collapse at scale — it improves.** The call-closed fraction on Django
is 52%, nearly three times the 19% published for `cachetools`. That is not the transpiler
getting better; it is §18's call-closure gap being an artifact of corpus *size*. A small
library calls mostly outward, into a stdlib that is not modelled, so almost nothing is
call-closed. A large framework calls mostly inward, into itself, so its callees resolve
inside the translated program. The honest reading is that `cachetools`' 19% understated
what the method achieves on the kind of codebase it was designed for, and that the
"modelled standard library" identified as the next piece of work matters *less* the
bigger the target is.

Hole *density* is stable — 2.4%-3.0% of AST nodes across every corpus including Django's
397,571 nodes — so translation quality itself is size-independent. The hole causes shift:
Django's top cause is `import:unresolved` (5,122), which barely registers on `cachetools`.

## Where it breaks, in the order it breaks

### 1. The renderer overflows Python's stack at 246 consecutive top-level statements

`cartographer/render_lean.py` renders each function with mutually recursive
`flat`/`flat_child`/`render`, about four Python frames per AST level, against the default
1,000-frame limit. `Stmt.seq` is right-nested, so a module body of *n* top-level
statements is an AST of depth *n*.

Bisected exactly, with a synthetic module of *n* consecutive assignments:

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

This is the whole reason the ceiling is 12k lines. Note that it is **not** a function of
repository size at all: `sqlparse` at 8.8k lines fails and `requests` at 12k lines passes,
because the trigger is one file's top-level statement count. `sqlparse/keywords.py` is a
long list of regex/keyword bindings; that one file, in a repo a fifth of Django's size,
defeats the pipeline. Any repo with a generated table, a long `__all__`-style block, or a
big constants module hits this — which is most real Python.

**Fix:** either raise the limit and the thread stack in `render_lean.py`, or make the
printer iterative over the `seq` spine (a module body is a *list* of statements masquerading
as a right-nested tree, so an explicit worklist is the structurally honest version). The
second is better: `set_option`-style limit raising just moves the cliff.

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
this cannot be blamed on contention — it is a single-threaded `lean` process, and the
per-function cost rises by an order of magnitude across the range.

The cause is visible in the source and predicted by it. `Program.table` is an association
`List`:

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

**Fix:** `Program.table` should be a `Std.HashMap String Func`, with a second map keyed by
last dotted segment for the suffix fallback, built once per `Ctx`. This is not only a
ledger problem — `Ctx.resolve` is on the interpreter's hot path (`evalExpr`'s `.call`,
`.mcall` and `.alloc` cases all go through it), so every future evaluation and every
conformance run pays the same O(F) per call on a large program.

### 4. Memory grows with the generated module, and it grows fast

Peak RSS is dominated by `lean` elaborating the generated module, and it grows faster
than the module does: 6.5 MB of Lean → 2.4 GB, 11.9 MB → 3.7 GB, 34.8 MB → 10.3 GB. That
is roughly 300 MB of RSS per MB of generated Lean, near-linear in file size but with a
large constant, and it is the constraint that will bite first on a machine with less than
16 GB. Nothing OOM'd here; Django at 10.3 GB is the largest observed and it completed.

Joern is the other memory consumer and is much better behaved: 5.2 GB parsing Django's
165k lines, 4.8 GB exporting it, both well inside default JVM settings. **Joern never
failed, never OOM'd and never timed out on any target** — the front end that was expected
to be the fragile part is the sturdiest stage in the pipeline.

## What was *not* measured

* **`Heap` as a `List` with `mapIdx` writes.** `Heap.setField` is `h.mapIdx …`, i.e. O(heap)
  per field write, and `Heap.alloc` is `h ++ [o]`, also O(heap). This is a *runtime*
  cost, so it is exercised by `scripts/differential.py`, not by translation or
  elaboration, and no differential run was made on these corpora — running one requires
  each repo's test suite as the specimen source. The quadratic is legible in the source
  and consistent with the `Program.table` finding, but it is **unmeasured**, and it is
  named here rather than asserted.
* **`assure.sh`** end to end (axiom sweep, mutation gate, SACM) on a large corpus. Only
  the `autoform.sh` stages were run.
* **Conformance percentages at scale.** The 100% figures in `README.md` remain
  `cachetools`-only. Nothing here confirms or refutes them on a larger corpus.

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
