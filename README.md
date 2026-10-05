# autoform

Turn an arbitrary codebase into autoformalized Lean 4 by mapping it onto a formal
interpreter written in Lean. See `STRATEGY.md` for the design and the build/buy audit.

**Approach:** formalize the *language* rather than the program. The program becomes data,
and every property is a theorem about `eval` applied to it.

**Generalization:** Joern's code property graph is a universal AST. C, C++, Java,
JavaScript, TypeScript, Go, Python, Kotlin and binaries normalize to one node vocabulary,
so one semantics and one exporter cover all of them. There is no per-language transpiler.
How far that holds is measured per language in `docs/languages.md`. Python is checked
against CPython (the corpus's own test suite, plus fixtures); C against `cc` (fixtures, and
a 9-function SQLite sample limited to integer-argument functions: the harness crashed on
`sds`'s `char *` API); JavaScript against Node (a 55-case fixture, §65); and integer
arithmetic for Java, Go and Kotlin against the real runtimes (§63, §66). There is no
whole-corpus oracle for Java, Go, TypeScript or JavaScript; real Kotlin projects cannot be
exported (Joern's dataflow overlay crashes on them), and binaries were not tested.

## Use

The preferred entry point is the `autoform` CLI. It owns pipeline orchestration and provides config-file support, dry-run mode, dependency checks, run manifests and JSON output for CI. The legacy shell scripts now delegate to it.

```sh
python3 -m pip install -e .[dev]
autoform --repo-root /path/to/autoform doctor
autoform validate --json               # validate autoform.toml before fleet runs
autoform translate <source-dir> <ModuleName>
autoform assure <source-dir> <ModuleName>
autoform batch                         # run configured [targets.<name>] entries
autoform gate --manifest .autoform-runs/<run-id>/run.json --json
```

The legacy shell scripts remain supported:

```sh
./autoform.sh <source-dir> [ModuleName]   # translate + type-check + conformance + ledger
./assure.sh   <source-dir> <ModuleName>   # the above, plus audit, mutation gate, SACM case
```

See [`docs/cli.md`](docs/cli.md) for configuration, CI usage and command details.

```
source ──Joern──▶ CPG ──▶ neutral JSON AST ──▶ Lean Core program ──▶ trust ledger
                   │                                   │
                   └─▶ formalization graph             └─▶ differential vs real runtime
```

> **Numbers in this file go stale.** A dozen artifacts describe the same metrics and they
> drift apart. Regenerate rather than trust:
> `./autoform.sh <src> <Name>` prints the ledger; `python3 scripts/sacm.py --module <Name>`
> prints the assurance case. `docs/` explains what each number means.

## Verified end to end

Figures in this table were measured at or before commit `16f7c88` (2026-08-20) and have
not been re-run since. Of the small corpora only the ASTs of `stress` and `sample` are
tracked (`ast-Stress.json`, `ast-Sample.json`: 6 and 5 functions, matching the table);
`ctest` and `shortcircuit` are not in the repository. Current `cachetools` figures are in
`docs/scale.md` and `docs/languages.md`, which `scripts/check_docs.py` checks against
`ledger-Cachetools.json`.

| Corpus | Language | Functions | Verifiable core | Conformance vs real runtime |
|---|---|---|---|---|
| `cachetools` (real repo) | Python | see below | see below | see below |
| stress corpus | Python | 6 | 6 (100%) | **30/30 (100%)** vs CPython |
| sample | Python | 5 | 2 (40%) | **10/10 (100%)** vs CPython |
| ctest | C | 5 | 5 (100%) | **25/25 (100%)** vs `cc` |
| shortcircuit | Python | 1 | 1 (100%) | **6/6 (100%)** vs CPython |

All generated Lean type-checks. The "verifiable core" is the set of **hole-free**
functions — the only ones that can be verified unconditionally.

Three figures are reported, because one number would mislead (`STRATEGY.md` §17):
**hole-free** (no static holes) is an upper bound; **call-closed** additionally requires
every callee to resolve inside the program, and is the verifiable core;
**dynamic-hole risk** counts constructs that can still hole on some input.
Static hole-freedom does not imply the interpreter never holes — an untranslated callee
is invisible in the AST.

## Scale: SQLite (C, full source tree)

Exporter-level hole census on the full `sqlite/sqlite` tree (7,772 functions, Joern
4.0.606, `--define SQLITE_OS_UNIX --define SQLITE_TEST`). Hole-free here is the static
upper bound (see above); the census runs did not re-check call-closure or conformance,
and no Lean was built for them. The conformance sample at the end of this section is the
only part that did.

| Exporter | Hole-free | Holes |
|---|---|---|
| before spec 011 (`77542bb`) | 4,602 (59.2%) | 13,291 |
| after spec 011 (pointer, address-of, indirection, casts/sizeof, control flow) | **5,054 (65.0%)** | 11,759 |

Per function: 551 became hole-free and 99 lost it. Every loss is a translation that
was wrong and now refuses. 69 are `sizeof` values that disagreed with gcc; the struct
layout now matches gcc on 97 types and 1,536 sites. 15 are boxed-local initializers
that used to be dropped. The rest are type-punning casts and pointer cursors that were
tracked two ways. Along the way this fixed several hole-free-but-wrong translations:
`&&`/`||` ran the right operand's side effects unconditionally, `do`/`while` swapped
its body and condition, `0` and `NULL` compared unequal in null tests, `char**` was read
as a byte cursor, and `int n; f(&n)` holed at run time.

What remains is mostly the missing address model: `cstr:address-compare` (1,244 of
1,478 are in one function, `sqlite3__wasm_enum_json`), `&buf[i]` into memory of unknown
provenance, pointer↔integer casts, and `sqlite3VdbeExec`'s `goto`s.

**With the generated `sqlite3.h`** (`scripts/sqlite_corpus.sh`: SQLite's own
`tool/mksqlite3h.tcl`, run by the `jimsh0` it ships for builds without `tclsh`; the
result is byte-identical to `./configure && make sqlite3.c`'s header) and SQLite's
linkage macros defined (`--define "SQLITE_API= "`; the trailing space matters, because
`c2cpg` crashes on an empty `NAME=`):

| Exporter / parse | Functions | Hole-free | Holes |
|---|---|---|---|
| after spec 011, checkout as is | 7,772 | 5,054 (65.0%) | 11,759 |
| same exporter, generated `sqlite3.h` + linkage macros | 8,105 | 5,736 (70.8%) | 10,451 |
| plus the `<operators>.` fix below | 8,105 | **5,724 (70.6%)** | 10,497 |

With the header c2cpg parses 367 more function bodies (mostly `src/test*.c`; net +333,
because some `<duplicate>N` names were renumbered); on the 7,738 present in both runs, 441 became hole-free and 43 lost it, all
to more precise refusals now that the types are known (a `sqlite3_module` initializer
had been a positional list; `*pOut = (int)iCur` with an unknown `sqlite3_int64`).
`op:cast*` holes fell 1,511 → 404 and `op:sizeOf*` 1,083 → 652. The header also
expanded the `SQLITE_OK`-style constants that hole-free functions had been reading as
free names: 1,597 hole-free functions read an unexpanded `SQLITE_`/`TK_`/`OP_` name
before, 291 after (`TK_`/`OP_` come from `parse.h`/`opcodes.h`, which are also
generated and still absent).

`<operators>.` fix: Joern names six compound assignments (`|=` `&=` `^=` `<<=` `>>=`
`%=`) with a plural `<operators>.` prefix that every `startsWith("<operator>")` test in
the exporter missed, so `x |= m` was exported as a call to a function of that name with
`x` passed by value: no hole, write lost. 157 "hole-free" functions had one; they now
translate like `x = x | m` (145) or hole honestly (12).

**Conformance sample.** Hole-free is still only an upper bound. `scripts/sqlite_sample.py`
selects the functions the C leg of `scripts/differential.py` can run without inventing
anything: hole-free, call-closed through candidates only, every parameter and the return
an integer type, no preprocessor line in the body, no free names, compiled by the default
amalgamation of the same checkout. **9 of 5,724** qualify (most take a pointer or
return `void`). Round 1 measured **140/170 agree, 30 diverge, 10 inconclusive** against
`cc`, and all 30 divergences were one root cause: C's comparison and logical results are
`int` 0/1, Core's were `Val.bool`, and Core's `==` on `bool`/`int` was false, so
`int t = (a<b); if (t == 1) return 7; return 3;` returned 3 where `cc` returns 7. Core
now promotes a `bool` to 0/1 wherever it meets a number under `.cLike`
(`Dialect.promotesBool`; the C++ rule, unreachable from well-typed Java/Go/Kotlin, which
share the dialect), and the harness reads a `bool` result as 0/1 (the C return
conversion). Same sample, same 20 random cases each: **170/170 agree, 0 diverge, 10
inconclusive**. The C leg is now typed (`csrc/ctypes.json`: real widths, signedness and
`_Bool`, arguments over each type's full range): **168/168 agree, 12 inconclusive**. The
inconclusive cases were holes or `outOfFuel` where `cc` has an answer, and both traced to
Core computing C `i64`/`u64` arithmetic at 32 bits (`validJulianDay`'s `<< 32`;
`vdbeSorterTreeDepth`'s `i64` loop wrapped and ran out of fuel). With width-typed integer
operators (STRATEGY.md §63; `Lang/Core/TypedInt.lean`) the re-selected sample gives
**198/198 agree, 2 inconclusive**, both genuine C undefined-behaviour shifts in
`sqlite3LogEstToInt`. A 15-case fixture, `tests/test_cboolint_cc.py`, pins the fix against `cc`.
`.cLike` float `%` is now Java's truncated remainder (`-5.5 % 2.0` is `-1.5`), not
Python's floored one. See `docs/scale.md`.

**Address model and integer widths (STRATEGY.md §60, §63).** Two later changes moved the
census in opposite directions, both for honest reasons. The block-plus-offset address
model (`Expr.ptrOp`) translates pointer comparison, `&p[i]` and pointer arithmetic within
one array: on the amalgamation, hole-free went **1,907 → 1,985** with no function gaining a
hole. Width-typed integer arithmetic then made every C integer operation carry its type and
turned an unresolvable type into the hole `op:int:unresolved-type` instead of a 32-bit
default: amalgamation hole-free **1,985 → 1,774** (the 211 lost functions had been counted
hole-free while computing at the wrong width; 1,073 `op:int:unresolved-type` holes remain,
mostly members of nested/anonymous structs). Full tree with both: **5,295 of 8,105**
hole-free; there is no full-tree run isolating each change. Fixtures pin both against the
real compilers: 282/282 address cases agree with `cc` (38 refused as undefined
behaviour), 23/23 C width cases with `cc -fwrapv`, 22/22 Java cases with `java`.
Go and Kotlin integer arithmetic got the same treatment (STRATEGY.md §66): operators carry
their operand type (Go `*:g64`, `-:w08`; Kotlin `*:k64`, `-:q32`) with each language's own
overflow, shift and division rules, and the fixtures pin them against the real runtimes: 55
of 56 Go cases agree with `go` (the 56th is a documented hole) and 61 of 61 Kotlin cases
with the Kotlin compiler; with the previous exporter the same CPGs gave 15 and 20 agreeing.

## The oracle

Each item below was found by the tooling, not designed in. On its first run the
differential harness found a bug:

```
DIVERGENCE fmod(6, -9): cpython=-3 lean=6
DIVERGENCE gcdish(16, -20): cpython=-4 lean=4
```

Python floors integer division and modulo; C and Java truncate toward zero. The
semantics had assumed one convention. The fix was not to patch an operator but to make
the semantics **dialect-parameterized** (`Core.Dialect`), with the transpiler recording
the source language. Mislabelling C as Python reproduces 7 divergences, so the harness
discriminates.

This is the failure mode `STRATEGY.md` §5 describes — a proof about a semantics that does
not match the runtime — caught automatically rather than by inspection.

## Layout

| Path | Layer | Role |
|---|---|---|
| `Autoform/Lang/Core/Syntax.lean` | 3 | Universal deep embedding: objects, heap, exceptions, containers, iteration. `Expr.hole`/`Stmt.hole` are the effect boundary. |
| `Autoform/Lang/Core/Semantics.lean` | 2 | Fuel-indexed total interpreter with an explicit heap, method dispatch, exceptions. Dialect-parameterized. No `sorry`, no `partial`. |
| `Autoform/Lang/Core/Float.lean` | 2 | IEEE-754 binary32/binary64 as explicit bit patterns (`Fl`), exact-rational rounding, Python float semantics. Wired into `Val.float` (see "Not yet built" for what still holes). |
| `Autoform/Lang/Core/TypedInt.lean` | 2 | Width-typed integer operators. The exporter names the operand type inside the operator (`"*:i64"`, `"+:j64"`, Go `"*:g64"`, Kotlin `"*:k64"`); Core converts the operands to that type and runs the operation at that width under the language's own overflow, shift and division rules. An unresolved type is the hole `op:int:unresolved-type` (§63, §66). |
| `Autoform/Lang/Core/Address.lean` | 2 | C address model: block plus offset. Pointer comparison, `&p[i]` and pointer arithmetic within one array are answered from the heap; undefined or unspecified cases are holes (§60). |
| `Autoform/Lang/Core/Boxed.lean` | 2 | Python lists and dicts as heap objects, so `e[i] = v`, `del e[i]` and `append`/`pop` are seen through every alias. See `docs/boxed-containers.md`. |
| `Autoform/Contracts.lean` | 5 | Contracts at holes: `RefinesUnder`, refinement relative to stated assumptions about named holes. See `docs/contracts.md`. |
| `Autoform/HoleContracts.lean` | 5 | Contracts at *statement* holes, with worked examples on real cachetools code (`delitem_refines`, `rrclear_under`). |
| `Autoform/Ledger.lean` | 6 | Coverage, holes-by-cause, verifiable core; JSON evidence for the assurance case. |
| `Autoform/Tactics/Portfolio.lean` | 5 | Tiered proof portfolio; records open obligations instead of admitting them. |
| `scripts/audit_all.py` | 6 | Axiom sweep over every declaration, source sweep for escape hatches, and the independent kernel replay (`leanchecker --fresh`). `--skip-kernel` reports the replay as DELEGATED (never a pass); `--kernel-only` runs just the replay, which CI does as its own job because it takes hours. |
| `scripts/provenance.py`, `check_provenance.py`, `check_render.py`, `check_specs_fresh.py` | 6 | Which committed artifacts were produced by what: every tracked AST is attributed (tool, version, source revision, exact command, exporter digest) or named in `provenance/unattributed.json`; committed Lean modules are renders of committed ASTs; specs describe the corpus in the tree. |
| `scripts/mutate.py` | 4 | Source-level mutation gate — the *sufficient* anti-vacuity test. |
| `scripts/sacm.py` | 6 | SACM assurance case + in-toto attestation. |
| `scripts/fvspec.py` | 4 | Vacuity screen over the FVSpec benchmark. |
| `Autoform/Harness/Audit.lean` | 6 | `#audit_axioms`, `#audit_depends`, `#audit_ledger` — Lean metaprogramming. |
| `Autoform/Harness/Conformance.lean` | 4 | Specimen-derived generators; the refutation gate. |
| `Autoform/Lang/Imp/*` | — | Minimal worked example with a proved `evalStmt_sound`. |
| `cartographer/formalization_graph.sc` | 1 | Joern query: call graph, effects, formalizability score. |
| `cartographer/export_ast.sc` | 3 | CPG → neutral AST. Deterministic; no LLM on this path. |
| `cartographer/render_lean.py` | 3 | Neutral AST → Lean. Infers dialect from file extension. |
| `scripts/differential.py` | 2 | Conformance oracle vs CPython / `cc`. |
| `tests/test_*_{cpython,node,cc,java,go,kotlin}.py`, `tests/fixtures/*` | 2 | Fixtures pinned against the real runtime: each exported by the current exporter (the fixture's `exporter_sha256` is checked, `tests/test_fixture_exporter_fresh.py`), rendered to Lean, evaluated by Core, and compared with CPython, Node, `cc`, `java`, `go` or the Kotlin compiler. |
| `Demo.lean` | — | Refutation gate, axiom audit, vacuity detection, ledger. |

## Design commitments

- **Nothing is silently dropped.** Untranslated constructs become holes tagged with the
  CPG node label that produced them, and the ledger counts them by cause.
- **Ignorance ≠ behaviour.** `outOfFuel` (didn't run long enough), `hole` (didn't
  translate), and a real value are three distinct outcomes.
- **The gate never manufactures its own evidence.** It uses `Testable.check`, never the
  `plausible` tactic, which closes goals with `sorry` — the thing the audit exists to
  catch.
- **Total semantics.** Structurally recursive on fuel; no `partial`, no `sorry`.

## Findings the tooling produced (not designed in)

- **Dialect arithmetic.** The differential harness caught Python's floored `%` against
  Lean's `Int`, which had mistranslated every C and Java program. Fix: the Core language
  is now parameterized by dialect.
- **Vacuity the dependency check cannot see.** The mutation gate scored `evalStmt_sound`
  at 25% (WEAK) — all six survivors were `evalBExpr` mutations, because `BigStep`'s side
  conditions are stated in terms of `evalBExpr` itself, so a mutation changes both sides
  of the equation. Adding independent characterization lemmas raised the *reported* score
  to 100%, but that run had no per-theorem attribution. Re-run with attribution
  (`mutation-Imp.json`; Lean 4.30.0-rc1, every one of the 48 mutants of
  `Autoform/Lang/Imp/*` run, 0 coarse attributions): at the 46c65fc theorems, **18 of 27**
  valid `Semantics.lean` mutants and **0 of 9** `Syntax.lean` (store) mutants were killed by
  any theorem; `evalStmt_sound` itself killed 7/27. The `evalBExpr` lemmas do kill their
  mutants. Two of them (`evalBExpr_and_ne_or`, `evalBExpr_tt_ne_ff`) killed nothing, because
  they were proved by `simp` through lemmas that had already failed, and Lean's error
  recovery kept those lemmas. The same vacuity reached `evalExpr` (`+`/`-`/`*` swaps
  survived everything), the store (`State.get`/`set`), and the hole/fuel distinction
  (reporting a hole as `.outOfFuel` survived, since `evalStmt_sound` constrains only
  `.ok`). Now added: `evalExpr_add/sub/mul`; the read-over-write laws `State.get_empty`,
  `get_set_self` and `get_set_ne`; `evalStmt_complete` (formerly an open obligation in
  `Portfolio.lean`); and `evalStmt_hole_complete` against an independent `HitsHole`
  relation. With those, **24/27** and **7/9** are killed. All 5 survivors are equivalent
  mutants: 3 are `_+1`→`_+0` fuel patterns already shadowed by the `0` arm, and 2 are
  store paddings that only append zeros, which `State.get` cannot observe. The rerun also
  fixed two `mutate.py` attribution bugs. A declaration-level error is reported at the doc
  comment above the keyword, and that comment was being credited to the *previous*
  theorem. A mutated definition that no longer elaborated was being scored as a kill,
  which caused 8 of `evalStmt_sound`'s 15 "kills" in the first rerun.
- **41% of the FVSpec benchmark is vacuous under static screening.** 3,833 of 9,352
  analyzed problems. The dominant pattern: Python determinism tests (`f(x) == f(x)`)
  transliterated into Lean, where purity makes them `rfl`. Spec *translation* is not spec
  *preservation*.
- **Short-circuit evaluation returned a wrong answer.** `safemod(-11, 0)` returned `0` in
  CPython and raised `ZeroDivisionError` in Lean, because `b != 0 and a % b == 0` divided
  anyway. It had been conservative until exceptions were added — fidelity work makes other
  fidelity bugs findable, so the gaps are not independent.
- **A stale `.olean` made the oracle lie.** It answered with the previous semantics and
  produced 10 fictitious divergences before being caught. An oracle reading a stale cache
  is worse than no oracle: it is specifically wrong. Oracles must now establish they are
  reading the current artifact before reporting.
- **`<operator>.and`/`.or` are bitwise, not logical.** They had been mapped to `&&`/`||`,
  computing wrong answers. Now holes.
- **Static hole-freedom does not imply the program runs.** An untranslated callee is
  invisible in the AST, so the ledger reports hole-free, call-closed, and dynamic-hole
  risk as three separate numbers.

## Trust chain

Every link is mechanically checked, and each check is a different kind of oracle. The
status column was last measured at commit `16f7c88` (2026-08-20), except the hole count
(`99f386e`, 2026-08-22; `scripts/check_docs.py` re-checks it against `ast-Cachetools.json`
on every run). The differential and mutation rows predate the current 209-function
population (see `docs/languages.md`) and have not been re-run against it.

| link | oracle | status |
|---|---|---|
| semantics matches the real runtime | differential testing vs CPython / `cc`, inputs recorded from the corpus's own test suite | **42 of 209** `cachetools` functions compared, **220/220 cases agree, 0 divergences** since the re-export with the class table and builtin exception classes resolving through `builtins` (STRATEGY.md §62); before it, 48 compared and 12 divergences, all root-caused to Core's name-suffix resolution and now named holes, not exclusions ([docs/conformance.md](docs/conformance.md)) |
| specifications constrain behaviour | source-level mutation gate | **78/88 (88.6%)** on the translated module; 10 survivors, all analysed. **Not re-run since the two `mutate.py` attribution fixes** (see Findings): treat it as unverified for the current tree. The attributable re-run covers `Autoform/Lang/Imp/*` only (24/27 and 7/9 killed) |
| proofs depend on no unsound axiom | axiom sweep over every declaration (`audit_all.py --skip-kernel`, 2026-10-02) | clean: 7,974 declarations, using only `propext` (2,609), `Quot.sound` (1,495) and `Classical.choice` (1,422); no `axiom` of our own; no `sorryAx`/`ofReduceBool`/`ofReduceNat`; no escape hatch under `Autoform/Lang/Core` |
| `.olean`s match a kernel replay | `leanchecker --fresh` | **not observed on the current tree.** It passed when the import graph was small (about 1.5 minutes). With the 73 V8Base spec parts in the graph it takes hours: about 2.5-3 h single-threaded, *extrapolated* from five timed pieces (core 396 s, `V8Base.Base` 291 s, `Part1` 283 s, `Part33` 574 s, `Part60` 774 s), because both attempts at a full run were lost (one to the audit's own old 60-minute timeout, one to a container restart). CI therefore runs it as its own job, `kernel-replay`; see Continuous integration |
| untranslated code is declared | hole counting + SACM assumptions | 46 holes, all named |

The second row used to read "100%, HAS TEETH". That number was an artifact of the gate,
not a property of the specifications: `scripts/mutate.py`'s `error_lines` regex matched
the *older* Lean diagnostic format, so on this toolchain it never matched anything and
every "kill" came from the coarse "the build failed, credit all theorems" fallback. There
was no per-theorem attribution behind it. The on-subject score against
`Autoform/Generated/Cachetools.lean` is 78/88, with all 10 survivors analysed — 4 are
docstring deletions, 1 is an observably identical `.ret unit` → `.expr unit`, 2 are
operand swaps under a self-comparison witness, 2 sit behind a `Stmt.hole`. G4 is recorded
UNSUPPORTED rather than suppressing the equivalent mutants to turn it green.

The 78/88 run's output is not in the repository. The tracked `mutation-Cachetools.json`
is a *different* run (seed 20260819, `generated-ast` operators, against
`Autoform/Specs/CachetoolsSpec.lean`): 57 mutants, 2 invalid, and 50 of the remaining 55
killed by at least one theorem (counted from its `mutants[].verdict`). Do not quote one
run's score as the other's.

The first row used to read "100% on all corpora", which was wrong in both directions.

It was wrong to say 100%, because the denominator is small. Only 42 of 209 `cachetools`
functions are compared (60 before the item-L re-export of `ast-Cachetools.json`, whose
honest parameter defaults hole 12 previously compared functions; 48 before the item-M
re-export with the class table, which turned the 12 remaining divergences and 10 legacy
agreements on a fake `OrderedDict` into named holes) (`python3.11 scripts/differential.py ast-Cachetools.json
<cachetools@01af8e5> Cachetools 5`). The rest are INCONCLUSIVE, and each one carries a
counted reason in `conformance.json`: a value the harness cannot encode, a receiver it
cannot build, or a hole. **The limit is reach, not agreement.** A conformance rate quoted
without its coverage is the self-flattering metric this project keeps finding.

The "0 divergences" this row also used to show was partly the recorder's doing. It wrote
down generator yields as return values, and that agreed with an exporter that translates
`yield` as `return`, so `TLRUCache.__iter__` counted as an agreement. It also replayed
closures without their captured variables, and it refused, as parameter mismatches, the
calls that would have exposed an exporter call misbinding. With the recorder fixed, the
same corpus at the same commit gives 14 divergences. They are three findings, not noise.
The exporter halves of findings 1 and 2 are now fixed (generators are holes; a call through
a local name is emitted by that name); after the re-export the count is 12. The Core
halves (method lookup along the C3 MRO, bare names by Python scoping) and the re-export
with the class table take it to 0, with 215 of 215 compared cases agreeing (220 of 220,
42 functions, once builtin exception classes resolve through `builtins`). See
[docs/conformance.md](docs/conformance.md).

It was then briefly wrong in the other direction: an intermediate run reported 5
divergences, and this file attributed them to `class _HashedTuple(tuple)`. That
attribution was false. All five were an artifact of a **concurrent mutation run** holding
`Autoform/Generated/Cachetools.lean` — `_DefaultSize.pop` was a live mutant returning 0
instead of 1, and it is in that run's `decls` list. The harness now detects the
`.mutate-backup` sentinel, sets `build_stable: false`, and refuses to let a mutated module
be read as a divergence. See STRATEGY.md §33.

The `_HashedTuple` gap was real but separate, and is now closed in both the semantics
and the oracle: an instance of a class whose single base is `tuple`/`list`/`dict`/`str`
is `Val.bobj cls payload` (STRATEGY.md §35), and `scripts/differential.py` encodes
CPython's instance the same way and compares **class and payload**, so a result that
loses or invents the class is a divergence rather than agreement. On `cachetools` v7.1.7
`representation:value-vs-object` is 0 INCONCLUSIVE, and the four `_HashedTuple` methods
are now attempted instead of skipped as `self-not-object` (1,358 skipped calls → 0);
`__add__`, `__radd__` and `__getstate__` are compared and agree. See STRATEGY.md §57.

`leanchecker` ships with the Lean toolchain itself from v4.28.0 onward, so the pinned
toolchain (`lean-toolchain`: v4.30.0-rc1, see Dependencies) already includes it as
`lake env leanchecker`. The standalone `lean4checker` is deprecated and there is no
Homebrew formula. **Use `--fresh`**: without it the checker can silently pass
a root module that has only imports, which is `Autoform.lean`'s shape.

## Not yet built

- **Boxed mutable containers, remainder.** Python list/dict displays are heap objects;
  `e[i] = v`, `del e[i]` and `append`/`pop`/... write through every alias. Still holes:
  slices, live dict views, mutation during iteration, list/dict subclasses, and the
  differential oracle's encoder still passes lists/dicts by value (`docs/boxed-containers.md`).
- **Scoping and calling convention, remainder.** `nonlocal` writes (cell conversion),
  literal default values, keyword-only/positional-only parameters and starred assignment
  are translated (STRATEGY.md §58). Still holes: non-literal defaults
  (`param:default-nonliteral`; Core would have to execute `def`), the `TypeError` for a
  missing required argument, late-binding reads of captured non-`nonlocal` variables, and
  `scope:del-cell`.
- **Floats, partially.** `Val.float`/`Lit.float` exist and are wired: the exporter emits
  float literals, `render_lean.py` encodes them as exact binary64 bit patterns, and
  `Semantics.lean` evaluates `+ - * / %` (with int→float promotion), the six comparisons
  (exact int/float comparison under `.python`, promote-then-compare under `.cLike` and
  `.javascript`), unary `-`, truthiness and `==` (NaN ≠ NaN, `-0.0 == 0.0`). Still holes:
  float `//` (`binop://:float-floordiv`), float `**` (`float:pow`), casts to a floating
  type in C (`op:cast:float`), and `float()`/`str()`/`repr()` conversions (the Python
  stdlib model has no float builtins). Float `%` is the truncated remainder (`fmod`) under `.cLike` and `.javascript`
  (`-5.5 % 2.0` is `-1.5`, as in C, Java and Node) and the floored one only under `.python`.
  Python `/` on two ints is
  true division (a correctly rounded float when both operands are at most 2^53 in magnitude,
  the hole `binop:/:int-true-division-beyond-2^53` beyond that, `ZeroDivisionError` for a zero
  divisor), `//` is its own operator, and `bool` is an `int` under `.python` (`True == 1`,
  `True + True == 2`; `bool & bool` stays `bool`): `Autoform/PyArith.lean`,
  `tests/test_pyarith_cpython.py`, STRATEGY.md section 64. The differential harness
  now encodes float arguments recorded from the test suite (`docs/conformance.md`).
- **Contract *inference* at holes.** The mechanism for reasoning about partially translated
  functions under named assumptions exists (`Autoform/Contracts.lean` for expression holes,
  `Autoform/HoleContracts.lean` for statement holes), as do the ledger's separate
  conditional count and a worked example (`docs/contracts.md`); every hole contract is
  still hand-written.

## Continuous integration

`.github/workflows/ci.yml` runs four jobs.

- **`pytest (Python tooling)`**: the whole `tests/` suite and `check_provenance`. No Lean, no
  Joern. Minutes.
- **`build + trust audit`**: the build, in stages, then the axiom and source audit
  (`audit_all.py --strict --skip-kernel`), `check_render`, `check_specs_fresh`, the cachetools
  conformance oracle (must compare more than zero functions), a regenerated ledger and
  `check_docs`, three guard checks (the FuelMono exclusion list is exactly
  `["Stmt.tryFinally"]`; the proof-inventory floors do not shrink; the cachetools spec still
  records the refutation, not the premise), and the demo. The build is staged because a single
  `lake build` ran several V8Base parts at once, and one heavy part alone peaks at 6.6-8.7 GB
  (measured), so the runner ran out of memory and was shut down partway through (runs 115 and
  117, exit 143, no Lean error): stage 1 builds everything except the 73 V8Base parts; stages
  2-6 build them one at a time (`scripts/ci_build_v8base_parts.sh FROM TO`); a final default
  `lake build` checks completeness. Each stage is followed by its own `.lake` cache save that
  runs even when the stage fails, so a runner loss costs at most one stage. The job limit is
  340 minutes. A cold build is slow: in the first run to get past 60 minutes, 472 of 497
  modules were built after 108 minutes.
- **`kernel-replay`**: `audit_all.py --kernel-only --strict`, the independent kernel replay,
  single-threaded and measured in hours. It needs the build job, restores the `.lake` that
  job saved, and fails fast on a cache miss instead of becoming a second build.
  `tests/test_ci_kernel_replay.py` fails if this job, or the build job's `--skip-kernel`,
  is removed.
- **`end-to-end pipeline (Joern, manual only)`**: not part of the gate.

**Status (2026-10-02):** `pytest` and `check_provenance` pass on `main`. The staged build
has not yet run on a real runner, and neither have the build job's later steps or the
`kernel-replay` job: the single-`lake build` layout that preceded it was ended by the
runner's memory limit in every run that got far enough (see STRATEGY.md section 67).
Three corpora (Ansible, LinuxCrypto, LinuxLib) have no committed AST by policy, and
`check_render` reports them as *not checked* (never as verified).

## Dependencies

Lean 4.30.0-rc1 (pinned in `lean-toolchain`; includes `leanchecker`) · [Specimen](https://github.com/strata-org/specimen) ·
[Plausible](https://github.com/leanprover-community/plausible) ·
[Joern](https://github.com/joernio/joern) 4.0.606 · Python 3 · a C compiler (for C conformance)

Used by the oracle tests: `cc` (the C fixtures need a C compiler), and, optional, `java`,
`node`, `go` (1.24 was used) and a Kotlin compiler (`kotlinc` on `PATH`, or
`AUTOFORM_KOTLIN_JARS`): the Java, Node, Go and Kotlin tests skip when their runtime is
absent. `differential.py` on cachetools needs Python 3.11. Exporting
JavaScript, TypeScript, Go and Kotlin needs the matching Joern frontends
(`jssrc2cpg`, `gosrc2cpg`, `kotlin2cpg` 4.0.606), which are not part of the base Joern
install; `docs/running.md` and the provenance records give the exact commands.
