# autoform

Build executable Lean 4 models of source and machine code using formal interpreters.
Coverage is incomplete and unsupported behavior is recorded explicitly. See
`STRATEGY.md` for the design and the build/buy audit.

Open-source CLI with paid engineering support. Original Autoform code uses
[Apache-2.0](LICENSE); bundled third-party material retains its
[own notices](THIRD_PARTY.md). The current package is an alpha. See
[support scope](SUPPORT.md) and [release acceptance](docs/releasing.md).

**Approach:** formalize the *language* rather than the program. The program becomes data,
and every property is a theorem about `eval` applied to it.

**Language coverage:** source code uses Joern frontends and a shared Core interpreter,
with language-specific gaps. A separate machine-code path uses SLEIGH raw p-code and
fixed-width Lean semantics for compiled code and assembly. Neither path currently
formalizes every language or instruction set faithfully. See
[machine-code support and remaining gaps](docs/machine-code.md).

## Use

Install from a checkout with Python 3.10+:

```sh
python -m pip install '.[machine]'  # omit [machine] for source code only
autoform doctor
autoform https://github.com/OWNER/REPOSITORY.git
autoform --workspace ./proofs source /path/to/source MyProject
autoform --workspace ./proofs machine /path/to/executable MyBinary
```

The package bundles the Lean library, Joern exporter, proof tools and examples.
Git, Lean/elan, Joern and the source language's runtime are external prerequisites.
Each workspace holds its own build cache and evidence; installed package files stay
read-only. See [pip installation and CI releases](docs/packaging.md).
`doctor` checks tool availability and validates Lean and Joern against the versions
pinned in this package, returning `1` if a required tool is missing or mismatched.
It does not run the release checks.

A Git URL inventories the repository and runs supported source languages through
translation, native comparisons, proof generation, mutation checks and independent
proof replay. Mixed-language repositories receive separate language results and a
combined report. Unsupported and unparsed files remain visible in the file inventory;
an unsupported-only repository receives a gap report with no proof claims.
Use `--ref <commit-or-tag>` to select a revision and `--subdir <path>` to select
part of a repository. The exact checkout commit is recorded automatically.
A repository cloned from a URL is deleted when the run ends; the recorded commit, not
the temporary path, is what makes the result reproducible. Pass `--keep-checkout` to
retain it under `<workspace>/sources/` for inspection. A source directory you supply
yourself is never deleted.
Each assurance stage has a two-hour deadline; `--stage-timeout SECONDS` changes it.
Timed-out stages retain their logs and withhold verification.
`.autoform-work/artifacts/pipeline/Translated/guarantee.json` states the proved properties, recorded
input cases, assumptions, and evidence hashes. It does not guarantee that arbitrary
software is bug-free; failed or unsupported checks produce an explicit gap report.
The assurance command returns `1` for unresolved gaps. Inspect `run.json` alongside
the scoped certificate: a certificate can verify particular properties while the
broader assurance case still has gaps.
See [repository analysis and language routing](docs/repository-analysis.md) for the
inventory, per-language evidence, source stability and remaining capability limits.

Supply independent security requirements in `autoform.properties.json` at the root
of the selected source directory, or override them with `--properties properties.json`.
The tool attempts those Lean propositions, checks their dependence on the selected
functions, runs mutation checks and independently replays the proofs. Quantified
claims retain their stated domain; failed proof attempts remain open obligations.
See [security properties and the runnable ownership example](docs/security.md).

From a checkout, the original entry points remain available:

```sh
./autoform.sh <source-dir> [ModuleName]   # translate + native conformance + kernel proofs
./assure.sh   <source-dir> <ModuleName>   # the above, plus audit, mutation gate, SACM case
./autoform.sh --machine <binary> <ModuleName> # machine semantics + coverage report
```

```
source ──Joern──▶ CPG ──▶ neutral JSON AST ──▶ Lean Core program ──▶ trust ledger
                   │                                   │
                   └─▶ formalization graph             └─▶ differential vs real runtime
```

For assembly and concrete kernel-checked assertions, start with:

```sh
python3.11 -m venv .venv   # machine dependencies require Python 3.10+
.venv/bin/python -m pip install -r requirements-machine.txt
./autoform.sh --machine examples/machine/add_aarch64.s Add \
  --assemble aarch64-unknown-linux-gnu --entry 0 \
  --register x0=3 --register x1=4 --stop 4 --expect x0=7
```

This proves the specified observation of the generated model. It does not prove
the compiler/lifter correct or infer a specification for all inputs.

> **Numbers in this file go stale.** A dozen artifacts describe the same metrics and they
> drift apart. Regenerate rather than trust:
> `./autoform.sh <src> <Name>` prints the ledger; `python3 scripts/sacm.py --module <Name>`
> prints the assurance case. `docs/` explains what each number means.

## Verified end to end

| Corpus | Language | Functions | Verifiable core | Conformance vs real runtime |
|---|---|---|---|---|
| `cachetools` (real repo) | Python | see below | see below | see below |
| stress corpus | Python | 6 | 6 (100%) | **30/30 (100%)** vs CPython |
| sample | Python | 5 | 2 (40%) | **10/10 (100%)** vs CPython |
| ctest | C | 5 | 5 (100%) | **25/25 (100%)** vs `cc` |
| shortcircuit | Python | 1 | 1 (100%) | **6/6 (100%)** vs CPython |

The generated Lean in these runs type-checks. Hole-free functions are candidates for
verification; that classification alone proves neither source equivalence nor correctness
for all inputs. The generated theorem statements and guarantee reports define the scope.

Three figures are reported, because one number would mislead (`STRATEGY.md` §17):
**hole-free** (no static holes) is an upper bound; **call-closed** additionally requires
every callee to resolve inside the program, and is the verifiable core;
**dynamic-hole risk** counts constructs that can still hole on some input.
Static hole-freedom does not imply the interpreter never holes — an untranslated callee
is invisible in the AST.

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
| `Autoform/Ledger.lean` | 6 | Coverage, holes-by-cause, verifiable core; JSON evidence for the assurance case. |
| `Autoform/Tactics/Portfolio.lean` | 5 | Tiered proof portfolio; records open obligations instead of admitting them. |
| `scripts/audit_all.py` | 6 | Axiom sweep over every declaration + source sweep for escape hatches. |
| `scripts/mutate.py` | 4 | Mutation gate — tests whether selected changes to the translated subject invalidate its specifications. |
| `scripts/sacm.py` | 6 | SACM assurance case + in-toto attestation. |
| `scripts/fvspec.py` | 4 | Vacuity screen over the FVSpec benchmark. |
| `Autoform/Harness/Audit.lean` | 6 | `#audit_axioms`, `#audit_depends`, `#audit_ledger` — Lean metaprogramming. |
| `Autoform/Harness/Conformance.lean` | 4 | Specimen-derived generators; the refutation gate. |
| `Autoform/Lang/Imp/*` | — | Minimal worked example with a proved `evalStmt_sound`. |
| `cartographer/formalization_graph.sc` | 1 | Joern query: call graph, effects, formalizability score. |
| `cartographer/export_ast.sc` | 3 | CPG → neutral AST. Deterministic; no LLM on this path. |
| `cartographer/render_lean.py` | 3 | Neutral AST → Lean. Infers dialect from file extension. |
| `scripts/differential.py` | 2 | Conformance oracle vs CPython / `cc`. |
| `Demo.lean` | — | Refutation gate, axiom audit, vacuity detection, ledger. |
| `Autoform/Lang/Core/Syntax.lean` — `Payload`, `Val.unbox`, `DefaultValue` | 3 | Boxed containers (`Obj.payload`, `Obj.version`); the view through a box that splatting and indexing read; and the closed two-constructor type of parameter defaults Core can bind without function-object state. |
| `Autoform/Lang/Core/Semantics.lean` — `execForRef` | 2 | Live iteration over a boxed container: a list re-reads its payload per step, a dict raises `RuntimeError` when `Obj.version` moves, as CPython's iterators do. |
| `Autoform/FuelMono.lean` | 2 | Eight-way simultaneous fuel-monotonicity induction over the interpreter. Every recursive branch needs a clause; a new one announces itself here. |
| `scripts/check_provenance.py` | 6 | Every tracked AST is attributed to a Joern build + exporter hash, or named in `provenance/unattributed.json` with a reason. Required CI gate. |
| `scripts/synth_specs.py` | 4 | Layer-4 specification synthesis from observations; emits `Autoform/SpecsGen/*`. |

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
  at 25% (WEAK) — every survivor was an `evalBExpr` mutation, because `BigStep`'s side
  conditions are stated in terms of `evalBExpr` itself, so a mutation changes both sides
  of the equation. Characterization lemmas were added to fix that, and a 100% score was
  reported; that figure was never attributable, because `scripts/mutate.py`'s
  `error_lines` regex did not match this toolchain's diagnostics. Both the regex and the
  coarse "credit every theorem" fallback are now gone, and the gate has been **re-run
  over all 39 mutants of `Autoform/Lang/Imp/*`** with attribution working
  (`mutation-Imp.json`, 0 coarse / 0 inconclusive):
  **24 of 27 scored mutants are killed by some theorem.** The 3 survivors are `_+1` →
  `_+0` on the fuel patterns, which are equivalent mutants — `| 0, _, _` is the first
  arm, so they are unkillable by construction. Two things the re-run found that the
  100% had hidden: `evalExpr` was characterized by nothing at all, so `+`→`-`, `-`→`+`
  and `*`→`/` survived every theorem in the file; and a hole reached under a loop could
  be reclassified as `outOfFuel` with no theorem objecting — the *"Ignorance ≠
  behaviour"* distinction two lines up. Both are now pinned. No single theorem scores
  above 26%: the useful quantity is the union, not a per-theorem percentage.
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
- **A Python trap named itself in prose.** `1 << -1` raised `.exn (.str "negative
  shift count")` where CPython raises `ValueError`, so `except ValueError:` could not
  catch it. `Numeric.lean`'s own dialect table had said `ValueError` all along; nothing
  compared the table to the code. Fixed, and `python_shiftCount_trap` keeps it fixed.
- **A `@property` read computed `unit`, silently, in the tracked corpus.** `c.currsize`
  calls a getter; the exporter lowered it to a field read; the field is name-mangled, so
  it does not exist; `evalExpr` answered `unit` with no hole. CPython says `1`. The read
  now holes, which *raised* the hole count by 18 — a metric that falls when a silent wrong
  answer is corrected is measuring the wrong thing (STRATEGY.md §57.6).
- **Re-exporting the stale corpus would have cost 86 functions.** 26 holes committed,
  134 in a fresh export, none of them bugs — the exporter had learned to refuse what it
  cannot model. The remedy everyone reaches for was measured and not applied
  ([integrity](docs/integrity.md)).
- **`nonlocal` was filed under "needs new semantics"; Core already expressed it.**
  Capturing a `Val.ref` by value shares the object behind it, which is a closure cell.
  The blocker was in the exporter, and the fix reused the boxing machinery built for C
  address-taken locals (STRATEGY.md §57.7).
- **163 became 3.** The container switchover broke 163 declarations across 34 files and
  was nearly abandoned as needing a corpus nobody has. 33 of the files were a `.cLike`
  corpus, only Python boxes, and one dialect gate removed them all. Same measurement,
  wrong inference, caught (STRATEGY.md §57.8).
- **The switchover left the oracle byte-identical.** Boxing every list and dict literal
  moved not one compared case on `cachetools`, because its inconclusive cases are
  unmodelled builtins, not containers. A capability can be verified against the runtime
  and leave every headline exactly where it was.
- **Cheaper to write is not cheaper to prove.** Property dispatch by a name marker needs
  no new `Ctx` field, and its side condition needs a proof that a name is *absent* from a
  209-entry table — which neither `rfl` nor `simp` can do. The `Ctx` field that cost 289
  declarations makes absence `[] = []`. Which design is cheap is not visible until the
  proof is attempted (STRATEGY.md §57.10).

## Trust chain

Every link is mechanically checked, and each check is a different kind of oracle:

| link | oracle | status |
|---|---|---|
| semantics matches the real runtime | differential testing vs CPython / `cc` | `conformance.json`: **219 agree, 0 divergences, 306 INCONCLUSIVE** on `cachetools` v7.1.7 re-exported by the current exporter (basis `python-exception-guards-v3`); 209/0/256 on the previous artifact, byte-identical before and after the container switchover. Coverage, not agreement, is the limit — re-measure with `scripts/differential.py ast-Cachetools.json <src> Cachetools` |
| specifications constrain behaviour | source-level mutation gate | **78/88 (88.6%)** on `Autoform/Generated/Cachetools.lean`, 10 survivors all analysed; **24/27** on `Autoform/Lang/Imp/*` with per-theorem attribution working (`mutation-Imp.json`) |
| proofs depend on no unsound axiom | axiom sweep over every declaration | clean — `propext`, `Quot.sound`, `Classical.choice` only; declaration count lives in `audit.json` (6,785 at the last recorded run, 2026-09-21; re-measure with `scripts/audit_all.py --strict`) |
| `.olean`s match a kernel replay | `leanchecker --fresh` | VERIFIED |
| untranslated code is declared | hole counting + SACM assumptions | 22 holes, all named |
| every AST names the exporter that made it | `scripts/check_provenance.py` | **0 violations**; 0 of 14 tracked ASTs attributed, all 14 named in `provenance/unattributed.json` with a reason |

The second row used to read "100%, HAS TEETH". That number was an artifact of the gate,
not a property of the specifications: `scripts/mutate.py`'s `error_lines` regex matched
the *older* Lean diagnostic format, so on this toolchain it never matched anything and
every "kill" came from the coarse "the build failed, credit all theorems" fallback. There
was no per-theorem attribution behind it. The on-subject score against
`Autoform/Generated/Cachetools.lean` is 78/88, with all 10 survivors analysed — 4 are
docstring deletions, 1 is an observably identical `.ret unit` → `.expr unit`, 2 are
operand swaps under a self-comparison witness, 2 sit behind a `Stmt.hole`. G4 is recorded
UNSUPPORTED rather than suppressing the equivalent mutants to turn it green.

The first row used to read "100% on all corpora", which was wrong in both directions.

It was wrong to say 100%, because the denominator is small: `conformance.json` compares
cases, not functions, and 256 of them are INCONCLUSIVE — a value the harness cannot
encode (`skip_unencodable_ret`), a receiver it cannot build (`skip_no_instance`), or a
hole reached during the run (`call:set`, `call:type`, `mcall:warnings.warn`,
`expr:genExp` are the current ones). **The limit is reach, not agreement.** A conformance
rate quoted without its coverage is the self-flattering metric this project keeps
finding — and the byte-identical result after the container switchover is the same
lesson from the other side: a real capability can leave the number exactly where it was.

It was then briefly wrong in the other direction: an intermediate run reported 5
divergences, and this file attributed them to `class _HashedTuple(tuple)`. That
attribution was false. All five were an artifact of a **concurrent mutation run** holding
`Autoform/Generated/Cachetools.lean` — `_DefaultSize.pop` was a live mutant returning 0
instead of 1, and it is in that run's `decls` list. The harness now detects the
`.mutate-backup` sentinel, sets `build_stable: false`, and refuses to let a mutated module
be read as a divergence. See STRATEGY.md §33.

The `_HashedTuple` gap is real but separate: Core has no inheritance from builtin types,
so instances are opaque `Val.ref`s while CPython's instance *is* a tuple. It surfaces as
a counted `representation:value-vs-object` INCONCLUSIVE, not as a divergence, because the
oracle cannot compare the two encodings.

`leanchecker` ships with the Lean toolchain (v4.28.0+) — `lean4checker` is deprecated and
there is no Homebrew formula. **Use `--fresh`**: without it the checker can silently pass
a root module that has only imports, which is `Autoform.lean`'s shape.

## Not yet built

Source coverage's four long-standing gaps now stand differently, and each claim below is
a measurement rather than an impression:

* **Mutable containers — done.** A Python list or dict literal allocates; containers have
  identity; `a = [1,2]; b = a; b[0] = 9` makes `a[0]` nine, as in CPython. See
  [the migration](docs/boxed-containers.md).
* **Cross-scope writes — done** for the case where the binding dominates the capture.
  `nonlocal` is boxed in the defining scope and shared with the closure; anything else
  still holes ([§11](docs/languages.md)).
* **Calling conventions — done.** Literal, in-program-function, module-attribute and
  class-attribute-sentinel defaults all bind (`Cache.pop(default=__marker)` is seeded
  from the heap where the binding happens), as do `@staticmethod`, `@classmethod` and
  `@property` definitions and recovered signatures. What remains is a receiver followed
  by nothing but `*args, **kwargs` — 11 functions in `cachetools`, listed below.
* **Language-specific numeric behavior — no open divergence.** The differential suite was
  run across the whole language matrix against real runtimes: 5 passed, 2 xfailed, and
  neither xfail is numeric ([typed numerics](docs/typed-numerics.md)).

`Val.float` is now wired into Core semantics; that does not establish coverage of all
source float operations or machine floating-point instructions. Boundary contracts exist,
but partially translated programs still need explicit assumptions and satisfiability
evidence.
See [the source-language measurements](docs/languages.md) and
[the machine-code gap list](docs/machine-code.md#remaining-work-toward-arbitrary-codebases)
for the scope of the remaining work, and [the goal statement](docs/GOAL-arbitrary-codebases.md)
for the bar it is measured against — eight milestones, each with the artifact that
proves it and the gate that fails if it regresses.

**The Python gaps, measured rather than listed.** A gap list without counts invites
picking the easy one. The table below is a **snapshot to re-measure, not a current
figure**: passes close labels concurrently, and a count in prose is stale the day it is
written. Last measured 2026-09-21 on `cachetools` v7.1.7 with the exporter at that
commit: **22 holes across 20 of 209 functions**, down from 134 across 111 at the start of
the pass (and from 97 across 74 midway, when 18 had been *added* because they were
concealing a wrong answer). Reproduce it before quoting it:

```sh
# from a checkout of cachetools v7.1.7 with src/cachetools as the export root
./autoform.sh /path/to/src Cachetools          # stage 3 leaves ast-Cachetools.json
python3 scripts/lang_matrix.py ast-Cachetools.json   # holes by cause, per corpus
```

| label | holes (snapshot) | what would close it |
|---|---|---|
| `call:python-receiver-signature` | 11 | every one was `def f(self, *args, **kwargs)` — a receiver followed by nothing but collectors (`_TimedCache.get/pop/setdefault`, the six `Descriptor.Wrapper.__call__`s, the two descriptor bases). **Done** since this snapshot: the stripped receiver's name travels in the signature (`receiverName`) and `kwargsRejected` refuses the `self=` keyword that `**kwargs` used to be able to swallow — the only thing the refusal was protecting (`#guard`s in `Semantics.lean`, `tests/test_python_receivers.py`). What still holes is a method with no ordinary first positional `self` (`def f()`, `def f(*, self)`, `def f(*self)`) or one named otherwise (`def f(receiver, a)`); re-measure to see the count move. Was 23 |
| `call:computed-callee` | 6 | `_cache.decorator` and the five `*_cache` factories call a closure chosen by a branch — the callee is a run-time value, not a name. Calling through an arbitrary expression — a value-callee form beside `Expr.call`'s name-callee — is the feature |
| `op:stringExpressionList:non-literal-part` | 3 | f-strings whose parts are not literals (the `_DescriptorBase` deprecation messages) — `str()` of an arbitrary value is the `__str__`/`__repr__` protocol, which Core does not model |
| `expr:genExp` | 2 | **lowered where it is consumed at once** — `tuple(g)`, `sum(g)`, `sorted(g)`, `"".join(g)` materialise the generator as a list, observationally equal for a finite iterable; `typedkey`'s two are that shape and go on the next re-land. A generator that is stored or returned keeps the hole: laziness is observable there. List and dict comprehensions lower outright, with the loop variable rebound so it cannot leak ([§10.6](docs/languages.md)) |
| `control:TRY-exception-representation` | 0 | **done** (was 34). The guard was standing in for a proof; `ExcSafe.lean` is the proof — under `.python` every exception Core raises names a represented class, by simultaneous induction over the interpreter ([§10](docs/languages.md)) |
| `call:python-property-access` | 0 | **done** (was 21). The getter runs: a `.field` read that misses the instance and names a `@property` of the receiver's class calls it (`Program.properties`), proved fuel-monotone; `Cache.maxsize`/`currsize` now translate and their theorems survived the re-land unchanged |
| `call:python-defaults` | 0 | **done** (53 → 0). Literals, in-program functions and module attributes bind at the call; the class-attribute sentinel `Cache.pop(default=__marker)` is seeded from the heap at bind time (`classAttrDefaults`) |
| `op:delete-index` | 0 | **done.** `del xs[i]` / `del d[k]` emit `Stmt.delIndex` on the boxed container; slices (`xs[a:b]`, `xs[a:b] = ys`, `del xs[a:b]`) landed with them, checked against CPython ([docs/boxed-containers.md](docs/boxed-containers.md)) |
| `scope:nonlocal-write` | 0 | **done.** The enclosing scope boxes the name, the closure shares the cell. Refused unless the binding dominates the capture — bound at top level before the first nested `def` — because a box that does not exist yet cannot be captured ([§10](docs/languages.md)) |

Each is a feature, not a fix. Two things this table is for: it is the reason
[re-exporting the tracked corpora was measured as a coverage regression rather than an
integrity fix](docs/integrity.md) — at 134 holes it was; at 97 it is closer — and it is
the order to work in.

## Dependencies

Lean 4.30.0-rc1 · [Specimen](https://github.com/strata-org/specimen) ·
[Plausible](https://github.com/leanprover-community/plausible) ·
[Joern](https://github.com/joernio/joern) 4.0.606 · Python 3 · a C compiler (for C conformance)
