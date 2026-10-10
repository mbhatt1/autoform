# autoform

**Executable Lean 4 models of real code, checked against the real runtime, with every
gap named.** A Python command and library over a Lean core: point it at a repository
and it translates the source into a formal interpreter's input, runs the project's own
test suite against the model, proves what it observed in the Lean kernel, attacks its
own proofs with mutants, and writes an evidence directory whose every claim is bound to
the artifacts that support it.

Autoform does not formalize *programs*; it formalizes the *language*. The program
becomes data (`Autoform.Core.Program`), and every property is a theorem about `eval`
applied to that data. Anything the translation cannot model faithfully is a named hole,
never a guess, and the hole counts are the coverage metric. There is no `sorry`, no
`native_decide` and no added axiom anywhere in the trusted path; a gate checks that on
every build.

Open-source (Apache-2.0 for original code; bundled third-party material keeps
[its own notices](THIRD_PARTY.md)) with paid engineering support
([scope](SUPPORT.md)). The package is an alpha: it does not warrant the correctness of
arbitrary software, and its reports say so. See [release acceptance](docs/releasing.md).

## Install

Python 3.10+ on macOS or Linux. External prerequisites: Git, Lean via `elan`, Joern,
and the runtime of each source language you want compared (CPython, `cc`, Java, Go,
Node, Kotlin). `autoform doctor` names every missing one and how to install it.

```sh
python -m pip install '.[machine]'      # omit [machine] for source code only
autoform doctor
```

The distribution is `autoform-lean`; the command and import name are `autoform`. Pip
installs the Python package with a bundled runtime (the Lean library, the Joern exporter,
the oracle scripts); the heavy toolchains run in a **workspace** (`--workspace`, default
`.autoform-work`) that holds the build cache and evidence, so installed files stay
read-only. [Packaging and CI releases](docs/packaging.md).

## Sixty seconds

```sh
autoform https://github.com/tkem/cachetools.git Cachetools --ref v7.1.7 --subdir src
```

A Git URL alone is the full assurance workflow: clone at `--ref`, inventory the
repository, translate every supported language, compare the model with the real runtime
on the repository's own tests, prove the observations, run the mutation gate, audit the
axioms, replay the proofs in a fresh kernel, and write
`.autoform-work/artifacts/pipeline/Cachetools/guarantee.json`. Exit `0` means every
required check passed; `1` means the workflow finished with named gaps (the usual outcome
on a real repository — read `run.json` and `guarantee.json` together); `2` means it could
not run.

```sh
autoform --workspace ./proofs source  /path/to/src MyProject     # translate, compare, prove
autoform --workspace ./proofs assure  /path/to/src MyProject     # ...plus gate, audit, assurance case
autoform --workspace ./proofs regress /path/to/repo MyProject --base v1.2.0 --head main
autoform --workspace ./proofs regress /path/to/repo MyProject --base v1.2.0 --machine --files lib/lcm.c lib/gcd.c
autoform --workspace ./proofs pr      /path/to/repo --base v1.2.0 --sarif pr.sarif --markdown pr.md   # evidence level per changed function
autoform --workspace ./proofs machine /path/to/binary MyBinary
autoform formalize MyProject            # infer and judge candidate claims, verify in the kernel
autoform autoformalize /path/to/src     # code -> English -> Lean statements -> kernel proofs
```

Every subcommand, flag, artifact, environment variable and exit code:
[**docs/cli.md**](docs/cli.md). Using it from Python, and reading the artifacts:
[**docs/library.md**](docs/library.md).

## What a run produces

`artifacts/pipeline/<Module>/` holds one JSON artifact per oracle, each a different kind
of evidence about the same model:

| artifact | says |
|---|---|
| `conformance.json` | every call the real runtime made into a translated function, replayed in Lean: **agree / diverge / inconclusive**, with the hole that stopped each inconclusive case |
| `ledger-<Module>.json` | static coverage: holes by cause, hole-free functions, the **verifiable core** (hole-free *and* every callee resolves in the program) |
| `specs.json`, `Autoform/SpecsGen/<Module>.lean` | the observations as kernel-checked theorems, open obligations stated as data, subjects excluded by name and why |
| `mutation.json` | whether the theorems notice changes to their subject — on-subject scores, every survivor listed |
| `audit.json` | axiom sweep, escape-hatch sweep, `leanchecker --fresh` replay, artifact snapshot |
| `guarantee.json` | the claims actually established, each bound to artifact hashes; `verified_scoped` or `unverified` with the failed checks named |

A claim is about the recorded inputs it names unless its theorem is universally
quantified; a scoped certificate can coexist with an assurance case that still has gaps.
Supply your own properties in `autoform.properties.json` and the run proves, gates and
replays them too ([security properties](docs/security.md)).

## How it works

```
source ──joern-parse──▶ CPG ──export_ast.sc──▶ neutral JSON AST ──render_lean.py──▶ Autoform.Generated.<M>
                                                        │                                  │ lake build
   repository's own tests ──sys.settrace──▶ recorded calls ──differential.py──▶ conformance.json
                                                                                           │
             ledger.lean ──▶ ledger.json      synth_specs.py ──▶ SpecsGen/<M>.lean ──▶ mutate.py ──▶ audit_all.py ──▶ guarantee.json
```

1. **Parse** — [Joern](https://github.com/joernio/joern) builds a code property graph. The frontend is pinned (`joern-version`); the neutral AST is a function of it.
2. **Export** — `cartographer/export_ast.sc` lowers the CPG into one language-neutral AST. An embedded Python sidecar (`ast`, `symtable`) answers what a CPG gets wrong about Python: scopes, signatures, class bodies, imports, bare annotations. What cannot be modelled faithfully becomes `Stmt.hole "<label>"`.
3. **Render** — `render_lean.py` prints the AST as a Lean term, deterministically; a model over 1000 functions is split into part modules Lean elaborates in parallel (`--shard-functions`).
4. **Type-check** — the model is a `Program` for the fuel-indexed, total interpreter in `Autoform/Lang/Core/Semantics.lean` (dialect-parameterized: Python, C-like, JavaScript, Java, Go).
5. **Conformance** — `scripts/differential.py` traces the project's own test suite, snapshots each receiver into a Lean heap literal, replays the call, and compares. "Not compared" is never "passed".
6. **Ledger** — `Autoform/Ledger.lean` counts holes by cause and computes the verifiable core.
7. **Specs** — `scripts/synth_specs.py` turns observations into `conform_*` theorems proved by kernel computation, mines algebraic laws and fuzzes them before emitting; each candidate is probed alone under a time/memory budget and excluded *by name* if it blows up.
8. **Gate** — `scripts/mutate.py` perturbs the generated program and rebuilds the specs; a theorem that notices no mutant of its subject is reported vacuous.
9. **Audit and guarantee** — `scripts/audit_all.py --strict` (axioms, escape hatches, fresh kernel replay), the SACM assurance case, `guarantee.json`.

A separate path formalizes **machine code**: binaries and assembly are lifted through
Ghidra's SLEIGH into raw p-code with fixed-width Lean semantics, for concrete
kernel-checked assertions and for `regress --machine`, which finds inputs on which two
commits' compiled functions differ and proves the divergence
([machine-code](docs/machine-code.md)). [Architecture](docs/architecture.md) describes
every module; [the trust model](docs/trust-model.md) says what is claimed and on what
basis.

## Scale

Peak memory used to grow with the generated module (about 300 MB of resident memory per
MB of Lean). Sharded rendering fixes that: Django's `django/` package — 10,658 functions
after lowering — builds in **244 s at 3.3 GB** peak against **459 s at 16.7 GB** as one
module, and the sharded `program` is kernel-equal to the unsharded one by `rfl`.
Measured 2026-10-09; the commands are in [docs/scale.md](docs/scale.md), which also
records where the pipeline breaks next and in what order.

## Fidelity, measured

The reference corpus is `cachetools` v7.1.7, re-landed on the current exporter on
2026-10-09. The figures below are read from the artifacts by `scripts/check_docs.py`,
which fails the build when a document and an artifact disagree.

| link | oracle | status |
|---|---|---|
| semantics matches the real runtime | differential testing vs CPython / `cc` | `conformance.json`: **94 agree, 0 divergences, 133 INCONCLUSIVE** on 227 cases of `cachetools` v7.1.7 re-landed 2026-10-09 (the September artifact compared 245: it carried no class metadata and so could not refuse the test suite's own `TTLCache` subclasses; see `docs/integrity.md`). Coverage, not agreement, is the limit — re-measure with `scripts/differential.py ast-Cachetools.json <src> Cachetools --tests <tests>` |
| the model translates the corpus | ledger | **204 of 209** functions hole-free, **150** in the verifiable core (`ledger-Cachetools.json`; `scripts/ledger.lean.tmpl`) |
| specifications constrain behaviour | source-level mutation gate | **68/73 (93.2%)** on-subject on `Autoform/Generated/Cachetools.lean` (2026-10-09, 51 mutants, 0 invalid; the 5 survivors and 2 untested theorems are all analysed in `Autoform/Specs/CachetoolsSpec.lean` §4); **24/27** on `Autoform/Lang/Imp/*` with per-theorem attribution (`mutation-Imp.json`) |
| proofs depend on no unsound axiom | axiom sweep over every declaration | clean — `propext`, `Quot.sound`, `Classical.choice` only (`scripts/audit_all.py --strict`) |
| `.olean`s match a kernel replay | `leanchecker --fresh` | VERIFIED |
| untranslated code is declared | hole counting + SACM assumptions | 5 holes, all named |
| every AST names the exporter that made it | `scripts/check_provenance.py` | the four Python corpora carry full provenance (`provenance/*.prov.json`, `exporter_sources` pinned) |

Three figures are reported because one would mislead: **hole-free** is an upper bound;
**call-closed** additionally requires every callee to resolve in the program and is the
verifiable core; **dynamic-hole risk** counts constructs that can still hole on some
input. The other re-landed corpora (`ledger-<M>.json`, `Autoform/SpecsGen/<M>.lean`):
requests 2.32.5 — 226/260 hole-free, core 134, 147 agree / 0 diverge, 29 specs;
click 8.2.1 — 475/549, core 265, 135 / 0, 47 specs with 12 subjects excluded by name;
jinja2 3.1.6 — 662/817, core 438, 133 / 0, 50 specs with 6 over the proof budget.

## Languages

| | translates | differential oracle | notes |
|---|---|---|---|
| Python | yes | CPython | the reference dialect: objects, closures, exceptions, generators, boxed containers, calling conventions, properties, class hierarchies with [external base contracts](docs/contracts.md) |
| C / C++ | yes | `cc` / `clang`, including Linux kernel units through a declaration shim | typed fixed-width numerics; UB is a hole, never a number |
| Java, Kotlin | yes | JVM | |
| Go | yes | `go` | |
| JavaScript, TypeScript | yes | Node | |
| machine code | SLEIGH p-code | native execution where the host can | ELF, PE, Mach-O, raw bytes, `.s` via clang |

Per-language coverage, with what each front end does and does not provide, is in
[docs/languages.md](docs/languages.md). Whole-repository formalization is not the goal:
the output is a verified core plus declared assumptions for everything else, and
[the goal statement](docs/GOAL-arbitrary-codebases.md) sets the bar as milestones with
named exit criteria.

## Design commitments

- **Nothing is silently dropped.** Untranslated constructs are holes tagged with the
  construct that produced them; the ledger counts them and the assurance case names each.
- **Ignorance ≠ behaviour.** `outOfFuel` (did not run long enough), `hole` (did not
  translate) and a value are three outcomes, never collapsed.
- **Only the kernel sets a status.** Judges rank, agents propose, oracles compare; a
  theorem is proved when Lean says so and audited when `leanchecker` replays it.
- **Total semantics.** Structurally recursive on fuel; no `partial`, no `sorry`.
- **A number nobody can reproduce by a named command is not a result.** Documents name
  the command; `check_docs.py` keeps the quoted figures equal to the artifacts.

## Findings the tooling produced

Each was found by an oracle, not designed in; the design record (`STRATEGY.md`) has the
full account.

- **Dialect arithmetic.** The first differential run found `fmod(6, -9)`: CPython −3,
  Lean 6. Python floors, C truncates. The semantics became dialect-parameterized.
- **A stale `.olean` made the oracle lie** — ten fictitious divergences from the previous
  semantics. Oracles now fingerprint the artifacts they read and re-run if they moved.
- **A live mutant was reported as a divergence.** The oracle now refuses a module with a
  `.mutate-backup` sentinel.
- **A `@property` read computed `unit`, silently.** The read now holes, which *raised*
  the hole count by 18; a metric that falls when a wrong answer is corrected measures the
  wrong thing.
- **A bare annotation was an attribute read.** `self.name: str` raised `AttributeError`
  in the model (click's `Parameter.__init__`); Language Reference §7.2.2 evaluates the
  target's sub-expressions and never its final access.
- **A bare call resolved to a method.** `set()` beside jinja2's only `….set`,
  `_MemcachedClient.set` — eight divergences, one resolution rule (`Ctx.resolveCall`).
- **Class metadata made the model honest and empty at once.** Recording hierarchies let
  the oracle refuse receivers it could not model; `class Cache(MutableMapping)` then
  compared 40 calls instead of 245. External base-class contracts, verified against the
  live class, brought it back to 94 with every inconclusive case named.
- **One theorem held 63 GB.** A click spec module sat in swap for 90 minutes; 47 of its 59
  theorems prove alone in seconds. Candidates are now probed alone under a budget.
- **41% of the FVSpec benchmark is vacuous under static screening** — 3,833 of 9,352
  problems, mostly determinism tests that purity makes `rfl`.
- **The mutation gate's "100%" was an artifact of the gate.** Its diagnostic regex never
  matched this toolchain, so every kill came from a coarse fallback. Attribution is now
  per theorem and the fallback is gone.

## Not yet built

The four gaps that stood for most of the project's life, each stated as a measurement
rather than an impression:

* **Mutable containers — done.** A Python list or dict literal allocates; containers have
  identity; `a = [1,2]; b = a; b[0] = 9` makes `a[0]` nine, as in CPython
  ([the migration](docs/boxed-containers.md)).
* **Cross-scope writes — done** where the binding dominates the capture. `nonlocal` is
  boxed in the defining scope and shared with the closure; anything else still holes
  ([§11](docs/languages.md)).
* **Calling conventions — done.** Literal, in-program-function, module-attribute and
  class-attribute-sentinel defaults bind; `@staticmethod`, `@classmethod` and `@property`
  definitions and recovered signatures translate; a receiver followed by only
  `*args, **kwargs` binds; a callee that is a run-time value is called
  (`Expr.callValue`). Every calling shape `cachetools` uses translates.
* **Language-specific numeric behavior — no open divergence.** The differential suite
  runs across the whole language matrix against real runtimes: 5 passed, 2 xfailed,
  neither xfail numeric ([typed numerics](docs/typed-numerics.md)).

What remains is listed per language in [docs/languages.md](docs/languages.md) and for
machine code in [docs/machine-code.md](docs/machine-code.md); the bar is
[the goal statement](docs/GOAL-arbitrary-codebases.md). Generator expressions that are
stored or returned, `async`/`await`, decorators the exporter cannot apply
(`functools.total_ordering`), and stdlib classes beyond the contracted ABCs are the open
Python items; each is a counted hole label, not a silent approximation.

**The remaining cachetools holes, measured.** The table is a snapshot to re-measure, not
a current figure: passes close labels concurrently, and a count in prose is stale the
day it is written. Reproduce it before quoting it:

```sh
./autoform.sh /path/to/src Cachetools                  # stage 3 leaves ast-Cachetools.json
python3 scripts/lang_matrix.py ast-Cachetools.json     # holes by cause, per corpus
```

| label | holes | what it is |
|---|---|---|
| `class-construction:unresolved-lexical-identity` | 5 | `collections.OrderedDict()` and `weakref.WeakKeyDictionary()` in the cache constructors: the exporter declines to allocate an instance of a class it cannot identify, where it used to hand back an opaque object. A contract for those two classes, like the external base-class contracts in [docs/contracts.md](docs/contracts.md), would close it. |

On 2026-10-09 that is 5 holes across 5 of 209 functions; on 2026-09-21 it was 3 across
2, down from 134 across 111 at the start of the pass that closed them.

## Documentation

[docs/README.md](docs/README.md) is the index. Start with
[cli.md](docs/cli.md), [library.md](docs/library.md) and
[architecture.md](docs/architecture.md); [running.md](docs/running.md) covers the
checkout entry points (`./autoform.sh`, `./assure.sh`, `scripts/reland_corpus.sh`) and
troubleshooting; [integrity.md](docs/integrity.md) explains the checks that keep the
program measured equal to the program intended, each named after the incident that
motivated it. [CONTRIBUTING.md](CONTRIBUTING.md) has the working rules.

## Dependencies

Lean 4.30.0-rc1 · [Specimen](https://github.com/strata-org/specimen) ·
[Aesop](https://github.com/leanprover-community/aesop) ·
[Plausible](https://github.com/leanprover-community/plausible) ·
[Joern](https://github.com/joernio/joern) 4.0.606 · Python 3.10+ · the source language's runtime ·
[SemIf (OpenJev)](https://github.com/TheoLeeCJ/SemIf-OpenJev) for `formalize`'s default judge ·
pypcode and friends for `[machine]`.
