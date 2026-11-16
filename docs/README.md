# docs

Reference documentation for autoform. `../README.md` is the overview and `../STRATEGY.md`
is the design record, which carries the reasoning behind everything here.

| Document | What it covers |
|---|---|
| [`cli.md`](cli.md) | The `autoform` command: every subcommand and flag, what a run leaves behind and what each artifact means, environment variables, exit codes. |
| [`library.md`](library.md) | Using autoform from Python: the installed package, reading `guarantee.json` and the other artifacts, the oracle and gate scripts as modules, the Lean library. |
| [`evidence-levels.md`](evidence-levels.md) | The evidence levels `autoform pr` reports per changed function (`none`, `hole`, `translated`, `oracle-agreed`, `proved`, `refuted`): what each claims, what it does not, which artifact proves it. One page. |
| [`adoption.md`](adoption.md) | For an engineering manager or security reviewer: what is and is not proved, language coverage, security posture, integration, scale, named gaps and a first-week evaluation plan. |
| [`github-action.md`](github-action.md) | The composite GitHub Action (`action.yml`) that runs `autoform pr` on a pull request: workflow, permissions, requirements and cold-start cost. |
| [`examples/pr-cachetools-7.1.5/`](examples/pr-cachetools-7.1.5/README.md) | A real `autoform pr` report on cachetools v7.1.4 to v7.1.5, and what it does and does not say about the fix. |
| [`architecture.md`](architecture.md) | How the pieces fit: the approach, why the CPG is treated as a universal AST, the pipeline stage by stage, and what every module and script is for. Start here. |
| [`core-language.md`](core-language.md) | Reference for the Core language: every `Val`/`Expr`/`Stmt` constructor, the heap/env/context model, the four evaluation outcomes, dialects, and the hole taxonomy. |
| [`trust-model.md`](trust-model.md) | What is claimed and on what basis: the four independent oracles, the G1–G5 assurance goals, the status lattice, and an explicit list of what the system does *not* establish. |
| [`security.md`](security.md) | Security applications, a vulnerability-fix workflow, current proof boundaries and the features needed for security automation. |
| [`autoformalize.md`](autoformalize.md) | `autoform autoformalize`: code → English → Lean statements → bounded and real-runtime checks → kernel proofs, over AI-written validated models (L0) or the deep translation, with the L1 step that proves a model equal to the deep translation. |
| [`harness.md`](harness.md) | `autoform formalize`: candidate claims, the SemIf/OpenJev judge (selection, intent, counterexample classification, repair ranking), Lean-kernel verification, CEGIS, certificates and the formalization diff. |
| [`running.md`](running.md) | Installation (Lean/`elan`, Joern, Python), the entry points, how to read the ledger, and troubleshooting. |
| [`packaging.md`](packaging.md) | Pip installation, writable workspaces, distribution validation and CI publishing. |
| [`fuel.md`](fuel.md) | The fuel-indexed interpreter: why `outOfFuel` is not divergence, fuel monotonicity across all eight mutually recursive interpreter functions, finalizer state and failure propagation, and generated fuel-independent proofs. |
| [`integrity.md`](integrity.md) | Checking that the program measured is the program intended. Each check is named after the incident that motivated it, including a mutant that survived four commits with every proof passing. |
| [`contracts.md`](contracts.md) | Boundary contracts for code outside the verified core, and the external base-class contracts (`collections.abc`) that make `class C(MutableMapping)` resolvable. |
| [`boxed-containers.md`](boxed-containers.md) | Boxed mutable containers, landed for Python and JavaScript: list/dict literals allocate, `setIndex`/`delIndex`/slices and the mutating builtins write through the payload, aliasing and `==`-vs-`is` work; the history of the migration and the named exclusions that stay holes (§9). `setIndex:immutable-containers` now names only a container *value* under a dialect that does not box. |
| [`java-strings.md`](java-strings.md) | The Java `String` model (implemented 2026-10-10): a `DYNAMIC_DISPATCH` call to a method outside the corpus keeps its receiver and becomes an `mcall`; `Stdlib.javaStringMethod` answers the common methods on a `.str` receiver with UTF-16 code-unit semantics on BMP strings. The pre-change analysis is kept as written. |
| [`python-module-namespaces.md`](python-module-namespaces.md) | Python module namespaces: globals belong to the defining module's object, `global` and augmented assignment write it, a `from` import binds the member value present when the import executes. |
| [`native-heap-observations.md`](native-heap-observations.md) | The `heap-graph-v1` measurement basis — a call's input heap, outcome and final heap — and `HeapObservation.compare`, which checks every object reachable from the receiver, arguments and return value. An unencodable post-state makes the observation unavailable, never return-only. |
| [`languages.md`](languages.md) | Per-language support, and what each front end does and does not provide. |
| [`typed-numerics.md`](typed-numerics.md) | Preserving Joern's integer types through Core, numeric conformance tests, and remaining gaps. |
| [`machine-code.md`](machine-code.md) | Binary and assembly formalization, raw p-code semantics, concrete proofs, and remaining coverage gaps. |
| [`rust.md`](rust.md) | Rust via rustdoc, Charon and Aeneas: every public function accounted for, a function translated only if its Aeneas model is CLOSED (no `sorry`, no non-standard axiom), a differential oracle against the compiled crate, kernel-checked statements. |
| [`repository-analysis.md`](repository-analysis.md) | `autoform <git-url>`: pinned checkout revision, directory inventory, adapter selection from the files actually present, and what adapter availability does not establish. |
| [`compiler-rewrite.md`](compiler-rewrite.md) | The compiler simplification: `export_ast.sc` loads `compiler/SourceCompiler.scala`, keeping the CPG → JSON AST → Lean Core interface for Python, C, C++, Java, Go, JavaScript, TypeScript and Kotlin. A compatibility-preserving simplification, not a coverage claim. |
| [`scale.md`](scale.md) | How the pipeline behaves on codebases larger than the reference corpus, and sharded rendering (Django in 244 s at 3.3 GB). |
| [`GOAL-arbitrary-codebases.md`](GOAL-arbitrary-codebases.md) | The bar for "works on arbitrary codebases", as eight milestones with named exit criteria — a goal statement, not a status report. |
| [`ledger-schema.md`](ledger-schema.md) | The trust ledger as a SACM profile: node vocabulary, evidence types, combination rules. |
| [`fvspec.md`](fvspec.md) | The FVSpec benchmark harness and the anti-vacuity screen run across it. |
| [`interpreter-recovery.md`](interpreter-recovery.md) | Recovery record of the 2026-09 interpreter rounds: the preserved worktrees, the iterator, generator, truth-protocol and class-attribute checkpoints, and their validation artifacts under `artifacts/interpreter-recovery/`. A dated record (last changed 2026-09-26), not a completion claim. |
| [`releasing.md`](releasing.md) | Release acceptance: a checklist where every line is a gate, ticked only with the command's actual output in hand — `autoform doctor --strict`, a clean tree, a clean build, and the rest. |
| [`evidence-cachetools.md`](evidence-cachetools.md), [`evidence-cachetools-negative-size.md`](evidence-cachetools-negative-size.md), [`evidence-linux-lcm.md`](evidence-linux-lcm.md) | Three fixed defects in code the project did not write, each caught by the cross-revision oracle: cachetools 7.1.6 (replace-with-larger-value), cachetools 7.1.4 (negative size), and the Linux `lcm()` overflow (kernel commit 74a5fef7cb08). Each names the divergence row and the replay test. |
| [`evidence-ansible.md`](evidence-ansible.md), [`evidence-LinuxCrypto.md`](evidence-LinuxCrypto.md), [`evidence-LinuxLib.md`](evidence-LinuxLib.md) | Dated measurements of three corpora whose artifacts were **unpinned on 2026-10-10** (`docs/integrity.md`, "Input availability"): nothing in the repository can regenerate them, so each is a record of a past artifact, not a current figure. |
| [`evidence-V8Base.md`](evidence-V8Base.md) | A dated measurement of V8 `src/base` (C++) against a *previous* render, carrying the staleness notice from the merge (STRATEGY.md §40); `core_oracle.py` against the current module is how to refresh it. |
| [`../CONTRIBUTING.md`](../CONTRIBUTING.md) | The project's working rules. Read them before submitting anything. |

**Standing caveat.** Coverage figures, hole counts and claim statuses move with every
change to the exporter, the semantics or the modelled stdlib. Documents here name the
command that regenerates a figure rather than quoting it. Where a snapshot is unavoidable
it is labelled with a date and a commit. If a document and an artefact disagree, the
artefact wins and the document is a bug.
