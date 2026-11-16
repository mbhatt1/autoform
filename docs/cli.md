# The `autoform` command

`autoform` is the installed entry point (`pip install .`; distribution `autoform-lean`,
import name `autoform`). It unpacks a Lean project, the Joern exporter and the oracle
scripts into a **workspace**, runs the heavy toolchains there, and writes evidence under
`<workspace>/artifacts/`. Nothing is written into the installed package.

```
autoform [--workspace DIR] <subcommand> ...
autoform <git-url> [Module] [--ref REF] [--subdir PATH]      # shorthand for `assure`
```

`--workspace` (default `.autoform-work`) names the writable directory; two commands
may not share one workspace at the same time (a lock refuses the second). Start with
`autoform doctor`.

## Subcommands

| command | what it does | exit `0` means |
|---|---|---|
| `doctor` | checks every external tool against this package's pins | every required tool present and matching |
| `init` | extracts the bundled Lean project and tools into the workspace | workspace ready |
| `source SRC [Module]` | translate, build, differential conformance, ledger, proofs | every stage ran and the oracle agreed |
| `assure SRC [Module]` | `source`, then coverage oracle, mutation gate, audit, contracts, assurance case, guarantee | every required check passed |
| `regress SRC --base REF [--head REF]` | the pipeline at two commits, compared by what each could prove | nothing that held at `--base` is lost |
| `regress ... --machine --files F...` | the same comparison on compiled code, kernel-checked on lifted p-code | no diverging input found |
| `pr SRC [Module] --base REF [--head REF]` | evidence level of every function the change touched, as SARIF and Markdown | no function refuted |
| `autoformalize SRC [Module]` | code → validated Lean model → English → statements → kernel proofs | see `docs/autoformalize.md` |
| `formalize Module` | candidate claims, SemIf judge, kernel verification, CEGIS repair | see `docs/harness.md` |
| `machine INPUT [Module]` | binary/assembly → SLEIGH p-code → Lean model, concrete assertions | see `docs/machine-code.md` |

`SRC` is a directory or a Git URL. A URL is cloned to a detached checkout at `--ref`
(default: the remote's HEAD), the exact commit is recorded in the report, and the
checkout is deleted when the run ends unless `--keep-checkout` is given. `--subdir`
selects a directory inside the checkout. `Module` is the Lean module name the model is
rendered under (`Autoform.Generated.<Module>`); it must be a Lean identifier starting
with an uppercase letter and defaults to `Translated`.

### `doctor`

```
autoform doctor [--strict] [--json]
```

Required: Python 3.10+, git, `lake`, `lean`, `leanchecker`, `joern` — each checked
against `lean-toolchain` and `joern-version`, because the neutral AST is a function of
the frontend build. Optional: the language runtimes (`python3`, `cc`, `clang`, `java`,
`javac`, `go`, `node`, `kotlinc`), the Rust path (`cargo`, `rust-toolchain`, `charon`,
`aeneas`, `aeneas-lean-project`, each checked against `rust-pins.json`) and the `[machine]`
extra. A missing runtime only
disables that language's differential oracle; `--strict` makes it fatal too. `--json`
prints a `schema_version: 1` document, one entry per tool with `path`, `found_version`,
`expected_version`, `status`, `required`, an install `hint`, and the languages a missing
runtime `disables`. Exit `1` on a required-tool problem, `2` if the check itself could
not run.

### `source` and `assure`

```
autoform source SRC [Module] [--ref REF] [--subdir PATH] [--keep-checkout]
                [--lang auto|rust|joern] [--rust-lean-project DIR]
                [--shard-functions N] [--timeout SECONDS] [--max-file-bytes N]
                [--python PY] [--pytest-addopts project|ignore]
autoform assure SRC [Module] [--ref REF] [--subdir PATH] [--keep-checkout]
                [--lang auto|rust|joern] [--rust-lean-project DIR]
                [--shard-functions N] [--timeout SECONDS] [--max-file-bytes N]
                [--python PY] [--pytest-addopts project|ignore]
                [--stage-timeout SECONDS] [--properties FILE]
```

`source` runs the eight translation stages (`autoform.sh`): parse, call graph, export,
render, type-check, differential conformance against the real runtime, ledger, and the
proofs of the recorded observations. `assure` continues with the execution-coverage
oracle, the mutation gate, the axiom audit and fresh kernel replay, the contract
summary, the SACM assurance case and `guarantee.json`. Mixed-language repositories get
one child module per language (`TranslatedPython`, `TranslatedJava`, ...) and a parent
report; see `docs/repository-analysis.md`.

* `--shard-functions N` (default 1000; `0` = one module) renders the model as part
  modules of at most N functions that Lean elaborates in parallel, so one process never
  holds the whole corpus. See `docs/scale.md`.
* `--timeout` bounds the whole run (exit `143`; `pipeline.json` or `run.json` names the
  stage it stopped in; for `regress` it bounds **each** of the two pipeline runs instead); `--stage-timeout` (`assure`, default 7200 s) bounds each stage,
  and a timed-out stage keeps its log and withholds the guarantee.
* `--max-file-bytes N` (default 16 MiB, `0` = no cap) keeps a supported source file
  larger than N bytes away from Joern. It is never dropped silently: the inventory keeps
  it as an unsupported file listed under `excluded` with reason `max_file_bytes`, and
  `context.json` lists it under `excluded_files`. See `docs/scale.md`, "Operating limits".
* `--properties FILE` supplies independent Lean security properties (default
  `autoform.properties.json` in the selected source directory); see `docs/security.md`.
* `--lang` picks the route. `auto` (default) takes the **Rust path** when the selected
  directory is a Cargo package with a library target, and the Joern pipeline otherwise;
  `rust` forces the Rust path, `joern` refuses it. The Rust path (`scripts/rust_aeneas.py`,
  `docs/rust.md`) runs rustdoc, Charon and Aeneas instead of the eight Joern stages and
  writes `ledger-<Module>.json`, `conformance.json`, `rust-provenance.json`, the case
  theorems and `summary.md` (with `assure`, also `run.json` and `guarantee.json`; exit `1`
  on any hole, inconclusive case, divergence or unproved case theorem). `--properties` is
  not supported there. A missing tool or scratch project is a named error in
  `rust-error.json`, exit `2`.
* `--rust-lean-project DIR` names the scratch Lake project holding Aeneas' Lean library
  (default `$AUTOFORM_RUST_LEAN_PROJECT`; `scripts/rust_setup.sh` creates one).

Exit `1` from `assure` is not a crash: the workflow finished with unresolved gaps
(`run.json`: `completed_with_gaps`). A scoped certificate in `guarantee.json` can
coexist with it. Exit `2` is an invocation or setup failure, including a **refused**
tree: a run never starts over a live mutant (`*.mutate-backup`) or modified tracked
artifacts (`AUTOFORM_ALLOW_DIRTY=1` lifts only the second).

### `regress`

```
autoform regress SRC [Module] --base REF [--head REF] [--subdir PATH] [--timeout SECONDS]
                 [--shard-functions N] [--keep-checkout]
                 [--lang auto|rust|joern] [--rust-lean-project DIR]
autoform regress SRC [Module] --base REF [--head REF] --machine --files F... [--functions G...]
                 [--target {aarch64,x86_64,i386}]
```

Runs the source pipeline at both commits and compares *facts*, never text: a function
that holes at `--head` but not at `--base`, a theorem proved then refuted or gone, a
recorded runtime case that now diverges, a recorded `(function, self, args)` whose
outcome changed (a **behaviour change**, `proven_both` when the theorem holds at both
commits). Reports land in `artifacts/regression/<Module>/{base,head}/` plus
`runs.json` (each run's ref, resolved commit and exit code), `regression.json` and
`regression.md`. `--lang` and `--rust-lean-project` mean what they do for `source`: a
Cargo library crate at `--base` takes the Rust leg (`docs/rust.md`) under `auto`. With `--machine` the listed files are compiled at
both commits for a Linux target, linked, lifted through SLEIGH, searched for diverging
inputs (type-width boundaries and seeded random values, run natively when the host can)
and each divergence is kernel-checked. Exit `1` on a regression or a divergence.

### `pr`

```
autoform pr SRC [Module] --base REF [--head REF] [--subdir PATH] [--ast FILE] [--tests DIR]
            [--cases N] [--behaviour-cases N] [--mutants N] [--sarif FILE] [--markdown FILE]
            [--no-behaviour] [--fail-on {behaviour-changed,no-evidence}]
            [--python PY] [--pytest-addopts project|ignore]
            [--stage-timeout SECONDS] [--timeout SECONDS] [--keep-checkout]
```

Runs the chain for the functions a change touched and reports each one's **evidence
level** -- `none`, `hole`, `translated`, `oracle-agreed`, `proved` or `refuted` -- with
the artifact it traces to (`docs/evidence-levels.md`). `SRC` is a Git URL or a local
checkout; `--head` defaults to the working tree, untracked files included. Python
functions are found by comparing the standard-library `ast` of each changed file at
both commits, which is also where the SARIF line numbers come from; for other
languages every function the exporter exported from a changed file is reported. The
head tree is exported with Joern, or `--ast FILE` supplies an AST the exporter produced
earlier (recorded as such). The changed functions, their scopes and their resolvable
callees are rendered as `Autoform.Generated.<Module>` (default `PullRequest`), then
`scripts/differential.py`, the ledger, `scripts/synth_specs.py --conformance-only` and,
with `--mutants N`, `scripts/mutate.py` run on that module alone. Reports land in
`artifacts/pr/<Module>/` (`pr.json`, `conformance.json`, `specs.json`, `mutation.json`,
the stage logs); `--sarif` writes SARIF 2.1.0 with one result per function, validated
for GitHub code scanning before it is written, and `--markdown` the review comment.
Exit `1` when a function is refuted, or, with `--fail-on behaviour-changed`, when a
changed function's behaviour changed. Exit `3` (inconclusive: no evidence) when
`--fail-on behaviour-changed` or `--fail-on no-evidence` is given and not one changed
non-test function reached behaviour `changed` or `unchanged-on-inputs`: the gate compared
nothing, which is neither a pass nor a failure, and the log and the first line of
`--markdown` say so (`gate` in `pr.json`). `1` and `2` take precedence over `3`; without
`--fail-on` the exit code never is `3`. A stage that cannot run leaves its functions
at the level below and is named in the report. A supported source file that changed
but got no AST from the exporter (Joern missing or crashed) exits `2`: nothing was
analysed, so a CI gate must not read it as a pass. A change with nothing to analyse (no
changed file in a supported language, or no changed `def` in the changed Python files)
exits `0` without running the exporter, and `pr.json` records why. Nothing in pr mode
reads a CI system's environment, so it runs the same under any CI
([github-action.md](github-action.md#other-ci-systems)).

Besides the level, each changed Python function gets a **behaviour** result
(`changed`, `unchanged-on-inputs` or `not-compared`): the base revision's model run
against the head runtime on the head tests' inputs, so a change of behaviour that the
single-revision levels cannot see is flagged with up to three counter-inputs (SARIF rule
`autoform/behaviour-changed`, comment section "PR verdict", which leads the comment). It affects
the exit code only under `--fail-on` (above). Divergences the same base model shows against the base runtime are
reported as `suppressed-as-model-noise: n`. It needs Joern for the base export; without
it every function is `not-compared` with that reason. `--no-behaviour` skips it;
`--behaviour-cases N` (default 100) sets the oracle cases per function it draws, separately
from `--cases` (default `$AUTOFORM_CASES`, else 5), which sizes the single-revision oracle.
See `docs/evidence-levels.md`.

### `autoformalize`, `formalize`, `machine`

Each owns its flags; `autoform <cmd> --help` is the reference.
`autoformalize` writes a language model's Lean model of each function and validates it
against real executions and a second translation (`--deep` uses the Joern translation
instead; `--deep-too` proves the two equal). It needs a model backend
(`AUTOFORM_CLAUDE_AUTH=login|api-key|api|bedrock`, see `docs/autoformalize.md`) and caps the
run's spend with `--budget-usd`: every model stage stops at the function that would cross
the cap and names the rest in `budget.json` and the report. Its last stage writes the
properties that survived checking as pytest tests into the analysed tree's
`tests/autoform_generated/` and runs them (`--emit-dir DIR` relocates them, `--no-emit`
skips the stage; `docs/autoformalize.md`, "The emit stage").
`formalize` needs a translated module in the workspace and, for the default judge, a
SemIf (OpenJev) installation. `machine` needs the `[machine]` extra; `--assemble`
also needs `clang`. The checkout entry points `./autoform.sh`, `./assure.sh` and
`scripts/reland_corpus.sh` run the same stages from a Git clone (`docs/running.md`).

## What a run leaves behind

`<workspace>/artifacts/pipeline/<Module>/`:

| file | written by | contents |
|---|---|---|
| `pipeline.json` | `autoform.sh` | the stage the run reached, its exit code and status (`running` while it runs), `finished_at`, the signal when interrupted, overlays the parse had to drop |
| `repository.json`, `checkout.log` | `autoform.repository.resolve_source` | how the source was acquired: `kind`, `ref`, resolved `commit`, `checkout`, `subdir`, `status` |
| `inventory.json`, `selection.json` | repository scan | every file, its hash and language, exclusions, scan errors |
| `inventory-after.json`, `source-coverage.json` | `assure` (`scripts/assure.py`) | the scan repeated after the run, and which inventoried files the model covers |
| `repository-summary.json` | `scripts/repository_assurance.py` | the parent report of a mixed-language repository: per-language child modules, routing, remaining obligations |
| `parse.log`, `graph.log`, `export.log`, `render.log`, `build.log`, `provenance.log`, `conformance.log`, `ledger.log`, `specs.log`, `specs-build.log` | each stage of `autoform.sh` | the stage's full output; `provenance.log` holds the reason when the AST could not be attributed |
| `formalization-graph.json`, `graph.log` | `cartographer` call-graph pass | the call graph the export is selected from |
| `ast-<Module>.json`, `frontend.json`, `export.log` | exporter | the neutral AST; CPG population and excluded declarations |
| `Autoform/Generated/<Module>.lean` (+ `<Module>/PartNNNN.lean`) | renderer | the model; part modules when sharded |
| `conformance.json` | `scripts/differential.py` | every compared case: agree / diverge / inconclusive, the measurement basis, provenance hashes; a `cache` block and `cached_from` on every verdict replayed from `.autoform-work/oracle/<Module>/` rather than compared now (`differential.py --no-cache` re-compares everything, `--cache-dir DIR` relocates the store; docs/running.md §4) |
| `ledger-<Module>.json`, `ledger.json` | `scripts/ledger.lean.tmpl` | holes by label, hole-free count, verifiable core, call closure (`ledger.json` is the same file under a module-independent name) |
| `specs.json`, `Autoform/SpecsGen/<Module>.lean` | `scripts/synth_specs.py` | the proved observation theorems; open obligations; subjects excluded by name and why |
| `core-oracle.json` | `scripts/core_oracle.py` | execution coverage of the recorded observations |
| `mutation.json` | `scripts/mutate.py` | per-theorem on-subject scores, every survivor listed |
| `audit.json` | `scripts/audit_all.py --strict` | axiom sweep, `leanchecker --fresh` replay, artifact snapshot |
| `contracts-<Module>.json`, `sacm-<Module>.json`, `assurance.md` | contract and SACM emitters | assumptions and the assurance case |
| `properties.json`, `security-claims.json`, `security-mutation.json`, `security-audit.json`, `security.json`, `security.md` | `assure --properties`, `scripts/security_specs.py` | the supplied independent security properties, each one's proof attempt or open obligation, their mutation and audit results, and the human summary (`docs/security.md`) |
| `guarantee.json`, `guarantee.md`, `summary.md`, `run.json`, `context.json` | `scripts/guarantee.py`, orchestration | the claims actually established, bound to artifact hashes (`evidence_sha256`), and the same as Markdown; stage statuses and timings |

`guarantee.json` has `status: verified_scoped` only when every required check passed
and every listed claim's artifacts hash as recorded; otherwise `unverified` with the
failed checks named. It never claims whole-program correctness.

`<workspace>/artifacts/pr/<Module>/` (`autoform pr`): `pr.json` (per function: level,
reason, artifacts, holes, oracle counts, theorems, mutation verdicts; per stage: status,
seconds, log), the selected `ast-<Module>.json`, and the same `conformance.json`,
`ledger-<Module>.json`, `specs.json` and `mutation.json` as above for that module.

## Environment variables

| variable | read by | effect |
|---|---|---|
| `JOERN_HOME` | every stage | Joern installation (`~/joern` or `~/joern/joern-cli` by default) |
| `AUTOFORM_SHARD_FUNCTIONS` | renderer | functions per part; the CLI sets it from `--shard-functions` |
| `AUTOFORM_MAX_FILE_BYTES` | inventory, parse | per-file cap on supported source (default 16 MiB, `0` = none); the CLI sets it from `--max-file-bytes` |
| `AUTOFORM_JOERN_XMX`, `JAVA_OPTS` | parse, graph, export | Joern's JVM heap: `AUTOFORM_JOERN_XMX=8g` appends `-Xmx8g` to `JAVA_OPTS`, which Joern's launchers honour (default heap: a quarter of RAM; `doctor` reports it) |
| `AUTOFORM_TESTS` | `reland_corpus.sh` | a test suite outside the source tree, passed to the oracle (`differential.py --tests DIR`) |
| `AUTOFORM_CASES` | oracle (`autoform.sh`, `scripts/pr_mode.py`) | random cases per function (default 5); `autoform pr --cases` overrides it for that run, and without the flag `pr` reads the variable |
| `AUTOFORM_CASE_CAP` | `scripts/differential.py` | cap on the total compared cases, keeping the generated Lean file compile-bounded (default 600; an integer >= 1). Lift it for a run that must compare every built case; the value in force is recorded in `conformance.json` (`case_cap.limit`, with the raw setting as `case_cap.requested`; `docs/running.md` §4 lists the block) |
| `AUTOFORM_LEAN_CHUNK_TIMEOUT` | `scripts/differential.py` | wall-clock bound, in seconds, on one Lean evaluation chunk (default 1800; a positive integer, anything else is a named refusal). A chunk past it is not bisected: each of its cases is INCONCLUSIVE with label `lean-chunk-timeout (...)` and the chunk is listed in `conformance.json` `lean_chunk_failures` |
| `AUTOFORM_LEANCHECKER_TIMEOUT` | `scripts/audit_all.py` | seconds the trust audit gives `leanchecker --fresh` (default 3600; positive integer). A replay cut short is reported as `leanchecker timed out` and fails the verdict; raise it when the machine is shared with a build or a test suite. |
| `AUTOFORM_LANGUAGE` | `autoform.sh`, `scripts/source_context.py` | restrict the export to one language (set by `assure` for each child module of a mixed-language repository); `repository_scope.py` records the selection in `selection.json` |
| `AUTOFORM_NODE_MODULES` | oracle (JavaScript/TypeScript) | a `node_modules` directory linked into the oracle's copy of the project when the project has none, so imports resolve; a missing directory is a named refusal |
| `AUTOFORM_JAVA_SOURCEPATH` | oracle (Java) | extra source roots (`os.pathsep`-separated) given to `javac` when the analysed tree is a subset of a larger source tree; recorded under `extra_source_roots`, a missing directory is a named refusal |
| `AUTOFORM_ORACLE_PYTHON_EXEC` | `scripts/differential.py` (internal) | set by the oracle on itself when it re-executes under `AUTOFORM_ORACLE_PYTHON`, so the child knows it is already the target interpreter; not for users |
| `AUTOFORM_ORACLE_PYTHON` | oracle (Python) | the interpreter the oracle runs the project's tests and functions under -- one with the project's dependencies installed (a virtualenv's `bin/python`; not resolved through symlinks). `differential.py` re-executes itself under it (it is stdlib-only); recorded in `conformance.json` `oracle_interpreter` and the measurement basis (`+oracle-interpreter-v1`). The CLI sets it from `--python`. `pr` alone, when neither is given and the change touches an analysed Python file, uses the analysed repository's lone `.venv/bin/python` or `venv/bin/python` at its root -- validated like `--python` and recorded as `auto: .venv`/`auto: venv` in `pr.json`; when the repository has both, neither is chosen and a note names them (never guessed). Otherwise the default is autoform's own interpreter |
| `AUTOFORM_ORACLE_PYTEST_ADDOPTS` | oracle (Python) | `ignore` runs the suite with `-o addopts=`, dropping the project's pytest `addopts` (e.g. `--cov` options that need pytest-cov or a config path relative to the project root); recorded (`test_runs[].runner`, `+pytest-addopts-ignored-v1`). Default `project`. The CLI sets it from `--pytest-addopts` |
| `AUTOFORM_JAVA_CLASSPATH` | oracle (Java) | the project's dependency classpath (`mvn dependency:build-classpath`, a Gradle classpath task; `dir/*` allowed), given to `javac` and the driver JVM; recorded in `backend_info.dependency_classpath`. Without it a real service compiles almost no candidate file |
| `AUTOFORM_JAVA_PROCESSORPATH` | oracle (Java) | annotation processors (e.g. the Lombok jar) used instead of `-proc:none`, so generated members exist; recorded in `backend_info.processor_path` |
| `AUTOFORM_DELOMBOK_MODE` | parse (Java) | Joern's `--delombok-mode` (default `types-only`: original sources are parsed, delombok output is used for types only) |
| `AUTOFORM_THEOREM_TIMEOUT`, `AUTOFORM_THEOREM_MEMORY_GB`, `AUTOFORM_PROBE_JOBS` | `synth_specs.py` | per-theorem proof budget (300 s, 16 GB, 2 jobs); an over-budget candidate is excluded by name |
| `AUTOFORM_SPEC_EXCLUDE` | `synth_specs.py` | `;`-separated subjects to leave out, recorded in the module |
| `AUTOFORM_SPLIT_GB` | `synth_specs.py` | split the proof module into `<M>/Base.lean` + `<M>/PartN.lean` when its predicted single-process peak exceeds this many GB (default 4; `0` disables) |
| `AUTOFORM_NO_CACHE`, `AUTOFORM_CACHE_DIR` | oracle, `synth_specs.py` | bypass or relocate `.autoform-work/cache` (verdicts keyed by function AST digest; `docs/running.md` §2) |
| `AUTOFORM_MUTANTS` | `assure` | mutants per gate run (default `max(8, 2 × proved)`) |
| `AUTOFORM_MUTATE_LOG_DIR` | `scripts/mutate.py` | keep every mutant's full build output under this directory (default: not kept), so a run where every mutant survives can be told from a build that never saw the mutant |
| `AUTOFORM_CFLAGS`, `CPP_DEFINES`, `AUTOFORM_COMPILE_COMMANDS` | C/C++ parsing and native runs | compiler flags, defines, a compilation database |
| `AUTOFORM_FRONTEND`, `AUTOFORM_DATA_MODEL` | parse/export | force a Joern frontend; `lp64` (default), `llp64`, `ilp32` or `unknown` integer model for source integers |
| `AUTOFORM_CLAUDE_AUTH` | `autoformalize`, `formalize --prover` | `login` (default) or `api-key` (the `claude` CLI), `api` (the Messages API through the `anthropic` SDK; text stages only), or `bedrock` (Claude on Amazon Bedrock through the same SDK, text stages only; needs `AUTOFORM_LLM_MODEL`, `AWS_REGION` and AWS credentials) |
| `AUTOFORM_LLM_ALLOWED_BACKENDS` | every model call, `doctor` | comma list of `AUTOFORM_CLAUDE_AUTH` values that may be used; any other backend, including the backend a `claude` CLI child would reach, is refused before anything is sent. Set but empty refuses all; unset is no policy (SECURITY.md, "Operating on proprietary code") |
| `AUTOFORM_LLM_CACHE` | `autoformalize` | prompt-hash cache of model answers (default `~/.cache/autoform/llm`; directory 0700, entries 0600) |
| `AUTOFORM_LLM_MODEL` | `autoformalize` | model for the text stages (`api`: default `claude-opus-5-5`, must have a row in `llm.PRICES`) |
| `AUTOFORM_PROOF_CACHE` | `autoformalize` (`nl/prove.py`, `nl/refine.py`) | cache of previously found proofs (default `~/.cache/autoform/proofs`); a cached proof is re-checked by the kernel before it counts, and the report says so |
| `AUTOFORM_NL_FUZZ_CASES`, `AUTOFORM_NL_FUZZ_SEED`, `AUTOFORM_NL_FUZZ_TIMEOUT` | `autoformalize` model stage (`nl/fuzz.py`) | inputs compared with the Lean model per fuzz round (default 300; `0` disables), the seed (default 0), seconds per real CPython call (default 2.0); the `--fuzz-cases/--fuzz-seed/--fuzz-timeout` flags override them |
| `AUTOFORM_NEURAL`, `AUTOFORM_NEURAL_BACKEND`, `AUTOFORM_NEURAL_MODEL` | `scripts/prover/propose.py` (the proof portfolio's neural proposer) | off unless `AUTOFORM_NEURAL=1`, so a build never silently depends on a model; backend `ollama` (default), `anthropic` or `openai`; the model name, whose default depends on the backend (`qwen2.5:7b`, `claude-opus-5-5`, `gpt-4o-mini`) |
| `AUTOFORM_NEURAL_MODEL_<BACKEND>` | `scripts/prover/propose.py` | per-backend model name (e.g. `AUTOFORM_NEURAL_MODEL_OLLAMA`); falls back to `AUTOFORM_NEURAL_MODEL`, then the backend default |
| `AUTOFORM_SMT_TIMEOUT` | `scripts/prover/smt.py` (the proof portfolio's solver driver) | per-solver budget in seconds (default 30) for the `cvc5` and `z3` binaries and the `z3` Python module; a solver that exists but exceeds it reports `timed out`, never `unavailable` (which means no solver was tried at all) |
| `AUTOFORM_SEMIF_PYTHON`, `AUTOFORM_SEMIF_MODEL`, `AUTOFORM_SEMIF_REVISION`, `AUTOFORM_SEMIF_BITS` | `formalize` judge (`harness/judge.py`, `nl/judge.py`) | internal: the SemIf (OpenJev) interpreter (default `~/semif/.venv/bin/python`), model, revision and quantisation the judge loads; `autoform formalize --help` is the reference |
| `AUTOFORM_EST_FORMALIZE_USD`, `AUTOFORM_EST_PROVE_USD`, `AUTOFORM_PROVE_SHARE`, `AUTOFORM_PROVE_CALL_CAP_USD` | `autoformalize` budgeting (`nl/judge.py`, `harness/prover.py`) | internal: the per-function cost estimates (0.08, 0.60 USD), the budget share reserved for proving (0.4) and the cap on one prover call (1.50 USD) that `--budget-usd` plans with; measured defaults, not tuning knobs |
| `AUTOFORM_REPOSITORY_REPORT` | `assure`, `scripts/repository_assurance.py` (internal) | set by the CLI to the run's `repository.json` so the assurance stages can bind the guarantee to the acquired commit; not for users |
| `AUTOFORM_ALLOW_DIRTY` | checkout entry points | run over modified tracked artifacts (never over a live mutant) |
| `AUTOFORM_SCRATCH`, `AUTOFORM_PYTHON` | scripts | scratch directory; the Python the stages run under |
| `AUTOFORM_DIFF_KEEP`, `AUTOFORM_NO_REEXEC` | oracle debugging | keep the Lean file a case failed in; skip the `PYTHONHASHSEED=0` re-exec |
| `AENEAS_HOME` | Rust path | the unpacked pinned Aeneas release (`aeneas`, `charon`, `charon-driver`, `rust-toolchain`); otherwise they are looked up on `PATH` |
| `AUTOFORM_RUST_LEAN_PROJECT` | Rust path, `doctor` | the scratch Lake project with Aeneas' Lean library built (`--rust-lean-project` overrides) |
| `AUTOFORM_RUST_REQUIRED`, `AUTOFORM_RUST_GCD_CRATE` | `tests/test_rust_aeneas.py` | `1` turns a missing Rust prerequisite into a failure instead of a skip (the Rust CI job); the unpacked gcd 2.3.0 crate for the real-crate reproduction test |
| `AUTOFORM_SANDBOX` | oracle, native worker, nl runners | `on` (default: refuse without a mechanism), `strict` (as `on`, but refuse the `unshare` fallback, which confines only the network), `off` (run the subject unconfined; recorded in every artifact), or `seatbelt`/`bwrap`/`unshare` to force one (`scripts/sandbox.py`) |

## Exit codes

`0` success for the command's own claim; `1` a stage failed, gaps remain, a regression
or divergence was found, or `pr` refuted a function; `2` invocation, setup or orchestration failure (bad module
name, missing Joern, busy workspace, unreadable package, refused dirty tree); `3` `pr
--fail-on behaviour-changed|no-evidence` was inconclusive (no changed non-test function was
behaviour-compared); `128+N`
interrupted by signal N (`--timeout` expiry is `143`). The per-command table is in
`docs/running.md` §7.
