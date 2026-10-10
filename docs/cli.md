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
`javac`, `go`, `node`, `kotlinc`) and the `[machine]` extra. A missing runtime only
disables that language's differential oracle; `--strict` makes it fatal too. `--json`
prints a `schema_version: 1` document, one entry per tool with `path`, `found_version`,
`expected_version`, `status`, `required`, an install `hint`, and the languages a missing
runtime `disables`. Exit `1` on a required-tool problem, `2` if the check itself could
not run.

### `source` and `assure`

```
autoform source SRC [Module] [--ref REF] [--subdir PATH] [--keep-checkout]
                [--shard-functions N] [--timeout SECONDS]
autoform assure SRC [Module] [--ref REF] [--subdir PATH] [--keep-checkout]
                [--shard-functions N] [--stage-timeout SECONDS] [--properties FILE]
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
* `--timeout` (`source`) bounds the whole run; `--stage-timeout` (`assure`, default
  7200 s) bounds each stage, and a timed-out stage keeps its log and withholds the
  guarantee.
* `--properties FILE` supplies independent Lean security properties (default
  `autoform.properties.json` in the selected source directory); see `docs/security.md`.

Exit `1` from `assure` is not a crash: the workflow finished with unresolved gaps
(`run.json`: `completed_with_gaps`). A scoped certificate in `guarantee.json` can
coexist with it. Exit `2` is an invocation or setup failure, including a **refused**
tree: a run never starts over a live mutant (`*.mutate-backup`) or modified tracked
artifacts (`AUTOFORM_ALLOW_DIRTY=1` lifts only the second).

### `regress`

```
autoform regress SRC [Module] --base REF [--head REF] [--subdir PATH] [--timeout SECONDS]
                 [--shard-functions N] [--keep-checkout]
autoform regress SRC [Module] --base REF [--head REF] --machine --files F... [--functions G...]
                 [--target {aarch64,x86_64,i386}]
```

Runs the source pipeline at both commits and compares *facts*, never text: a function
that holes at `--head` but not at `--base`, a theorem proved then refuted or gone, a
recorded runtime case that now diverges, a recorded `(function, self, args)` whose
outcome changed (a **behaviour change**, `proven_both` when the theorem holds at both
commits). Reports land in `artifacts/regression/<Module>/{base,head}/` plus
`regression.json` / `regression.md`. With `--machine` the listed files are compiled at
both commits for a Linux target, linked, lifted through SLEIGH, searched for diverging
inputs (type-width boundaries and seeded random values, run natively when the host can)
and each divergence is kernel-checked. Exit `1` on a regression or a divergence.

### `pr`

```
autoform pr SRC [Module] --base REF [--head REF] [--subdir PATH] [--ast FILE] [--tests DIR]
            [--cases N] [--mutants N] [--sarif FILE] [--markdown FILE]
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
Exit `1` only when a function is refuted; a stage that cannot run leaves its functions
at the level below and is named in the report.

### `autoformalize`, `formalize`, `machine`

Each owns its flags; `autoform <cmd> --help` is the reference.
`autoformalize` writes a language model's Lean model of each function and validates it
against real executions and a second translation (`--deep` uses the Joern translation
instead; `--deep-too` proves the two equal). It needs a model provider
(`AUTOFORM_CLAUDE_AUTH=login|api-key`) and caps spend with `--budget-usd`.
`formalize` needs a translated module in the workspace and, for the default judge, a
SemIf (OpenJev) installation. `machine` needs the `[machine]` extra; `--assemble`
also needs `clang`. The checkout entry points `./autoform.sh`, `./assure.sh` and
`scripts/reland_corpus.sh` run the same stages from a Git clone (`docs/running.md`).

## What a run leaves behind

`<workspace>/artifacts/pipeline/<Module>/`:

| file | written by | contents |
|---|---|---|
| `inventory.json`, `selection.json` | repository scan | every file, its hash and language, exclusions, scan errors |
| `ast-<Module>.json`, `frontend.json`, `export.log` | exporter | the neutral AST; CPG population and excluded declarations |
| `Autoform/Generated/<Module>.lean` (+ `<Module>/PartNNNN.lean`) | renderer | the model; part modules when sharded |
| `conformance.json` | `scripts/differential.py` | every compared case: agree / diverge / inconclusive, the measurement basis, provenance hashes |
| `ledger-<Module>.json` | `scripts/ledger.lean.tmpl` | holes by label, hole-free count, verifiable core, call closure |
| `specs.json`, `Autoform/SpecsGen/<Module>.lean` | `scripts/synth_specs.py` | the proved observation theorems; open obligations; subjects excluded by name and why |
| `core-oracle.json` | `scripts/core_oracle.py` | execution coverage of the recorded observations |
| `mutation.json` | `scripts/mutate.py` | per-theorem on-subject scores, every survivor listed |
| `audit.json` | `scripts/audit_all.py --strict` | axiom sweep, `leanchecker --fresh` replay, artifact snapshot |
| `contracts-<Module>.json`, `sacm-<Module>.json`, `assurance.md` | contract and SACM emitters | assumptions and the assurance case |
| `guarantee.json`, `summary.md`, `run.json`, `context.json` | `scripts/guarantee.py`, orchestration | the claims actually established, bound to artifact hashes; stage statuses and timings |

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
| `AUTOFORM_TESTS` | `reland_corpus.sh` | a test suite outside the source tree, passed to the oracle (`differential.py --tests DIR`) |
| `AUTOFORM_CASES` | oracle | random cases per function (default 5) |
| `AUTOFORM_THEOREM_TIMEOUT`, `AUTOFORM_THEOREM_MEMORY_GB`, `AUTOFORM_PROBE_JOBS` | `synth_specs.py` | per-theorem proof budget (300 s, 16 GB, 2 jobs); an over-budget candidate is excluded by name |
| `AUTOFORM_SPEC_EXCLUDE` | `synth_specs.py` | `;`-separated subjects to leave out, recorded in the module |
| `AUTOFORM_MUTANTS` | `assure` | mutants per gate run (default `max(8, 2 × proved)`) |
| `AUTOFORM_CFLAGS`, `CPP_DEFINES`, `AUTOFORM_COMPILE_COMMANDS` | C/C++ parsing and native runs | compiler flags, defines, a compilation database |
| `AUTOFORM_FRONTEND`, `AUTOFORM_DATA_MODEL` | parse/export | force a Joern frontend; `lp64`/`ilp32` integer model |
| `AUTOFORM_CLAUDE_AUTH` | `autoformalize`, `formalize --prover` | `login` (default) or `api-key` |
| `AUTOFORM_ALLOW_DIRTY` | checkout entry points | run over modified tracked artifacts (never over a live mutant) |
| `AUTOFORM_SCRATCH`, `AUTOFORM_PYTHON` | scripts | scratch directory; the Python the stages run under |
| `AUTOFORM_DIFF_KEEP`, `AUTOFORM_NO_REEXEC` | oracle debugging | keep the Lean file a case failed in; skip the `PYTHONHASHSEED=0` re-exec |

## Exit codes

`0` success for the command's own claim; `1` a stage failed, gaps remain, a regression
or divergence was found, or `pr` refuted a function; `2` invocation, setup or orchestration failure (bad module
name, missing Joern, busy workspace, unreadable package, refused dirty tree); `128+N`
interrupted by signal N (`--timeout` expiry is `143`). The per-command table is in
`docs/running.md` §7.
