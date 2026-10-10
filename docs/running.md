# Installing and running autoform

For pip installation, the installed `autoform` command, and CI-built wheels, see
[packaging.md](packaging.md). The shell commands below run from a checkout.
The Git URL and assurance workflow automatically inventories and dispatches supported
languages; see [repository analysis](repository-analysis.md) for mixed-language scope
and the files that remain unsupported.

For independent security requirements, place `autoform.properties.json` in `SOURCE`
and use `./assure.sh SOURCE Module`, or supply an explicit `--properties properties.json`
override; see [the property format and runnable example](security.md).
Python test discovery stays within the selected source directory. It does not search
parent directories; the differential tool's explicit `--tests DIR` option can select
an external suite. When analyzing a repository root, its tests remain discoverable
even when imports resolve under a `src/` subdirectory.

For compiled binaries or assembly, use the independent
[machine-code workflow](machine-code.md). It needs the pinned Lean toolchain and
`requirements-machine.txt`, and does not require Joern.

Written for someone who has never run this repository. Nothing below embeds a result;
where a number would be useful, the command that produces it is given instead. Figures
move with every change; where a document and an artifact disagree, the artifact wins.

---

> The installed command is documented in [cli.md](cli.md) (subcommands, flags, artifacts,
> environment variables, exit codes) and its use from Python in [library.md](library.md).
> This page covers the checkout entry points and the mechanics behind both.

## 1. Prerequisites

### One command: `scripts/bootstrap.sh`

From a fresh clone, this installs everything below and ends in the trust audit's
`VERDICT: PASS`, or fails at a named step:

```sh
git clone <this repository> autoform && cd autoform
scripts/bootstrap.sh
```

In order: elan and the toolchain in `lean-toolchain`; a `.venv` from the first Python 3.10+
it finds (`python3.12`, `python3.11`, `python3.13`, `python3`, or `AUTOFORM_PYTHON`) with
`requirements.txt`; the Joern release pinned in `joern-version` into `JOERN_HOME`
(default `~/joern`), its zip verified against the release's `.sha512` before unpacking and
the jars on disk checked against the pin afterwards; the build with the memory sequencing
CI uses (`Autoform.SpecsGen.Cachetools`, then `Autoform.Specs.CachetoolsSpec`, then
`Autoform.CI`, under `taskset -c 0` on Linux and one after another on macOS, which has no
`taskset`); the cachetools corpus at the commit `ast-Cachetools.json` was exported from
(`AUTOFORM_CACHETOOLS_DIR`, default `/tmp/cachetools`, as CI); the "oracle is alive"
check (the differential oracle must compare more than zero cases); then
`scripts/audit_all.py --strict --module Autoform.CI`. It finishes by printing `git status`,
which is clean on a fresh clone. A second run re-checks each step and rebuilds only what
changed. The things it will not do are said in its output rather than skipped: it never
installs a JDK (Joern needs one; CI uses temurin 21), and it refuses to overwrite a Joern
in `JOERN_HOME` that does not match the pin. `AUTOFORM_BOOTSTRAP_ROOT=Autoform` builds and
audits the whole project including the V8Base parts, which CI cannot (`Autoform/CI.lean`).
Written and run on macOS arm64; the Linux branches follow `.github/workflows/ci.yml` and
have not been run on Ubuntu from this script. Expect the first run to take the better
part of an hour, most of it in the build. The rest of this section is what the script does
by hand.

### Lean, via `elan`

The toolchain is pinned in `lean-toolchain` (Lean 4.30.0-rc1 at the time of writing).
Install `elan` and let it read the pin:

```sh
curl -sSfL https://elan.lean-lang.org/elan-init.sh -o elan-init.sh
sh elan-init.sh -y --default-toolchain "$(cat lean-toolchain)"
export PATH="$HOME/.elan/bin:$PATH"
lean --version && lake --version
```

`leanchecker` — the independent kernel replay used by the trust audit — **ships with the
toolchain** (v4.28.0+). There is nothing to install and no Homebrew formula; the
standalone `lean4checker` is deprecated. Verify:

```sh
command -v leanchecker
```

Then build. The first build fetches and compiles Specimen and Plausible and is slow;
subsequent builds are incremental.

```sh
lake build
```

### Joern — pinned, like the Lean toolchain

Joern supplies the code property graph that is this project's universal front end. It is a
**~1.7 GB download**. The source-runtime CI workflow caches the pinned distribution
and runs all eight source fixtures; the main library build does not need Joern.

**The version is pinned in `joern-version`, and the pin is load-bearing.** The neutral AST
is a *function of the front end*: which nodes exist, how `fullName`s resolve, whether
`IS_VARIADIC` is set, whether an absent clause is elided. Two machines running different
Joern builds produce different `ast-*.json` from identical source, and until this pin
existed nothing would have shown it. Treat it exactly as you treat `lean-toolchain`.

```sh
cat joern-version                                  # 4.0.606
python3 scripts/provenance.py joern-version --check # compares it to what is installed
```

The check reads the version out of `$JOERN_HOME/joern-cli/lib/io.joern.joern-cli-*.jar`
rather than booting `joern --version`: it is a fact about the bytes on disk, it takes
milliseconds instead of a JVM start, and it catches the "installed nothing, exited 0"
failure below, which a version banner cannot.

Changing the pin is a deliberate act that invalidates every artifact: bump it, regenerate
each `ast-*.json`, re-render each `Autoform/Generated/*.lean`, re-record provenance. §5
describes how that is checked.

**On macOS arm64, do not trust the official installer.** `joern-install.sh` can **exit 0
while having failed**, leaving no `joern-cli` directory and a shell that reports success.
Fetch the release asset directly instead:

```sh
# the release ships per-platform zips: joern-cli-{linux,macos}-{x86_64,arm64}.zip
# (there is no joern-cli.zip); the .sha512 beside each names it as target/<asset>
v=$(cat joern-version); a=joern-cli-macos-arm64.zip
mkdir -p target ~/joern
curl -fL -o target/$a https://github.com/joernio/joern/releases/download/v$v/$a
curl -fL -o $a.sha512 https://github.com/joernio/joern/releases/download/v$v/$a.sha512
shasum -a 512 -c $a.sha512                        # sha512sum -c on Linux
unzip -q target/$a -d ~/joern
python3 scripts/provenance.py joern-version --check
```

The scripts look for `"$JOERN_HOME/joern-cli"` with `JOERN_HOME` defaulting to `~/joern`,
so the layout above needs no configuration. Joern needs a JDK (temurin 21 is what CI uses).

On Linux the official installer generally works:

```sh
curl -L https://github.com/joernio/joern/releases/latest/download/joern-install.sh -o joern-install.sh
chmod +x joern-install.sh && sudo ./joern-install.sh --without-plugins
```

Confirm the binary runs before believing the install — "exit 0" is the shape a silent
failure takes.

### The source tree the CPG was built from — a hard precondition

**The exporter needs the source tree, not only the CPG. CPG-only analysis is not
possible.** This is a new precondition and the most likely reason an otherwise-correct
invocation fails, so it is stated here rather than in troubleshooting alone.

`cartographer/export_ast.sc` reads the original source text, and the reason is `*args` /
`**kwargs`. Joern's `pysrc2cpg` sets `IS_VARIADIC` on `*args` and sets **nothing** on
`**kwargs`: by every graph property, `**kwargs` is indistinguishable from an ordinary
positional parameter. No CPG property records the stars. What the CPG does carry is
`OFFSET`, the parameter name's byte offset in its file, so the exporter opens the file at
that offset and counts the `*`s before the name.

The alternative — treating `**kwargs` as positional — is a silent mistranslation of exactly
the kind the hole mechanism exists to prevent, so the exporter **aborts** instead:

```
export_ast: cannot read source for <file> (root='<cpg.metaData.root>') to decide
whether parameter '<name>' is `*args` or `**kwargs`. Run the exporter against the tree
the CPG was built from.
```

What this means in practice:

* The tree must still be at the path recorded in `cpg.metaData.root` when the exporter
  runs. Moving or deleting a source tree after `joern-parse` breaks a later re-export.
* A `.cpg` archived on its own is **not** sufficient to regenerate an AST. Archive the
  source revision with it — which is what `provenance/<artifact>.prov.json` records (§5).
* The star-count is gated to `.py` files. In C and C++ a `*` before a parameter name is a
  pointer, not a splat.

A missing source tree fails the run loudly instead of producing a mistranslation. That is
the intended behaviour; the fix is to re-parse from the tree, or to run the exporter
somewhere that path resolves.

### Python

Python 3 is required for the transpiler's printer, the oracles and the assurance-case
emitter. **Some corpora need a specific interpreter**: the differential and execution
oracles import and run the target repository's own test suite in-process, so they must run
under a Python the corpus supports. `cachetools`' suite needs **Python 3.11**, and the
oracles say so when they detect a mismatch:

```sh
python3.11 scripts/differential.py ast-Cachetools.json ~/src/cachetools Cachetools 5
```

A C compiler (`cc`) is needed only for the C conformance corpus.

## 2. The entry points

### `./autoform.sh <source-dir> [ModuleName]` — translate

Eight stages, each announced:

| Stage | What it does | What it writes |
|---|---|---|
| `[1/8] parsing` | `joern-parse` builds the CPG | `cpg.bin` in a temp dir |
| `[2/8] cartographer` | call graph, effects and formalizability | `formalization-graph.json` |
| `[3/8] transpiler` | CPG → language-neutral JSON AST | `ast-<Module>.json` |
| `[4/8] rendering Lean` | deterministic JSON → Lean printer | `Autoform/Generated/<Module>.lean` |
| `[5/8] type-checking` | build the generated Lean module | `.olean` |
| `[6/8] differential conformance` | compare actual runtime observations with Core execution | `conformance.json` |
| `[7/8] coverage ledger` | compute static holes and call closure | `ledger.json` |
| `[8/8] runtime proofs` | prove the compared observations in the kernel | `specs.json`, `Autoform/SpecsGen/<Module>.lean` |

then instantiates `scripts/ledger.lean.tmpl` and `#eval`s it, which prints the ledger and
writes `ledger-<Module>.json`.

**Large models render in parts.** With `AUTOFORM_SHARD_FUNCTIONS=N` (the installed CLI's
`--shard-functions N`, default 1000; `0` disables it), stage 4 writes definitions into
`Autoform/Generated/<Module>/PartNNNN.lean`, at most N functions each. The parts import
only the semantics, so stage 5 elaborates them in parallel, and each `lean` process holds
one part instead of the whole corpus. The root module imports every part and still defines
`moduleInits` and `program`, so every downstream name is unchanged. A model of N functions
or fewer renders as the single module it always was. Tracked corpora are always rendered
unsharded, because their pins in `artifact-manifest.json` are hashes of that render. See
[`scale.md`](scale.md) §4.

**Proof budget.** Stage 8 compiles each candidate theorem alone before emitting the module.
Any candidate that runs past `AUTOFORM_THEOREM_TIMEOUT` seconds (default 300) or
`AUTOFORM_THEOREM_MEMORY_GB` resident (default 16) is excluded by name. Up to
`AUTOFORM_PROBE_JOBS` (default 2) probes run concurrently. Each exclusion and its reason
appear in the generated module (`budgetExcluded`, printed when it builds) and in
`specs.json` (`budget_excluded`). A candidate that simply fails to prove is not affected:
it stays an open obligation.

Stage 6 failures are recorded and propagate a nonzero exit status after the ledger.
Proof synthesis runs only after successful conformance. Stage logs, reports and a
final `pipeline.json` live in `artifacts/pipeline/<Module>/`. A new run invalidates
previous evidence before starting, so an interrupted run cannot reuse a passing report.

### `./assure.sh <source-dir> <ModuleName>` — translate and argue

Runs `autoform.sh`, then:

| Stage | Tool | Artefact |
|---|---|---|
| execution coverage | `scripts/core_oracle.py`, using the same observations | `core-oracle.json` |
| specification adequacy | `scripts/mutate.py`, targeting the generated proofs | `mutation.json` |
| proof audit | `scripts/audit_all.py`, after restoring the mutated subject | `audit.json` |
| contracts and assurance case | `scripts/emit_contracts.py`, `scripts/sacm.py` | `contracts-<Module>.json`, `sacm-<Module>.json`, `assurance.md` |

Every run finishes with `summary.md`, `run.json`, and `assurance.md`, including runs
where parsing, compilation or native execution fails. Dependent checks are marked
blocked and fresh evidence is required before proof/mutation/audit stages run.
The exit status remains nonzero for failed checks or an unsupported assurance claim;
`execution_status: completed_with_gaps` does not mean the source was verified.
Sampled conformance cannot establish translation correctness for all inputs.

Linux trees are detected from their ancestors' Kbuild/Kconfig files. Without a
compilation database the frontend supplies kernel annotation macros and the selected
integer model's `BITS_PER_LONG`. The native adapter automatically tries scalar
entry points in separate, unchanged translation units using Linux's own userspace
compatibility headers. A failed unit leaves diagnostics in `native-build.json` and
does not discard successful units. These are host portability observations, not
execution in a booted kernel. `context.json` records that boundary.

A `compile_commands.json` at the source/kernel root, or `AUTOFORM_COMPILE_COMMANDS`,
is passed to Joern as a compilation database. A configured target requires a
matching runtime adapter; Autoform refuses to substitute host portability
observations for that target. `CPP_DEFINES` reaches both parsing and native
compilation. `AUTOFORM_CFLAGS` adds native compiler flags. Header dependencies used
by native observations are hashed and rechecked before proof synthesis.

`frontend.json` records the CPG population and excluded declarations. Functions with
unparsed nonempty bodies remain visible as holes. The CPG population is not an
independent source census. Kernel synchronization is explicitly represented by
`effect:kernel-sync:<operation>` holes.

### `autoform regress <repo> [Module] --base REF [--head REF]` — compare two commits

Runs `autoform.sh` at two commits of one repository and compares what each run could
prove, never the source text. `<repo>` is a Git URL or a local checkout with a `.git`
directory; `--head` defaults to the repository's `HEAD`; `--subdir` selects the same
directory inside both checkouts; `--timeout` bounds each of the two runs. The same
module name is used at both commits on purpose, because theorem identifiers are per
function and must line up across the runs.

Each run's report is copied from `artifacts/pipeline/<Module>/` to
`artifacts/regression/<Module>/{base,head}/` before the next run overwrites it, and
`scripts/regression.py compare` writes `regression.json` and `regression.md` next to
them (`runs.json` records the resolved commits and exit codes). The comparison is over
the facts a run records:

| Fact at `--base` | Lost at `--head` | Reported as |
|---|---|---|
| a function translated without holes | it holes (`hole` / `holeS` in `ast-<Module>.json`) | regression `translation`, with the labels |
| a theorem in `specs.json` was proved | refuted, open, or no longer emitted while the function still exists | regression `proof` |
| every recorded runtime case of a function agreed with the runtime | a recorded case diverges | regression `conformance` |
| the pipeline passed | it stops at an earlier stage | regression `pipeline` |
| a recorded case `(function, self, args)` had outcome `x` | the same inputs have outcome `y` | **behavior change**; `proven_both` when the function's theorem holds at both commits |

The reverse of each row is an improvement; functions present at only one commit are
listed as added or removed and are never regressions by themselves (a removed
function's proved theorems are named). Exit `0` when nothing regressed and no outcome
changed, `1` otherwise, `2` when a run never reached translation or the source is not a
Git repository. A behavior change is reported under its own heading and still exits `1`:
the tool can show that the two commits provably compute different things on the same
inputs, not whether that was intended.

Scope: a function the runtime never reached has no cases to compare, and an outcome
that changed on inputs recorded at only one commit is not visible. Random cases are
drawn with a fixed seed so the two runs see the same inputs; test-suite cases follow
the repository's own tests at each commit. `scripts/regression.py profile <report>`
prints the facts one run recorded; `compare <base> <head>` diffs any two report
directories, including ones produced by hand or by CI at different times.

### `autoform regress <repo> [Module] --base REF [--head REF] --machine --files FILE...` — compare compiled code

Instead of running the source pipeline, `--machine` compiles the listed files at both
commits for a Linux target (`--target aarch64`, the default, or `x86_64` or `i386`),
links each commit's objects with `ld.lld` so calls between files resolve, and lifts
each compared function through Ghidra's SLEIGH descriptions into the p-code Lean model.
`--functions` names the functions to compare; by default every function whose compiled
bytes changed is compared. It works for any language `clang` compiles to these
targets; kernel headers are replaced by the declaration-only shim in
`scripts/kernel_shim/`.

For each function:

1. **Search.** Candidate inputs are each parameter type's width boundaries (powers of
   two straddling 32 and 64 bits, the type's extremes, their neighbours) and seeded
   random values; parameter and return shapes come from DWARF. If this host can execute
   the target's calling convention (an arm64 host for AArch64 integer functions), both
   commits are also built for the host and run natively. Otherwise the lifted Lean
   models are executed on the candidates. `scripts/machine_regress.py --input a,b,c`
   supplies known reproducers, which are tried first and always reported.
2. **Confirmation.** Each diverging input is re-run on both lifted models, which must
   agree with native execution, and then **kernel-checked**: one Lean theorem per
   commit states the exact return value its machine code produces on that input, proved
   by `rfl` against the SLEIGH-lifted program.

`artifacts/regression/<Module>/machine/` holds `regression.json`, `regression.md`,
both commits' linked images, and the Lean check files. Exit `0` when no divergence was
found, `1` when at least one was found and kernel-checked, `2` on a build or usage
failure.

What it proves and what it does not: a reported divergence is a machine-checked fact
that the two commits' compiled code returns different values on that input. Which
result is correct needs a specification or a reference; a divergence on an input
outside the function's contract (for example a result that cannot fit its type) is
reported like any other. "No divergence found" means none among the inputs tried,
never equivalence. SLEIGH descriptions are trusted, and arguments are limited to
integer registers (no stack-passed arguments, floats or aggregates).

## 3. Reading the ledger

The human form is printed at the end of `autoform.sh`:

```
╭─ autoform trust ledger ─ <Module>
│ functions translated : …
│ AST nodes            : …
│ holes                : …  (…% of nodes)
│ hole-free (upper bd) : … / … functions
│ VERIFIABLE CORE      : … / … functions — hole-free AND call-closed
│ dynamic-hole risk    : … constructs may hole at runtime (input-dependent)
│ semantics            : Autoform.Core (fuel-indexed, total, no sorry)
│ transpiler           : Joern CPG → Core, deterministic
│ NOT PROVED           : transpiler faithfulness — see conformance.json
├─ holes by cause ─────────────────────────────────────────────
│ N  <hole label>
…
```

How to read it:

* **hole-free** is an *upper bound*: no holes in the AST. It says nothing about what the
  interpreter does with that AST.
* **VERIFIABLE CORE** = hole-free **and** call-closed (every call and method target
  resolves inside the translated program). This is the honest number, because an
  untranslated callee is invisible in the AST — a call to a function that was never
  translated looks exactly like a call to one that was.
* **dynamic-hole risk** counts constructs that *can* hole on some input. It is the static
  analysis admitting what it cannot adjudicate; only `scripts/core_oracle.py` settles it.
* **holes by cause** is the taxonomy from `docs/core-language.md`. Nothing is dropped
  silently, so this table lists everything the translation refused to guess at.
* **NOT PROVED : transpiler faithfulness** is the trust boundary, not boilerplate.

`ledger-<Module>.json` is the same data, tagged with `module` and `dialect` so that
`scripts/sacm.py` can attribute it. Untagged evidence cannot support a claim about a
subject, and the assurance case caps it accordingly.

## 4. Running individual oracles

```sh
# conformance vs the real runtime (CPython / cc)
python3.11 scripts/differential.py ast-<M>.json <src-dir> <M> 5 [--tests DIR] \
        [--no-cache] [--cache-dir DIR]

# execution oracle over the claimed verifiable core
python3.11 scripts/core_oracle.py ast-<M>.json <M> <src-dir> [-n 24] [--fuel 5000]

# axioms, escape hatches, kernel replay  (--strict fails on a missing leanchecker)
python3 scripts/audit_all.py --strict

# mutation gate, hand-written Lean
python3 scripts/mutate.py Autoform/Lang/Imp/Semantics.lean Autoform.Lang.Imp.Semantics --max-mutants 8

# mutation gate, generated module (mutate the data, rebuild the specs about it)
python3 scripts/mutate.py Autoform/Generated/<M>.lean Autoform.Generated.<M> \
        --spec-file Autoform/Specs/<M>Spec.lean --spec-module Autoform.Specs.<M>Spec \
        --decls f_a,f_b

# assurance case
python3 scripts/sacm.py --module <M> [--markdown sacm-<M>.md]

# scale measurement, stage by stage (see docs/scale.md)
python3 scripts/scale_test.py --out results.json --target Name /path/to/repo
```

**The conformance oracle is incremental by default.** It stores one verdict file per
function under `.autoform-work/oracle/<M>/` (`--cache-dir DIR` relocates it) and, on the
next run, sends back to the Lean interpreter only the functions whose key changed: the
function's own AST record and its rendered Lean definition, the same for every function
it can reach (by name, by dispatch through its class hierarchy, or through the classes
of the objects in its cases), the module bodies and the rest of the rendered module,
`Autoform/Lang/Core`, the renderer, the harness, the Lean toolchain, the runtime
version, or the recorded cases themselves. A change to
`Autoform/Lang/Core` invalidates every entry. The test suite is traced on every run; only
the evaluation is skipped. Replayed verdicts are reported as such -- the summary reads
`N COMPARED now, M cached from <timestamp>`, and each replayed observation in
`conformance.json` carries `cached_from` -- and are never counted as comparisons made
now. `--no-cache` ignores the store and re-compares everything (the entries are still
refreshed). The store is scratch state: delete the directory to start cold.

`Demo.lean` (`lake env lean Demo.lean`) is a guided tour of the refutation gate, the axiom
audit, vacuity detection and the ledger. It **deliberately contains an admitted theorem and
two failing audits**, so `lean` exits non-zero by design; what matters is that
`TRUSTED-CODE LEAK` and `VACUOUS` appear in the output. CI asserts exactly that.

## 5. Reproducibility and provenance

`lake-manifest.json` pins every Lean dependency and `lean-toolchain` pins the compiler, so
the Lean half of the pipeline is reproducible. `joern-version` plus the records under
`provenance/` do the same for the front-end half.

### The cheap check — run it anywhere

```sh
python3 scripts/check_provenance.py             # no Joern, no CPG, no source tree needed
python3 scripts/check_provenance.py --strict    # also refuse the unattributed backlog
python3 scripts/check_provenance.py --verify-source   # re-derive source_revision if present
```

It answers six questions from tracked bytes alone:

| Check | Fails when |
|---|---|
| coverage | an `ast-*.json` has neither a record nor a named backlog entry |
| integrity | the record's `artifact_sha256` is not the file's digest |
| pin | the record's `joern_version` differs from `joern-version` |
| **exporter** | `cartographer/export_ast.sc` changed since the artifact was exported |
| fields | a field a regeneration needs is missing or empty |
| orphans / backlog expiry | a record describes nothing, or a backlogged artifact's digest moved |

The **exporter** row is the one that matters most, because the `.cpg` files are not tracked
and never will be — they are hundreds of megabytes. A committed AST therefore cannot be
diffed against a re-export of its own CPG. But it does not need to be: the moment the
exporter changes, every AST recorded against the old exporter is *mechanically known* to be
stale, and its record carries the exact command that regenerates it.

Finding nothing to check is a failure, not a pass: with no `ast-*.json` present the script
exits 2 and says so.

### Producing an attributed artifact

```sh
scripts/export_with_provenance.sh <source-dir> <ModuleName>
```

`joern-parse` → `export_ast.sc` → `provenance.py record`, refusing to start unless the
installed Joern matches the pin. `./autoform.sh` does **not** yet record provenance (see
docs/architecture.md, "Merge-phase changes this asks for elsewhere"), so an AST it produces
is unattributed and the checker will name it.

To record provenance for an artifact produced some other way:

```sh
python3 scripts/provenance.py record \
  --artifact ast-<M>.json --source <source-dir> \
  --exporter cartographer/export_ast.sc --command '<the exact command you ran>'
python3 scripts/provenance.py show ast-<M>.json
```

`source_revision` is the source tree's git commit when it is a checkout (with `+dirty` when
it is not clean) and a `tree-sha256:<digest>:<n>files` content digest when it is not — an
unpacked tarball, for instance. Both are re-derivable from the same bytes later, which is
the only property required. `record` refuses rather than inventing a value it cannot
determine.

### The expensive check — independent recomputation

```sh
python3 scripts/reproduce_ast.py ast-<M>.json [--source <dir>] [--keep <dir>]
```

Rebuilds the CPG from the recorded source tree with the pinned Joern, re-runs the committed
exporter, and diffs. It never reads the committed AST to decide what to expect. Exit 0 =
byte-for-byte reproduction, 1 = differs (with a summary of how), 2 = could not run, with the
reason. Minutes per corpus, which is why it is a command and not a build step.

### The unattributed backlog

`provenance/unattributed.json` lists the `ast-*.json` files that predate this mechanism.
It is a **named gap, not an exemption**: every entry is printed by name on every run, and an
entry stops applying the moment its artifact's digest changes — regenerate one and you must
record real provenance for it.

Three of them were re-exported to find out rather than assumed, and **all three differ from
a fresh export** with the pinned Joern and the committed exporter: `ast-Sample.json` and
`ast-Stress.json` are missing the module-initializer entries the exporter now emits, and in
`ast-CMath.json` every integer literal is `"v": 0` where a fresh export writes `"v": "0"`.
That is recorded in the file as the finding it is. The remaining eight were not reproduced
because the source tree they came from is not identified anywhere in the repository — which
is the same gap, one step earlier.

## 6. Troubleshooting

**A large AST hits Python's recursion limit.** The main source pipeline reads JSON
containers and walks AST bodies iteratively through `scripts/deep_json.py`; it does
not require callers to raise Python's recursion limit. The reader preserves standard
JSON string and number decoding and rejects malformed containers. Rebuild an older
installed package and use a new workspace to pick up this change.

**Native comparisons agree but proof synthesis reports an exhausted budget.** Native
conformance reports record `interpreter_fuel` and `initializer_fuel`. Proof synthesis
uses those budgets and checks a smaller sufficient proof budget when possible. Older
native reports without these fields use the differential harness's established default.
An exhausted execution or failed execution precondition remains unverified; it is not
reported as a counterexample to the native behavior. A completed execution that disagrees
with the expected result can still refute a candidate.

**`leanchecker` passes but checked nothing.** Always pass `--fresh`. Without it the checker
can silently no-op on a module that has only imports and no declarations of its own —
exactly the shape of `Autoform.lean`. `scripts/audit_all.py` uses `--fresh` by default and
records which mode ran in `audit.json`; `--no-fresh` exists but is strictly weaker. If you
invoke the checker by hand, use `lake env leanchecker --fresh Autoform` (~1.5 min).

**`leanchecker` is missing.** The audit reports UNVERIFIED — never a pass — and `--strict`
turns that into a non-zero exit. A gap that is reported is a gap; a gap that is skipped
silently is a lie.

**`export_ast: cannot read source for …`.** The exporter needs the source tree the CPG was
built from, at the path recorded in the CPG metadata — see §1, "The source tree the CPG was
built from". It is deciding whether a parameter is `*args` or `**kwargs`, which no CPG
property records. Re-parse from the tree, or run the exporter where that path resolves.
The failure is deliberate: without the source text the exporter would have to guess, and a
guess here is a mistranslation rather than a hole. If all you have is a `.cpg`, you cannot
export from it; you need the source revision, which is why `provenance/` records it.

**`joern-version: MISMATCH`.** The installed Joern is not the pinned one. Do not just
proceed: the neutral AST is a function of the front end, so anything you regenerate will
differ from its neighbours for reasons that have nothing to do with the source. Install the
pinned release (§1) or change the pin deliberately and regenerate everything.

**`check_provenance: … changed since this artifact was exported`.** The exporter moved and
the committed ASTs did not. This is the check working. Regenerate the artifact with the
command in its record (`scripts/provenance.py show ast-<M>.json`), re-render the Lean module
from it, and re-record. Do not edit the record to match the new exporter digest — that
turns a real staleness finding into a green check.

**`check_provenance: found no ast-*.json … Nothing was checked`.** Exit 2, not 0. You are
running it somewhere without the artifacts; pass `--root`.

**The oracle reports divergences that make no sense.** Suspect a stale `.olean` first. An
oracle reading a stale cache answers with the *previous* semantics and produces confident,
specific, wrong findings. `differential.py` and `core_oracle.py` both `lake build` before
comparing; if you are running something by hand, build first.

**The audit reports a build failure or changed artifacts.** It builds its root module
before replay and records the source, compiled imports and supplied evidence. Fix the
build failure or let concurrent edits finish, then rerun the audit. `--module` selects
the root; the default is `Autoform`. An old passing audit cannot validate changed files.

**Joern "installed" but nothing works.** See §1 — the macOS arm64 installer exits 0 on
failure. Check that `$JOERN_HOME/joern-cli/joern-parse` exists and runs.

**The differential harness finds zero comparable cases.** Usually one of: (a) the test
suite was not found — discovery walks up from the source root, and a `src/`-layout repo
with sibling `tests/` needs the repo root, not `src/`; (b) the interpreter is wrong for the
corpus (try `python3.11`); (c) the arguments are unencodable (floats, sets, locks, very
wide containers) or the receivers are `tuple`/`dict` subclasses, which Core cannot
represent as objects. Cases refused for (c) are counted under `unencodable_reasons` in
`conformance.json` — refused, never silently compared.

**A mutation run reports inconclusive checks.** Timeouts, dependency errors and failures
without a diagnostic in the subject theorem receive no kill credit. Inspect the recorded
reason and build output. The gate also requires the original source to rebuild after
mutation; an incomplete run cannot support a guarantee.

**Build is slow.** Specimen and Plausible dominate. Cache `.lake` (CI keys the cache on
`lean-toolchain`, `lake-manifest.json`, `lakefile.toml` and the source hashes).

**`Autoform/Generated/*.lean` looks wrong.** Do not hand-edit it. It is a pure function of
`ast-<Module>.json`; re-run `cartographer/render_lean.py`, and if the AST is wrong, fix the
exporter.

## 7. Exit codes

One table, matching the code. `autoform --help` prints the short form; this is the
authority when they disagree, and a disagreement is a bug to file.

| command | `0` | `1` | `2` | other |
|---|---|---|---|---|
| `autoform doctor` | every **required** tool (Python 3.10+, git, lake, lean, leanchecker, joern) present and matching its pin | a required tool missing or mismatched; with `--strict`, also an optional one | the check itself could not run (package payload unreadable) | — |
| `autoform init` | workspace extracted or already matching this package | — | workspace not empty, from a different package, or an init already in progress | — |
| `autoform source` / `./autoform.sh` | every stage ran and the differential oracle agreed | a stage failed (parse, graph, export, render, build, ledger, proofs) or the oracle reported divergences — the stage's log is under `artifacts/pipeline/<Module>/` | usage error, module name not a Lean identifier, Joern not installed, busy workspace, or the run was **refused** because the tree holds a live `.mutate-backup` or modified tracked artifacts (§5, `docs/integrity.md`) | `128+N` interrupted by signal N; `--timeout` expiry is `143` |
| `autoform assure` / `./assure.sh` / a Git URL | every required check completed | the workflow finished with unresolved verification gaps — `completed_with_gaps` in `run.json`; a scoped certificate in `guarantee.json` can coexist with this | invocation, setup or orchestration failure; source acquisition failed; property input invalid; refused tree as above | `128+N` |
| `autoform regress --machine` | no divergence found among the inputs tried | at least one kernel-checked diverging input (`machine/regression.json`) | usage error, a build, link or lift failure, or a source that is not a Git repository | `128+N` |
| `autoform regress` | both runs translated and nothing that held at `--base` is lost at `--head`, and no recorded case changed outcome | a regression or a proven behavior change (`regression.json` says which), or a run that never produced an AST | usage error, the source is not a Git repository, a ref could not be fetched, busy workspace, or a refused tree as above | `128+N` from either run; `--timeout` expiry is `143` |
| `autoform machine` | as `scripts/formalize_machine.py` | as `formalize_machine.py` | CLI-level failure (workspace, lock, extraction) | — |

Two things worth stating plainly. A `1` from `assure` is **not** a crash: it is the
workflow saying the assurance case has gaps, which is the honest outcome for most
real repositories — read `run.json` and `guarantee.json` together. And a `2` from the
integrity guard is deliberate: `AUTOFORM_ALLOW_DIRTY=1` lifts the modified-artifact
check for someone iterating on a render they know is uncommitted; nothing lifts the
live-mutant check, because there is no legitimate evidence to collect over a mutant.
