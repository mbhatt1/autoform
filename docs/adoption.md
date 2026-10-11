# Adoption brief

For an engineering manager or a security reviewer deciding whether to try autoform.
Every claim below points at the document or artifact it comes from. Where a figure is
bound by `scripts/check_docs.py` (it fails if the figure and its artifact disagree) the
text says so; every other figure is quoted from the document named and is only as
current as that document.

Status: version 0.0.0, alpha (`Development Status :: 3 - Alpha`), not yet published on
PyPI. The project is an open-source CLI; `docs/releasing.md` describes it as having paid
engineering support, and `SUPPORT.md` is the support scope.

## 1. What it proves, and what it does not

autoform translates source (through the Joern code property graph) into a Lean model,
runs the real code and the model on the same inputs, and has the Lean kernel check
theorems about the recorded behaviour. For a change under review, `autoform pr` assigns
each touched function the highest of six levels its own artifacts reach:
`none`, `hole`, `translated`, `oracle-agreed`, `proved`, `refuted`.
[evidence-levels.md](evidence-levels.md) states, level by level, what is claimed, what is
not, and which artifact to open.

The short version of the limits:

* `proved` is a kernel-checked theorem that the model reproduces **recorded cases**,
  at a stated fuel. It is not a proof that the function is correct for all inputs.
* The translation from source to model (Joern, the exporter, the renderer) is not
  proved. It is checked against the real runtime by the differential oracle, which only
  covers the inputs it generated or recorded, and only for the functions it could run.
* A `hole` is a construct the model does not cover. It is named, never guessed.
* `refuted` is a witness that the model and the runtime disagree; it does not say which
  is right.

[trust-model.md](trust-model.md) lists the independent oracles, the status lattice, and
an explicit list of what the system does not establish. Read it before relying on any
number from the tool.

## 2. Language coverage

Cells are taken from [languages.md](languages.md) (its support matrix is a historical
measurement and says so: "not a current capability registry") and the README language
table. "Real corpus" means a measured open-source repository, not a fixture.

| Language | Source -> Lean model | Differential oracle against the real runtime | Measured on a real corpus (languages.md) |
|---|---|---|---|
| Python | yes; the reference dialect | CPython; yes | `cachetools`: 209 functions, 204 hole-free, 150 in the verifiable core (bound by check_docs). Pipeline run on Django (`django/`, 10,623 functions) in [scale.md](scale.md) |
| Java | yes; own dialect, 64-bit `long` | JVM backend; ran on a real corpus | Apache commons-lang3 3.17.0 subset: 488 functions, 421 hole-free, 196 in the verifiable core; oracle compared **83** functions, 196/196 cases agree, 0 divergences, 404 cases inconclusive (all bound by check_docs) |
| Go | yes; own dialect | `go test` backend; ran on a three-function fixture only | matrix row: 83 functions, 21 hole-free, 6 in the verifiable core (historical; oracle "not yet on this corpus") |
| C | yes; typed fixed-width numerics, UB is a hole | `cc`; the matrix row records the oracle as crashed on that historical corpus; README lists `cc`/`clang` | matrix row: 59 functions, 17 hole-free, 8 in the verifiable core (historical). Linux `lib/math` (`LinuxLcm`) is re-landed from kernel v7.2 |
| C++ | yes, through the C front end (README groups it with C) | as for C | no row in the support matrix. The V8 corpus (C++) is assessed in [evidence-V8Base.md](evidence-V8Base.md): "every function translated without holes" is marked UNSUPPORTED there |
| Kotlin | yes on a toy; runs as `.java` dialect | JVM through a `@JvmStatic` thunk; **no** corpus run | the matrix row for a real Kotlin repository records the front end as failing (historical); the toy row has 3 functions |
| TypeScript | yes; `.javascript` dialect | Node backend; fixture run covers `.js` only, not `.ts` | matrix row: 86 functions, 44 hole-free, 18 in the verifiable core (historical) |
| JavaScript | yes; `.javascript` dialect | Node backend; fixture only | small corpus: 14 functions, 5 hole-free. A 693-function `lodash.js` run did **not** translate (historical renderer failure) |
| **Rust** | yes, for library code Aeneas translates: rustdoc gives the public API, Charon + Aeneas the Lean (separate Lake project on Lean v4.31.0); every public function is translated or a named hole | native cargo harness (debug profile, sandboxed) vs Aeneas `#eval`, on integers, `bool`, tuples, fixed arrays and shared refs; anything else inconclusive with a reason; in CI (`rust.yml`) | gcd 2.3.0: 60 public functions, 12 translated, 12 compared, 1178/1178 cases agree, 0 divergences, 121/144 case theorems kernel-checked (bound by check_docs to `evidence-RustGcd.json`, re-derived by the Rust CI job); [rust.md](rust.md) lists what is not covered |
| **Hack** | **not supported** | none | not mentioned in `languages.md`; no front end, dialect or oracle |

The percentages and function counts that are not marked "bound" are quoted from a
historical table whose language rows have not been re-run since the fixes the document
lists. [languages.md](languages.md) records, among others, that `.tsx` once got the
Python dialect and that JavaScript numbers and Java `long` were modelled as 32-bit
before their dialects were added; the rows are from before or around those fixes.
Machine code (ELF, PE, Mach-O, assembly) is a separate path
([machine-code.md](machine-code.md)).

For a typical stack this means: Python and Java have the deepest evidence;
Go, C, C++, Kotlin, TypeScript and JavaScript translate and type-check but have little or
no oracle evidence on real code; Rust has a narrow real-crate result (integer library code that Aeneas translates) and Hack gets nothing. A hole-free function is
far from a verified function (Java: 83 compared of 421 hole-free).

## 3. Security posture

**Running the tool executes the code under analysis.** The differential oracle runs the
target's functions (and its own test suite where present) in the real runtime;
[SECURITY.md](../SECURITY.md) says this is arbitrary code execution as the analysing
user. Analyse untrusted code only in a disposable environment.

* **Sandbox.** One layer, `scripts/sandbox.py`, confines the oracle, its Node/JVM/Go
  drivers, the native C worker, the harness native replay and the nl runners: no network,
  writes only under the work directory. macOS uses `sandbox-exec` (seatbelt), Linux uses
  `bwrap`, falling back to `unshare -rn`. `tests/test_sandbox.py` is the check: a
  subject that connects to a port and writes beside its work directory fails at both.
  The record `sandbox: {mechanism, enforced}` is written into the artifacts; a run with no
  mechanism refuses unless `AUTOFORM_SANDBOX=off`, which is recorded as `enforced: false`.
* **What the sandbox does not do** ([trust-model.md](trust-model.md)): it is not a
  container or syscall filter, does not limit CPU, memory or descriptors, does not hide
  readable files from the subject, and the `unshare` fallback confines the network only.
  The documented list of confined processes does not include Joern, `lake` builds or
  compiler steps, and I found nothing in `scripts/sandbox.py` that routes them; treat
  them as unconfined and run them where a compromised build would be acceptable.
* **Linux in CI** needs unprivileged user namespaces. On Ubuntu 24.04 the workflows run
  `sysctl -w kernel.apparmor_restrict_unprivileged_userns=0` on the ephemeral runner so
  `bwrap` works. If your CI images do not allow that, bubblewrap will not start and the
  oracle refuses (or you fall back to `unshare`, network only).
* **Provenance of the inputs.** Joern is pinned (`joern-version`) and its release is
  SHA-512 verified in CI; the Lean toolchain is pinned (`lean-toolchain`); each tracked
  AST carries a provenance record naming the command that regenerates it
  (`scripts/check_provenance.py`). The gate reports `7/20 in-repository artifacts fully
  attributed` and **13 unattributed ASTs** that predate the mechanism, listed by name in
  `provenance/unattributed.json` (a named backlog, not an exemption).
* **Network.** Nothing in the analysis path needs the network except fetching the
  toolchain: `elan` and the Lean toolchain, Lake's Lean dependencies (from GitHub), Joern,
  and the JDK. Analysis of a local checkout does not call out; the subject has no network
  inside the sandbox. Exceptions you opt into: `autoform <git-url>` clones (network
  egress), and the `autoformalize` features call a model API (the `llm` and `bedrock`
  extras).
* **Release supply chain.** Third-party GitHub Actions are pinned to commit SHAs; each
  workflow job has an explicit least-privilege `permissions:` block; the publish path
  attaches a CycloneDX SBOM and a build-provenance attestation to the release, and PyPI
  upload uses trusted publishing (no stored token). These are defined in
  `.github/workflows/package.yml` and have not yet run, because no release exists
  ([packaging.md](packaging.md)).
* **License.** `Apache-2.0 AND MIT` (`pyproject.toml`); notices in `LICENSE`, `NOTICE`,
  `licenses/` and [THIRD_PARTY.md](../THIRD_PARTY.md). The one runtime dependency of the
  wheel is `hypothesis`.

## 4. Integration

* **CLI.** `autoform pr SRC --base REF --sarif pr.sarif --markdown pr.md` for a change;
  `autoform assure`, `source`, `regress` for whole modules ([cli.md](cli.md)). Exit
  status: `pr` is `0` reported, `1` a function was refuted, `2` could not run.
* **SARIF.** One result per changed function, rule `autoform/<level>`, validated against
  the shape GitHub code scanning ingests; the committed fixture output was checked against
  the SARIF 2.1.0 schema ([evidence-levels.md](evidence-levels.md)). Other SARIF
  consumers have not been tried.
* **GitHub Action.** `action.yml`; see [github-action.md](github-action.md). Not yet run
  on GitHub.
* **Bazel and Buck are not integrated.** The tool takes a Git checkout and a directory;
  there are no rules, aspects or build-graph integration. A monorepo needs `--subdir`
  and a Git history with the base commit.
* **Other CI systems.** Run the CLI; there is no packaged integration beyond GitHub.

## 5. Scale and cost

From [scale.md](scale.md), measured in 2026 on one development machine under concurrent
load ("treat the shape of the growth as the result and the absolute seconds as an upper
bound"):

* The pipeline completed on Django's `django/` package: 165,118 lines, 10,623 functions,
  with two limits raised. Lean elaboration took 110 s at 10.3 GB peak; the ledger
  stage took 363 s at the time, which the scale document identifies as superlinear.
  With sharded rendering (12 parts) the same Lean build took 244 s at 3.3 GB. A Python
  ledger from the AST later ran in 6.98 s ([GOAL-arbitrary-codebases.md](GOAL-arbitrary-codebases.md)).
  **The Django figures are not bound by `check_docs`**: the checker reports them
  UNBOUND when `ledger-Django.json` is absent, and CI does not export Django.
* Coverage is far from total at scale: in the table of seven Python repositories in
  `scale.md` the hole-free share is between 40% and 65% and the verifiable core between
  14% and 52% (table is historical and unbound; `cachetools` is bound and is 97% / 71%).
* `autoform pr` runs on the changed functions only, but its cold start is dominated by
  building Lean from source: [docs/running.md](running.md) says the first run takes the
  better part of an hour. Cache `.lake` ([github-action.md](github-action.md)).
* Generated Lean modules are large. Django's elaboration peaked at 10.3 GB and
  unsharded at 16.7 GB (scale.md); the CI workflow builds two cachetools constructor
  parts that its history describes as 11 GB each, and builds `Autoform.CI` because the
  full build's parts "exceed the runner's memory" (`docs/releasing.md`). Size runners for the
  corpus you analyse and measure on yours.
* Model API cost applies only to `autoformalize`/`formalize`, which have a per-run
  budget (`docs/autoformalize.md`); `autoform pr` does not call a model.

## 6. Named gaps

* **Django figures are unbound** in `check_docs` when `ledger-Django.json` is absent
  (it is not regenerated by CI), so those numbers in the docs are not guarded against
  drift.
* **13 ASTs are unattributed** (`provenance/unattributed.json`): the tree and revision
  that produced them is not recorded, including the V8 corpora. They are evidence of
  what the tool did, not reproducible from the repository.
* **Linux sandboxing needs unprivileged user namespaces.** CI relaxes the Ubuntu 24.04
  AppArmor restriction to get `bwrap`; on hosts that forbid it, only the network-only
  `unshare` fallback or no confinement is available.
* **Java evidence is 83 of 421** hole-free functions compared with the real JVM
  (commons-lang3 subset). The inconclusive cases are named in
  [languages.md](languages.md): `String` methods beyond the modelled set
  (`trim`, `toLowerCase`, `toCharArray`, ...), static calls into `java.lang`, and
  Java class initializers, which are not exported.
* **Joern, `lake` and compiler steps are not sandboxed** (section 3).
* **Joern's export is not byte-stable** on some inputs: re-exports differ in the choice of
  an overload resolution on commons-lang3 and in an argument order on Jinja2
  ([languages.md](languages.md)). Provenance records name the command, not a promise of
  identical bytes.
* **No Hack, Bazel or Buck support, and Rust only for library code Aeneas translates** (pure integer-style functions; traits, generics, floats, strings, collections and `unsafe` end as named holes or inconclusive, see rust.md). C#, PHP, Ruby and Swift were not tested.
* **The GitHub Action and the release supply-chain jobs have not run.**

## 7. A first-week evaluation plan

Aim: learn whether the evidence is useful on your code before committing anything.
Use a disposable machine or VM; the tool executes the code it analyses.

**Day 1: install and verify the toolchain.** Install from a checkout until the first
release is on PyPI (`python -m pip install .`, see [packaging.md](packaging.md));
run `autoform doctor --strict`. Expect it to name each missing prerequisite (Lean via
`elan`, Joern at the pinned version, a JDK, the runtimes of your languages, a sandbox
mechanism). Run the fixture from [evidence-levels.md](evidence-levels.md); it should
print the levels the document lists (`quotient`, `clamp`, `label` proved).

**Day 2: pick a corpus that fits the table in section 2.** A pure-Python or
static-method Java library of a few thousand lines is the best match to what has been
measured. Avoid starting with Go, Kotlin, TypeScript, or code that is mostly I/O,
reflection or C extensions: you will mostly see `hole` and `translated`. Run
`autoform assure` or the source command on a module and read the ledger: how many functions
are hole-free, how many are in the verifiable core, and the named holes by cause. Decide
now whether that coverage is enough to be useful.

**Day 3: history replay.** Take 10 to 20 merged changes from that repository, including
a known bug fix. Run `autoform pr SRC --base <parent> --head <commit>` on each. Record the level per touched function and the time taken.
Questions to answer: how often are changed functions `proved` or `oracle-agreed` versus
`hole` or `none`? Does any change land `refuted`, and is it a true defect or a modelling
gap (the report gives the witness)? The count of `refuted` that are real defects, and the
count of false alarms, are the numbers your decision should rest on.

**Day 4: the sandbox and the CI environment.** Confirm the sandbox actually confines on
your CI images: run `python -m pytest tests/test_sandbox.py -q`. On Linux CI, check
that unprivileged user namespaces are permitted. Decide how Joern, `lake` and compilers
will be isolated, since they are not confined by autoform.

**Day 5: the GitHub Action on a throwaway repository.** Use the workflow in
[github-action.md](github-action.md) on a fork, pinned to a commit SHA. Measure the
cold start and a warm run; check the SARIF appears in code scanning and the summary
renders. This is the first real exercise of the action.

**Decision criteria at the end of the week.** Write them down before Day 3: for example,
"at least X% of changed functions reach `translated` or better on our code" and "no more
than Y false `refuted` per 100 changes". The tool cannot supply those thresholds; the
documents above say what each level does not prove, so a threshold should be about
review effort saved, not about correctness assurance.

Tell the project what you found: [SUPPORT.md](../SUPPORT.md).
