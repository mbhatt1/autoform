# GitHub Action: evidence levels on a pull request

`action.yml` at the repository root is a composite action that runs
[`autoform pr`](cli.md#pr) on a pull request and reports, for each function the
change touched, the evidence level its artifacts reach (`none`, `hole`, `translated`,
`oracle-agreed`, `proved`, `refuted`; see [evidence-levels.md](evidence-levels.md)).
It is derived from `.github/workflows/pr.yml`, which runs the same chain on this
repository's own fixture.

What it does with the result:

* writes SARIF 2.1.0 (one result per changed function) and uploads it with
  `github/codeql-action/upload-sarif` to code scanning;
* appends the Markdown report to the **job summary only**. It does not comment on the
  pull request, so it needs no `pull-requests: write` permission.

What the output means is limited the way `docs/evidence-levels.md` says: `proved` is a
kernel-checked statement about recorded cases under the interpreter's semantics, not a
correctness proof of the function.

## Copy-paste workflow

```yaml
name: autoform
on:
  pull_request:

permissions:
  contents: read
  security-events: write   # SARIF upload to code scanning

concurrency:
  group: autoform-${{ github.ref }}
  cancel-in-progress: true

jobs:
  evidence:
    runs-on: ubuntu-latest        # Linux x64 only when install-toolchain is true
    timeout-minutes: 60
    steps:
      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4
        with:
          fetch-depth: 0          # the base commit must be present
      - uses: actions/setup-python@a26af69be951a213d495a4c3e4e4022e16d87065 # v5
        with:
          python-version: '3.11'
      # Pin to a full commit SHA you have reviewed; this one is main on 2026-10-11, the
      # commit whose CI passed all four required workflows and that release_check.sh
      # reports as READY.
      - uses: mbhatt1/autoform@becfe15f513aa52a7906772657b32dc411b6a4e4
        with:
          module: PullRequest
          # base defaults to the pull request's base commit
          # subdir: src/mypackage        # restrict to one directory
          # mutants: '4'                 # mutation gate over proved theorems (slower)
```

Pin the action to a full commit SHA, as the rest of your workflows should be; a tag can
move. Inputs: `base`, `module`, `subdir`, `sarif-path` (default `autoform-pr.sarif`),
`markdown-path` (default `autoform-pr.md`), `upload-sarif`, `sarif-category`, `mutants`,
`install-toolchain`, `cache`, `fail-on-refuted`, `fail-on`, `python`, `pytest-addopts`,
`java-classpath`, `java-processorpath`. Outputs: `sarif`, `markdown` (absolute paths),
`exit-code` (0, 1, 2, or 3).

## A real run

[Pull request #14](https://github.com/mbhatt1/autoform/pull/14) changes
`unit_price(total, count)` in `examples/demo/pricing.py` to return 0 when `count == 0`
instead of raising, and runs this Action pinned to `becfe15`
([run 38149891759](https://github.com/mbhatt1/autoform/actions/runs/38149891759), 2026-10-11).
The run took 6 minutes 27 seconds from job start to finish, on a warm workspace cache. It
reported:

* 2 changed functions, both `proved` in the kernel over their recorded cases
  (`unit_price` and the test function `test_unit_price`).
* Behaviour: 1 `changed`, 1 `not-compared` (the test function); suppressed as model noise: 0.
* The code-scanning alert `autoform/behaviour-changed` on `examples/demo/pricing.py:4`:
  `unit_price(int 11, int 0): base model raises Val.str "ZeroDivisionError", head runtime
  returns int 0`, with further inputs of the same shape.

The change was deliberate, so the alert is the intended result: the Action reports a
behaviour change, and deciding whether it is a bug is the reviewer's call.

## Permissions

| permission | why | if you do not grant it |
|---|---|---|
| `contents: read` | checkout | the checkout fails |
| `security-events: write` | `upload-sarif` | set `upload-sarif: 'false'`; the Markdown summary still works |

Code scanning upload for private repositories requires GitHub Code Security (or Advanced
Security) on that repository; without it the upload step fails. Pull requests from
forks receive a read-only token, so the upload step cannot succeed there: set
`upload-sarif: 'false'` for them. Nothing else is requested: no `pull-requests`, `issues`
or `checks` write.

## Exit status

| Exit code | Meaning | When the step fails |
|---|---|---|
| 0 | Reported; nothing refuted (or refuted but `fail-on-refuted: false`) | Never (unless another step fails) |
| 1 | A function was refuted, or a behaviour change under `--fail-on behaviour-changed` | Always, unless `fail-on-refuted: false` and no `fail-on` set |
| 2 | Could not run (bad module name, missing Joern, missing base commit, etc.) | Always |
| 3 | Inconclusive: no changed function reached evidence under `--fail-on` conditions | Only when `fail-on` includes `behaviour-changed` or `no-evidence` |

`autoform pr` exits `0` when it reported and nothing was refuted, `1` when at least one
function was refuted (the model and the real runtime disagree on a recorded input), `2`
when it could not run. The action fails on `1` unless `fail-on-refuted: 'false'` and no
`fail-on` input is set, and always on `2`. A `hole`, `none` or `translated` function is
a statement about evidence, not a failure.

`3` means **inconclusive: no evidence**. It is returned only when `--fail-on
behaviour-changed` or `--fail-on no-evidence` was passed in the `fail-on` input and
not one changed non-test function reached behaviour `changed` or `unchanged-on-inputs`:
the gate compared nothing, so it can say neither "pass" nor "fail". The log and the first
line of the Markdown comment say so, and `pr.json` records it under `gate`. `1` and `2`
take precedence. Treat `3` as a failed gate (or as "needs a human"), never as a pass.

## Inputs

| Input | Description | Default |
|---|---|---|
| `base` | Commit the change is measured against | `${{ github.event.pull_request.base.sha }}` |
| `module` | Lean module name the changed functions are rendered under | `PullRequest` |
| `subdir` | Directory inside the checkout to analyse (default: whole checkout) | `''` |
| `sarif-path` | Where the SARIF 2.1.0 file is written (relative to workspace) | `autoform-pr.sarif` |
| `markdown-path` | Where the Markdown report is written (appended to job summary only) | `autoform-pr.md` |
| `upload-sarif` | Upload the SARIF to code scanning | `'true'` |
| `sarif-category` | Code-scanning category for the upload | `autoform-pr` |
| `mutants` | Mutants for the mutation gate over the proved theorems (0 skips it) | `'0'` |
| `install-toolchain` | Install pinned Lean (elan), Joern, and bubblewrap on Linux | `'true'` |
| `cache` | Cache the autoform workspace (built Lean project) between runs | `'true'` |
| `fail-on-refuted` | Fail the step when a function is refuted (exit 1) | `'true'` |
| `fail-on` | Space-separated `--fail-on` conditions: `behaviour-changed` (exit 1 when a changed function's behaviour changed), `no-evidence` (exit 3 when no changed function was compared). With either set, exit 3 also fails the step and `fail-on-refuted` is ignored. | `''` |
| `python` | Python interpreter to run the project's tests and functions under (must have project dependencies installed) | `''` (use autoform's own) |
| `pytest-addopts` | `'ignore'` runs the project's tests without its pytest addopts, e.g. when they need a plugin the interpreter lacks | `''` (use `'project'`) |
| `java-classpath` | JVM dependency classpath for the differential oracle (exported as `AUTOFORM_JAVA_CLASSPATH`) | `''` |
| `java-processorpath` | JVM annotation processor path for the differential oracle (exported as `AUTOFORM_JAVA_PROCESSORPATH`) | `''` |

## Outputs

| Output | Description |
|---|---|
| `sarif` | Absolute path of the SARIF file |
| `markdown` | Absolute path of the Markdown report |
| `exit-code` | Exit code from autoform pr (0, 1, 2, or 3) |

## Other CI systems

The action is a thin wrapper: everything it reports comes from one command, which reads
no CI-specific environment and works on any Git remote (self-hosted servers, plain bare
repositories, `user@host:path` remotes):

```sh
autoform --workspace "$WORK" doctor          # fail fast, naming what is missing
autoform --workspace "$WORK" pr . PullRequest --base "$BASE_SHA" --head "$HEAD_SHA" \
  --sarif autoform-pr.sarif --markdown autoform-pr.md
```

* **Base commit.** Pass the merge base of the change explicitly. The clone must hold it;
  `autoform pr` fetches a missing `--base` from `origin` once, and otherwise exits `2`
  saying to fetch more history.
* **Outputs.** `--sarif` is SARIF 2.1.0 with the tool version, every rule in
  `tool.driver.rules`, percent-encoded repository-relative URIs under `%SRCROOT%`, and a
  credential-free `repositoryUri`, so a SARIF consumer other than GitHub code scanning can
  ingest it. `--markdown` is the review comment; post it with your review tool's API if
  you want one. `<workspace>/artifacts/pr/<Module>/pr.json` is the machine-readable
  report (per function: level, reason, artifacts, behaviour; plus `summary` counts and
  every stage's status and reason) for a bot.
* **Exit status** is the one [above](#exit-status): `0`, `1` (refuted, or a behaviour
  change under `--fail-on behaviour-changed`), `2` (could not run), `3` (inconclusive: a
  `--fail-on` gate that compared no changed function), `128+N` when stopped by signal N
  (`--timeout` expiry is `143`). A CI gate should pass `--fail-on behaviour-changed` and
  fail on any non-zero code. A change with
  nothing to analyse exits `0` without running the exporter, with the reason in `pr.json`.
* **Scope.** Change detection reads only the files `git diff` names, and the Lean stages
  run only on the changed functions and their resolvable callees (`selection` in
  `pr.json`). The Joern export, though, covers the whole head tree (or `--subdir`): on a
  large repository bound it with `--subdir`, or supply an export made earlier with `--ast`.
* **Prerequisites** are the ones listed below; install them in the runner image rather
  than per job, and cache the workspace (`--workspace`) between runs.

Untested starting points: [`examples/ci/gitlab-ci.yml`](../examples/ci/gitlab-ci.yml) and
[`examples/ci/Jenkinsfile`](../examples/ci/Jenkinsfile). Neither has been run on its CI
system; treat the first run as the test.

## What it needs

* **Lean.** The pinned toolchain (`lean-toolchain`) and the bundled Lean project
  (`autoform pr` renders the changed functions to Lean and has the kernel check them).
  With `install-toolchain: 'true'` the action installs it through `elan`. Lake fetches
  its Lean dependencies from GitHub on a first build.
* **Joern**, at the version in `joern-version`, plus a JDK (the action installs
  Temurin 21 and downloads the Joern release with its SHA-512 check). Joern's release
  asset is selected for Linux x64 only; on other runners, install Joern yourself,
  set `JOERN_HOME`, and pass `install-toolchain: 'false'`.
* **The runtime of the language you analyse** if you want the differential oracle to
  compare against it (CPython for Python; `node`, a JDK, `go`, `cc` for the others).
  Without it the affected functions stay at `translated`, and the report says so.
* **A sandbox mechanism.** On Linux the oracle refuses to run without `bwrap` or
  `unshare`. The action installs bubblewrap and, as `pr.yml` does, sets
  `kernel.apparmor_restrict_unprivileged_userns=0` through `sudo` (Ubuntu 24.04
  restricts the user namespaces bubblewrap needs). That changes a kernel setting for the
  whole runner VM, which is acceptable on an ephemeral GitHub-hosted runner and may not
  be on yours. `AUTOFORM_SANDBOX=off` runs the code under test unconfined and records
  `enforced: false` in every artifact; do not use it on code you do not trust.
* **Python 3.10 or newer** on the runner (the example sets 3.11).
* **A Git checkout with the base commit.** Use `fetch-depth: 0`; the action also fetches
  the base commit if it is missing.

## Cost, and the cold start

The workspace (the bundled Lean project and its `.lake` build) is cached under a key
that is the exact digest of everything the action's package bundles into the workspace
(the selection `build_support.runtime_files()` makes: the Lean project, `scripts/`,
`cartographer/`, `docs/`, `examples/`, the toolchain pins and the notices) plus the CLI
sources, with no restore-keys: `autoform` refuses a workspace whose manifest differs
from the package's bundle, so a near match would fail instead of helping. Hashing the
bundle selection itself, rather than a hand-kept list of directories, means a commit
that touches only `scripts/` gets a fresh key rather than a refused cache.

* **Cold start.** The first run on a cache miss builds Lean's dependencies and the
  project's semantics from source. `docs/running.md` says to expect the first run of the
  full pipeline to take the better part of an hour, most of it in the build, and
  `pr.yml` fails fast on a missing cache because a cold build "does not fit the
  10-minute budget". We have no measured cold-start time for this action on a
  GitHub-hosted runner; budget up to an hour and set `timeout-minutes` accordingly.
* **Warm runs.** `pr.yml` bounds its fixture job to 10 minutes with a restored `.lake`;
  that is a time limit the workflow enforces on a five-function fixture, not a measured
  figure for your repository. Time depends on how many functions the change touches
  and on Lean elaboration; `AUTOFORM_PROBE_JOBS` is set to `1` to keep memory modest.
* **Cache scope.** Caches are scoped to the branch that wrote them; a pull request can
  read its base branch's cache. Run the workflow on your default branch (add a `push`
  trigger) so that cache exists.

If your repository does not use Python, C, Java or one of the other languages in
[languages.md](languages.md), the action will report `none` for every function. Rust and
Hack are not supported.
