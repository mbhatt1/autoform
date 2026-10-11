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

> **Not yet exercised on GitHub.** The action was written and YAML-validated in a
> development environment that cannot run GitHub Actions. Its steps are the ones
> `pr.yml` already runs (except the cache key, the `doctor` step and the base-commit
> fetch, which are new). Treat the first run on your repository as the test.

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
      - uses: mbhatt1/autoform@<full commit SHA of the release you reviewed>
        with:
          module: PullRequest
          # base defaults to the pull request's base commit
          # subdir: src/mypackage        # restrict to one directory
          # mutants: '4'                 # mutation gate over proved theorems (slower)
```

Pin the action to a full commit SHA, as the rest of your workflows should be; a tag can
move. Inputs: `base`, `module`, `subdir`, `sarif-path` (default `autoform-pr.sarif`),
`markdown-path` (default `autoform-pr.md`), `upload-sarif`, `sarif-category`, `mutants`,
`install-toolchain`, `cache`, `fail-on-refuted`. Outputs: `sarif`, `markdown` (absolute
paths).

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

`autoform pr` exits `0` when it reported and nothing was refuted, `1` when at least one
function was refuted (the model and the real runtime disagree on a recorded input), `2`
when it could not run. The action fails on `1` unless `fail-on-refuted: 'false'`, and
always on `2`. A `hole`, `none` or `translated` function is a statement about
evidence, not a failure.

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
that is the exact digest of the action's Lean project, with no restore-keys: a
workspace built from a different bundle is refused by `autoform`, so a near match would
fail instead of helping.

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
