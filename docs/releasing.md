# Releasing

The product is an open-source CLI with paid engineering support (`SUPPORT.md`). A release
is a specific wheel and source distribution of `autoform-lean`, the toolchain pins it
carries, and the body of evidence that was green on the commit it was cut from. This page
is the procedure for cutting one. Every line is a gate: tick it only with the command's
actual output in hand. A gate skipped because a tool was missing is an unmet gate, and
"the last release passed it" is not evidence about this one. The current package is an
alpha (`pyproject.toml` classifiers; `SUPPORT.md`) and does not warrant correctness of
arbitrary source repositories.

Versions, wheel names and counts below are written as `<version>` or named by the
command that prints them (CONTRIBUTING.md rule 7). The last release is the latest
`v*` tag (`git tag -l`); publication is documented in [packaging.md](packaging.md).

## 1. Preconditions

- `git status --porcelain` is empty. `scripts/release_check.sh` refuses otherwise, and
  the integrity guard sourced by `autoform.sh` and `assure.sh` refuses a modified tracked
  `Autoform/Generated`, `Autoform/SpecsGen` or `ast-*.json` and any `*.mutate-backup`
  (`scripts/integrity_guard.sh`).
- Python 3.11 for release tooling (what `package.yml`'s build job uses), the Lean
  toolchain in `lean-toolchain`, Joern at the version in `joern-version` installed by
  `scripts/bootstrap.sh` (which verifies the zip against `joern-sha512`), and the source
  runtimes and assembly tools the workflows install. `autoform doctor` exits `0` when
  every required tool matches its pin, `1` when one is missing or mismatched (with
  `--strict`, also when an optional runtime or `[machine]` extra is), `2` when the check
  itself could not run.
- Two generated modules are gitignored (`.gitignore`, `Autoform/Generated/*.lean`) and
  must be rendered from their tracked ASTs before `lake build`, with the two commands
  `ci.yml` runs:

  ```sh
  python3 cartographer/render_lean.py ast-V8Base.json Autoform/Generated/V8Base.lean V8Base
  python3 cartographer/render_lean.py ast-CommonsLang3.json Autoform/Generated/CommonsLang3.lean CommonsLang3
  ```

- The Python tooling and both extras the gates below need (`pyproject.toml`,
  `[project.optional-dependencies]`): `python -m pip install '.[test,machine]'`.

## 2. The local gate chain

Run in this order; each must reach the line shown.

| Gate | Green | Exit codes |
|---|---|---|
| `lake build` | clean, no errors | non-zero on failure |
| `python3 scripts/audit_all.py --strict` | `VERDICT: PASS (no trusted-code leak)`; keep `audit.json` | `1` on any failure |
| `lake env lean Demo.lean 2>&1 \| grep -E "TRUSTED-CODE LEAK\|VACUOUS"` (CONTRIBUTING.md) | both strings appear | `lean` exits non-zero by design (running.md, "Demo.lean") |
| `python3 scripts/check_render.py` | every module `OK`, nothing `UNVERIFIABLE` | `0` ok, `1` mismatch, `2` nothing checkable, `3` some UNVERIFIABLE |
| `python3 scripts/check_specs_fresh.py` | `check_specs_fresh: <N> spec module(s) match the corpus they were generated from` (a `; <k> untracked spec module(s) skipped` suffix is fine) | `0`, `1` stale, `2` nothing checkable, `3` a tracked spec module has no verifiable corpus |
| `python3 scripts/check_docs.py` | `check_docs: <N> documented figures all match their artifacts` | `0`, `1` stale, `2` artifacts missing |
| `python3 scripts/check_provenance.py` | `check_provenance: <a>/<t> in-repository artifacts fully attributed to Joern <pin>; <b> unattributed (baselined); <l> local-only (gitignored, not judged); 0 violation(s).` then `check_provenance: PASS` (or `PASS with a named gap` while the baseline is non-empty) | `0`, `1` violation, `2` nothing checked |

Notes on the chain:

- `lake build` with no target builds `Autoform` (`lakefile.toml`, `defaultTargets`),
  which includes `Autoform.SpecsGen.V8Base`. CI builds and audits `Autoform.CI`, which is
  `Autoform.lean` minus that import because its parts exceed the runner's memory
  (`Autoform/CI.lean`, whose header records the memory involved). A release candidate
  needs the full build on a machine that can hold it.
- `audit_all.py --strict` runs the axiom sweep, the source sweep and `leanchecker --fresh`
  (its module docstring) and fails on a missing `leanchecker` instead of reporting
  UNVERIFIED. The fresh replay is single-threaded; running.md's troubleshooting section
  carries a dated timing.
- `check_docs.py` binds figures to `ledger-Cachetools.json` and `ledger-CommonsLang3.json`,
  which are build products: regenerate them first as `ci.yml` does
  (`scripts/ledger.lean.tmpl` with `@MODULE@` substituted, then `lake env lean` on it).
- `check_provenance.py --strict` refuses the `provenance/unattributed.json` baseline and
  exits `1` while that file is non-empty, so it is not a release gate today. The summary
  line is the attribution figure to quote, never a number copied from a document.
- `assure.sh` builds evidence for one module; a successful scoped run does not establish
  release readiness (integrity.md, "Running them").

## 3. The test matrix

Default suite, no Lean or Joern needed: `python3 -m pytest tests/ -q` (CONTRIBUTING.md
gives its approximate duration). Add `-rs -rx` so every skip and strict xfail prints its
reason. The gated suites below each need their prerequisite present **and** must not
skip; a skip whose reason says `set AUTOFORM_TEST_JOERN=1` (or the gate's own variable)
is an unmet gate. `ci.yml` makes that check by grepping its own pytest log for exactly
`set AUTOFORM_TEST_JOERN=1`.

| Gate | Prerequisite (tests/README.md) | Which workflow runs it |
|---|---|---|
| `AUTOFORM_TEST_JOERN=1` | Joern at `$JOERN_HOME` (default `~/joern`), verified by `scripts/bootstrap.sh` | `ci.yml` (nine files, incl. `test_production_gaps.py`); `source.yml` (twelve files, with `AUTOFORM_REQUIRE_LEAN=1`) |
| `AUTOFORM_TEST_LEAN=1` | this checkout's `lake build` | local |
| `AUTOFORM_TEST_ORACLES=1` | `javac`, `node`, `go`, `cc`, `kotlinc` on PATH | local |
| `AUTOFORM_REQUIRE_LEAN=1` | Lean; clang with AArch64 target and `ld.lld` for the machine comparisons | `machine.yml` (`pytest tests -q`) |
| `AUTOFORM_TEST_WHEEL=<whl>` | a built wheel | `package.yml` `install` job, on ubuntu and macOS, Python 3.10/3.12/3.13 |
| `AUTOFORM_TEST_INSTALLED_E2E=1` | the candidate wheel installed, `autoform` on PATH | `source.yml`, after the gated suites |
| Rust: `AENEAS_HOME`, `AUTOFORM_RUST_LEAN_PROJECT`, `AUTOFORM_RUST_REQUIRED=1`, `AUTOFORM_RUST_GCD_CRATE` | pins in `rust-pins.json`; `scripts/rust_setup.sh`; the sha256-verified `gcd-2.3.0.crate` (`rust.yml`) | `rust.yml` -- **not** in `release_check.sh`'s required list; trigger it with `workflow_dispatch` on the candidate commit |

Copy the file lists from the workflows rather than from here (`ci.yml`, "Gated suites
against the real runtimes"; `source.yml`, "All source languages, real runtimes and
generated kernel proofs"). `tests/test_source_pipeline.py::test_source_to_native_conformance_proofs`
runs `autoform.sh`, so on a dirty checkout it fails through the integrity guard: the guard
working, not a flaky test.

Skips that are legitimate, by name: `tests/test_sandbox.py` on a host with no sandbox
mechanism, `tests/test_ledger_py.py`'s Django cross-check when the Django AST (a local
product) is absent, optional machine tools in `tests/test_machine_frontend.py` without
`AUTOFORM_REQUIRE_LEAN`, and the one strict xfail recording string-encoded integers in
`ast-V8Numbers.json` (tests/README.md, "House rules"). Anything else needs an explanation
before the release proceeds.

## 4. Build and check the candidate

```sh
python -m build --outdir dist/candidate            # wheel is built FROM the sdist
python -m twine check --strict dist/candidate/*
python scripts/check_distribution.py dist/candidate
AUTOFORM_TEST_WHEEL="$(find "$PWD/dist/candidate" -name '*.whl' -print -quit)" python -m pytest tests/test_package.py -q
python -m pip install --force-reinstall "$(find "$PWD/dist/candidate" -name '*.whl' -print -quit)[machine]"
AUTOFORM_TEST_INSTALLED_E2E=1 python -m pytest tests/test_installed_assurance.py -q
```

`check_distribution.py` opens the actual wheel and sdist and requires the file set,
runtime resources, CLI modules, dependency metadata and license notices to match this
checkout, the wheel's metadata version to equal `__version__` in
`src/autoform/__init__.py`, and the filenames to be
`autoform_lean-<version>-py3-none-any.whl` / `autoform_lean-<version>.tar.gz`; it prints
a JSON record whose `artifacts` field holds the sha256 of both files, which is the
distribution hash to retain. `tests/test_package.py`
also checks that `joern-sha512` pins every release asset of `joern-version` and is in the
runtime bundle. `SOURCE_DATE_EPOCH=$(git log -1 --format=%ct) python -m build` makes two
builds of one commit byte-identical (packaging.md, "Reproducible builds").

Third-party notices: `THIRD_PARTY.md` names the pinned cachetools revision whose LICENSE
`licenses/cachetools-MIT.txt` matches, and `ci.yml` re-compares it against a clone at
that pin on every run. It also names what the `machine`, `llm` and `bedrock` extras
install; re-read it against `pyproject.toml`'s `[project.optional-dependencies]` before
tagging.

## 5. The version cut

1. Set the same `<version>` in `pyproject.toml` (`version`), `src/autoform/__init__.py`
   (`__version__`) and `lakefile.toml` (`version`). `scripts/release_check.sh` compares
   those three with each other and with the `CHANGELOG.md` heading in step 2 (its "four
   version sources"); `check_distribution.py` compares the built wheel against
   `__version__`.
2. In `CHANGELOG.md`, rename the top heading `## [Unreleased]` to `## [<version>]`.
   `release_check.sh` reads the first `## [...]` heading and fails while it is
   `Unreleased` (CHANGELOG.md header). Open a new `## [Unreleased]` only **after** the tag
   exists.
3. Push, and wait for `ci.yml`, `package.yml`, `source.yml` and `machine.yml` to complete
   on that exact commit (`REQUIRED_WORKFLOWS` in `release_check.sh`).
4. `scripts/release_check.sh [--repo OWNER/REPO]`. It checks: clean tree; the four
   version sources agree; tag `v<version>` exists neither locally nor on `origin`; each
   required workflow's latest completed run on `HEAD` concluded `success` (`gh run list`);
   `https://pypi.org/pypi/autoform-lean/<version>/json` returns 404. Exit `1` prints
   `release_check: NOT READY`; exit `2` means a tool (`git`, `gh`, `curl`, `python3`) is
   missing or a lookup did not answer the question. On success it prints
   `release_check: READY. Nothing was tagged, released or uploaded.` and these commands,
   which it does not run:

   ```sh
   git tag -a v<version> -m "autoform <version>" <HEAD sha>
   git push origin v<version>
   gh release create v<version> --verify-tag --title "autoform <version>" \
       --notes "See the [<version>] section of CHANGELOG.md."
   ```

Publishing the GitHub release is the irreversible step: a version on PyPI can never be
replaced (`release_check.sh`, check 4). Run those three commands by hand, in that order.

## 6. What `package.yml` does on `release: published`

`package.yml` runs on pushes to `main`, pull requests, `workflow_dispatch` and published
releases; only a release runs the publishing path. Jobs:

- `build` (Python 3.11): `python -m build`, `twine check --strict`,
  `scripts/check_distribution.py dist`, and on a release asserts
  `github.event.release.tag_name == 'v' + pyproject version`; uploads `python-distributions`.
- `install`: `tests/test_package.py` with `AUTOFORM_TEST_WHEEL` on ubuntu and macOS,
  Python 3.10, 3.12 and 3.13.
- `installed-proofs`: installs `<wheel>[machine]` and the pinned Lean, runs
  `autoform init` and `autoform machine` on the bundled aarch64 example outside the
  checkout, then `lake build Autoform.Lang.PCode.Properties` and
  `lake env leanchecker --fresh Autoform.Lang.PCode.Properties` in that workspace.
- `source-proofs` (release only): `source.yml` with `distribution_artifact`, so the
  installed source CLI and the installed E2E test use this exact wheel.
- `repository-checks` and `machine-checks` (release only): `ci.yml` and `machine.yml`.
- `evidence` (release only; needs the five above): a CycloneDX SBOM of the installed
  wheel (`cyclonedx-bom==7.5.0`, in its own venv) uploaded to the release as
  `autoform-lean-v<version>.cdx.json`, and `actions/attest-build-provenance` over the
  wheel and sdist, signed with the workflow's OIDC identity.
- `publish` (release only; needs all six): `pypa/gh-action-pypi-publish` in environment
  `pypi` with `id-token: write` only. The trusted publisher is configured on PyPI for
  owner `mbhatt1`, repository `autoform`, workflow `package.yml`, environment `pypi`
  (packaging.md, "CI and publishing").

Verify a downloaded wheel with `gh attestation verify <file> --repo mbhatt1/autoform`.
A failing `repository-checks` or `machine-checks` blocks publication by design; do not
work around it.

## 7. After publishing

- From a machine without the checkout: `python -m pip install 'autoform-lean[machine]'`
  (packaging.md). Then `autoform --version` must print
  `autoform <version> (lean-toolchain <lean-toolchain pin>, joern <joern-version pin>)`,
  and `autoform doctor` must exit `0`.
- Run a pinned Git URL through the installed CLI in a **fresh** workspace (an existing
  workspace must match the package's bundled resources; packaging.md, SUPPORT.md) and
  retain the evidence directory, including a negative run whose guarantee was withheld.
  `AUTOFORM_TEST_INSTALLED_E2E=1 python -m pytest tests/test_installed_assurance.py -q`
  is that check in test form.
- Retain: the `check_distribution.py` JSON (distribution hashes), `audit.json`,
  `autoform --version`, the full test output, the release's SBOM and the attestation
  verification output.
- Update the places that currently say the package is not on PyPI (`README.md`,
  `docs/adoption.md`) and `CHANGELOG.md`'s "changes since" sentence; open the new
  `## [Unreleased]` heading.

Composite Action consumers are unaffected by a PyPI release: `action.yml` installs
autoform from `$GITHUB_ACTION_PATH` and reads `lean-toolchain`, `joern-version` and
`joern-sha512` from the same checkout, and consumers are told to pin a reviewed full
commit SHA (github-action.md). To move them, point them at the release commit.

## 8. Never

- Never re-record a hash you have not reviewed: `check_render.py --record` and
  `check_specs_fresh.py --record` turn evidence into a rubber stamp (integrity.md,
  `artifact-manifest.json`; `check_specs_fresh.py` docstring). A STALE verdict means
  regenerate, then record.
- Never edit a `provenance/*.prov.json` record to match a new exporter digest; regenerate
  with the command in the record (`scripts/provenance.py show ast-<M>.json`), re-render,
  re-record (running.md troubleshooting).
- Never hand-edit `Autoform/Generated/*.lean` (CONTRIBUTING.md). Land an AST, its render,
  `check_render.py --record <Module>`, regenerated specs and the manifest in one commit.
- Never close a broken theorem after a re-land with a re-recorded hash: restate the
  domain or delete the claim (section 10).
- Never put a number in this document that no artifact or command reproduces.

## 9. Re-pinning

**Joern.** `joern-version` holds the version; `joern-sha512` starts with the line
`# joern <version>` followed by one line per release asset,
`<sha512>  target/joern-cli-<os>-<arch>.zip` for `linux`/`macos` x `x86_64`/`arm64`,
copied from the release's own `<asset>.sha512` manifests (`joern-sha512` header). Change
both in one commit: `tests/test_package.py` asserts the header matches the pin and all
four assets are present, and `scripts/bootstrap.sh`, `ci.yml`, `pr.yml`, `source.yml` and
`action.yml` all die with `joern-sha512 does not pin joern <version>` otherwise. The Joern
cache keys hash both files (`ci.yml`, `pr.yml`, `source.yml`). `check_provenance.py`'s PIN
check then fails every tracked AST whose record names the old Joern, so a Joern re-pin is
a re-export of every attributed corpus (`scripts/reland_corpus.sh`, section 10), not a
two-line change. `scripts/provenance.py joern-version --check` compares the installed
Joern with the pin.

**Lean.** `lean-toolchain` pins the compiler; `lakefile.toml` pins `aesop` to the tag
matching it (comment there) and `lake-manifest.json` pins the resolved revisions of
aesop, specimen, batteries, proofwidgets and plausible. Move all three together and
rebuild from scratch; the `.lake` cache keys hash `lean-toolchain` and
`lake-manifest.json`. `leanchecker` ships with the toolchain (audit_all.py docstring);
`autoform doctor` checks `lean` against the pin. `rust-pins.json`'s `lean_toolchain` is
Aeneas's own and is not this pin (docs/rust.md, "Setup").

**Rust path.** `rust-pins.json` (Aeneas release and asset sha256s, Charon version and
commit, `rust_toolchain`, mathlib revision) is read by `scripts/rust_aeneas.py` and
`autoform doctor`; `rust.yml`'s `env` block must hold the same values, and its
`GCD_CRATE_SHA256` must equal `evidence-RustGcd.json`'s `crate.crate_sha256`
(`tests/test_rust_unit.py::test_pins_file_and_workflow_agree`). `docs/rust.md` "Setup"
quotes the pins in prose and must move with them.

## 10. Re-landing a corpus

A tracked `ast-<Module>.json` is evidence about the exporter that produced it. When a
fresh export should replace it (integrity.md says how to decide), AST, render, manifest
pins, provenance record, conformance evidence, generated specs and ledger move together,
or every gate stays green while agreeing on a mixture of old and new.
`scripts/reland_corpus.sh <source-dir> <Module>` performs that cascade from a clean tree,
stops at the first failure, retires the module's `provenance/unattributed.json` entry, and
ends by listing the gates still to run by hand. It does not commit. Expect theorems to
break: the part files under `Autoform/Specs/CachetoolsSpec/` mark the theorems a re-land
changed with `RELAND:` comments; the honest fix is a restated domain or a deleted claim,
never a re-recorded hash. The source must exist at the recorded revision. `V8Base` cannot
be re-landed: its `provenance/unattributed.json` entry records that the V8 tree and
revision were never identified.

## 11. Troubleshooting

- **`check_provenance.py` fails locally on `ast-Pipeline<Lang>.json` but CI is green.**
  `ast-Pipeline*.json` is gitignored (a run product of `tests/test_source_pipeline.py`),
  but the `provenance/ast-Pipeline*.prov.json` it leaves is an untracked record, and a
  local artifact that carries a record is checked in full (`check_provenance.py`
  docstring, COVERAGE). After an exporter change it fails its EXPORTER check. Re-run the
  test to regenerate both, or delete both local files; never edit the record.
- **`autoform: refusing to run: a mutation gate is live or was interrupted`** (exit 2).
  `scripts/mutate.py <path-to-M>.lean --recover` restores each file from its
  `.mutate-backup`, then `lake build <module>` before trusting any `.olean` built while
  the mutant was live (integrity.md, "Getting out of a stranded mutation").
  `AUTOFORM_ALLOW_DIRTY=1` lifts only the dirty-tracked-file check, never this one.
- **A mutation report ends `RESTORE_TIMEOUT`.** The source is restored and every verdict
  stands, but the tree's build state is unverified until `lake build <spec-module>`
  succeeds; the gate does not exit 0 on it (integrity.md; `scripts/mutate.py` docstring).
- **`lake build` is killed on the V8Base parts.** That is the module CI excludes; see
  `Autoform/CI.lean` for the memory it needs, build on a larger machine, or build
  `Autoform.CI` first and the V8Base parts one at a time afterwards.
- **`check_docs.py` exits 2, "artifacts missing".** Regenerate the ledgers (section 2).
- **`release_check.sh` exits 2.** It could not answer (`gh` unauthenticated, no route to
  `origin` or PyPI). Fix the tool; a network error is not "not on PyPI".
