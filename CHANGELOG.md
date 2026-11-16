# Changelog

Entries are derived from `git log` (first commit 2026-08-19) and cite the commit that
introduced each item, so every line can be checked with `git show <hash>`. Subjects are
paraphrased closely; no figure appears here that is not in the cited commit's subject.
Figures about what the tool proves live in the bound docs (`scripts/check_docs.py`),
not in this file. The package is alpha (`Development Status :: 3 - Alpha`).

The version in `pyproject.toml`, `src/autoform/__init__.py` and `lakefile.toml` must equal
the section heading of the release being cut, and the release tag is `v<version>`
(see [docs/packaging.md](docs/packaging.md)). Work since the last tag accumulates under
`## [Unreleased]`; cutting a release renames that heading to the version, which is what
`scripts/release_check.sh` requires of the first heading.

## [Unreleased]

Changes since `v0.0.1` (`fde1166`), summarised coarsely; `git log v0.0.1..HEAD` is the
record. Figures (agreement counts, hole counts, mutation scores) live in the bound docs
and the evidence files, not here.

### Pipeline and semantics
- Kotlin: `when`, `?:`, `?.`, string templates, enum entries, implicit-receiver calls, and
  `is T` where Core can decide it (`93d5835`, `f2ac7c7`, `d4d9810`, `f380197`); Go `if`
  no longer holes beside its `ifte` (`e4ae663`); JS/TS template literals (`ada0499`).
- JVM boxed `==`/`!=`: Kotlin null-safe value equality, Java box identity a named hole,
  Java unboxing raises `NullPointerException` (`9515cd0`).
- Java and Kotlin array `.length` is the `op:sizeOf:array-length` hole rather than a
  folded byte count; the fold had silently mistranslated every such read (`ea9a058`).
- Python `str` methods, `in`, `list()` and `range` headers; Node arrays, objects and module
  bindings (`892149f`); a 7-field `SyntaxError` details tuple is a hole (`b85de7b`).

### Oracles and `pr` mode
- JVM oracle: Java instance methods on a built receiver, enums, boxes, null Strings and
  the static state a call reads, read-only collection parameters, static `void` and
  `CharSequence` results (`6b46c9c`, `42cd70c`, `9c32a51`, `822af57`); Kotlin compiled with
  the same-repo files it references and the project classpath (`f78bfaa`, `d7df4d4`).
- Node oracle: instance methods on a driver-built receiver, string inputs, ancestor
  `node_modules`, static methods (`78d026c`, `13238a1`). Python oracle runs under the
  project's own interpreter or lone virtualenv (`d6192f1`, `cd26534`). C++ through the
  native oracle (`6de0540`); Rust regressions across commits (`a4a805f`, `d278e47`).
- `pr`: cross-revision behaviour for Go, JS/TS, C, C++, Java/Kotlin and Rust; `--fail-on
  behaviour-changed` / `no-evidence` with exit `3` for a gate that compared nothing;
  exit `2` when a changed source file got no AST; runs under any CI and any Git remote
  (`0f652e4`, `5ac6970`, `b621762`, `4102bf0`, `ade2477`, `89f57b0`).
- Agreements replayed from the verdict cache count as evidence only when the key binds
  model, inputs and runtime source (`8c4f767`).

### Corpora and evidence
- First oracle-compared open-source corpora for Go, JavaScript, TypeScript and Kotlin
  (`AlgosGo`, `BitJS`, `AlgosTS`, `AlgosKt`), with the mutation gate measured on each
  (`edf9c28`, `a54480d`, `8a90a93`, `e475498`, `958a8da`, `4c9b4c9`, `729d3db`).
- Click, Jinja2, Requests, Cachetools, LinuxLcm and CommonsLang3 re-landed on the current
  exporter; the example corpora (LangC/Go/JS/Java/Kt/TS) re-exported with provenance
  (`71f41a9`, `90fc3d4`, `09f8720`, `34bd308`, `60f3857`, `a279268`, `9993e99`, `d89adc6`,
  `75aa5fe`, `1dbaaf1`).
- `mutate.py --targeted-parts` builds only the mutated subject's spec part per mutant and
  reports its narrower `build_scope` (`9ebb7f1`).

### Security, robustness, hosts
- Egress allow-list for model backends, private caches, URL-credential scrubbing and a
  strict sandbox mode (`e8f2b17`); per-file size cap, Joern heap knob, honest timeout
  records (`5293f6b`); `doctor` names the blockers of minimal Linux hosts and a Joern whose
  launcher cannot start (`ee54f3c`, `dc887ce`).
- Gradle/Maven layouts detected, build outputs and test sources excluded; Java parsed
  under Lombok, and an empty AST is a failed export (`34467c6`, `9d672ef`).
- `scripts/bootstrap.sh` takes Joern from a mirror or a local zip, verified against the
  committed `joern-sha512` (`7f8164c`).

### Action, packaging and release plumbing
- The Action exposes `fail-on`, `python`, `pytest-addopts`, `java-classpath`,
  `java-processorpath` and an `exit-code` output (`28466cb`).
- Packaging and CI (2026-11-13): `joern-sha512` ships in the runtime bundle and sdist, so the
  bundled `bootstrap.sh` can install Joern from a workspace; the CI workflows and the
  Action verify the Joern zip against the committed pin instead of the release's own
  `.sha512`; the Action's workspace cache key is the digest of the whole bundle selection;
  the sdist carries `tests/fixtures` and `examples/ci`; `lakefile.toml`'s version follows
  the package version and `release_check.sh` checks it; `package.yml` installs on 3.13.

## [0.0.1] - 2026-10-11

Tagged `v0.0.1` at `fde1166`. Changes since `v0.0.0` (`8aabb2e`):

### Documentation
- The GitHub Action's first real run on a pull request: PR #14 changes `unit_price` to return 0
  for a zero count, and the run flags it as a behaviour change (`630c3f5`).

## [0.0.0] - 2026-10-11

Tagged `v0.0.0` at `8aabb2e`. This section describes the tree at `ddcebff` (2026-10-10), the
first release candidate, plus the commits up to the tag.

### Pipeline and semantics
- First commit and the first object, refinement and oracle tiers (`4e56c11`, `1c30a7e`).
- Fuel-independence obligations closed (72 in `9d3e6a3`); reachability-free fuel
  transport (`1c1cc01`).
- Per-corpus Lean namespaces so V8, Linux and cachetools theorems build together (`5fd17ae`).
- C: provenance-based address model with bounds-checked interior-pointer access (`4c31d5b`);
  a C front-end recovery of silently dropped Linux functions (`54a5dc0`).
- Python: C3 method resolution order and `super()` (`041f113`), boxed lists and
  dicts (`8d3a970`), external base-class contracts (`235a332`).
- Go and Kotlin integer arithmetic at their own widths (`1c8142d`).
- Java corpus through the full chain: Apache commons-lang3 3.17.0 (`b43a540`, `92b6feb`).
- Python 3.12 inlined-comprehension scopes in the exporter (`de12bbd`).

### Evidence and honesty gates
- Trust audit, `check_render`, `check_docs` and provenance pinning of the Joern front
  end (`8e52811`); CI enforcement of render and docs checks.
- A conformance oracle with a dual-oracle undefined-behaviour detector for C (`174c5ad`).
- Ledger closure by contract and an external-callee ranking (`d41b824`).
- Doctor command that names what to install, and a Joern-gated CI job (`a6a4498`).
- Corpora re-landed under the current exporter: cachetools (`e852b34`), Click (`d8eff28`),
  LinuxLcm from kernel v7.2 (`d2fcb3d`); Django ledger from the AST (`85bbca3`).
- Defect-hunt records for cachetools and Linux lcm (`f123b68` and the two commits
  that track their result rows).

### Tooling
- Prover agent whose proofs the Lean kernel re-checks (`2d2bc20`).
- `autoformalize`: natural-language describe, prove and report stages (`acd9432`),
  shipped in the wheel (`379e478`); Anthropic API backend with per-run budget
  (`9116230`) and Amazon Bedrock backend (`5f582ac`).
- `autoform pr`: per-function evidence levels for the functions a change touched,
  with SARIF and Markdown output (`7eaa0ad`).
- One confinement layer (seatbelt on macOS, bubblewrap or unshare on Linux) for the
  oracle, the native worker and the harness replay (`f3cdec9`); Linux sandbox enabled
  in CI (`2853126`).

### Packaging and release
- Runnable from a clean clone (`4142a5d`); wheel built from the sdist and checked by
  `scripts/check_distribution.py`; installed-wheel tests on macOS and Linux.
- Supply-chain evidence in the publish path: CycloneDX SBOM and build-provenance
  attestation as release assets, third-party actions pinned to commit SHAs, per-job
  least-privilege `permissions`. Defined in `.github/workflows/package.yml`; whether it
  has run is not verified from this checkout (it runs on a published release, so `gh run
  list --workflow package.yml` on the repository is the record).
- `scripts/release_check.sh` and the composite GitHub Action at `action.yml`
  ([docs/github-action.md](docs/github-action.md)).
- Adoption brief: [docs/adoption.md](docs/adoption.md).
