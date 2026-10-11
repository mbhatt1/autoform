# Changelog

Entries are derived from `git log` (first commit 2026-08-19) and cite the commit that
introduced each item, so every line can be checked with `git show <hash>`. Subjects are
paraphrased closely; no figure appears here that is not in the cited commit's subject.
Figures about what the tool proves live in the bound docs (`scripts/check_docs.py`),
not in this file. The package is alpha (`Development Status :: 3 - Alpha`).

The version in `pyproject.toml` and `src/autoform/__init__.py` must equal the section
heading of the release being cut, and the release tag is `v<version>`
(see [docs/packaging.md](docs/packaging.md)).

## [0.0.1] - not yet published

Changes since `v0.0.0` (`8aabb2e`):

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
  least-privilege `permissions`. Defined in `.github/workflows/package.yml`; **not yet
  exercised**, because Actions cannot be run before a release exists.
- `scripts/release_check.sh` and the composite GitHub Action at `action.yml`
  ([docs/github-action.md](docs/github-action.md)).
- Adoption brief: [docs/adoption.md](docs/adoption.md).
