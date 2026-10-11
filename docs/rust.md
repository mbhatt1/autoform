# Rust (experimental, via Charon + Aeneas)

Autoform has no Rust parser. This path ingests the Lean that
[Aeneas](https://github.com/AeneasVerif/aeneas) emits from [Charon](https://github.com/AeneasVerif/charon)'s
LLBC, and attaches the usual differential oracle: the REAL Rust function runs natively
(a generated cargo harness binary) and the Aeneas-emitted Lean function is `#eval`ed on the
same integer inputs. Any disagreement is a finding. `scripts/rust_aeneas.py` writes a
`conformance.json` (agree/total/divergences/divergence_detail) with a `provenance` block
(Charon and Aeneas versions, harness rustc, charon's rust toolchain, Lean toolchain).
Status: prototype on one 6-function crate (`tests/fixtures/rust_proto`), not wired into
`differential.py`, `autoform.sh`, the ledger or the kernel-checked statements.

## Feasibility (measured 2026-10-10, macOS arm64, no sudo)

* Aeneas release `nightly-2026.10.10-d119a47` ships `aeneas-macos-aarch64.tar.gz`, which
  contains `aeneas`, `charon` (0.1.281, commit 798016509139...), `charon-driver`, the Lean
  backend (`backends/lean`) and `rust-toolchain`. No opam/nix needed. Charon's own release
  page only has linux-x86_64, so use the one bundled with Aeneas (it is the pinned pair).
* Charon needs rustc `nightly-2026-09-17` with `rustc-dev`: `rustup toolchain install` (user level).
* Aeneas' Lean library pins Lean `v4.31.0` and mathlib `v4.31.0`; Autoform pins
  `v4.30.0-rc1`. This IS a mismatch, so the Aeneas side lives in a separate scratch Lake
  project with its own toolchain; Autoform's `lean-toolchain` and lakefile are not changed
  and nothing is imported into Autoform. The oracle compares stdout of `lake env lean`.
* Cost: mathlib cache download (~8.5k files) and building the Aeneas library (1721 jobs);
  after that, a Proto module builds in seconds and `#eval` of loops (`gcd`) works.

### Setup used (everything under `/tmp/af-agents/rust-work`, plus user-level toolchains)

    curl -L .../nightly-2026.10.10-d119a47/aeneas-macos-aarch64.tar.gz   # -> rust-work/aeneas-dl/x
    rustup toolchain install nightly-2026-09-17 --profile minimal -c rustc-dev -c llvm-tools -c rust-src
    elan toolchain install leanprover/lean4:v4.31.0
    cp -R x/backends/lean leanproj; (cd leanproj; lake update; lake exe cache get; lake build Aeneas)
    export AENEAS_HOME=.../x AUTOFORM_RUST_LEAN_PROJECT=.../leanproj
    python scripts/rust_aeneas.py --crate tests/fixtures/rust_proto --lean-project $AUTOFORM_RUST_LEAN_PROJECT

(`lake build -j` is not accepted by this Lake; the heavy build was run under the shared lock.)

## Prototype result

`gcd`, `clamp`, `add_wrapping`, `add_checked`, `sub_sat`, `div_floor_u8`; boundary values plus
seeded random (seed 20261010), 709 cases.

* debug profile: 709/709 agree, 0 divergences, 0 inconclusive.
* release profile: 659/709 agree, 50 divergences, all in `add_checked`
  (Rust wraps, Aeneas `fail`): the expected, deliberate test of the overflow assumption.

These figures come from a local run's `conformance.json` (a gitignored run product); they are
NOT bound in `check_docs.py`, which has no mechanism for an artifact that CI does not produce.

## Semantics mapping (assumptions, each recorded in conformance.json)

* Overflow: Aeneas models `+ - *` on fixed-width ints as checked (`fail integerOverflow`).
  Rust debug builds panic on overflow, release builds wrap. The oracle assumes the DEBUG
  profile; `wrapping_*`/`saturating_*` are modelled by Aeneas' `core.num` functions and agree.
  `tests/test_rust_aeneas.py::test_release_wrap_is_an_expected_divergence` pins the difference.
* Panic vs `fail`: any Rust panic (overflow, division by zero, array bound, explicit) is mapped
  to any Aeneas `fail`; the error kind is not compared. A panic message is silenced, not read.
* Aeneas `div` (the interaction-tree divergence marker) is INCONCLUSIVE, never agreement
  (none occurred). An effect other than `fail` would be reported as `fail` by the current
  stringifier (Aeneas' `Result` has only the `fail` effect today; unchecked).
* Inputs/outputs: integers only (`u8..u64`, `i8..i64`, `usize/isize` as 64-bit).

## Not modelled / not covered

Traits, generics, closures, references/borrowing beyond what Aeneas translates (and Aeneas
rejects some programs outright), `unsafe`, interior mutability, floats, strings/collections as
oracle values, concurrency, multi-crate dependencies, `const fn` evaluation, process-level
effects. Functions Charon/Aeneas leave opaque are not compared. The comparison is evidence on
sampled inputs, not a proof; no theorem about the Rust function is produced or checked in
Autoform's kernel, and there are no named holes yet for the Rust path.

## Test

`AENEAS_HOME=... AUTOFORM_RUST_LEAN_PROJECT=... pytest tests/test_rust_aeneas.py`. Without
them it skips with the named reason (missing tools, or the unset scratch project).

## Smallest next steps

1. Typed `Bool`/tuple/`Option` values in the harness and comparison.
2. Feed `conformance.json` into the ledger and add a CI job that restores the scratch project cache.
3. Surface Aeneas `fail` kinds and compare them with Rust panic classes (overflow vs div-by-zero).
