# Rust (via rustdoc, Charon and Aeneas)

Autoform has no Rust parser and Joern has no Rust frontend. The Rust path takes every fact
about a crate from the tool that owns it, and holds each one to the same discipline as the
other languages: every public function accounted for, every hole named, a differential
oracle against the real compiled code, and kernel-checked statements.

| step | tool | what Autoform takes from it |
|---|---|---|
| public API | `cargo rustdoc --output-format json` | every public function: free functions, inherent methods, trait-impl methods, provided trait methods |
| model | [Charon](https://github.com/AeneasVerif/charon) (LLBC) then [Aeneas](https://github.com/AeneasVerif/aeneas) (Lean) | one Lean definition per Rust function, with Aeneas' own error for each it could not translate |
| holes | Aeneas' log, Lean's errors, `#print axioms` | a function is translated only if its model is CLOSED: no `sorry`, no non-standard axiom |
| native truth | a generated cargo harness, debug profile, sandboxed | the real function's result or panic on each input |
| model truth | `#eval` of the Aeneas function | `ok v`, `fail <kind>` or `div` |
| checked evidence | the Lean kernel | for each agreeing case, `f args = result` proved by `rfl` |

Run it with `autoform source <crate-dir> <Module>` (or `assure`): a directory holding a
Cargo package with a library target takes this path automatically, `--lang rust` forces it
and `--lang joern` refuses it. The driver is `scripts/rust_aeneas.py`; the run directory
`<workspace>/artifacts/pipeline/<Module>/` receives:

| file | contents |
|---|---|
| `ledger-<Module>.json` | the ledger, in the shape `check_docs.py` and `autoform pr` read (`functions`, `holes`, `holeFree`, `verifiableCore`, `holesByLabel`, ...) plus `functionsDetail`: per public function its Lean name, status, hole labels, oracle state and theorem counts |
| `conformance.json` | agree / total / divergences / inconclusive, every divergence, the inconclusive functions with their reason, the kernel-checked counts, the assumptions, the stages and the provenance |
| `rust-provenance.json` | the exact tools: Aeneas release, Charon version and commit, rustc `-vV` of the pinned nightly, cargo, Lean and Lake versions of the scratch project, its mathlib revision, the crate's source-tree digest, the sandbox records, and `matches_pins` against `rust-pins.json` |
| `rust-cases-<Module>.lean`, `rust-theorems.json` | the case theorems and, per theorem, proved or the Lean error and its class |
| `aeneas-<Module>.lean` (+ `.built.lean`), `aeneas.log`, `charon.log` | what Aeneas emitted, what Lean accepted after rejected declarations were removed, and the tools' logs |
| `summary.md`; with `assure` also `run.json`, `guarantee.json` | the human summary; the gaps, and claims that never include whole-program correctness |

## Real crate: gcd 2.3.0

[`gcd`](https://crates.io/crates/gcd) 2.3.0 from crates.io: const binary and Euclid GCD for
`u8`..`u128`/`usize`, their `NonZero` variants and the `Gcd` trait, written as
macro-generated code. The `.crate` archive is pinned by sha256
(`1d758ba1b47b00caf47f24925c0074ecb20d6dfcffe7f6d53395c0465674841a`, also in
`~/.cache/autoform/corpora/gcd-2.3.0.crate.sha256`). The figures below are bound by
`check_docs.py` to the tracked `evidence-RustGcd.json`, which the Rust CI job re-derives from
the downloaded, digest-verified crate and compares field by field
(`tests/test_rust_aeneas.py::test_real_crate_reproduces_the_tracked_evidence`).

| | |
|---|---|
| public functions (rustdoc) | 60 |
| translated (closed Aeneas model) | 12 |
| hole occurrences | 48 under 7 labels |
| compared by the oracle | 12 |
| cases agree | 1178/1178 |
| divergences | 0 |
| inconclusive cases | 0 |
| case theorems proved by the kernel | 121/144 |

The three required methods of the `Gcd` trait have no body; they are listed as
declarations in the ledger, not counted as functions. Holes by label:

* `lean:depends-on-rejected:core::num::nonzero::ZeroablePrimitive: Field markerCopyInst has
  already been declared` -- every `NonZero` function and method. Aeneas emits a model of
  the std trait `ZeroablePrimitive` that Lean rejects (a duplicate field); the Rust path
  removes that declaration and, transitively, everything that needs it, and names the root
  cause on each. Nothing is replaced.
* `aeneas:external-axiom:core::num::{uN}::trailing_zeros`, one label per integer width --
  the binary GCD (`binary_*`, and the `gcd` and `gcd_binary` trait methods that call it).
  Aeneas' Lean library has no model of `trailing_zeros`, so it is an axiom, and a model that
  rests on an axiom is a hole, not a translation.

What is translated is the Euclid family: `euclid_*` and the `gcd_euclid` trait methods,
loops included. All of them were compared and agree on every case. The unproved case
theorems are all `usize` ones: `usize` is `BitVec System.Platform.numBits` in Aeneas, and
the kernel cannot evaluate `numBits` (it is `opaque`). A rerun on any 64-bit host with the
same pins writes the same evidence file.

Why this crate: the published integer crates tried first do not reach the oracle with this
Aeneas release. `num-integer` 0.1.46 stops Aeneas itself (an internal error while
translating `num_traits::PrimInt`'s method signatures), which the path records as one
`aeneas:crash:` label on every function. `bit_field` 0.10.3 translates, but every method
reads `core::mem::size_of`, which Aeneas only axiomatizes, so every function is an
`aeneas:external-axiom:core::mem::size_of` hole. Both are correct outcomes of the path, and
neither has anything to compare. (Measured 2026-10-10; not re-derived by CI.)

## The fixture crate

`tests/fixtures/rust_proto` (one file) exercises every branch: integer arithmetic with
overflow, a loop, recursion, saturating and wrapping std operations, `bool`, a tuple, a
fixed-size array, shared references, a trait implemented on `u16`, a provided trait method,
a struct with an inherent `impl`, `&mut`, a generic function, and four things Aeneas does
not model (a float, `&str`, a raw pointer, `count_ones`). `tests/test_rust_aeneas.py` pins
its figures -- the public functions, the four holes named exactly as Aeneas names them, the
compared and the inconclusive functions, and that the only unproved case theorems are the
recursive function's and the loop cases beyond `--fuel` -- and that its release-profile run
diverges on exactly the two functions that overflow (`add_checked`, `fact`).
`tests/test_rust_unit.py` tests the parsers, the ledger, the hole labelling and the
encoders without any toolchain, on tool output recorded from this crate
(`tests/fixtures/rust_proto/recorded/`).

## The oracle

Values the harness encodes exactly on both sides: `u8`..`u128`, `i8`..`i128`,
`usize`/`isize` (64-bit hosts only), `bool`, tuples and fixed-size arrays (literal length
1..16) of those, and shared references to them as arguments (Aeneas models `&T` as the value).
The Rust side prints `{:?}`; the Lean printer is generated from the same Rust type to print
the same text. Anything else makes the function INCONCLUSIVE with the reason: a struct,
enum or alias type, a slice, `&mut` (Aeneas returns the updated value; the harness does not
compare it), a generic parameter (no monomorphic instance is chosen), a provided trait method
(generic over `Self`), an `unsafe fn` (not called on generated inputs), floats, `str`/`char`.

Inputs: the product of per-type boundary values (sampled to `--cases`, default 60) plus
`--random` (default 40) seeded random inputs per function (`--seed`, default 20261010).
The harness and the crate's build run under the sandbox (`scripts/sandbox.py`: no network,
writes confined), after a `cargo fetch` that runs no crate code. A case that hangs natively is
cut after 10 s and the harness restarts at the next case; a hanging `#eval` is isolated to its
function. Both are inconclusive, never agreement.

Recorded assumptions (in `conformance.json`):

* DEBUG profile: overflow checks and debug assertions on, which is what Aeneas models
  (`fail integerOverflow`). `--profile release` wraps and is expected to diverge; the
  fixture test pins that it diverges exactly on the overflowing functions.
* Any Rust panic corresponds to any Aeneas `fail`. The kind Aeneas reports
  (`integerOverflow`, `divisionByZero`, `panic`, ...) is written into the case theorem, but
  it is not compared with the panic, which the harness does not classify.
* Aeneas `div` (its non-termination marker) is inconclusive.
* `usize`/`isize` are 64-bit; on another host they are inconclusive.

## Kernel-checked case theorems

For every compared function, up to `--theorems-per-function` (default 12) agreeing cases
become theorems in the scratch project, stating that the Aeneas model returns on that input
exactly what the native function returned (`ok v`), or the `fail <kind>` the model agreed
with a native panic:

    theorem case_17 : gcd.euclid_u64 ((12)#u64) ((18)#u64) = (Aeneas.Std.Result.ok ((6)#u64) : ...) := by
      rust_case

`rust_case` unfolds the crate's non-recursive definitions, rewrites Aeneas' `bind` and
`loop` with two equations proved in `AutoformRust.Eval` (`scripts/rust_eval.lean.tmpl`;
no axiom: `bind` is one case split because Aeneas' only effect is `fail`, and
`loop body x = loopK body n x` holds for every `n` because `loopK` falls back to `loop`),
unfolds the std operations the model calls and Aeneas' `irreducible_def` integer bounds by
their own `_def` theorems, and closes the goal with `rfl`. No `native_decide`, no `sorry`;
each theorem's `#print axioms` is read back and anything beyond `propext`, `Classical.choice`
and `Quot.sound` does not count. Cases the kernel cannot evaluate are reported, never
assumed, in classes: recursion (Aeneas' `partial_fixpoint`), a loop longer than `--fuel`
(default 4096 iterations), `usize`/`isize`.

These theorems are about the MODEL on recorded inputs. Together with the oracle they say
the model and the compiled code agree on those inputs, kernel-checked on the model side.
They do not quantify over all inputs.

## Ledger semantics

* A function is translated when Aeneas emitted a definition for it, Lean accepted it, and
  `#print axioms` shows no `sorryAx` and no axiom outside the standard three. Hole-free and
  call-closed coincide (`verifiableCore` = `holeFree`), because the axiom check is transitive.
* Hole labels quote the tool: `aeneas:error:<Aeneas' message>`,
  `aeneas:external-axiom:<Rust path of the std function>`,
  `aeneas:calls-untranslated:<Rust path>`, `lean:rejected:<declaration>: <Lean's message>`,
  `lean:depends-on-rejected:<root cause>`, `charon:error:<message>`, `aeneas:no-definition`,
  and for a whole-crate failure `charon:failed:` or `aeneas:crash:`. `holeFunctionsByCategory`
  groups them coarsely (float, string, raw-pointer/unsafe, external-std, lean-rejected-model,
  ...); the category is our reading, the label is the tool's words.
* `dynamicHoleRisk` is 0: an Aeneas `fail` is defined behaviour of the model, not a hole.
  `nodes` is `null`: there is no neutral AST on this path.

## Setup

Pinned in `rust-pins.json` and checked by `autoform doctor`, which lists the Rust runtime
(`cargo`, `rust-toolchain`, `charon`, `aeneas`, `aeneas-lean-project`) as optional and says
what each missing piece disables:

* Aeneas release `nightly-2026.10.10-d119a47`. Its assets ship `aeneas`, `charon` (0.1.281,
  commit `798016509139eb51f0d764645f76d068d34ba5f6`), `charon-driver`, the Lean backend and
  `rust-toolchain`, for linux-x86_64, linux-aarch64 and macos-aarch64; each asset's sha256 is
  in `rust-pins.json`. Charon's own releases are linux-only, so the pair bundled with Aeneas
  is the pin. No opam or nix.
* Rust `nightly-2026-09-17` with `rustc-dev`, what Charon is built against; the harness is
  built with the same toolchain.
* The scratch Lake project: Aeneas' Lean library pins Lean v4.31.0 and its own mathlib, which
  differ from Autoform's (`lean-toolchain`), so it lives in a separate project and nothing is
  imported into Autoform.

```
curl -sSfL -o aeneas.tgz https://github.com/AeneasVerif/aeneas/releases/download/nightly-2026.10.10-d119a47/aeneas-macos-aarch64.tar.gz
shasum -a 256 aeneas.tgz            # compare with rust-pins.json
mkdir -p ~/.aeneas && tar xzf aeneas.tgz -C ~/.aeneas && export AENEAS_HOME=~/.aeneas
rustup toolchain install nightly-2026-09-17 --profile minimal -c rustc-dev -c llvm-tools -c rust-src
bash scripts/rust_setup.sh "$AENEAS_HOME" ~/.cache/autoform/aeneas-lean   # mathlib cache + Aeneas library
export AUTOFORM_RUST_LEAN_PROJECT=~/.cache/autoform/aeneas-lean
autoform source path/to/crate MyCrate
```

`--rust-lean-project` overrides the environment variable. A missing piece is a named error
(`tool-missing`, `rust-toolchain-missing`, `lean-project-missing`, `lean-project-unbuilt`,
`not-a-library`, `not-a-package`, `sandbox-unavailable`, ...) written to `rust-error.json`,
exit 2.

## CI

`.github/workflows/rust.yml` downloads the linux-x86_64 Aeneas asset and the matching
prebuilt Aeneas Lean library by URL and sha256, installs the pinned nightly, builds the
scratch project (mathlib cache via `lake exe cache get`, cached between runs), downloads
gcd 2.3.0 by URL and sha256, and runs `tests/test_rust_unit.py` and `tests/test_rust_aeneas.py`
with `AUTOFORM_RUST_REQUIRED=1`: a missing prerequisite fails the job, and a JUnit check
asserts nothing was skipped. Every action is pinned by commit SHA; the job has
`contents: read` only. The run's evidence is uploaded as an artifact.

## Not covered

* Anything the oracle cannot encode (above), and every hole: those functions get no
  comparison and no theorem.
* Theorems for recursive functions, loops beyond `--fuel`, and `usize`/`isize` arithmetic.
* Panic kinds (overflow vs division by zero vs explicit `panic!`) are not compared.
* Floats, strings and collections as values; traits and generics beyond what Aeneas
  translates monomorphically; `unsafe`; interior mutability; concurrency; process effects.
* Multi-crate models: dependencies are opaque to Charon by default, so a crate whose
  functions call into a dependency gets external-axiom or no-definition holes there.
* Workspaces: point the CLI at a member package, not the workspace root.
* `autoform pr` and `regress` do not take the Rust path; they run the Joern pipeline.
* Proofs about all inputs. The ledger, the oracle and the case theorems are evidence on the
  sampled inputs; there is no `∀ x` theorem about a Rust function here.
