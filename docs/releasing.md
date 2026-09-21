# Release acceptance

The product is an open-source CLI with paid engineering support. A release is a
specific wheel, source distribution, toolchain and body of evidence. The current
alpha does not warrant correctness of arbitrary source repositories.

Use Python 3.11 for release tooling and the pinned Lean and Joern versions. Install
the source runtimes and assembly tools required by the CI workflows. From a checkout,
prepare a new candidate directory containing only this release's artifacts:

```sh
python -m pip install '.[test,machine]'
python cartographer/render_lean.py ast-V8Base.json Autoform/Generated/V8Base.lean V8Base
python -m build --outdir dist/candidate
python -m twine check --strict dist/candidate/*
python scripts/check_distribution.py dist/candidate
AUTOFORM_TEST_WHEEL=dist/candidate/autoform_lean-0.1.0-py3-none-any.whl python -m pytest tests/test_package.py -q
python -m pytest tests -q
lake build
python scripts/audit_all.py --strict
python scripts/check_render.py
python scripts/check_docs.py
python scripts/check_specs_fresh.py
AUTOFORM_TEST_JOERN=1 AUTOFORM_REQUIRE_LEAN=1 python -m pytest tests/test_source_pipeline.py tests/test_source_numeric.py tests/test_python_binding.py tests/test_python_signatures.py tests/test_python_receivers.py tests/test_python_callable_shapes.py tests/test_control_flow.py tests/test_python_handlers.py tests/test_python_raises.py tests/test_spec_synthesis.py tests/test_linux_pipeline.py -q
AUTOFORM_REQUIRE_LEAN=1 python -m pytest tests/test_machine_frontend.py -q
lake env leanchecker --fresh Autoform.Lang.PCode.Properties
python -m pip install --force-reinstall 'dist/candidate/autoform_lean-0.1.0-py3-none-any.whl[machine]'
AUTOFORM_TEST_INSTALLED_E2E=1 python -m pytest tests/test_installed_assurance.py -q
```

Use the candidate's actual version in the wheel path. The distribution checker
compares every runtime resource and CLI module with source, checks both package
versions, and verifies license notices in the wheel and source distribution.
The installed-distribution tests execute outside the source checkout and exercise
failure cases that must invalidate old evidence. A missing required tool, skipped
required integration test, or failed check is an unmet gate.

Use the installed environment's `autoform` on `PATH` for the final acceptance test.
It runs two pinned revisions of a temporary Git repository through the CLI, checking
a proved ownership property and a false property whose guarantee must be withheld.

The package workflow adds macOS/Linux installation checks, installed machine
proofs, and source proofs using the exact candidate wheel. Publishing requires
the machine workflow and full repository CI, including fresh kernel replay and
historical artifact integrity checks, to pass in the same release workflow. Do not bypass
a failing historical artifact check by treating unavailable evidence as passed.

Before publishing, retain the distribution hashes, environment/toolchain
versions, test output and audit JSON. Run a pinned Git URL through the installed
CLI in a fresh workspace and retain the entire evidence directory. Check an
independent requested property as well as a deliberately unsupported case. A
negative run should withhold its guarantee; it is not a successful verification.
A positive scoped certificate can coexist with `completed_with_gaps` and exit `1`
when broader assurance claims remain unresolved. Preserve both statuses.
Clean network bootstrap and supported-platform CI must run on the release
candidate, even when local checks used cached dependencies.

The support agreement must specify scope and response terms before a paid
engagement begins. Confirm the distribution's third-party notices against its
upstream revisions. The Cachetools notice was compared byte for byte with the
license at the full pinned revision; [THIRD_PARTY.md](../THIRD_PARTY.md) records
that revision and links its immutable license text.
Historical repository corpora need their own provenance review if
redistributed beyond the CLI package. See [THIRD_PARTY.md](../THIRD_PARTY.md).

Publishing is a separate action described in [packaging.md](packaging.md).
Passing local checks prepares a candidate; it does not publish it or establish
that every release gate has run.

## Re-landing a corpus

A tracked `ast-<Module>.json` is evidence about the exporter that produced it, not about
the exporter in the tree. When the exporter has moved far enough that a fresh export
should replace the tracked artifact — see [`docs/integrity.md`](integrity.md) for how to
decide that, and why it is a coverage question before it is an integrity one — the
replacement is a cascade, not a copy: AST, render, manifest pins, provenance record,
conformance evidence, generated specs and ledger all move together or every gate stays
green while agreeing on a mixture of old and new.

`scripts/reland_corpus.sh <source-dir> <Module>` performs that cascade in the documented
order, from a clean tree, and stops at the first failure. It records real provenance for
the new artifact and retires its `provenance/unattributed.json` entry, re-pins the
manifest, rebuilds, re-runs the conformance oracle, regenerates the specs and the ledger,
and then lists the gates that still have to be run by hand (`check_docs`, `check_render`,
`audit_all --strict`, the mutation gate). It does not commit.

Expect theorems to break. A spec whose truth depended on the old rendering will fail on
the first `lake build`; for `Cachetools` each theorem in `Autoform/Specs/CachetoolsSpec.lean`
carries a `RELAND:` annotation saying whether it survives, breaks because its subject is
now a hole, or breaks because its subject is *no longer* a hole and the negative result it
proved has become false in the good direction. A broken theorem is a finding to be read,
not a build error to be silenced: the honest fix is a restated domain or a deleted claim,
never a re-recorded hash.

The corpus source must be available at the identified revision. `cachetools` is the
upstream repository at tag `v7.1.7`, with `src/` as the export root (the tracked AST
records paths as `cachetools/…`). `V8Base` cannot be re-landed here: its source revision
is unrecorded, which is the gap its provenance entry names.

