# Installing the Python package

Autoform requires Python 3.10+ on macOS or Linux. Build/install from this repository:

```sh
python -m pip install .
# With the optional binary and assembly frontend:
python -m pip install '.[machine]'
autoform --version
autoform doctor
```

CI builds `autoform_lean-<version>-py3-none-any.whl` and a source distribution.
Download the `python-distributions` artifact from the **Python package** workflow
and install the wheel with `python -m pip install /path/to/the.whl`. The source
distribution also installs with pip. This does not require a Git checkout at run
time. Editable development installs (`pip install -e .`) are supported.

`autoform-lean` is the distribution name; `autoform` is the command and import name.
Once a release is published to PyPI, it can be installed with
`python -m pip install 'autoform-lean[machine]'`. Configuring the workflow alone
does not publish a release.

## Tools and workspace

Install elan/Lean and Joern as described in [running.md](running.md). Source runs
also need the corresponding runtime: CPython, `cc`/`c++`, Java/Javac, Go, Node,
or Kotlin/JVM. Kotlin can use Joern's bundled Kotlin compiler. Machine runs need
Lean and the `machine` extra; assembling `.s` files also needs clang. These external
toolchains are not silently installed by pip. Initial Lean builds fetch the pinned
Lake dependencies and may need network access.
`autoform doctor` reports, per tool, its path, the version found and the version
pinned in this package, and a `status` of `ok`, `missing`, `version-mismatch` or
`unknown-version`. It returns `1` when a **required** tool (Python 3.10+, git, lake,
lean, leanchecker, joern) is absent or disagrees with its pin, and `0` otherwise;
`--strict` also fails on an absent optional item. Lean is checked against
`lean-toolchain` and Joern against `joern-version` -- both pins are load-bearing,
because the neutral AST is a function of the frontend build. Language runtimes and
the `[machine]` extras are reported but optional, so `doctor` still does not tell
you that a *particular* language is ready end to end.

```sh
autoform https://github.com/OWNER/REPOSITORY.git
autoform --workspace ./linux-proofs https://github.com/torvalds/linux.git Linux --subdir lib --ref v6.12
autoform --workspace ./proofs init
autoform --workspace ./proofs source /path/to/code MyProject
autoform --workspace ./proofs assure /path/to/code MyProject
autoform --workspace ./proofs machine /path/to/binary MyBinary
autoform machine --help
```

A URL without a subcommand means `assure`. URLs also work as the source argument of
`source` and `assure`. Each invocation gets a fresh detached checkout and records its
commit in `repository.json`; tags and branches are resolved to that commit before
analysis. Submodules are initialized recursively. `--subdir` selects analysis scope;
the full checkout is retained so sibling headers and other source dependencies remain available.
Local paths continue to work without a clone. Concurrent installed CLI runs for the
same workspace are refused before changing evidence, including different modules.

The final `guarantee.md` and `guarantee.json` describe guarantees about the recorded
cases and initial states of the Lean model. A `verified_scoped` result requires native
conformance proofs, specification mutation checks, a successful independent kernel
replay, and matching source/model/header provenance. It includes theorem names,
assumptions, exclusions, source commit, and artifact hashes. This is a finite-domain
model guarantee; it is not an all-input correctness or security guarantee for the
original repository. Failed acquisition clears prior verdicts and writes a failure
report without a verified guarantee.

`assure` and the Git URL shorthand discover `autoform.properties.json` in the
selected source directory; `--subdir` also restricts property discovery to that folder.
An explicit `--properties properties.json` overrides the repository manifest.
These independent Lean propositions receive a separate security certificate and
may quantify over their inputs. A requested property that is unproved, missing or
unsupported by current evidence withholds the overall guarantee. See the
[property format and ownership example](security.md). This does not prove universal
source-to-model fidelity or infer the intended security policy from a repository.

For a Linux tree, the same command detects the kernel context, collects translation
and per-unit native evidence, proves supported observations, runs mutation and
independent proof checks, and writes `artifacts/pipeline/<Module>/summary.md`.
Failed or unsupported stages also receive a final report. A nonzero result and
`completed_with_gaps` mean the workflow finished with unresolved verification gaps;
they must not be read as whole-kernel verification. See [running](running.md) for
configuration and native-runtime boundaries.

For `assure` and the Git URL shorthand, exit `0` means the workflow's required
checks completed, `1` means unresolved verification gaps, and `2` reports an
invocation, setup or orchestration failure. Interruptions can produce signal-based
exit codes. Read `run.json` and the certificates together: `verified_scoped`
can coexist with exit `1` when the broader assurance case has gaps. The status
never expands a theorem beyond its stated inputs, assumptions and subject.

Global `--workspace` goes before the subcommand; the default is `.autoform-work` in
the current directory. Input paths and machine `--out` paths are relative to the
caller's directory. Reports live under the workspace's `artifacts/pipeline/<Module>`
or `artifacts/machine/<Module>`. Source runs also emit `Autoform/Generated/<Module>.lean`
and `Autoform/SpecsGen/<Module>.lean` inside the workspace.

The bundled project includes the import closure of `Autoform.Runtime`: semantics,
ledger, contracts, proof synthesis vocabulary and audit tools. The repository's
historical corpus proof collection is checked separately by repository CI. The
bundle contains no local caches, credentials or previous pipeline evidence.

An existing workspace must match the package's bundled resources. After upgrading
the package, choose a new workspace; Autoform refuses to overwrite changed
semantics or user files. Generated output and build caches do not prevent reuse.

## CI and publishing

`package.yml` builds the wheel from the source distribution, validates metadata,
tests installation outside the checkout on macOS/Linux and Python 3.10/3.12, and
checks an installed assembly example in Lean. `source.yml` runs the eight source
language fixtures through Joern, real runtimes and kernel proofs, then exercises the
installed source CLI. The machine workflow checks the p-code models and host-native
conformance and is also a required publication gate. Source CI includes the installed
Git URL acceptance test for both proved and false requested security properties.

For PyPI releases, configure a [trusted publisher](https://docs.pypi.org/trusted-publishers/)
for project `autoform-lean`, owner `mbhatt1`, repository `autoform`, workflow
`package.yml`, environment `pypi`. Create that GitHub environment as well. Bump both
`pyproject.toml` and `src/autoform/__init__.py`, then publish a GitHub release tagged
`v<version>`. The publishing job waits for package installation, installed machine
proofs, the source-runtime workflow using that same wheel, the machine workflow, and the repository's
full build, trust audit, tooling and integrity checks. It rejects a release tag
that disagrees with the metadata. A missing historical corpus or failed audit
blocks publication; a successful package build alone is insufficient.
This follows the [PyPA publishing workflow](https://packaging.python.org/en/latest/guides/publishing-package-distribution-releases-using-github-actions-ci-cd-workflows/).

Local distribution checks:

```sh
python -m pip install '.[test]'
python -m build
python -m twine check --strict dist/*
python scripts/check_distribution.py dist
AUTOFORM_TEST_WHEEL=dist/autoform_lean-0.1.0-py3-none-any.whl python -m pytest tests/test_package.py -q
AUTOFORM_TEST_JOERN=1 python -m pytest tests/test_source_pipeline.py -q
```

See [release acceptance](releasing.md), [support scope](../SUPPORT.md), and
[third-party notices](../THIRD_PARTY.md). These commands prepare and check a
candidate; publishing requires a separate release action.
