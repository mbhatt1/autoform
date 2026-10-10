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
`autoform doctor` prints a summary with one `install:` line per problem, chosen for
the host OS (Homebrew on macOS, apt on Linux, otherwise a URL), and `autoform doctor
--json` prints the same facts as a `schema_version: 1` document for scripts: per tool
its `path`, `found_version`, `expected_version`, `status` (`ok`, `missing`,
`version-mismatch`, `unknown-version`), whether it is `required`, an install `hint`,
and for an optional runtime the list of languages it `disables`. It returns `1` when a
**required** tool (Python 3.10+, git, lake, lean, leanchecker, joern) is absent or
disagrees with its pin, `0` otherwise, and `2` if the check itself could not run;
`--strict` also fails on an absent optional item. Lean is checked against
`lean-toolchain` and Joern against `joern-version` -- both pins are load-bearing,
because the neutral AST is a function of the frontend build. A missing language
runtime is a **warning**: translation and kernel proofs still run, and only that
language's differential oracle is unavailable -- `java`/`javac` gate Java and Kotlin,
`go` gates Go, `node` gates JavaScript and TypeScript, `cc` gates C, `clang` gates C++
and assembling `.s` inputs. `autoform --version` prints the package version together
with both pins, which is the line to paste into a bug report.

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

### Reproducible builds

The wheel is a pure-Python archive plus `autoform/runtime.zip`, which `build_support.py`
assembles from a fixed, sorted list of source files -- there is no compiled code and no
timestamp of the build's own. Two builds of the same commit therefore differ only in
archive metadata, and setting `SOURCE_DATE_EPOCH` pins that too:

```sh
SOURCE_DATE_EPOCH=$(git log -1 --format=%ct) python -m build
sha256sum dist/*
```

`scripts/check_distribution.py dist` is the check that matters more than a matching
hash: it opens the actual wheel and sdist and compares every runtime resource and CLI
module byte-for-byte with this checkout, both package versions with `pyproject.toml`,
the dependency metadata with the TOML contract, and the bundled license notices. A
wheel that passes it contains exactly what the tree says it should and nothing else.
The Python package workflow runs it on every build; `tests/test_package.py` runs it
against `AUTOFORM_TEST_WHEEL` and additionally proves it *rejects* a wheel with an
undeclared module, a startup hook, a wrong entry point or a tampered RECORD.

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
