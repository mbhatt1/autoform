# Autoform CLI

`autoform` is the stable command-line interface for teams that want to run Autoform in a
repeatable CI or enterprise workflow. The Python CLI owns pipeline orchestration;
`autoform.sh` and `assure.sh` are compatibility shims that delegate to it. This keeps one
execution path for local use, CI, run manifests and future fleet integration.

## Install for development

```sh
python3 -m pip install -e .[dev]
```

For Python 3.9 or 3.10, install the TOML extra as well if you want config-file support:

```sh
python3 -m pip install -e .[dev,toml]
```

## Commands

```sh
autoform doctor                       # check Lean, Lake, Git and Joern paths
autoform init                         # write an autoform.toml template
autoform targets                       # list configured services/repos
autoform translate <src> <Module>      # run one translation pipeline
autoform translate --target payments   # run a named target from autoform.toml
autoform assure <src> <Module>         # run one assurance pipeline
autoform plan                          # write a deterministic fleet execution plan
autoform spec-plan <src> <Module>       # plan tests -> traces -> Lean behavior specs
autoform seed-python-tests <src> <Module> \
                                      # write pytest characterization tests
autoform trace-python-tests <src> <Module> \
                                      # run Python tests and emit behavior trace/spec
autoform spec-from-trace trace.jsonl Service \
                                      # render test observations as a Lean spec module
autoform verify-plan --plan fleet-plan.json
autoform batch                         # run or dry-run configured targets
autoform validate                      # validate fleet configuration
autoform schema run-manifest           # print the run manifest JSON schema
autoform schema manifest-index         # print the fleet index JSON schema
autoform schema fleet-plan             # print the fleet plan JSON schema
autoform schema behavior-trace-observation
autoform schema config                 # print the autoform.toml JSON schema
autoform gate --manifest out/run.json  # evaluate a CI run manifest
autoform bundle --manifest out/run.json --output evidence.tar.gz
autoform report --manifest out/run.json --output evidence.md
autoform index .autoform-runs/*/run.json --output fleet-index.json
autoform render ast-Name.json Name     # render neutral AST to Lean
autoform audit --with-kernel           # include slow independent kernel replay
autoform check --junit autoform-checks.xml --sarif autoform.sarif
```

Every pipeline command accepts `--dry-run`, `--json`, `--repo-root`, `--lake`, `--run-id`, `--artifact-dir` and
`--keep-work`. JSON mode is the preferred mode for CI systems and dashboards. `autoform spec-plan` is a planning command for test-first autoformalization: it records how a real test command will become runtime traces, Lean behavior specs, conformance checks and mutation gates before the expensive translation run starts. `autoform seed-python-tests` writes pytest characterization tests for Python project functions using provided sample cases and zero-argument functions, while leaving skipped TODO cases for functions that still need inputs. `autoform trace-python-tests` runs a Python test command under Autoform's behavior tracer, writes JSONL observations for project functions, and renders the same observations into a Lean behavior-spec module unless `--trace-only` is passed. `autoform spec-from-trace` reads behavior trace JSONL and writes a Lean module that imports `Autoform.Generated.<Module>` and records every runtime observation, including explicit skip reasons. Non-dry-run
translate and assure executions write a manifest to `.autoform-runs/<run-id>/run.json` by
default, with every planned command, return code and discovered artifact.
Each manifest also records audit metadata: the config path, CLI version, repo commit and dirty flag, Python runtime, selected Lake executable, Joern home, and whether C/C++ defines were set.
They also check the pinned Joern version and record `provenance/ast-<Module>.json.prov.json` for exported ASTs.

## Repository root selection

The CLI can be installed once and pointed at a checkout with `--repo-root /path/to/autoform`
or `AUTOFORM_ROOT=/path/to/autoform`. Config discovery checks the current directory first
and then the repository root, so CI jobs can keep service-specific configs beside the job
or use the root-level `autoform.toml`.

## Configuration

The CLI reads `autoform.toml` or `.autoform.toml` from the current directory, or an explicit
`--config` path.

```toml
[project]
source = "/repo/service"
module = "Service"

[runtime]
joern_home = "~/joern"
lake = "/opt/lean/bin/lake"
cpp_defines = ["SQLITE_TEST", "SQLITE_API= "]

[targets.payments]
source = "/repos/payments"
module = "Payments"
mode = "assure"
owner = "payments-platform"
tier = "critical"
tags = ["pci", "python", "nightly"]

[targets.search]
source = "/repos/search"
module = "Search"
mode = "translate"
owner = "search-platform"
tier = "standard"
tags = ["go", "nightly"]
```

Command-line arguments override config values. Environment variables such as `JOERN_HOME`,
`AUTOFORM_LAKE`, `CPP_DEFINES`, `LANG`, `LC_ALL` and `JAVA_TOOL_OPTIONS` are still honored by the underlying
pipeline.

## CI pattern

A large organization should treat Autoform as an evidence-producing job rather than a
single pass/fail linter:

```sh
autoform doctor --json
autoform targets --json
autoform validate --json
autoform --run-id nightly-2026-10-04 --json translate /repo/service Service
autoform gate --manifest .autoform-runs/nightly-2026-10-04/run.json --json
autoform bundle --manifest .autoform-runs/nightly-2026-10-04/run.json --output autoform-evidence.tar.gz --json
autoform report --manifest .autoform-runs/nightly-2026-10-04/run.json --output autoform-evidence.md --json
autoform --run-id nightly-2026-10-04 --json plan --tag nightly --output fleet-plan.json
autoform verify-plan --plan fleet-plan.json --json
autoform --json batch --plan fleet-plan.json
autoform index '.autoform-runs/nightly-2026-10-04-*/run.json' --output fleet-index.json --json
autoform gate --manifest fleet-index.json --json
autoform report --manifest fleet-index.json --output fleet-report.md --json
# Gate an individual target too when a reviewer needs the exact failing step:
autoform gate --manifest .autoform-runs/nightly-2026-10-04-payments/run.json --json
autoform check --fail-fast --json --junit autoform-checks.xml --sarif autoform.sarif
```

The generated artifacts (`ast-*.json`, `ledger-*.json`, `sacm-*.json`, `audit.json`,
`mutation.json`) plus `.autoform-runs/<run-id>/run.json` are the review payload. Use `autoform plan` to review the exact selected targets before execution, `autoform verify-plan --plan fleet-plan.json` to catch config drift, `autoform batch --plan fleet-plan.json` to apply that reviewed plan, then `autoform index` to collapse many target manifests into one dashboard-friendly JSON file. Store them
as CI artifacts even when a gate fails. Use `autoform report --manifest <run.json> --output evidence.md` for a single run, or `autoform report --manifest fleet-index.json --output fleet-report.md` for a batch summary. Then use `autoform bundle --manifest <run.json> --output evidence.tar.gz` to package a run manifest and its listed artifacts as one uploadable file.

## Enterprise gates

Use `autoform check --junit autoform-checks.xml --sarif autoform.sarif` when CI should display render, docs and provenance checks as first-class test results and code-scanning findings.

Use `autoform validate` before scheduling fleet jobs. It checks target tables, module names,
allowed modes and optional source-path existence. Use `autoform schema config`,
`autoform schema run-manifest`, `autoform schema manifest-index`, `autoform schema fleet-plan` and `autoform schema behavior-trace-observation` to pin the config, manifest and trace contracts in downstream systems. Use `autoform gate --manifest <run.json>` after
a single run, or `autoform gate --manifest fleet-index.json` after `autoform index`, to fail CI when a pipeline return code, required step, or indexed target failed; add
`--require-artifacts` when the CI worker should also confirm listed artifacts exist before
upload.

## Compatibility entry points

Existing automation can keep calling:

```sh
./autoform.sh <source-dir> <ModuleName>
./assure.sh <source-dir> <ModuleName>
```

The wrappers preserve global CLI flags such as `--dry-run`, `--json`, `--run-id`,
`--artifact-dir`, `--joern-home` and `--cpp-defines`, then inject the appropriate
`translate` or `assure` subcommand.

## Fleet targets

Use `[targets.<name>]` tables for service-scale operation. Each target can carry `owner`, `tier` and `tags` metadata for rollout control and reporting. `autoform plan` resolves explicit target names plus filters into a stable JSON plan without invoking Joern or Lean. The plan records the requested target subset, so `autoform verify-plan --plan fleet-plan.json` can recompute the same selection from the current config and fail on drift. `autoform targets --tag nightly --owner payments-platform` lists only the matching fleet slice, and `autoform batch --plan fleet-plan.json` runs exactly the reviewed slice. Repeating `--tag` requires every tag to be present.

`autoform batch` runs every configured target by default, or the named subset passed on the command line. Filters apply after explicit names, which lets CI jobs select a safe subset from a precomputed service list. In batch mode a supplied `--run-id fleet42` is expanded to target-scoped run IDs such as `fleet42-payments`; a supplied `--artifact-dir out` becomes `out/payments`, `out/search`, and so on.
