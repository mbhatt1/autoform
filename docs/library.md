# Using autoform as a library

The distribution `autoform-lean` installs one package, `autoform`, with three parts:

| import | what it is |
|---|---|
| `autoform.cli` | the command (`main(argv) -> int`), workspace management, `doctor` |
| `autoform.repository` | Git URL handling and source acquisition |
| `autoform.harness` | the claim harness behind `autoform formalize`: CPIR, generators, critic, judge, verifier, prover, ledger, reports |
| `autoform.nl` | the natural-language autoformalizer behind `autoform autoformalize`: model, describe, formalize, check, prove, refine, repair, report |

The oracle and gate scripts (`scripts/*.py`) and the exporter (`cartographer/`) are not
installed as importable modules: they are shipped inside the package's `runtime.zip` and
unpacked into a workspace by `autoform init`, where the CLI runs them as subprocesses.
From a checkout, or from `<workspace>/scripts`, they are ordinary Python modules and the
second half of this page is about them.

## The command, from Python

```python
import autoform.cli

code = autoform.cli.main([
    "--workspace", "./proofs",
    "assure", "https://github.com/tkem/cachetools.git", "Cachetools",
    "--ref", "v7.1.7", "--subdir", "src", "--shard-functions", "1000",
])
```

`main` returns the process exit code (`docs/cli.md`, "Exit codes") and writes evidence
under `./proofs/artifacts/pipeline/Cachetools/`. It takes a workspace lock, so two calls
with the same workspace cannot overlap. `autoform.cli.doctor(env, strict=False,
as_json=False)` runs the environment check and returns its exit code;
`autoform.cli.environment()` builds the environment the stages run under (`PATH` with
`~/.elan/bin`, `AUTOFORM_PYTHON`). `autoform.cli.prepare_workspace(path)` extracts the
runtime payload atomically and refuses a workspace initialised by a different package
build.

### Reading the result

Every artifact is JSON with a stable shape (`docs/cli.md`, "What a run leaves behind").
The one to read first:

```python
import json, pathlib

report = pathlib.Path("proofs/artifacts/pipeline/Cachetools")
guarantee = json.loads((report / "guarantee.json").read_text())
guarantee["status"]            # "verified_scoped" or "unverified"
guarantee["claims"]            # [{theorem, subject, recorded_cases, all_inputs, property}, ...]
guarantee["failed_checks"]     # names of the gates that did not pass, when unverified
guarantee["artifacts"]         # sha256 of every artifact the claims are bound to

conformance = json.loads((report / "conformance.json").read_text())
conformance["agree"], conformance["divergences"], conformance["inconclusive"]
conformance["divergence_detail"]       # function, inputs, both outcomes
conformance["inconclusive_detail"]     # per function: the hole label that stopped the comparison
conformance["measurement_basis"]       # what "compared" meant for this run

ledger = json.loads((report / "ledger-Cachetools.json").read_text())
ledger["functions"], ledger["holeFree"], ledger["verifiableCore"], ledger["holesByLabel"]
```

A claim in `guarantee.json` is about the recorded inputs it names (`all_inputs: false`)
unless the theorem is universally quantified. `status` is `unverified` whenever any
required gate did not pass; the claims list is then empty and `failed_checks` says why.

### Source acquisition

```python
from autoform.repository import is_git_url, resolve_source

source, checkout = resolve_source("https://github.com/OWNER/REPO.git", workspace,
                                  "Module", ref="v1.2.0", subdir="src")
```

`resolve_source` clones to a detached checkout under `<workspace>/sources/`, records the
exact commit, and returns the directory to analyse; a local directory is returned as is.
Output from `git` is redacted of credentials before it is shown.

## The harness and the autoformalizer

`autoform.harness.pipeline.Options` and `run(...)` are what `autoform formalize` calls;
`autoform.nl.pipeline.main(argv)` is `autoform autoformalize`. Both are documented by
their modules' docstrings and by `docs/harness.md` and `docs/autoformalize.md`. The pieces
that are useful on their own:

* `autoform.harness.claims.validate(claim, program)` — type-check a claim (a small JSON
  DSL over function identifiers) against a program's CPIR.
* `autoform.harness.verifier` — `run_lean(root, path, timeout)`, `axioms_of(output)`,
  `certified(name, axioms)`: run a Lean file and read the axiom base of a theorem.
* `autoform.harness.prover` — an autonomous proving loop whose every result is re-checked
  by the kernel; `forbidden(text)` is the filter that rejects `sorry`, `native_decide` and
  friends in proposed proofs.
* `autoform.nl.pyvalues` — Python values ↔ tagged JSON ↔ Lean `Val` literals, the encoding
  the oracle and the autoformalizer share.
* `autoform.nl.llm` — the one model backend (`ask(prompt, ...)`), with
  `AUTOFORM_CLAUDE_AUTH` selecting login or API-key authentication.

## The scripts, from a checkout

These run as modules from the repository root or a workspace (`sys.path.insert(0,
"scripts")`). They are the oracles and gates the CLI chains; each is also a command
with `--help`.

| module | use from Python |
|---|---|
| `differential` | the conformance oracle. Set `AUTOFORM_NO_REEXEC=1` or `PYTHONHASHSEED=0` before importing: it re-executes itself under a fixed hash seed otherwise. `Encoder(class_identities)` snapshots live Python objects as Lean heap literals; `lean_val`, `lean_heap` print them. |
| `runtime_backends` | `load_observations(report, ast, source_root, module, generated)` accepts recorded evidence only for the exact source, AST and model it was recorded against; `source_fingerprints`, `semantics_fingerprints`. |
| `generated_module` | the files that make up a rendered model: `model_files(generated)`, `model_digest(generated)`, `build_files(repo, module)`, `is_sharded`. Use these, never the root file alone, when hashing or snapshotting a model. |
| `external_bases` | the external base-class contracts: `CONTRACTS`, `verify(cls)` (`None` or the reason the live class cannot be trusted), `lean_text()` (the Lean mirror). |
| `synth_specs` | `budget_probe`, `emit`, `compile_repair`: observation theorems from a `conformance.json`. |
| `mutate` | `parse_decls`, `gen_mutants_generated`: the mutation operators over a rendered model, and the gate itself. |
| `proof_artifacts` | `digest`, `snapshot`, `replay_current`: binding evidence to compiled modules and configuration. |
| `provenance` | `source_revision(path)` (a Git commit or a tree digest), `record`: how an AST is attributed to the exporter and source that produced it. |
| `guarantee`, `security_specs`, `sacm`, `audit_all` | the gates, each `main(argv)`. |
| `pr_mode` | `autoform pr` without the workspace: `changed_functions(repo, base, head, subdir)`, `select_functions(ast, names)`, `evidence(...)`, `sarif_document(report)`, `validate_sarif(document)`, `markdown_comment(report)`; `main(argv)` runs the chain. |

The Lean side is a library too: `import Autoform.Lang.Core.Semantics` gives the
interpreter (`runFunc`, `applyFunc`, `initGlobals`, `runMain`), `Autoform.Refine` the
refinement vocabulary (`Refines`, `RefinesUnder`, contracts), `Autoform.Ledger` the
coverage accounting, and a rendered `Autoform.Generated.<Module>` exposes `program`,
`moduleInits` and one `def` per function. `docs/core-language.md` is the reference.

## Stability

The package is an alpha (`0.1.0`). The CLI's flags and exit codes, the JSON artifact
shapes listed in `docs/cli.md`, and the Lean names above are the interface; the
harness and autoformalizer internals move with their stages. Numbers in these documents
are reproduced by named commands, and `scripts/check_docs.py` fails when a documented
figure disagrees with the artifact it is pinned to.
