# Security reports and execution boundary

A proof accepted for the wrong source, incorrect translation reported as
agreement, stale evidence accepted as current, or an unsupported operation
reported as verified is a security-relevant Autoform bug.

Use the repository's private vulnerability-reporting facility if available,
or the private channel in your support agreement. If neither is available,
open a public issue requesting a private contact without including exploit
details, credentials or confidential source. No private contact address or
response SLA is currently published by this project.

Include the affected CLI version, source revision, command, minimal reproducer,
expected and observed behavior, and relevant evidence hashes. A maintainer
should reproduce the issue, identify affected claims, add a native regression,
replay the corrected proofs independently, and document whether prior evidence
must be regenerated. Until resolved, treat affected guarantees as unverified.

Autoform executes analyzed code, compiler tools and proof elaboration. Its
process deadlines bound wall-clock time only. Isolation comes from one sandbox
layer (`scripts/sandbox.py`): the code under test runs with the network denied
unless `AUTOFORM_SANDBOX=off`, and with filesystem writes confined to the work
tree under `bwrap` (Linux) or `sandbox-exec` (macOS); the Linux `unshare`
fallback denies the network but does not confine writes, and
`AUTOFORM_SANDBOX=strict` refuses it. Every artifact records which mechanism
was enforced. That layer confines the target, not the analysing user's
privileges or data, so analyze untrusted repositories in a disposable
environment with no credentials and restricted access to other systems.
Evidence hashes assume a trusted runner; they do not authenticate evidence
against a malicious runner.

The alpha has no published long-term maintenance window. Supported versions
and remediation timelines for a paid engagement must be stated separately.

## Threat model: this tool runs the code it analyses

Autoform is not a static analyser. Several stages **execute the analysed repository, or
code derived from it, with a real runtime on the analysing machine**, and a reader who
assumes "it only parses" will run untrusted code with their own credentials. Stated by
stage, so nothing below is a surprise:

| stage | what runs | what it can do |
|---|---|---|
| `autoform <git-url>` | `git clone` of an arbitrary URL | network egress; writes under the workspace |
| `joern-parse` | Joern's frontends on the source (JVM) | parses only, but the JVM frontends are large and process attacker-chosen input |
| `cartographer/export_ast.sc` with `cartographer/compiler/SourceCompiler.scala` | a Joern script; for each Python source file the compiler spawns an **embedded Python decoder** (`python3 -I -S -c`, interpreter overridable with `AUTOFORM_PYTHON`, 30 s timeout) with the file on stdin | the decoder uses `ast.parse`/`symtable` and does not `import` or `exec` the target — but it is a Python process reading attacker-chosen text |
| `cartographer/generator_lowering.py` (from `render_lean.py` and the oracles) | rewrites generator bodies in the exported AST JSON | pure Python over the exporter's own output; no target code runs |
| `scripts/differential.py` | **the target's own functions, in the real runtime** — CPython, `cc`-compiled C, `node`, `javac`, `go` — on generated inputs, and the target's own test suite where present | **arbitrary code execution as the analysing user**; filesystem, network, credentials |
| `scripts/synth_specs.py` (non-synthetic mode) | the target's test suite and functions, to *observe* behaviour before synthesising specs | same as above |
| `scripts/native_c.py`, `scripts/runtime_backends.py` | compile and run target C/Go/Java/JS | same as above |
| `scripts/mutate.py` | `lake build` of a **mutated** copy of the translated module | Lean elaboration of a rewritten file; no target code runs |
| `lake build`, `leanchecker` | Lean elaboration and kernel replay of generated modules | the generated Lean is data, not code, but elaboration of adversarial terms can exhaust memory or time |

The differential oracle is the reason this project can make any faithfulness claim at
all, and it is also the sharpest edge here: a repository that wants to attack the analyst
only has to be analysed. `import os; os.system(...)` at module scope runs when the oracle
imports the module. A `setup.py`, a `conftest.py`, a C source with a constructor
attribute, a Go `init()` — all execute.

**Run untrusted repositories in a disposable environment.** Concretely: a container or VM
with no credentials mounted, no access to other systems, network restricted to the
package indexes the target legitimately needs (or none), and a filesystem you will throw
away. `--stage-timeout` bounds wall-clock, not capability; the process deadlines in
`scripts/assure.py` kill runaway stages and clean up their process groups, and nothing
more. Evidence hashes recorded in `guarantee.json` and `provenance/` assume the runner was
trusted while it ran — they authenticate the artifacts against later tampering, not the
runner against itself.

Two smaller boundaries worth knowing:

* **Lean is a program.** A generated module that elaborates for a very long time or
  allocates without bound is a denial of the analyst's machine, not a proof. `autoform.sh`
  stages are time-bounded; the mutation gate additionally kills the whole process group of
  a timed-out build so a detached compiler cannot write stale artifacts into the
  restoration build.
* **Reports name the target's identifiers.** Hole labels, function names and file paths
  from the analysed repository appear verbatim in `ledger-*.json`, `guarantee.json` and
  the SACM case. Treat those artifacts as containing whatever the target chose to name
  things.

What this project does *not* claim: that a proof about the translated program is a proof
about the source. The trust chain in `README.md` and `docs/trust-model.md` names every link
between them, and each is checked by a different oracle; a break in any one of them is a
security-relevant bug in the sense given at the top of this file.

## Operating on proprietary code

What leaves the machine, by command. Everything not listed stays local: artifacts are
written under the workspace and nothing is uploaded.

| what | when | where it goes |
|---|---|---|
| `git clone`/`fetch` of the target and its submodules | `autoform <git-url>`, `assure`/`source`/`regress`/`pr` given a URL, `pr` fetching a missing base | the Git remotes the repository names; a local checkout needs no network |
| prompts containing **source code, function bodies, generated Lean and test observations** | `autoformalize`, `formalize --prover claude`, `formalize --generators llm`, `formalize prove` | the backend chosen by `AUTOFORM_CLAUDE_AUTH`: `login`/`api-key` through the `claude` CLI, `api` through the Messages API SDK, `bedrock` through the SDK's cloud client (and the CLI agents with `CLAUDE_CODE_USE_BEDROCK=1`) |
| proof goals (fragments of the translated code) | the tier-3 proposer, only with `AUTOFORM_NEURAL=1` | `AUTOFORM_NEURAL_BACKEND`: local `ollama` by default; the two others are remote APIs |

`source`, `assure`, `pr` and `regress` make no model call. The code under test runs with
the network denied (`scripts/sandbox.py`) unless `AUTOFORM_SANDBOX=off`, which every
artifact records.

Settings for a host with data-egress rules:

* `AUTOFORM_LLM_ALLOWED_BACKENDS=<comma list>` restricts model calls to the named
  `AUTOFORM_CLAUDE_AUTH` values. Any other backend is refused before a prompt is sent,
  including the backend a `claude` CLI child (the proving agents) would reach, the harness
  `llm` generator (`api`) and the tier-3 proposer (its Messages API backend counts as `api`;
  its other remote backend is never allowed under a policy). Set but empty refuses every backend. `autoform doctor` prints the
  policy and warns when the configured backend is refused.
* Model answers are cached by prompt hash in `AUTOFORM_LLM_CACHE` (default
  `~/.cache/autoform/llm`) and proofs in `AUTOFORM_PROOF_CACHE`; the directories are made
  0700 and the entries 0600. Point both inside the workspace to keep them with the run.
* `AUTOFORM_SANDBOX=strict` refuses the Linux `unshare` fallback, which denies the network
  but does not confine filesystem writes; only `bwrap` or `sandbox-exec` is accepted.
* Credentials in a Git URL (`https://user:token@`, `ssh://user:pw@`, a remote-helper
  `helper::https://user:token@` address, a query string) are removed from the acquisition
  records, `checkout.log`, SARIF and console messages. Prefer a credential helper to a URL
  credential anyway: the URL is still in the `git` process's argv while it runs.
* Records (`run.json`, `guarantee.json`, `repository.json`, the autoformalizer's run
  directory) do not contain environment values; tests scan them for planted secrets.
  Logs of the stages (`*.log`, agent transcripts) contain whatever the analysed code and
  the tools print.
