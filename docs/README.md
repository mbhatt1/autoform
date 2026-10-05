# docs

Reference documentation for autoform. `../README.md` is the overview and `../STRATEGY.md`
is the design record, which carries the reasoning behind everything here.

| Document | What it covers |
|---|---|
| [`architecture.md`](architecture.md) | How the pieces fit: the approach, why the CPG is treated as a universal AST, the pipeline stage by stage, the integrity checks beside it, provenance, and what every module and script is for. Start here. |
| [`core-language.md`](core-language.md) | Reference for the Core language: every `Val`/`Expr`/`Stmt` constructor, the heap/env/context model, the four evaluation outcomes, the three dialects (`.python`, `.cLike`, `.javascript`), and the hole taxonomy. |
| [`trust-model.md`](trust-model.md) | What is claimed and on what basis: the four independent oracles (including exactly what the audit fails on and why the kernel replay is a separate multi-hour CI job), the integrity gates, the G1–G5 assurance goals, the status lattice, and an explicit list of what the system does *not* establish. |
| [`conformance.md`](conformance.md) | The differential oracle driven by the corpus's own test suite (Python leg, cachetools): how calls are recorded and replayed, what is refused and why, the current measured reach (figures first, intermediate states labelled history), and the divergences it found. |
| [`running.md`](running.md) | Installation (Lean/`elan`, Joern, Python, the optional real runtimes the oracles need), what each CI job runs, the two entry points, how to read the ledger, the audit modes, provenance, and troubleshooting. |
| [`cli.md`](cli.md) | Enterprise CLI usage: install, configure `autoform.toml`, run dry-runs, invoke translate/assure/check/audit, and integrate with CI. |
| [`enterprise-readiness.md`](enterprise-readiness.md) | Current CLI readiness, green checks, known evidence gaps, and the release-clean checklist. |
| [`fuel.md`](fuel.md) | The fuel-indexed interpreter: why `outOfFuel` is not divergence, fuel monotonicity across all seven interpreter functions, the `tryFinally` counterexample that bounds it, and how the 72 fuel obligations were discharged. |
| [`integrity.md`](integrity.md) | Checking that the program measured is the program intended: what is tracked and why, `check_render.py` and its reviewed not-tracked allowlist, provenance and fixture-exporter freshness, `check_docs.py`. Each check is named after the incident that motivated it, including a mutant that survived four commits with every proof passing. |
| [`contracts.md`](contracts.md) | Boundary contracts for code outside the verified core: contracts at expression holes and at statement holes, and the ledger's separate "conditionally verifiable" count. |
| [`boxed-containers.md`](boxed-containers.md) | Mutable containers as heap objects: the design and how steps 1-4 landed for Python (`Expr.boxContainer`, `Stmt.setIndex`/`delIndex`); the oracle encoder step is recorded as not done. |
| [`languages.md`](languages.md) | Per-language support, and what each front end does and does not provide. |
| [`scale.md`](scale.md) | How the pipeline behaves on codebases larger than the reference corpus: a dated seven-repository Python scale test, and the current SQLite (C) census and typed conformance sample. Opens with a table saying which parts are current. |
| [`ledger-schema.md`](ledger-schema.md) | The trust ledger as a SACM profile: node vocabulary, evidence types, combination rules. |
| `evidence-*.md` | Per-corpus evidence snapshots: [`V8Base`](evidence-V8Base.md), [`LinuxLib`](evidence-LinuxLib.md), [`LinuxCrypto`](evidence-LinuxCrypto.md), [`Ansible`](evidence-ansible.md). Dated 2026-08-19/20 and **not current**: each opens with a status block saying what was re-checked against the committed evidence JSON, what cannot be re-derived from a clone (the Ansible, LinuxCrypto and LinuxLib ASTs are in no clone), and what an older pipeline produced. |
| [`fvspec.md`](fvspec.md) | The FVSpec benchmark harness and the anti-vacuity screen run across it. |
| [`../CONTRIBUTING.md`](../CONTRIBUTING.md) | The project's working rules. Read them before submitting anything. |

**Standing caveat.** Coverage figures, hole counts and claim statuses move with every
change to the exporter, the semantics or the modelled stdlib. Documents here name the
command that regenerates a figure rather than quoting it. Where a snapshot is unavoidable
it is labelled with a date and a commit. If a document and an artefact disagree, the
artefact wins and the document is a bug.
