# docs

Reference documentation for autoform. `../README.md` is the overview and `../STRATEGY.md`
is the design record — the reasoning behind everything here lives there.

| Document | What it covers |
|---|---|
| [`architecture.md`](architecture.md) | How the pieces fit: the central bet, why the CPG is treated as a universal AST, the pipeline stage by stage, and what every module and script is for. Start here. |
| [`core-language.md`](core-language.md) | Reference for the Core language: every `Val`/`Expr`/`Stmt` constructor, the heap/env/context model, the four evaluation outcomes, dialects, and the hole taxonomy. |
| [`trust-model.md`](trust-model.md) | What is claimed and on what basis: the four independent oracles, the G1–G5 assurance goals, the status lattice, and an explicit list of what the system does *not* establish. |
| [`running.md`](running.md) | Installation (Lean/`elan`, Joern, Python), the two entry points, how to read the ledger, and troubleshooting. |
| [`contracts.md`](contracts.md) | Boundary contracts for code outside the verified core. |
| [`boxed-containers.md`](boxed-containers.md) | The design for mutable containers — the gap behind `setIndex:immutable-containers`. |
| [`languages.md`](languages.md) | Per-language support, and what each front end does and does not give us. |
| [`scale.md`](scale.md) | How the pipeline behaves on codebases larger than the reference corpus. |
| [`ledger-schema.md`](ledger-schema.md) | The trust ledger as a SACM profile: node vocabulary, evidence types, combination rules. |
| [`fvspec.md`](fvspec.md) | The FVSpec benchmark harness and the anti-vacuity screen run across it. |
| [`../CONTRIBUTING.md`](../CONTRIBUTING.md) | The project's working rules. They are unusual; read them before submitting anything. |

**A standing caveat.** Coverage figures, hole counts and claim statuses move with every
change to the exporter, the semantics or the modelled stdlib. Documents here name the
command that regenerates a figure rather than quoting it. Where a snapshot is unavoidable
it is labelled with a date and a commit. If a document and an artefact disagree, the
artefact wins and the document is a bug.
