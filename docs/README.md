# docs

Reference documentation for autoform. `../README.md` is the overview and `../STRATEGY.md`
is the design record, which carries the reasoning behind everything here.

| Document | What it covers |
|---|---|
| [`architecture.md`](architecture.md) | How the pieces fit: the approach, why the CPG is treated as a universal AST, the pipeline stage by stage, and what every module and script is for. Start here. |
| [`core-language.md`](core-language.md) | Reference for the Core language: every `Val`/`Expr`/`Stmt` constructor, the heap/env/context model, the four evaluation outcomes, dialects, and the hole taxonomy. |
| [`trust-model.md`](trust-model.md) | What is claimed and on what basis: the four independent oracles, the G1–G5 assurance goals, the status lattice, and an explicit list of what the system does *not* establish. |
| [`running.md`](running.md) | Installation (Lean/`elan`, Joern, Python), the two entry points, how to read the ledger, and troubleshooting. |
| [`fuel.md`](fuel.md) | The fuel-indexed interpreter: why `outOfFuel` is not divergence, fuel monotonicity across all seven interpreter functions, the `tryFinally` counterexample that bounds it, and how the 72 fuel obligations were discharged. |
| [`integrity.md`](integrity.md) | Checking that the program measured is the program intended. Each check is named after the incident that motivated it, including a mutant that survived four commits with every proof passing. |
| [`contracts.md`](contracts.md) | Boundary contracts for code outside the verified core. |
| [`boxed-containers.md`](boxed-containers.md) | The design for mutable containers — the gap behind `setIndex:immutable-containers`. |
| [`languages.md`](languages.md) | Per-language support, and what each front end does and does not provide. |
| [`scale.md`](scale.md) | How the pipeline behaves on codebases larger than the reference corpus. |
| [`ledger-schema.md`](ledger-schema.md) | The trust ledger as a SACM profile: node vocabulary, evidence types, combination rules. |
| [`fvspec.md`](fvspec.md) | The FVSpec benchmark harness and the anti-vacuity screen run across it. |
| [`../CONTRIBUTING.md`](../CONTRIBUTING.md) | The project's working rules. Read them before submitting anything. |

**Standing caveat.** Coverage figures, hole counts and claim statuses move with every
change to the exporter, the semantics or the modelled stdlib. Documents here name the
command that regenerates a figure rather than quoting it. Where a snapshot is unavoidable
it is labelled with a date and a commit. If a document and an artefact disagree, the
artefact wins and the document is a bug.
