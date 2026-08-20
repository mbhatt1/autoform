# The trust ledger as a SACM assurance case

The ledger (STRATEGY.md §3) is a precise statement of *what is proved, about what model,
under what assumptions*. Until now it was ad-hoc text. This document specifies it as a
**SACM profile** — the model, the evidence types, and the rules for combining them into a
claim. `scripts/sacm.py` emits it.

## Why SACM and not a bespoke format

STRATEGY.md §10: the "composition calculus for heterogeneous verification evidence" is
the assurance-case field, standardized for decades in safety-critical engineering. We
adopt rather than invent.

- **SACM** — OMG *Structured Assurance Case Metamodel* v2.1. Unifies and extends **GSN**
  (Goal Structuring Notation: goals, strategies, solutions, contexts, assumptions,
  undeveloped goals) and **CAE** (Claims–Arguments–Evidence). It models exactly our three
  concerns: *arguments* (claims + inferential links), *artifacts* (evidence with
  traceability), and *terminology*.
- **Isabelle/SACM** — arXiv:2009.12154. Integration of mechanized formal proof into SACM
  assurance cases. SACM claims admit **structured expressions**, so a formal statement
  (`∀ σ, evalStmt f σ ≈ spec_f σ`) embeds directly in the claim rather than being
  paraphrased in prose; proof results become first-class artifacts referenced by those
  claims. We port that pattern to Lean.
- **Envelope**: in-toto Statement v1 / SLSA style — `subject` (the evidence files, by
  sha256 digest) + `predicateType` + `predicate` (the SACM case). Provenance and
  transport are not our problem to solve.
- **Domain precedent** for arguing *from* formal evidence: DO-178C / DO-333 (formal
  methods supplement), ISO 26262. Tooling precedent: ACCESS (arXiv:2403.15236),
  Adelard/ASCE, AMASS/OpenCert.

Ours is only the last mile: the domain-specific evidence types below and their
combination rules.

## Node vocabulary (the profile)

| Emitted `sacmClass` | SACM / GSN counterpart | Use here |
|---|---|---|
| `Claim` | Claim / GSN Goal | Top claim `G1`, sub-claims `G2`–`G5`, defeaters `D*` |
| `Claim` with `assumed: true` | Assumption (GSN oval) | One per hole label; plus context claims `C*` |
| `ArgumentReasoning` | ArgumentReasoning / GSN Strategy | `S1`: decomposition over failure modes |
| `ArtifactReference` | ArtifactReference / GSN Solution | `E1`–`E5`, each naming a file on disk |
| `AssertedRelationship` | AssertedInference / AssertedEvidence / AssertedChallenge | typed `SUPPORTS` or `COUNTERS` |
| `TerminologyElement` | TerminologyPackage | *hole*, *verifiable core*, *conformance rate*, *axiom basis* |

`toBeSupported: true` is GSN's undeveloped-goal diamond.

## Evidence types

| Id | Metric | Source artifact | Produced by |
|---|---|---|---|
| `E1` | conformance rate (`agree/total`, divergence count, runtime) | `conformance.json` | `scripts/differential.py` |
| `E2` | verifiable-core fraction, hole occurrences, distinct causes | `ast-<Module>.json` | `cartographer/export_ast.sc` |
| `E3` | mutation score (`killed/total`) | `mutation.json` | `scripts/mutate.py` (source-level mutation gate) |
| `E4` | axiom basis, theorem count | `axioms.json`, falling back to `audit.json`'s `axiom_sweep` | `#audit_axioms` (`Autoform/Harness/Audit.lean`) |
| `E5` | population context: function count, purity, effect histogram | `formalization-graph.json` | `cartographer/formalization_graph.sc` |

`E5` is **context, not support**: the formalization graph is corpus-scoped, not
module-scoped, so it is attached to the strategy with an explicit context claim saying so.

## The argument structure

```
G1  module M behaves as specified
└── S1  argue over the four independent failure modes
    ├── G2  faithfulness   — semantics + transpiler agree with the real runtime   ← E1
    ├── G3  coverage       — every function translated without holes              ← E2
    │   └── G3.1  the hole-free verifiable core is analysable unconditionally
    ├── G4  adequacy       — the specifications are non-vacuous                   ← E3
    └── G5  proof validity — kernel-checked, no unsound axiom                     ← E4
    + one Assumption node per distinct hole label
```

The four legs are chosen to be the four independent ways the pipeline can be wrong
(STRATEGY.md §5): the semantics may not match the runtime; the translation may be
incomplete; the specification may be vacuous; the proof may rest on an unsound basis.

## Status lattice

| Status | Meaning |
|---|---|
| `SUPPORTED` | threshold met, no unaddressed defeater |
| `WEAK` | threshold met, but a defeater or provenance gap is unaddressed |
| `UNSUPPORTED` | evidence exists but does not reach the threshold |
| `DEFEATED` | evidence exists and *contradicts* the claim |
| `UNDEVELOPED` | no evidence artifact at all — GSN undeveloped goal |
| `ASSUMED` | asserted without support, on purpose, and visibly |

Order: `UNDEVELOPED ≈ DEFEATED < UNSUPPORTED < WEAK < SUPPORTED`.

## Combination rules — when does a claim count as supported?

**R0 (conjunction).** A parent claim is at most as strong as its weakest supporting leg.
There is no averaging: 3/4 legs green does not make a claim 75% true. Ties at rank 0
resolve to `DEFEATED` over `UNDEVELOPED` — a refuted leg is worse news than an unexamined
one.

**R1 (faithfulness, `G2`).** `SUPPORTED` iff `total > 0` and `divergences == 0` and
`agree == total`. If `divergences > 0` the claim is `DEFEATED` — a single divergence
refutes the semantics on that corpus and nothing else in the case can repair it. If
`total == 0` the claim is `UNSUPPORTED`, **not** supported: a vacuous oracle is not
evidence, it is an untested claim wearing a green tick. (This is exactly `cachetools`,
which yielded zero comparable cases — §13 Tier 2.3.) If `conformance.json` carries no
`module` tag, the artifact cannot be attributed, so any positive result is capped at
`WEAK`; if it is tagged for a *different* module the leg is `UNDEVELOPED`.

**R2 (coverage, `G3`).** `SUPPORTED` iff the module has zero holes. Any hole makes it
`UNSUPPORTED`. The restricted claim `G3.1` — that the *hole-free core* is analysable
unconditionally — can still be `SUPPORTED`, and is the honest thing to assert.

**R3 (adequacy, `G4`).** `SUPPORTED` iff every mutant is killed. Surviving mutants mean
the corresponding theorems do not constrain the behaviour they appear to. Absent `mutation.json`, `UNDEVELOPED`: the dependency-vacuity check in `Demo.lean` is necessary
but not sufficient, so its presence must not be mistaken for this evidence.

**R4 (proof validity, `G5`).** Any axiom leak reported by the sweep is a defeater. `DEFEATED` if `sorryAx` appears anywhere in the axiom
basis. `SUPPORTED` only if at least one theorem is recorded and the basis is confined to
`Classical.choice`, `propext`, `Quot.sound`. Zero theorems is `UNSUPPORTED` — nothing to
validate is not the same as validated.

**R5 (holes become assumptions).** Every distinct hole label becomes a named `Assumption`
node carrying its occurrence count and example sites, linked to both `G3` and `G1`. An
untranslated construct is not an absence from the argument; it is a premise the argument
rests on, and it must be readable as one.

**R6 (top claim, `G1`).** Assertable only if R0 gives `SUPPORTED` **and** the assumption
set is empty. Holes are an independent blocker: an argument resting on assumptions cannot
assert unconditional behaviour however green its sub-claims look. The blockers are listed
on the node.

**R7 (nothing vanishes).** A claim with no evidence is emitted as `UNDEVELOPED`, never
omitted. Absence of a node must never be usable as absence of a problem.

## Usage

```sh
scripts/sacm.py --module Cachetools [--out sacm-Cachetools.json] \
                [--markdown sacm-Cachetools.md] [--root .] [--quiet]
```

Reads whichever artifacts exist and degrades gracefully, marking the rest `UNDEVELOPED`.
Writes an in-toto Statement whose predicate is the SACM case, and prints a readable
argument tree so a reader can locate the trust boundary in seconds. **Exit status is 0
only if the top claim is assertable**, so it works directly as a CI gate.
