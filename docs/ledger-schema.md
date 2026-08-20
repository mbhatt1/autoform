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
| `Claim` | Claim / GSN Goal | Top claim `G1`, sub-claims `G2`–`G5` and their narrowed siblings `G2.1`, `G2.2`, `G3.1`, `G3.2`, `G5.1`, defeaters `D*` |
| `Claim` with `assumed: true` | Assumption (GSN oval) | One per hole label; plus context claims `C*` |
| `ArgumentReasoning` | ArgumentReasoning / GSN Strategy | `S1`: decomposition over failure modes |
| `ArtifactReference` | ArtifactReference / GSN Solution | `E1`–`E6`, each naming a file on disk, each tagged `evidenceKind` |
| `AssertedRelationship` | AssertedInference / AssertedEvidence / AssertedChallenge | typed `SUPPORTS` or `COUNTERS` |
| `TerminologyElement` | TerminologyPackage | *hole*, *verifiable core*, *conformance rate*, *axiom basis*, *tested, not proved*, *coverage of a claim* |

`toBeSupported: true` is GSN's undeveloped-goal diamond.

## Evidence types

| Id | Metric | Source artifact | Produced by |
|---|---|---|---|
| `E1` | conformance rate (`agree/total`, divergence count, runtime) | `conformance.json` | `scripts/differential.py` |
| `E2` | verifiable-core fraction, hole occurrences, distinct causes | `ast-<Module>.json` | `cartographer/export_ast.sc` |
| `E3` | mutation score (`killed/total`) | `mutation.json` | `scripts/mutate.py` (source-level mutation gate) |
| `E4` | axiom basis, theorem count | `axioms.json`, falling back to `audit.json`'s `axiom_sweep` | `#audit_axioms` (`Autoform/Harness/Audit.lean`) |
| `E5` | population context: function count, purity, effect histogram | `formalization-graph.json` | `cartographer/formalization_graph.sc` |
| `E6` | call-closed core (`verifiableCore`), `dynamicHoleRisk` | `ledger-<Module>.json` | `Program.ledgerJson` (`Autoform/Ledger.lean`) |

`E5` is **context, not support**: the formalization graph is corpus-scoped, not
module-scoped, so it is attached to the strategy with an explicit context claim saying so.

## The argument structure

```
G1  module M behaves as specified
└── S1  argue over the four independent failure modes
    ├── G2  faithfulness   — over ALL translated functions   [coverage-capped, R8]  ← E1
    │   ├── G2.1  … over the functions the harness EXERCISED  [TEST, not PROOF]
    │   └── G2.2  … over the remainder, never reached         [UNDEVELOPED]
    ├── G3  coverage       — every function translated without holes            ← E2
    │   ├── G3.1  the hole-free AND call-closed core is statically clean [STATIC] ← E6
    │   └── G3.2  that core is hole-free at RUNTIME too       [needs execution]
    ├── G4  adequacy       — the specifications are non-vacuous                 ← E3
    └── G5  proof validity — kernel-checked, no unsound axiom                   ← E4
        └── G5.1  … over the repository the sweep actually covers  [PROOF]
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

### Evidence kind — orthogonal to status

Status says *how strong the result was*; `evidenceKind` says *what kind of thing was
done*. They are independent axes and collapsing them is how a green tick comes to read as
a proof.

| `evidenceKind` | Means | Quantifies over |
|---|---|---|
| `PROOF` | kernel-checked in Lean | all inputs |
| `TEST` | sampled execution against an independent oracle | the sample |
| `STATIC` | computed from the artifact itself | the artifact, as an **upper bound** (§17) |

A claim with `evidenceKind: TEST` is never a proved claim, however green. `proved` is
emitted on every claim node so a reader cannot miss the distinction, and `G1` carries an
explicit blocker saying faithfulness is tested rather than proved. This is the SACM-side
statement of what `Autoform/Ledger.lean` prints as
`NOT PROVED : transpiler faithfulness — see conformance.json`. **The two artifacts now say
the same thing**: `G2.1` is `SUPPORTED; TEST`, and neither `G2` nor `G1` asserts that
faithfulness is proved.

### Coverage — stated on every quantified claim

Every claim quantified over a population carries a `scope` object naming that population,
how much of it the evidence touched, and the resulting fraction. A status with no stated
scope is not interpretable, so scope is emitted even when coverage is total.

## Combination rules — when does a claim count as supported?

**R0 (conjunction).** A parent claim is at most as strong as its weakest supporting leg.
There is no averaging: 3/4 legs green does not make a claim 75% true. Ties at rank 0
resolve to `DEFEATED` over `UNDEVELOPED` — a refuted leg is worse news than an unexamined
one.

**R8 (coverage bound — applies to every rule below).** A claim quantified over a
population may not be `SUPPORTED` unless the evidence touched **all** of that population.
Coverage ≥ 80% caps at `WEAK`; below that, `UNSUPPORTED`. The fraction is recorded in the
claim's `scope`, and where coverage is partial an undefeated **coverage defeater** (`D2`)
is attached to the claim.

This rule exists because of a real over-claim: `G2` read `SUPPORTED` off 104 agreeing
cases covering **92 of 238 functions**, a claim quantified over "the translated functions"
resting on evidence touching 39% of them. `divergences == 0` says nothing whatever about
the 146 functions no case reached.

*The preferred remedy is not the cap.* Where the exercised subject can be named, **narrow
the claim to it and add a sibling goal for the remainder**. Narrowing keeps the claim
*true*; capping the status of an over-broad claim leaves a false claim on the page with a
hedge attached, and hedges are what readers skip. The cap is the fallback for when the
covered subset cannot be named.

**R9 (proved ≠ tested).** `evidenceKind` is recorded on every claim and every artifact
reference, and a `TEST`-discharged claim never counts as proved regardless of status. `G1`
asserts behaviour for all inputs, so a `TEST` faithfulness leg is an explicit blocker on
it. This keeps the assurance case in step with the trust ledger's `NOT PROVED` line
instead of contradicting it.

**R1 (faithfulness, `G2`).** Three separate questions, previously collapsed into one tick:

- *Did the compared cases agree?* `total == 0` → `UNSUPPORTED` (a vacuous oracle is an
  untested claim wearing a green tick — this is `cachetools` before §19). `divergences > 0`
  → `DEFEATED`; a single divergence refutes the semantics on that corpus and nothing else
  in the case repairs it. `agree == total > 0` → threshold met.
- *How much of the subject was compared?* R8. `G2.1` is narrowed to the
  `functions_covered` the harness actually exercised and may be `SUPPORTED` there; `G2.2`
  covers the remainder and is `UNDEVELOPED` because there is no evidence about it at all;
  `G2` is their conjunction, additionally coverage-capped.
- *What kind of evidence is it?* `TEST` (R9). Real evidence — it is how floored modulo,
  short-circuit evaluation, `-INT_MIN` and private name mangling were caught — but it is
  not a theorem.

Provenance is unchanged: an untagged `conformance.json` caps any positive result at
`WEAK`; one tagged for another module makes the leg `UNDEVELOPED` and **no** `G2.1`/`G2.2`
are synthesised from it.

**R2 (coverage, `G3`).** `SUPPORTED` iff the module has zero holes; any hole makes it
`UNSUPPORTED`. The restricted claims are where the earned status lives, and §17 forces
them apart:

- `G3.1` — the **hole-free *and* call-closed** core (`verifiableCore` from
  `ledger-<Module>.json`, E6) is *statically* free of untranslated constructs. `SUPPORTED`,
  `evidenceKind: STATIC`, with the core's size in `scope`. Static hole-freedom alone is
  **not** enough: a call to an untranslated function is indistinguishable in the AST from a
  call to a translated one, so without the ledger's call-closure figure the claim is capped
  at `WEAK` and says so.
- `G3.2` — that core is hole-free *at runtime*. This is what a reader hears `G3.1` say, and
  static analysis cannot discharge it: `dynamic-hole risk` counts the constructs that may
  hole on some input. `SUPPORTED` only when that risk is 0; otherwise it starts at `WEAK`
  and is coverage-capped by how many functions execution has actually reached (R8) — 92/238
  on `cachetools`, hence `UNSUPPORTED`.
- Defeater `D3` records the reason: `Func.total` is computed from the same AST it
  describes, so it cannot see what the interpreter does with that AST.

**R3 (adequacy, `G4`).** `SUPPORTED` iff every mutant is killed, `evidenceKind: TEST`.
Absent `mutation.json`, `UNDEVELOPED`. Mutation evidence scoped to a different subject is
`UNDEVELOPED`, not borrowed: the gate runs over the Imp reference semantics, not over
translated modules, so its score is real but off-subject.

**R4 (proof validity, `G5`).** `DEFEATED` if `sorryAx` or any leak appears in the basis.
Otherwise `SUPPORTED` requires at least one recorded declaration **and** a basis confined
to `Classical.choice`, `propext`, `Quot.sound` **and** module scope. The fallback source
`audit.json:axiom_sweep` is **repo-wide**, so by the same provenance standard applied to
`conformance.json` and `mutation.json` it caps `G5` at `WEAK` — it is not off-subject (the
module is interpreted by the very environment that was swept), but it is not evidence about
theorems specific to this module, of which there are none. What the sweep *does* earn is
asserted as the narrowed sibling `G5.1`, `SUPPORTED; PROOF`, over the repository, with the
`lean4checker` result attached and a context claim `C2` saying so. Zero declarations is
`UNSUPPORTED`.

**R5 (holes become assumptions).** Every distinct hole label becomes a named `Assumption`
node carrying its occurrence count and example sites, linked to both `G3` and `G1`. An
untranslated construct is not an absence from the argument; it is a premise the argument
rests on, and it must be readable as one.

**R6 (top claim, `G1`).** Assertable only if R0 gives `SUPPORTED`, the assumption set is
empty, and no leg is discharged by `TEST` alone (R9). The blockers are listed on the node.

**R7 (nothing vanishes).** A claim with no evidence is emitted as `UNDEVELOPED`, never
omitted. Absence of a node must never be usable as absence of a problem. The converse
matters as much: rules R8/R9 must not be used to grind every claim down to `UNDEVELOPED`.
A case where everything is undeveloped is as useless as one where everything is supported.
Each restriction above comes with a narrowed sibling that states what *is* earned —
`G2.1`, `G3.1`, `G5.1` — so the case reports a real trust boundary rather than a shrug.

## Usage

```sh
scripts/sacm.py --module Cachetools [--out sacm-Cachetools.json] \
                [--markdown sacm-Cachetools.md] [--root .] [--quiet]
```

Reads whichever artifacts exist and degrades gracefully, marking the rest `UNDEVELOPED`.
Writes an in-toto Statement whose predicate is the SACM case, and prints a readable
argument tree so a reader can locate the trust boundary in seconds. **Exit status is 0
only if the top claim is assertable**, so it works directly as a CI gate.
