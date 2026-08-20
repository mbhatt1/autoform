# The trust model

What this system actually claims, on what basis, and — more importantly — what it does not
claim. If you read one document in `docs/`, read this one.

The deliverable is **not** "your codebase is verified." It is a precise, machine-generated
statement of *what is proved, about what model, under what assumptions*, such that a
reader can locate the trust boundary in seconds. That artefact is the trust ledger
(`ledger-<Module>.json`, `Autoform/Ledger.lean`) and the assurance case
(`sacm-<Module>.json`, `scripts/sacm.py`).

---

## 1. The one rule everything else follows from

> **A check that shares an assumption with the thing it checks will flatter it.**

This is not a slogan; it is the observed failure mode of this project, four separate times:

* A **coverage** metric computed by folding over an AST cannot see what the interpreter
  does with that AST. Static hole-freedom had to be corrected downward twice — once for
  synthetic front-end wrappers counted as real functions, once because an untranslated
  callee is, in the AST, indistinguishable from a translated one.
* A **dependency-vacuity** check (`#audit_depends`) cannot see whether a theorem
  *constrains* what it mentions. The mutation gate scored a soundness theorem WEAK because
  the relation's side conditions were stated in terms of the very function being mutated,
  so a mutation changed both sides of the equation.
* A **translated specification** cannot see that the translation destroyed its content.
  Python determinism tests (`f(x) == f(x)`) transliterated into Lean become `rfl`, because
  purity makes them contentless. Spec *translation* is not spec *preservation*.
* An **oracle reading a stale cache** shares the *previous* artefact's assumptions, which
  is worse than having no oracle: it produced ten confident, specific, wrong divergences
  before being noticed.

The defence is always the same: an oracle that does **not** share the artefact's
assumptions. For semantics that is the real runtime; for specifications it is mutation;
for coverage it is execution; for proofs it is an independent kernel replay. Any number
reported without one should be read as an upper bound.

## 2. The four oracles

They are not redundant. Each sees a class of failure the others are structurally blind to,
which is the argument for paying for all four.

### 2.1 Differential testing — catches *semantics that disagree with reality*

`scripts/differential.py`. Runs the repository's own test suite under a `sys.settrace`
hook, recording `(function, receiver, args, outcome)` for every call landing in a
translated function, then replays exactly those tuples against the Lean interpreter and
compares structured values and exceptions.

Blind spots of every other oracle that this one covers: a proof about a semantics that
does not match the runtime is theater, and *no amount of proving surfaces it* — the proofs
would all be about the wrong `eval`. Every one of the following was found here, not by
inspection:

* Floored vs truncated `%` and `/` — which had silently mistranslated every C and Java
  program, and which is why the semantics is now dialect-parameterized.
* Short-circuit evaluation: `b != 0 and a % b == 0` divided anyway. This had been
  "conservative" (a hole) until exceptions were added, at which point it became an actively
  wrong answer. **Fidelity work makes other fidelity bugs findable — the gaps are not
  independent.**
* Python private name mangling (`__x` → `_Cls__x` inside a class body): a silently wrong
  field read returning `unit`.

Three discipline rules this oracle operates under, each earned:

* **Outcomes are three-valued, never two**: agree / diverge / INCONCLUSIVE. A case that
  was not actually compared is never reported as passing. That is the cardinal sin here.
* **The oracle must establish it is reading the current artefact before it reports
  anything** — it `lake build`s the generated module first. That check belongs in the
  oracle, not in the caller.
* **An oracle must never report a disagreement it caused itself.** Receiver addresses are
  computed Lean-side and verified before comparison; representability of encoded values is
  checked recursively and *fatally*, so an unencodable nested value refuses the case rather
  than surfacing as a confident divergence. Fault injection confirms the guards fire.

The corresponding temptation, and the one that would destroy the number's meaning: fixing
the *measurement* to match a broken artefact. Exposing unmangled field aliases in the value
encoder would have made the numbers agree while leaving the transpiler wrong. Refusing that
is what keeps the conformance rate worth reading.

Strictness in an oracle buys **accuracy**, not just safety: the stricter the refusal, the
more of the remaining agreements mean something.

### 2.2 The mutation gate — catches *specifications that constrain nothing*

`scripts/mutate.py`. Injects a bug into the implementation, rebuilds, and asks whether the
theorem still proves. Mutant killed → the theorem has teeth. Mutant survived → the theorem
is vacuous with respect to that bug, and is scored a **failure**, not a success.

This is the *sufficient* anti-vacuity test. `#audit_depends` (dependency vacuity) is
*necessary but not sufficient*, and the gap between them is not hedging: a theorem can
mention a definition and still say nothing about it. Cheap check first, expensive check
second.

For generated modules the gate mutates `Autoform/Generated/<M>.lean` — the actual
transpiler output — and rebuilds `Autoform/Specs/<M>Spec.lean`, so the file mutated is the
subject of the theorems. Stating specifications about generated code *by import* rather
than by copying terms into the spec file is what makes this possible at all.

Known measurement caveat, stated rather than smoothed: when a mutant makes a module fail
to compile, every theorem in that module is recorded as having killed it, so per-theorem
attribution is coarse. The aggregate claim is sound; the per-theorem breakdown is not yet
trustworthy.

### 2.3 Axiom sweep + `leanchecker --fresh` — catches *unsound proofs*

`scripts/audit_all.py`, three independent checks:

1. **Axiom sweep** — every declaration in the built library is asked what it stands on via
   `Lean.collectAxioms`. `sorryAx` means "not proved at all"; `Lean.ofReduceBool` /
   `ofReduceNat` mean "the Lean compiler was trusted". Either is a trusted-code leak.
2. **Source sweep** — greps for the escape hatches that do not appear as axioms: `sorry`,
   `partial`, `unsafe`, `native_decide`, `@[implemented_by]`, `axiom`. Comments and
   docstrings are stripped first, so prose *about* `sorry` is not reported as one. The Core
   semantics is *claimed* to be free of all of these; this verifies the claim rather than
   restating it.
3. **Kernel re-verification** — `leanchecker` replays the compiled `.olean`s through the
   kernel from an empty environment.

Three things about check 3 are load-bearing:

* `leanchecker` **ships with the Lean toolchain** (v4.28.0+). The standalone `lean4checker`
  is deprecated; there is nothing to install and no Homebrew formula.
* **`--fresh` is mandatory.** Without it the checker can silently no-op on a module that has
  only imports and no declarations of its own — which is exactly the shape of
  `Autoform.lean`. The naive invocation produces a confident VERIFIED that checked nothing.
  The audit records *which mode ran*, because the two are not equally strong.
* **A missing checker is UNVERIFIED, never a pass**, and `--strict` (which CI uses) turns
  that into a build failure. An oracle that silently skips is worse than no oracle.

That the checker actually rejects bad input has been demonstrated twice rather than
assumed: by installing a bogus declaration with `Environment.addDeclCore (doCheck := false)`,
and by tampering with a copy of this project's own build tree. Both are rejected; the
untampered control passes. "Exit 0" is exactly the shape a no-op takes, so a green result
from an unexercised checker proves nothing.

### 2.4 Execution — catches *coverage claims that static analysis flatters*

`scripts/core_oracle.py`. The ledger's hole-free / call-closed / dynamic-hole-risk figures
are all computed by static analysis of the same AST they describe. So this oracle does not
analyse: it **runs** every function in the claimed core through the interpreter over many
inputs and reports which ones actually never hole.

It was not built on suspicion. Static hole-freedom has already been corrected downward
twice, and the ledger's own `dynamic-hole risk` count is the static analysis admitting
there are constructs it cannot adjudicate. There is no argument that call-closure was the
last correction.

Its discipline mirrors the differential harness: a function nothing exercised is
INCONCLUSIVE, never verified; `outOfFuel` is its own bucket because fuel exhaustion proves
nothing in either direction; and it rebuilds before reporting.

A fifth source of findings deserves a mention because it was not planned as an oracle at
all: **proof itself catches operations that were never given a specification.** Unary minus
kept returning mathematical negation after `Numeric.lean` was wired into binary operators,
so `-INT_MIN` evaluated to a value that does not exist in a 32-bit integer. No differential
test negated `INT_MIN`; the refinement layer found it, because stating
`applyUnop_int_neg` as an unconditional `rfl` made the unconditionality itself visibly
wrong.

## 3. The assurance case: G1–G5

`scripts/sacm.py` emits a SACM (OMG *Structured Assurance Case Metamodel* v2.1) profile —
the model is not ours, only the domain-specific evidence types and their combination rules
are. `docs/ledger-schema.md` specifies the node vocabulary.

The argument decomposes the top claim over the **four independent ways the pipeline can be
wrong**:

| Goal | Claim | Evidence | Kind |
|---|---|---|---|
| **G1** | The module behaves as specified. | roll-up of G2–G5 | — |
| **G2** | Faithfulness: the Lean semantics agrees with the real runtime on this module. | `conformance.json` | TEST |
| **G3** | Coverage: the module is translated without holes. Split into **G3.1** (the call-closed verifiable core) and **G3.2** (the claim people actually read G3.1 as making — that these functions do not hole at runtime), the latter answerable only by execution. | `ast-*.json`, `ledger-*.json`, `core-oracle.json` | STATIC / TEST |
| **G4** | Adequacy: the specifications are non-vacuous — they constrain the behaviour they appear to. | `mutation.json` | TEST |
| **G5** | Validity: all theorems are kernel-checked and depend on no unsound axiom. **G5.1** narrows this to what the repo-wide sweep actually earns. | `audit.json` | PROOF |

Two structural rules keep the roll-up honest:

* **Evidence kind is tracked separately from strength** (`PROOF` / `TEST` / `STATIC`). A
  claim discharged by kernel-checked proof and one discharged by a hundred passing test
  cases are not the same assertion even when both meet threshold. Blurring test evidence
  into a green tick that reads as proof is the thing the ledger's own
  `NOT PROVED : transpiler faithfulness` line exists to prevent.
* **Population-quantified claims are capped by coverage.** "Zero divergences" over cases
  touching a minority of the module's functions says *nothing whatsoever* about the rest,
  yet the earlier rule flipped the claim to SUPPORTED. Support is now bounded by the
  fraction of the subject the evidence actually exercised — and the preferred fix is to
  *narrow the claim*, not to weaken its status, because weakening the status of an
  over-broad claim leaves a false claim on the page.

Evidence that cannot be attributed to its subject cannot fully support a claim about that
subject. This rule has already fired three times: on an untagged `conformance.json`, on a
mutation run whose subject was a different module, and on the repo-wide axiom sweep.

## 4. The three statuses (there are five, and the distinction is the point)

| Status | Meaning |
|---|---|
| `SUPPORTED` | Threshold met, no unaddressed defeater. |
| `WEAK` | Threshold met, but a defeater is unaddressed or the evidence is not attributable to this subject. |
| `UNSUPPORTED` | **We checked, and the evidence does not reach the threshold.** |
| `DEFEATED` | We checked, and the evidence *contradicts* the claim. |
| `UNDEVELOPED` | **We never checked.** No evidence is cited at all — GSN's undeveloped-goal diamond. |

`UNSUPPORTED` and `UNDEVELOPED` are the pair worth staring at. "We looked and it is not
established" and "nobody has looked" are different epistemic states, and collapsing them —
in either direction — is how assurance cases become decoration. The combination rule is
conjunctive (an argument is only as strong as its weakest leg) and `UNDEVELOPED` and
`DEFEATED` share the bottom rank, with ties broken toward `DEFEATED`, because a refuted leg
is worse news than an unexamined one.

Missing evidence is therefore **never omitted**: a claim with no supporting artefact is
emitted as an `UNDEVELOPED` node with `toBeSupported: true`. Silently dropping it would
manufacture confidence.

Likewise every hole label becomes a named SACM `Assumption`. An untranslated construct is
not an absence — it is an assumption the argument rests on, and it must appear in the
argument structure.

A top claim coming out `UNDEVELOPED` on a real corpus is the **correct** answer, not a bug
in the tool.

## 5. What this system does NOT establish

Stated plainly, because the value of everything above depends on it.

* **Transpiler faithfulness is tested, never proved.** There is no theorem relating the
  Joern CPG, the exported JSON, the printed Lean term, and the source program's actual
  meaning. The evidence is differential testing on the corpus's own test suite plus the
  determinism of the printer. The ledger prints `NOT PROVED : transpiler faithfulness` for
  exactly this reason, and G2 is `TEST` evidence, never `PROOF`.
* **Conformance is sampling, not quantification.** It covers the cases the repository's
  test suite exercises, on values the harness can faithfully encode. Functions the suite
  never reaches, arguments it cannot encode (floats, sets, locks, very wide containers),
  and receivers Core cannot represent as objects (`tuple`/`dict` subclasses) are refused
  and counted, not compared. These structural ceilings bound how much of a real codebase
  this oracle can reach *regardless of translation coverage*.
* **Hole-freedom does not imply the program runs.** It is an upper bound. Call-closure
  removes the invisible-callee failure mode; execution is what settles the rest.
* **A verified core is not a verified repository.** You will never formalize the whole
  codebase; that is a design decision. Everything outside the core is covered by declared
  assumptions and boundary contracts.
* **The axiom sweep is repo-wide, not module-scoped.** It bounds the axiom basis of
  everything in the repository, including the semantics a given module is interpreted by,
  but it is not evidence about theorems specific to that module. G5 is capped accordingly.
* **The proof portfolio does not prove much yet.** Tiers 1–2 are real (including
  `bv_decide`, whose LRAT certificate is kernel-checked, so it adds no trusted code); the
  external SMT path produces an *opinion recorded on an open obligation* and cannot close a
  goal, because no Lean proof is reconstructed from a solver's answer; the neural tier is
  off by default and its output is untrusted text that must re-elaborate and pass screening
  like any other candidate.
* **Nothing here is a security claim.** Effect classification is a heuristic over pattern
  lists, not a soundness result.

## 6. How to check any of this yourself

Do not trust a number printed in a document, including this one. Every figure in this
repository is regenerable, and regenerating it is cheaper than arguing about it.

```sh
lake build && python3 scripts/audit_all.py --strict   # axioms, escapes, kernel replay
cat audit.json                                        # incl. which leanchecker mode ran
python3 scripts/differential.py ast-<M>.json <src> <M> 5 && cat conformance.json
python3 scripts/core_oracle.py ast-<M>.json <M> <src>  && cat core-oracle.json
python3 scripts/mutate.py <lean-file> <module>         && cat mutation.json
python3 scripts/sacm.py --module <M>                   && cat sacm-<M>.json
cat ledger-<M>.json
```

If a document and an artefact disagree, the artefact wins and the document is a bug.
