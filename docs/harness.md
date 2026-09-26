# The formalization harness (`autoform formalize`)

A counterexample-guided, neural-symbolic specification synthesis and verification loop
built on top of the Core interpreter. It turns a translated module into a set of
machine-checked claims, each carrying scope, property, assumptions, evidence, status and
provenance.

```
Core AST ─► CPIR ─► evidence ─► generators ─► critic ─► JUDGE ─► obligation compiler ─► Lean kernel
                                  (propose)   (reject)  (select,     (claim → Lean)        (certify)
                                                         route)                               │
                                                            ▲                    witness ◄────┘
                                                            │                       │
                                                         JUDGE ◄── repairs ◄── JUDGE (classify)
                                                         (rank)
```

**The architectural invariant.** Generators and the judge may *propose* and *rank*
hypotheses. Only deterministic machinery certifies them: the Lean kernel, and the
structural CPIR check. No status in any report is produced by a model.

| Role | Question | Component | Trusted? |
|---|---|---|---|
| Generator | What might be true? | `generator.py`: templates; optional Claude (`--generators template,llm`) | No |
| Judge | Which hypothesis is intended, useful, worth proving? What does a counterexample mean? Which repair? | `judge.py`: [SemIf (OpenJev)](https://github.com/TheoLeeCJ/SemIf-OpenJev) typed decisions | No |
| Verifier | Is it true under the model? | `verifier.py`: Lean kernel over `runFunc`; structural must-precede | Yes (TCB) |

## Running it

The module must already be translated (`autoform source`), so that
`Autoform/Generated/<Module>.lean` and `ast-<Module>.json` exist.

```sh
autoform formalize PipelineSecurityVulnerable --source path/to/source          # SemIf judge
autoform formalize PipelineC --source examples/source/c --function add --judge heuristic
autoform formalize diff old/report.json new/report.json                         # CI: exit 1 if a proof was lost
autoform formalize bench fit-temperature out/*/jevbench.jsonl --out temps.json
```

The same commands work as `python -m autoform.harness …`. Output goes to
`artifacts/harness/<Module>/`:

| File | Content |
|---|---|
| `report.md` / `report.json` | Repository summary, findings, the human-review queue, and a card for every claim |
| `certificates.json` | One certificate per kernel verdict: semantics hash, model hash, environment hash, assumptions, theorem names, artifact hash, and quantification scope |
| `ledger.json` | The assumption graph. Each assumption lists the claims that depend on it |
| `decisions.jsonl` | Every judge decision: state, question, options, logits, choice, and its downstream outcome |
| `jevbench.jsonl` | The same decisions, labeled by what verification later showed (Formalization-JEVBench) |
| `cpir.json`, `entities.json` | The canonical program IR and its deterministic entity table |
| `lean/*.lean` | The exact obligation and witness files the kernel checked |

A stale build is refused: `lake build Autoform.Generated.<M> --no-build` must succeed.
Pass `--build` to rebuild the one module. A stale `.olean` can encode an older
interpreter, and silently checking against it would be unsound.

## The judge: SemIf / OpenJev

SemIf reads option probabilities directly from a frozen model's next-token logits. A
state, a criterion and 2–16 typed options go in; one probability per option comes out,
with no generated text. The harness runs SemIf in its own interpreter as a long-lived
worker (`semif_worker.py`, JSON lines over stdio), so torch and MLX never enter
autoform's process.

Setup (Apple silicon uses the MLX backend; elsewhere, Torch):

```sh
git clone https://github.com/TheoLeeCJ/SemIf-OpenJev ~/semif
cd ~/semif && python3.11 -m venv .venv && .venv/bin/pip install -e '.[mlx]'   # or '.[test]' on CUDA
```

| Variable | Default |
|---|---|
| `AUTOFORM_SEMIF_PYTHON` | `~/semif/.venv/bin/python` |
| `AUTOFORM_SEMIF_MODEL` / `AUTOFORM_SEMIF_REVISION` | `Qwen/Qwen3.5-4B` @ `851bf6e8…` (SemIf's pinned baseline, about 9 GB) |
| `AUTOFORM_SEMIF_BITS` | unset (bf16); `8` or `4` quantize in memory |

The typed decisions are:

| Task | Options | Deterministic gate before the judge sees it |
|---|---|---|
| `PROPERTY_JUDGMENT` | USEFUL_PROPERTY, SECURITY_RELEVANT, TRIVIAL, UNSUPPORTED_BY_EVIDENCE, TOO_STRONG, TOO_WEAK, LIKELY_VACUOUS | The critic has already removed invalid, tautological, contradictory, vacuous and duplicate claims |
| `PROPERTY_SELECTION` | the candidates (listwise; chunks of 16, renormalized) | — |
| `INTENT_SELECTION` | mutually exclusive candidates | Rivalry is computed, not guessed: two claims are rivals when no function satisfies both |
| `BACKEND_SELECTION` | backends able to express the claim | Forced when only one is feasible |
| `COUNTEREXAMPLE_CLASSIFICATION` | REAL_BUG, PROPERTY_TOO_STRONG, MISSING_PRECONDITION, MODEL_INCOMPLETE, ENVIRONMENT_ASSUMPTION, SOLVER_ARTIFACT | hole or out-of-fuel ⇒ MODEL_INCOMPLETE; native run disagrees with model ⇒ MODEL_INCOMPLETE; `ub:` hole ⇒ {REAL_BUG, MISSING_PRECONDITION}; result of another sort ⇒ PROPERTY_TOO_STRONG; a rival of the chosen intent cannot be REAL_BUG |
| `REPAIR_SELECTION` | REJECT plus candidate repairs | Repairs come from the code (guards, divisors, operand widths), never from witness constants; complexity may grow by at most δ = 12 |
| `ASSUMPTION_ACCEPTABILITY` | ACCEPTABLE, UNACCEPTABLE, NEEDS_HUMAN_REVIEW | — |

Two design points came from running it:

* **Intent questions are asked without the implementation.** Shown `return True`, the
  judge rates "result is always true" as the intended contract (it matches the code).
  Claim judgment, selection and intent therefore see the name, signature, documentation,
  tests and callers. Counterexample classification, which must weigh the code against
  the claim, sees the body.
* **A finding needs support for the intent** (§31 cross-validation). A counterexample
  judged REAL_BUG is reported as a finding only if the claim has an independent evidence
  source (test, documentation, assertion, guard, caller), or if it is, or is implied by,
  the judge's chosen intent with probability at least 0.8. Otherwise it is a *suspected
  bug* in the human-review queue.

`--judge heuristic` uses the deterministic priors each task computes anyway. It is
reproducible and needs no model, and it is noticeably worse at intent.
`--judge replay:decisions.jsonl` replays recorded scores for audits and tests. SemIf's
scores are uncalibrated. `bench fit-temperature` fits one temperature per task on
verifier-labeled rows; this changes probabilities, never the argmax.

## Claims

Claims are JSON in a small typed grammar (`claims.py`). Terms are `{"param": V_id}`,
`{"result": true}`, literals, and `ADD SUB MUL NEG LEN`. Formulas are comparisons,
`AND OR NOT IMPLIES IFF`, the outcomes `RETURNS THROWS TERMINATES`, and the structural
predicates `CALLS NOT_CALLS BEFORE WRITES NO_WRITE`. The temporal, taint and resource
predicates of the design (`ALWAYS EVENTUALLY UNTIL FLOWS_TO NO_FLOW OWNED BALANCED …`)
parse and type-check, but no available backend expresses them, so they are reported as
UNSUPPORTED.

A claim may name only entities CPIR assigned (`F_0003`, `V_0002`), so a hallucinated
identifier is a validation error. Claim ids hash qualified *names*, not positional
ids, so a claim keeps its id across commits and the diff can match it.

## Verification

For each module, claims are compiled to Lean in chunks of 24. Each chunk runs twice:

1. **Universal attempt.** `af_eval` (emitted into the obligation file) head-normalizes
   every `runFunc …` by unfolding and iota-reduction. It then closes the goal with
   `simp`/`decide`/`omega`. The rewrite is a `change`, so the kernel re-checks it by
   definitional equality. `--deep-proofs` uses the full `portfolio` instead (slow).
   Result: **PROVED**.
2. **Bounded proof.** `decide +kernel` over an explicit finite domain: small values,
   program literals, and the bounds of each parameter's declared integer type (a `u8`
   never receives −2). Result: **BOUNDED_PROVED** over that domain, never "proved".
3. **Witness.** A compiled `#eval` searches the domain for a failing point. That is
   only a *candidate*: the second run proves `chk w = false` by `decide +kernel`.
   Result: **REFUTED** with a kernel certificate. If compiled evaluation and the kernel
   disagree, the result is **INCONSISTENT_MODEL**.

Every accepted theorem uses only `propext`, `Classical.choice` and `Quot.sound`.
Witnesses whose model outcome is `hole` or `outOfFuel` are **MODEL_INCOMPLETE**.
Holes labeled `ub:` are the C interpreter's explicit undefined behavior, such as signed
overflow or an out-of-range shift count. They stay **REFUTED** and are classified like
any other defect. For top-level Python functions, the witness is replayed natively, and
agreement or disagreement with the model is recorded.

The capability matrix (`verifier.BACKENDS`) lists Z3, CHC, CBMC, angr and a model
checker with `available: false` and a reason. Routing never sends a claim to them. Wiring
one in means giving it a lowering and a certificate story, not just a solver call.

## Confidence

Three scores are kept apart on every claim: `intent_confidence` (judge and evidence),
`model_confidence` (block coverage × external-summary coverage × native agreement), and
`proof_confidence` (from the kernel status). A kernel proof of a claim nobody
intended shows high proof confidence next to low intent confidence, and the report
prints both.

## Limits

* **Soundness contract.** `Proof(c) ⇒ Semantics_M(P) ⊨ c` for the Core interpreter M at
  this build. The unmodified trust story of [trust-model.md](trust-model.md) applies.
* **Coverage.** Universal proofs close when symbolic evaluation reaches a closed form.
  Branching on symbolic inputs usually leaves a case split the ladder does not close, so
  those claims end BOUNDED_PROVED.
* **`BEFORE` is call order.** A check whose result is ignored still "precedes". A
  result-guarded predicate needs dataflow and is not implemented.
* **Environment.** Filesystem, network, time, randomness, databases and concurrency are
  not modeled. Execution is assumed single-threaded (`A_SINGLE_THREADED`), and any
  unresolved callee is UNSUPPORTED unless `--environment` declares a summary:

  ```json
  {"externals": [{"name": "verify_ed25519", "semantics": "UNINTERPRETED", "trust_class": "assumed"}]}
  ```
* **The LLM generator** (`--generators llm`) calls Claude with structured output and
  validates every candidate. Its output is subject to the same critic and judge. It is
  optional; the default generator is deterministic.
* **Judge quality is model quality.** The zero-shot 4B baseline separates intended
  readings well when names carry intent (see the example below), and weakly when they do
  not. `jevbench.jsonl` is the training signal for doing better.

## Example (snapshot, 2026-09-25, uncommitted work on `d8aec57`)

The PipelineSecurity fixtures run with the SemIf judge (Qwen3.5-4B, MLX, bf16). The
vulnerable `authorize` body is `return True`. Among eight mutually exclusive readings,
the judge picks `result ↔ owner = caller` as the intent (p ≈ 0.90). Lean refutes it at
`owner=-2, caller=-1`, native Python agrees, and it is reported as a finding. On the
fixed module, the same claim is BOUNDED_PROVED and there are no findings. The diff from
fixed to vulnerable reports both owner-only claims as lost and exits 1:

```sh
autoform formalize diff artifacts/harness/Fixed/report.json artifacts/harness/Vulnerable/report.json
```

To regenerate, run the commands above. The numbers move with the judge model, the
templates and the interpreter.
