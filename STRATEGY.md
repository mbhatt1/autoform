# autoform — turning arbitrary codebases into autoformalized Lean 4

## 0. The central bet

Do **not** try to translate code directly into Lean definitions and then guess theorems
about them. That is the failure mode of every naive "LLM → Lean" pipeline: the
translation is unfaithful, nothing checks the faithfulness, and the theorems are
vacuous or trivially true.

Instead: **formalize the language, not the program.**

1. Build (or import) a **definitional interpreter** for the source language *inside Lean*:
   `Syntax` inductive types + `step : Config → Option Config` / `eval : Env → Expr → Value`.
   This is the semantic kernel. It is written once per language, reviewed hard, and reused.
2. Mechanically **transpile the codebase into a term of that `Syntax` type** — a deep
   embedding. This step is a parser + printer, not an LLM: it is total, deterministic,
   and diff-testable.
3. Now every property about the program is a theorem *about `eval` applied to a
   concrete AST*. Specifications become statable, and — crucially — **checkable against
   reality** by differential-testing `eval` against the real runtime.
4. Layer a **shallow embedding** on top for tractability: prove once that the deep term
   is observationally equivalent to a clean Lean function, then reason in the clean
   world (this is the Aeneas/`hax` playbook and it is the only thing that scales).

The agentic system's job is everything the compiler can't do: **choosing what to
formalize, inventing the specification, discovering invariants, and driving proof
search** — with the Lean kernel as an unfakeable oracle at every step.

## 1. Why this is now feasible off-the-shelf

Reusable open-source pieces, by layer:

**Front end / parsing (language → AST, no LLM)**
- `tree-sitter` — grammars for ~50 languages, error-tolerant, uniform CST API.
- Language-native: `libclang`, `rustc`/`charon`, `go/ast`, `ast` (Python), `ts-morph`.
- LLVM IR / MLIR as a convergence point for compiled languages.
- WebAssembly as a *universal* target: one small semantics covers everything that
  compiles to Wasm. There are already Wasm semantics in Coq (Wasmcert) and K.

**Existing formal semantics you should steal rather than rebuild**
- **K framework**: complete executable semantics for C (`C-semantics`), Java, JavaScript,
  Python, EVM (KEVM), LLVM, x86. These are the single largest asset in the field.
  Strategy: use K semantics as the *reference oracle* and as the spec you port to Lean.
- **CompCert** (C, Coq), **CakeML** (ML, HOL4), **JSCert/JSExplain** (JS, Coq),
  **Iris/RustBelt** (Rust concurrency, Coq) — port targets, and correctness benchmarks.
- **Aeneas** (Rust → pure functional Lean, via `charon`) — *already emits Lean 4*.
  For Rust, this is essentially step 1–3 done for you.
- **hax** (Rust → F*/Coq/**Lean**) — same, different subset, panic-freedom focus.
- **Lampe** (Noir → Lean), **Verus**/**Kani**/**Creusot** (Rust, SMT tier).
- **Lean core**: `Std`, `Mathlib`, `Batteries`; `bv_decide` (bit-blasting to CaDiCaL with
  LRAT-checked certificates) makes bitvector/word-level obligations nearly free.

**Proof automation**
- `aesop` (white-box search), `duper` (superposition), `lean-auto` + `duper` = hammer,
  `lean-smt` / `smt_lean` (cvc5 with proof reconstruction), `polyrith`, `omega`, `decide`,
  `native_decide` (with its trust caveat), `bv_decide`, `simp`+`grind`.
- Neural: **DeepSeek-Prover-V2**, **Kimina-Prover**, **Goedel-Prover-V2**, **InternLM2.5-StepProver**
  — open-weight, all speak Lean 4, all usable as tactic/proof proposers behind a kernel check.
- Retrieval: **LeanDojo/ReProver** (premise selection over Mathlib), **LeanAgent**,
  `Mathlib`'s `exact?`/`apply?`/`loogle`/Moogle.

**Interaction substrate (the agent's hands)**
- **`leanprover-community/repl`** — JSON-in/JSON-out Lean REPL with *proof-state pickling*.
  This is the load-bearing component: it gives you snapshot/restore, so tree search over
  proof states is cheap.
- **Pantograph** — richer goal-level API, designed for ML agents.
- **LeanDojo** — trace a whole repo, extract premises, replay tactics.
- `lake` + `reservoir` for builds; `lean4checker` for external re-verification of `.olean`s;
  `#print axioms` to detect `sorryAx`/`Classical.choice`/`native_decide` leakage.

## 2. Architecture

```
                    ┌──────────────────────────────────────────────┐
                    │  ORCHESTRATOR (planner + budget + ledger)     │
                    └───────────────┬───────────────────────────────┘
   ┌────────────┬──────────────┬────┴─────────┬──────────────┬──────────────┐
   │            │              │              │              │              │
Cartographer  Semanticist  Transpiler    Specifier      Prover        Auditor
(map repo)   (lang kernel) (AST→Lean)  (invent specs) (prove)    (attack results)
   │            │              │              │              │              │
   └────────────┴──────────────┴──────┬───────┴──────────────┴──────────────┘
                                      │
                       ORACLES (non-negotiable ground truth)
             Lean kernel · lean4checker · differential fuzzing vs real runtime
             · property-based tests · SMT countermodels · #print axioms
```

### Layer 1 — Cartographer (no formalization yet)
Builds the *formalization graph*: modules, call graph, purity/effect classification,
external boundaries (I/O, FFI, network, unsafe, reflection), and a **formalizability
score** per function. Output: a topologically sorted work queue where leaves are pure
total functions and the frontier grows outward. Tools: tree-sitter + language servers +
`cloc` + existing call-graph tools. This is 90% deterministic tooling, 10% LLM
(classifying "what is this module *for*").

Key product decision: **you will never formalize the whole codebase.** You formalize a
*verified core* and generate machine-checked *boundary contracts* for everything else.

### Layer 2 — Semanticist (per language, one-time, human-reviewed)
Produces `Autoform/Lang/<L>/{Syntax,Semantics,Metatheory}.lean`:
- `inductive Expr | Stmt | Value`
- `Env`, `Heap`, `step`/`eval` (fuel-indexed or well-founded)
- Determinism, progress, preservation lemmas
- A `Decidable`/executable `eval` so `#eval` works — this is what enables the oracle below.

**The conformance oracle**: extract `eval` to native code (Lean's compiler, or via
`native_decide`-free extraction), then differential-fuzz it against the *real*
interpreter/compiler on a corpus (the language's own test suite — CPython's, V8's
test262, csmith for C). Any divergence is a bug in your semantics, found automatically.
This is what makes an LLM-assisted semantics trustworthy: **the semantics is testable
even before it's proved.**

Agent loop here: propose rule → fuzz → shrink counterexample → repair rule → prove
metatheory lemma → repeat. Escalate to a human on repeated failure.

### Layer 3 — Transpiler (deterministic, verified-by-testing)
`source AST → Lean term of type Expr`. Written as ordinary code, not LLM output. Two
correctness checks:
- **Round-trip**: `pretty(parse(s)) ≡ s` modulo formatting, on the whole repo.
- **Behavioral**: `eval (transpile p) input == run p input` on the project's own test
  suite. The project's tests become the transpiler's validation set. This is the single
  highest-leverage trick in the design — every repo ships its own conformance suite.

Unsupported constructs are *not* silently dropped; they become `Expr.opaque (name, spec)`
holes that carry an explicit, tracked assumption. The ledger counts them.

### Layer 4 — Specifier (the hard, genuinely agentic part)
Given a function's deep-embedded AST, propose Lean statements worth proving. Sources of
specifications, in descending order of trustworthiness:
1. **Existing artifacts**: type signatures, refinement types, assertions, `require`s,
   docstrings, doctests, unit tests, property tests (Hypothesis/QuickCheck strategies map
   almost directly to `∀`-statements), issue trackers, RFCs.
2. **Structural/safety specs, free for all code**: totality, no-panic, no-overflow,
   memory safety, termination, absence of division by zero, resource bounds.
   These need no domain knowledge and are where you get volume.
3. **Algebraic laws mined from behavior**: run Daikon-style invariant detection over
   the test corpus, or fuzz for candidate equalities (idempotence, commutativity,
   inverse pairs `decode ∘ encode = id`, monotonicity, refinement between two impls).
   Candidates are *conjectures*; the fuzzer prunes the false ones before a prover
   wastes time.
4. **Cross-implementation equivalence**: the richest specs. `optimized == reference`,
   `new_version == old_version`, `rust_impl == c_impl`. Free from the repo's own history.
5. **LLM-invented domain specs** — lowest trust, always fuzz-tested before proof attempt,
   always human-reviewed before being counted as an assurance claim.

**Anti-vacuity gate** (mandatory): every candidate theorem must survive
(a) mutation testing — inject a bug into the implementation; if the theorem still proves,
it is vacuous; (b) `#print axioms` clean; (c) hypothesis satisfiability check — prove the
premises are inhabited, else you proved something about the empty set. A "proved" theorem
that fails the mutation gate is scored as a *failure*, not a success. This is what keeps
the system honest.

### Layer 5 — Prover (portfolio + search, kernel-gated)
Tiered escalation with a per-goal budget:
1. `rfl` / `decide` / `simp` / `omega` / `bv_decide` / `norm_num` — pennies.
2. `aesop`, `exact?`, hammer (`lean-auto`+`duper`), `lean-smt`+cvc5.
3. Neural proposer (DeepSeek-Prover-V2 / Kimina) whole-proof sampling, n=8..64.
4. Best-first tree search over REPL proof states (pickled snapshots), premise retrieval
   from ReProver, with the neural model as the tactic policy.
5. Decompose: agent proposes lemmas, recurses. Generalize the goal (often *easier*).
6. Give up → record as an open obligation, not a lie.

Everything the prover emits is checked by the Lean kernel; the agent cannot fake a
proof. This is why the system is safe to run unsupervised — **the reward is not
LLM-judged.**

### Layer 6 — Auditor (adversarial)
Independent agent that tries to break the result: hunts `sorry`, `axiom`, `unsafe`,
`native_decide`, `@[implemented_by]` divergence, opaque holes, vacuous hypotheses,
spec/implementation drift (does the theorem talk about the AST you actually ship?), and
re-verifies all `.olean`s with `lean4checker` in a clean environment. Produces the
**trust ledger**.

## 3. The trust ledger (the actual product)

The deliverable is not "your codebase is verified." It is a precise, machine-generated
statement of *what is proved, about what model, under what assumptions*:

```
module payments/ledger.py
  formalized:      412 / 507 LOC  (81%)
  opaque holes:    3   (datetime.now, decimal ctx, network)
  semantics:       Python-subset v0.4  (conformance: 99.2% on CPython test suite,
                                        12 known divergences, listed)
  transpiler:      behavioral-equiv on 1,204/1,204 project tests
  theorems proved: 47   (mutation-gated: 44 survive, 3 flagged vacuous)
    - no unhandled exception on well-typed input   ✔ kernel-checked
    - balance conservation across transfer         ✔ kernel-checked
    - idempotence of settle                        ✔ kernel-checked
  axioms used:     Classical.choice, propext, Quot.sound   (no sorryAx)
  open obligations: 9
```

Anyone reading this can locate the trust boundary in seconds. That is the thing nobody
currently ships, and it's more valuable than a bigger green checkmark.

## 4. Sequencing (what to build in what order)

**Phase 0 — Skeleton (weeks 1–3).** Lean repo + `lake`, REPL harness with pickled state,
theorem/obligation database (SQLite), `#print axioms` + `lean4checker` gate in CI, trust
ledger renderer. No agents yet. Prove the plumbing on hand-written examples.

**Phase 1 — Pick one narrow language.** *Recommendation: start with Rust via Aeneas*
(semantics + transpiler already exist and emit Lean 4, so you skip Layers 2–3 entirely
and can validate Layers 4–6 immediately) **and** in parallel a **toy imperative
language / Wasm subset** where you own the whole stack end-to-end. Resist starting with
Python or C++ — dynamic/undefined-behavior-rich languages will eat a year.

**Phase 2 — Specifier + anti-vacuity.** This is the research risk. Build the mutation
gate before the spec generator; otherwise you'll fool yourself for months.

**Phase 3 — Prover portfolio.** Cheap tactics first; measure what fraction each tier
closes. Only add the neural tier once tier-1/2 is exhausted and instrumented — for
safety/structural specs the classical tools close a surprising majority.

**Phase 4 — Second language (Python or C subset), from K semantics as reference.**
Now the Semanticist agent + conformance fuzzer earn their keep.

**Phase 5 — Shallow-embedding refinement.** Prove deep ≈ shallow, so proofs scale.

## 5. Honest failure modes

- **Semantic gap is the whole game.** A proof about a semantics that doesn't match the
  real runtime is theater. The conformance fuzzer is not optional infrastructure.
- **Vacuous theorems.** LLMs are extremely good at producing provable-and-useless
  statements. Mutation testing is the counterweight.
- **Concurrency, I/O, FFI, reflection, `eval`, dynamic loading** — these do not have
  cheap answers. Design the opaque-hole mechanism first-class from day one rather than
  pretending they'll be handled later.
- **Proof burden grows superlinearly with program size.** Hence: verified core +
  contracts, never whole-repo.
- **Mathlib drift / build times.** Pin toolchains; cache aggressively; expect the
  formalization to bit-rot without CI.

## 6. Minimal viable demo (what to aim at first)

Take a real, small, pure Rust crate (e.g. a parser, a codec, a data structure), run
`charon`+Aeneas to get Lean, auto-generate: totality + panic-freedom + `decode ∘ encode
= id` + equivalence against a reference implementation, prove them with the portfolio,
mutation-gate them, and emit the trust ledger. If that pipeline runs unattended on 20
crates with an honest ledger, the architecture is validated and every later language is
"just" Layers 2–3.

## 7. CSLib (cslib.io / `leanprover/cslib`) — where it fits

**What it is:** "Mathlib for computer science." Lean 4, from de Moura, Barrett, Montesi,
Chaudhuri, Kohli, Grundy, Rademaker, Yingchareonthawornchai (arXiv 2602.04846), with
Amazon / Google DeepMind / Stanford backing. Already contains: operational semantics
infrastructure, program equivalences, automata models, linear logic, some verified
sorting/searching. Explicit stated goals include a *program-reasoning toolkit* and
"a shared vocabulary to train models on."

**This is directly load-bearing for Layer 2, and it changes the plan.**

Do not invent private conventions for `Syntax` / `step` / `eval` / refinement. Build each
language kernel **against CSLib's operational-semantics API** (LTS, bisimulation, program
equivalence). Concretely:

- **Layer 2 substrate.** CSLib's bundled operational semantics + computable-definition
  discipline is exactly the interface the Semanticist agent should target. Free
  metatheory: determinism/confluence lemmas, bisimulation congruence, equivalence
  combinators — the machinery that otherwise eats months.
- **Layer 5 (deep ≈ shallow) becomes reuse, not research.** The refinement step —
  "prove the deep-embedded AST is observationally equivalent to a clean Lean function" —
  is precisely a program-equivalence/bisimulation obligation. CSLib is where that
  machinery should live, not in our repo.
- **Layer 5 retrieval.** ReProver/LeanDojo premise selection is Mathlib-shaped and
  performs badly on CS goals. **CSLibPremiseBench** (arXiv 2605.14549) exists for
  structure-guided premise retrieval over CSLib theorems — drop it in as the retriever
  for CS-flavored obligations and keep ReProver for the arithmetic/Mathlib tail.
- **Distribution strategy.** Language semantics are generic, reusable, and exactly what
  CSLib wants. Upstream them. That converts our per-language cost center into shared,
  externally-reviewed infrastructure — and external review of the semantics is worth
  more to trustworthiness than anything we can do alone.

**What CSLib is not, and what we still own.** It is a *metatheory and pedagogy* library,
not a pipeline for verifying real codebases. It will not ship a production-grade C,
Python, or JS semantics soon; it says nothing about extracting ASTs from a real repo,
inventing specifications, anti-vacuity, or trust accounting. Layers 1, 3, 4, 6 — the
Cartographer, Transpiler, Specifier, and Auditor — remain entirely ours. CSLib gives us a
better foundation and a better vocabulary; it does not give us the product.

**Risks:** young library, expect API churn (pin revisions, run against `main` in CI);
breadth-first coverage, so depth where we need it may be thin; governance/contribution
standards are Mathlib-strict, so upstreaming has latency — vendor locally, upstream
asynchronously.

**Revised Phase 0/1 action:** before writing any semantics, read `Cslib/Semantics`
and the whitepaper, and write the toy-imperative-language kernel *as a CSLib-conformant
development*. If our language kernels can't be phrased in CSLib's vocabulary, that's a
signal worth acting on early — either we're doing it wrong or it's a genuine upstream
contribution.

## 8. Build/buy inventory — what we actually hand-roll

Default posture: **buy or adapt everything; hand-roll only what is irreducibly ours.**
Re-audited after CSLib, this is the full component list.

| Component | Verdict | Source |
|---|---|---|
| Parsing / AST extraction | BUY | tree-sitter, `charon`, libclang, `go/ast`, LLVM/MLIR |
| Language semantics | ADAPT | CSLib, K (C/Java/JS/Python/EVM), CompCert, CakeML, Wasmcert |
| Rust front-to-Lean | BUY | Aeneas + charon, hax |
| Conformance corpora | BUY | test262, CPython suite, csmith, Wasm spec tests, AFL++/libFuzzer |
| Dynamic invariant mining | ADAPT | Daikon |
| LLM spec synthesis | ADAPT | SpecGen, Spec-Agent, Quokka, counterexample-guided refinement lineage |
| Mutation-based spec validation | ADAPT | **IronSpec**; MutantChick/MetaCoq (proof-assistant precedent); `universalmutator`, `cargo-mutants`, PIT |
| Vacuity detection | ADAPT | model-checking vacuity literature, ported to Hoare/refinement obligations |
| Proof automation | BUY | aesop, duper, lean-auto, lean-smt/cvc5, bv_decide, omega, grind |
| Neural provers | BUY | DeepSeek-Prover-V2, Kimina, Goedel-V2 |
| Proof-state interaction / search substrate | BUY | `leanprover-community/repl` (pickling), Pantograph |
| Premise retrieval | BUY | ReProver/LeanDojo (Mathlib tail) + CSLibPremiseBench (CS goals) |
| Agent orchestration | BUY | Claude Agent SDK or equivalent — **do not write an agent framework** |
| Build, cache, kernel re-check | BUY | lake, Reservoir, `lean4checker`, `#print axioms` |
| Attestation / findings format | BUY | in-toto/SLSA predicates, SARIF |
| Sandboxed execution | BUY | containers / nsjail |

**Correction to §4:** the Specifier and the anti-vacuity gate were listed as the research
risk. They are not novel — IronSpec already does mutation-based specification validation,
mutation analysis for Coq exists, and SpecGen/Spec-Agent already do
counterexample-guided LLM spec synthesis validated against a verifier. Our work there is
*integration and porting to Lean*, not invention. Downgrade the risk, and reuse the
designs rather than rediscovering them.

### What is genuinely ours (and therefore where the effort goes)

1. **The transpiler + effect-boundary calculus, per language.** Source AST → deep-embedded
   Lean term, with a principled treatment of what *cannot* be embedded (I/O, FFI, reflection,
   concurrency, dynamic loading) as tracked `opaque` holes carrying explicit assumptions.
   This is the bulk of the engineering mass and nobody ships it for us.
   *Main cost lever:* target **Wasm** and collapse N language front-ends into one semantics
   plus N existing production compilers. Pay for it in lost source-level structure — the
   shallow-embedding refinement gets harder — so treat it as a per-language decision, not
   a global one.
2. **The Cartographer.** Formalization graph, effect classification, formalizability
   scoring, and the *budget policy* deciding what to formalize and in what order. No prior
   art, because nobody attempts repo-scale — everyone formalizes a hand-picked artifact.
3. **The trust-ledger calculus.** Composing heterogeneous evidence — kernel proof,
   semantics conformance %, transpiler behavioral-equivalence rate, mutation score, hole
   count, axiom set — into one auditable claim with an explicit trust boundary. The
   *format* is in-toto/SARIF; the *composition rules* are ours, and this is the product.
4. **Thin oracle harnesses**: differential-fuzz driver, Lean-side mutation-gate driver,
   obligation database. Small, boring, unavoidable glue.

Everything else is integration. If a design discussion concludes "we should build our own
X" and X is not on that list of four, that is a signal to search harder first.

## 9. Killing #2, and making #4 Lean-native

### #2 Cartographer — mostly buyable after all

The formalization graph is a **code property graph** plus a policy. The graph is a solved,
commoditized problem:

- **Joern** (`joernio/joern`) — open-source CPG platform, C/C++/Java/JS/Python/Kotlin/binary,
  Scala DSL for queries. Effectively open-source CodeQL. Front-ends: CDT (C/C++), Soot
  (JVM bytecode), Ghidra (binaries). AST + CFG + PDG + call graph in one queryable graph.
- **CodeQL** — better ergonomics and maturity, more restrictive licensing; usable for
  effect/taint classification if terms permit.
- **SCIP** (Sourcegraph) — cross-language symbol/xref index; protobuf, 8× smaller and 3×
  faster than LSIF, with production indexers per language.
- **Glean** (Meta) — repo-scale fact database, ingests SCIP (~550 LoC mapping). Use if
  scale demands it; SCIP alone is enough to start.
- **Stack Graphs** (GitHub) / **tree-sitter-graph** — incremental name resolution.
- Purity/effect classification: LLVM `FunctionAttrs` (`readnone`/`readonly`/`nounwind`) for
  anything with an LLVM path, Rust's own type system, **Infer** for effect/nullability.

**Revised verdict:** the Cartographer is *Joern or SCIP+Glean, plus ~a few hundred lines of
policy*: formalizability scoring, effect classification into the opaque-hole taxonomy, and
the budget/ordering decision. The policy is ours; the graph is not. Drop it from the
"build" list — it becomes a query layer over a bought index.

That leaves the genuinely-ours list at **three**: the transpiler + effect-boundary
calculus, the trust-ledger calculus, and the harness.

### #4 harness — build it in Lean

Everything in the harness that touches Lean terms should be written in Lean, and the
ecosystem is now good enough to do it:

- **Plausible** (`leanprover-community/plausible`) — QuickCheck for Lean 4, integrated into
  the *tactic framework*: give it a goal, it derives generators from typeclasses and tries
  to **refute** it with a counterexample. This is precisely the conjecture-pruning and
  anti-vacuity engine, operating on the *same statement object* the prover will attack.
  No serialization layer, no drift between "the property we fuzzed" and "the theorem we
  proved."
- **Chamelean** — extends Plausible to auto-derive generators, enumerators, and checkers
  for **inductive relations**. Our semantics *are* inductive relations (`step`, typing
  judgments), so this is the differential-fuzzing engine for Layer 2, for free.
- **LSpec** — Lean test framework with `checkPlausibleIO'` for deferred runtime property
  tests; the CI-facing runner.
- **Lean's own metaprogramming** — and here Lean beats Coq structurally: mutation analysis
  needs no MetaCoq analog, because `Lean.Environment` / `ConstantInfo` / `Lean.Meta` are
  first-class in-language. Mutating a definition, re-elaborating dependents, and checking
  whether the proof survives is an ordinary Lean program.
- **Axiom/trust audit** — `#print axioms`, `lean4checker`, environment diffing: all
  in-language. Ledger evidence extraction becomes a Lean `Lake` script, not an external
  scraper parsing logs.
- **`FVSpec`** (arXiv 2606.01008) — 11,039 real-world Python property-based tests scraped
  and 2,772 auto-translated into 9,415 Lean 4 specifications with proof-obligation
  placeholders. This is *direct evidence* for the §4 claim that a repo's own property
  tests are the highest-value spec source — and it is both a corpus and a benchmark for
  our Specifier. Use it as the evaluation set.

**The elegant collapse this enables:** candidate spec → Plausible tries to refute it →
survivors go to the proof portfolio → mutation gate re-runs via Lean metaprogramming →
`#print axioms` audit → ledger. One language, one statement representation, end to end.
The only non-Lean glue left is process orchestration, external-runtime differential
testing, and the code-property-graph query layer.

**Where not to use Lean:** orchestration, HTTP, DB, sandboxing, driving external runtimes.
Thin ecosystem, and no benefit — those components never touch a Lean term.

## 10. #3 (trust ledger) — also mostly prior art

The "composition calculus for heterogeneous verification evidence" is the **assurance
case** field, which has been standardized for decades in safety-critical engineering.
Do not reinvent it.

- **SACM** (OMG *Structured Assurance Case Metamodel*, v2.1) — the target model. Unifies
  and extends **GSN** (Goal Structuring Notation) and **CAE** (Claims–Arguments–Evidence).
  Models exactly our three concerns: *arguments* (claims + inferential links),
  *artifacts* (evidence: results, techniques, activities, traceability), and *terminology*.
  Gives fine-grained modularity and argument-evidence traceability out of the box.
- **Isabelle/SACM** (arXiv 2009.12154) — *integration of mechanized formal proof into
  SACM assurance cases*. This is precisely our problem, already solved once for Isabelle;
  SACM claims admit structured expressions, so formal statements embed directly.
  Port the pattern to Lean rather than inventing a ledger format.
- **ACCESS** (arXiv 2403.15236), model-based system assurance tooling (arXiv 1905.02427),
  Adelard/ASCE, AMASS/OpenCert — tooling and metrics, including auto-generated assurance
  case fragments and case metrics, which is exactly what we want to emit per module.
- Transport/provenance envelope stays **in-toto/SLSA** + **SARIF** for findings.
- Domain precedent for arguing *from* formal evidence: **DO-178C / DO-333** (formal
  methods supplement), ISO 26262.

**Revised verdict:** the ledger is *SACM as the model + Isabelle/SACM's proof-integration
pattern + in-toto as the envelope*. Ours is only the domain-specific evidence types
(semantics conformance rate, transpiler behavioral-equivalence rate, hole count, mutation
score, axiom basis) and the rules for combining them into a claim. That is a schema and a
few hundred lines, not a research program.

**The genuinely-ours list is now two things:**

1. **The transpiler + effect-boundary calculus, per language.**
2. **The domain evidence types and their combination rules** (a SACM profile).

Plus integration glue. That is the honest scope of this project. Everything else is
assembly of existing parts — which is the correct outcome of a build/buy audit, not a
disappointment.

## 11. FVSpec — the Specifier's corpus, baseline, and leaderboard

**[GaloisInc/fvspec](https://github.com/GaloisInc/fvspec)** — benchmark of **9,415 Lean 4
verification challenges** derived from **2,772 of 11,039 real-world Python property-based
tests** scraped from **333 open-source repositories**. Leaderboard at `fvspec.galois.com`;
corpus on Hugging Face. **Correction, established by actually fetching it:** the GitHub
repo ships the generation pipeline, leaderboard and baselines — *not* the formalizations;
`GaloisInc/fvspec-pbt` is the upstream *Python* PBT corpus; the Lean benchmark is a third
artifact, **`GaloisInc/fvspec-fv`** (`train.jsonl`, 235 MB, exactly 9,415 rows).

Why it matters more than a benchmark citation:

- **It is a working instance of our Layer 4.** The pipeline scrapes GitHub for Hypothesis
  PBTs and uses a **three-agent LLM pipeline** to transpile them to Lean specs,
  *autoformalizing each function under test*. Each problem ships four artifacts, with
  `sorry` placeholders (~3 formalizations per PBT). Read their agent decomposition before
  writing ours; adapt rather than re-derive.
- **It validates the §4 ordering.** Their highest-yield spec source is the repo's own
  property-based tests — the same conclusion, arrived at independently and at scale.
  Note the yield: **25%** of scraped PBTs translated. Plan for that hit rate.
- **It is the right eval set**, and unusually clean: the source PBTs were written by
  practicing engineers and were **never formally verified**, so the resulting theorems are
  largely absent from model training data. Contamination risk is low, which is rare.
- **It gives us baselines for free** — the paper reports automated and model-based proof
  generation baselines, so our portfolio has something to beat on day one.
- **It is a ready-made target for the anti-vacuity gate.** Their specs are LLM-transpiled
  and *not* mutation-validated. Running our Plausible refutation gate and dependency-vacuity
  check across all 9,415 would (a) exercise our harness at scale immediately and (b) be a
  genuine contribution back to the benchmark.

**Action:** adopt FVSpec as the Phase-2 evaluation harness, and make "refute/confirm the
FVSpec specification set" the first at-scale run of the harness.

**Revised inventory rows:**

| Component | Verdict | Source |
|---|---|---|
| Spec corpus + eval + leaderboard | BUY | FVSpec, `GaloisInc/fvspec-pbt` |
| PBT→Lean spec transpilation agents | ADAPT | FVSpec's three-agent pipeline |
| Evidence/assurance model | ADAPT | SACM 2.1, Isabelle/SACM, GSN/CAE |

## 12. Built: the CPG as universal front end

The §8 conclusion was that the per-language transpiler is the irreducible cost centre,
with Wasm floated as the way to collapse N front ends into one. There is a better answer,
and it was already sitting in the Layer 1 tooling: **Joern's code property graph is
itself a universal AST.**

C, C++, Java, JavaScript, Python, Kotlin and binaries all normalize to one node
vocabulary — `CALL` / `IDENTIFIER` / `LITERAL` / `CONTROL_STRUCTURE` / `RETURN` / `BLOCK`,
with operators as `<operator>.*` calls. So the transpiler is written **once**:

* `Autoform/Lang/Core/*` — a semantics for that vocabulary, not for any one language.
* `cartographer/export_ast.sc` — CPG → neutral JSON AST.
* `cartographer/render_lean.py` — JSON → Lean.

Unlike the Wasm route, source-level structure survives, so the shallow-embedding
refinement stays tractable. Verified on Python (424 functions of a real repo) and C from
the same code path.

### The dialect lesson

The conformance oracle earned its place immediately. Its first run reported
`fmod(6,-9)`: CPython `-3`, Lean `6` — Python floors integer division and modulo, C and
Java truncate toward zero, and the semantics had silently picked one.

The tempting fix is to patch the operator. The correct fix is structural: a **universal
core language must be parameterized by the dialects it unifies**, and the transpiler must
record which one produced each program. Anything else is a semantics that is right for
one language and silently wrong for the rest — precisely the "semantic gap is the whole
game" failure of §5, and exactly the class of bug that no amount of proving would ever
surface, because the proofs would all have been about the wrong `eval`.

Generalize the lesson: every place the core language merges constructs that *look* alike
across languages (string mutability, integer width and overflow, evaluation order, name
resolution, equality) is a latent dialect parameter. Assume there are more, and let the
oracle find them rather than trying to enumerate them up front.

## 13. Gaps remaining — measured, not estimated

Numbers below are from `cachetools` (233 real functions after excluding Joern's
synthetic `<metaClassAdapter>` wrappers).

### Tier 1 — coverage: which gap unblocks the most code

Marginal value = functions whose *only* remaining blockers fall in that group.

| Gap | Newly hole-free | Cumulative |
|---|---|---|
| **Objects** (`fieldAccess` 183, `METHOD_REF` 58, `TYPE_REF` 46, `alloc` 30, non-identifier LHS 58) | **+166** | 176 |
| Exceptions (`TRY` 48, `raise` 12) | +35 | 211 |
| Containers (tuple/list literals, `starredUnpack` 33) + identity (`is`/`in`) | +44 | 255 |
| Iteration (`FOR`) | **+0** | — |

Two conclusions, both non-obvious:

* **Objects are the whole game.** One gap is worth more than every other gap combined.
  Attribute access, method dispatch, allocation, and assignment-to-non-identifier are one
  feature, and they need a heap — which the Core semantics does not have.
* **`FOR` has zero marginal value** despite looking like an obvious omission: every
  function containing a `FOR` is blocked by something else too. Fixing it in isolation
  would unblock nothing. This is exactly why the marginal metric beats the frequency
  histogram for prioritisation.

Cheap unmapped operators worth closing regardless (`floorDiv` — found by testing and
currently a hole for every Python `//`, `in`/`notIn`, `is`/`isNot`, `+=`/`-=`,
conditional expressions, `pass`, `delete`).

### Tier 2 — fidelity: bugs in what *is* translated

These matter more than coverage, because they are wrong rather than absent.

1. **Integer width is unmodelled.** Confirmed: `mulbig(100000, 100000)` gives
   `1410065408` in C (32-bit wraparound) and `10000000000` in Core. A latent dialect
   parameter of exactly the kind §12 predicted. C/Java/Go need fixed-width wrapping
   integers; Python needs bignums. **This silently produces wrong answers** — the worst
   category.
2. **No short-circuit evaluation.** Confirmed: `b != 0 and a % b == 0` with `b = 0`
   returns `0` in Python, but Core eagerly evaluates both operands and yields
   `hole "mod-by-zero"`. Currently *conservative* (a hole, not a wrong answer) only
   because Core has no side effects — it becomes a genuine soundness bug the moment
   assignment-in-expression or effectful calls are modelled.
3. **Differential coverage is thin.** Only module-level, int→int functions are compared.
   `cachetools` yielded **zero** comparable cases. Needed: instance construction for
   methods, comparison of lists/strings/dicts, and — the highest-leverage item, from §3
   and still unimplemented — **driving the differential harness from the repository's own
   test suite** instead of random arguments.
4. **No heap, aliasing, or mutation.** A prerequisite for Tier 1's objects, not
   independent of it.
5. **Scoping is naive.** `Env.set` conses; no block scope, globals, closures, or
   `nonlocal`.
6. **Strings are conflated.** Python `str` and C `char*` are the same `Val.str`.

### Tier 3 — the verification half does not exist

The system produces *verifiable* code and proves nothing about it.

* No proof portfolio (aesop / lean-auto+duper / lean-smt / bv_decide / neural tier).
* No specification synthesis; the FVSpec run (§11) has not happened.
* The mutation gate is only the **dependency-vacuity** check, which is necessary but not
  sufficient. Source-level mutation — the sufficient test — is unbuilt.
* No SACM ledger schema (§10); the ledger is still ad-hoc text.
* **The deep ≈ shallow refinement has not been started.** Without it, proofs are
  conducted against `evalExpr`/`execStmt` applied to a concrete AST, and will not scale
  past toy functions. This is the single largest architectural debt.

### Tier 4 — engineering

No CI; `lean4checker` not in the loop; Cartographer scoring weights uncalibrated
(operator dispatch inflates fan-out); build times dominated by Specimen/Plausible.

### If you do one thing next

**Objects + a heap.** It unblocks 166 functions (5% → ~76% on `cachetools`), and it is a
prerequisite for making the differential harness meaningful on real code, which in turn
is what makes every later number trustworthy. Integer width is a close second because it
is actively wrong rather than merely missing.

## 14. Execution log — Tier 1 spine and Tier 3

### Tier 1: the Core language now has a heap

`Autoform/Lang/Core/{Syntax,Semantics}.lean` were rewritten to add what §13 measured as
the dominant gap:

* **Objects** — `Val.ref`, an explicit `Heap` of `Obj { cls, fields }`, `Expr.field`,
  `Expr.mcall` with dispatch on the receiver's class, `Expr.alloc` running `__init__`,
  `Stmt.setField`. The heap is threaded explicitly through `evalExpr`/`execStmt` rather
  than hidden in a monad, so the fuel recursion stays visibly structural and the
  interpreter remains total.
* **Exceptions** — `EResult.exn` / `Ctl.exn`, `Stmt.raise`, `Stmt.tryCatch`. Division by
  zero and out-of-range indexing now raise `ZeroDivisionError` / `IndexError` / `KeyError`
  instead of being holes, which is both more faithful and more useful.
* **Containers** — `Val.list`/`tuple`/`dict`, `listE`/`tupleE`/`dictE`, `inOp`, `isOp`
  (reference identity for objects, structural for immediates), `cond`.
* **Iteration** — `Stmt.forIn` over any `Val.iterable`, with `break`/`continue`.
* **Name resolution** — `Ctx.resolve` falls back from exact name to *unique* suffix match,
  because Joern emits fully-qualified names while call sites carry short ones. An
  ambiguous match resolves to a hole, not a guess.

`Stmt.setIndex` is deliberately still a hole (`setIndex:immutable-containers`): container
mutation needs boxed containers, and inventing an answer would be exactly the
silent-mistranslation failure this project exists to prevent.

### Tier 3: the mutation gate found real vacuity, and closing it worked

`scripts/mutate.py` scored `evalStmt_sound` at **2 killed / 6 survived (25%, WEAK)**, and
every survivor was a mutation of `evalBExpr`. The diagnosis is worth recording because it
generalizes:

> `BigStep`'s `iteTrue`/`iteFalse`/`loopTrue`/`loopFalse` side conditions are *themselves*
> stated in terms of `evalBExpr`. Mutating `evalBExpr` therefore mutates both sides of the
> equation at once, and the proof goes through unchanged.

This is the vacuity class `#audit_depends` **cannot** see — `evalStmt_sound` does depend on
`evalBExpr` transitively, it simply says nothing about it. It is the concrete argument for
why §4's "dependency vacuity is necessary but not sufficient" is not a hedge.

The fix was to pin `evalBExpr` against something not defined in terms of itself — the
integer order and equality on `evalExpr`'s results (`Characterization` section in
`Autoform/Lang/Imp/Semantics.lean`). Re-running the gate: **8 killed / 0 survived, 100%,
HAS TEETH**.

*Caveat on the measurement:* when a mutant makes the module fail to compile, every theorem
in that module is recorded as having killed it, so per-theorem attribution is coarse. The
aggregate claim (these mutants are now caught) is sound; the per-theorem breakdown is not
yet trustworthy and should be refined by isolating theorems into separate modules.

### Tier 3: audit, portfolio, assurance case

* `scripts/audit_all.py` sweeps all **952** declarations: axiom basis is `propext` (225),
  `Quot.sound` (42), `Classical.choice` (15) — **zero** `sorryAx`/`ofReduceBool`/
  `ofReduceNat`, zero project axioms. `Autoform/Lang/Core/*` verified free of
  `sorry`/`partial`/`unsafe`/`native_decide`/`@[implemented_by]`/`@[extern]`, so the
  README's "total, no sorry" claim is now *checked* rather than asserted.
  Two honest findings: `Autoform/Harness/Audit.lean` uses `partial def transitiveDeps`
  (the audit tool's own walker is unproven-terminating), and **`lean4checker` is not
  installed**, so the `.olean` files have never been independently re-verified — Tier 4's
  gap is still open and now says so out loud.
* `Autoform/Tactics/Portfolio.lean` implements the escalation ladder with the honesty
  guard that matters: a rung counts as success only if it closes the goal *and* the proof
  term passes `hasSorry`/`hasExprMVar` screening; on exhaustion it errors with a full
  transcript, and unavailable tiers are printed so "unproved" is distinguishable from
  "not attempted". Open goals are recorded as `Obligation` *data*, never as admitted
  theorems.
* `scripts/sacm.py` + `docs/ledger-schema.md` replace the ad-hoc ledger with a SACM
  profile (Claim / ArgumentReasoning / ArtifactReference / Assumption / typed
  relationships) wrapped in an in-toto Statement. Every hole label becomes a named
  `Assumption` node, so untranslated constructs appear *in the argument* rather than
  vanishing. On Cachetools the top claim comes out **UNDEVELOPED**, which is the correct
  answer, and it caught a provenance defect: `conformance.json` carried no module tag, so
  its numbers could not be attributed and the faithfulness claim was capped at WEAK
  rather than accepted.

## 15. FVSpec results — the anti-vacuity gate at scale

`scripts/fvspec.py` ran the vacuity screen over the **entire** benchmark: 9,415 problems
(9,352 analyzed, 63 with no recognizable theorem declaration reported as `not_analyzed`
rather than passing), **73,046 theorems**, 251 source repos, 78,751 `sorry` placeholders.

| Check | Problems | Theorems |
|---|---|---|
| dependency vacuity (statement names no implementation symbol) | 2,485 | 7,388 |
| opaque subject (subject is a spec-local `axiom`/`sorry` stub) | 1,359 | 3,959 |
| reflexive conclusion (`t = t`, closable by `rfl`) | 920 | 1,221 |
| no `sorry` obligation at all | 328 | 1,028 |
| trivial conclusion (`: True`) | 256 | 444 |
| unsatisfiable hypotheses | 9 | 13 |
| empty quantification | 2 | 2 |

**3,833 of 9,352 analyzed problems (41.0%) are flagged**; 10,699 of 73,046 theorems
(14.6%); 1,047 of the 2,772 canonical formalizations (37.8%).

The dominant pattern is instructive and directly relevant to our own Specifier: Python
*determinism* property-tests (`f(x) == f(x)`) transliterated literally into Lean, where
purity makes them `rfl` and therefore contentless. A property that is meaningful in a
language with mutable state and nondeterminism becomes vacuous the moment it is moved
into a pure setting. **Spec translation is not spec preservation** — §4's anti-vacuity gate
is not defensive pedantry, it is load-bearing, and this is the empirical proof.

Two honesty notes carried in the report rather than smoothed over: survivors are labelled
`clean_static` ("no check that ran fired"), never "passed", with an explicit `not_checked`
list (Lean elaboration, Plausible refutation, mutation gate, axiom audit) — all of which
need Lean and are out of scope for a static screen. And the dataset's own
`actually_invokes_given` flag disagrees with our dependency check on 3,321 problems in
both directions; both are heuristics, and the report states the disagreement instead of
adjudicating it.

## 16. Tier 2: machine integers, and a choice that has to be made explicitly

`Autoform/Lang/Core/Numeric.lean` closes §13 Tier 2 item 1 — the confirmed silent
mistranslation where `mulbig(100000,100000)` gave `10000000000` in Lean against `cc`'s
`1410065408`.

It follows §12's rule (parameterize, don't hardcode): `Width`, `IntType`
(unbounded / signed / unsigned × 8/16/32/64), `NumConfig` with presets for Python, C32,
C64, unsigned, Java, Go, and `Dialect.toNumConfig` as the hook into the interpreter.

The important structural choice is that **`NumResult` has four outcomes**, mirroring the
discipline `EResult` already applies to evaluation:

| Outcome | Meaning |
|---|---|
| `ok v` | a defined result |
| `divZero` | division or remainder by zero |
| `trap r` | the language defines this as a runtime fault (Go's `INT_MIN / -1`) |
| **`ub r`** | **the language does not define this at all** |

`ub` is the one that matters. C's signed overflow, `INT_MIN / -1`, and shifts past the
width have *no* correct answer — the program's meaning depends on the compiler. Returning
a number there would be the same category of error as the original modulo bug, just
harder to detect. Wiring `ub ↦ Expr.hole` keeps undefined behaviour out of proofs
entirely: a program that relies on UB cannot be proved to do anything at that point, which
is exactly right.

### The configuration that must be recorded, not defaulted

`NumConfig.c32` uses `Policy.undefined` — what the C standard says, so UB *surfaces*.
`NumConfig.c32Wrapv` wraps — what `cc` actually does, so the differential oracle *agrees*.
These are both defensible and they are not interchangeable:

* Verifying with `c32Wrapv` proves things about the compiler you happened to test, and
  will silently bless code whose behaviour another compiler is free to change.
* Verifying with `c32` finds UB, but then the differential harness reports divergences
  against `cc` that are not bugs in the semantics — they are the semantics correctly
  refusing to commit.

So this cannot be a hidden default. **The ledger must record which integer policy a
result was obtained under**, exactly as it records the dialect — an assurance claim that
does not name its arithmetic model is not attributable. Current wiring picks `c32Wrapv`
so the conformance oracle stays meaningful; a verification run should flip to `c32`.

Proved: `wrap_inRange`, `wrap_of_inRange`, `wrap_wrap`, `finish_inRange`, and that the
Python config's operations equal plain `Int`/`Int.fdiv`/`Int.fmod`. Left as explicitly
stated open obligations (no `sorry`): the `wrap` ring-homomorphism laws, `shl_eq_mul`,
bitwise identities — closable via a `BitVec` refinement plus `bv_decide`.

## 17. The coverage metric was wrong — twice, in the same direction

Two corrections to the headline number, both found by testing the metric rather than
trusting it. Both moved it **down**.

1. **Synthetic inflation.** The first `cachetools` figure was 130/424 hole-free (30%).
   120 of those were Joern-synthesised `<metaClassAdapter>` wrappers duplicating real
   methods. Excluding them: **12/233 (5%)**.
2. **Static hole-freedom is an upper bound, not a guarantee.** `Func.total` only checks
   that the *AST* contains no holes. The interpreter can introduce holes at runtime:

   ```
   Func.total sneaky = true          -- statically clean
   run sneaky  3 ==> hole "field:attr:non-object"
   run sneaky2 3 ==> hole "call:not_translated"
   run sneaky3 3 ==> hole "index:unsupported"
   ```

   The dangerous one is `call:`. A call to a function that was never translated is, in the
   AST, indistinguishable from a call to one that was — so the metric counted functions as
   verifiable whose behaviour is entirely unknown. Requiring **call closure** (every
   call/method target resolves inside the program) gives **6/233 (2%)**, and the ledger now
   reports a third figure, `dynamic-hole risk` (384 constructs), for the residue that is
   input-dependent and therefore the conformance oracle's business, not the type system's.

The pattern is worth naming, because it will recur: **a coverage metric that is computed
from the same artifact it describes will flatter itself.** Static hole-counting over an
AST cannot see what the interpreter does with that AST, exactly as `#audit_depends` cannot
see whether a theorem constrains what it mentions (§14) and as FVSpec's translated
determinism properties cannot see that purity made them vacuous (§15). Three instances of
one failure mode: *the check and the thing checked share an assumption.*

The general defence is the one this project already relies on — an oracle that does not
share the artifact's assumptions. For semantics that is the real runtime; for
specifications it is mutation; for coverage it is execution. Any number reported without
one should be read as an upper bound.

## 18. Tier 1 measured: objects closed the gap

Full pipeline on `cachetools` (233 real functions), before and after the Tier 1 work:

| metric | before | after |
|---|--:|--:|
| holes | 745 (20% of nodes) | **102 (2%)** |
| hole-free (upper bound) | 12 (5%) | **166 (71%)** |
| verifiable core (hole-free **and** call-closed) | 6 (2%) | **45 (19%)** |

§13 predicted "+166 from objects", and 166 is exactly what landed. The marginal-value
metric was right.

### What the exporter work actually found

The CPG side turned out to matter more than the Lean side, and several of §13's
assumptions were wrong:

* **`FOR` does not exist in a Python CPG.** The frontend pre-desugars every `for` and
  every comprehension into `tmp = e.__iter__()` plus a `WHILE` whose condition is an
  `UNKNOWN` node. So §13's measurement of "`FOR` marginal value = +0" was right for the
  wrong reason — it was never a `control:FOR` hole, it was hiding inside `expr:UNKNOWN`.
  Reconstructing `forIn` from that shape is what unlocked iteration.
* **A latent fidelity bug, removed.** `<operator>.and` / `.or` had been mapped to `&&`/`||`.
  They are **bitwise** `&`/`|` (the logical ones are `logicalAnd`/`logicalOr`), and Core has
  no bitwise operators — so that mapping was silently computing the wrong answer. They are
  now holes. Same for float literals, which were becoming strings. This is the §12 lesson
  recurring: *constructs that look alike across languages are the dangerous ones.*
* **Resolved attribute access is not attribute access.** When Joern resolves `o.m`, it
  prepends the target, so the node has three children rather than two; those are `fnref`,
  not `field`.
* **`<operator>.alloc` is not the construction signal** — it appears only in metaclass
  adapters. Real construction is a call whose `methodFullName` ends in `.__init__`.

### What is deliberately still a hole (102 total)

Every one is a case where a faithful translation is not available and inventing one would
be the §12 failure:

* `starredUnpack` (33) — `*args` has no Core representation; splicing it changes arity.
* `try/finally` where the body can `return`/`break` (29) — the non-escaping case *is*
  translated, as `tryCatch(B, e, F; raise e); F`. When control escapes, `ret` bypasses the
  handler and would skip the trailing `F`, so it stays a hole.
* `try/except/else` (11) — `else` must run only when nothing was raised *and* its own
  exceptions must not be caught. One `tryCatch` cannot express that.
* `nonlocal` (8), `del d[k]` (8), multi-`except` (1, the CPG discards exception types).

### The call-closure gap is now the interesting number

166 hole-free but only 45 call-closed. The 121-function difference is functions that
contain no holes themselves but call something outside the translated program — mostly
Python builtins and stdlib. That is not a transpiler defect; it is the honest observation
that **a function is only as analysable as its callees**, and it points at the next piece
of work: a modelled standard library, not more CPG mapping.

## 19. Tier 2 closed, and the oracle caught itself lying

### The short-circuit bug became real, then was fixed

§13 Tier 2 item 2 recorded that `&&`/`||` evaluated both operands eagerly, and called it
*conservative* — a hole rather than a wrong answer — "only because Core has no side
effects". Adding exceptions removed that excuse. With `%0` now raising, the harness caught:

```
safemod(-11, 0):  cpython = 0,  lean = raised ZeroDivisionError
```

`b != 0 and a % b == 0` divides anyway. That is an actively wrong answer. `evalExpr` now
short-circuits before evaluating the right operand: **6/6 agree**.

Worth noting *why* this became detectable: the bug existed all along, but was invisible
until exceptions were first class. Fidelity work makes other fidelity bugs findable — the
gaps are not independent.

### `hole-free ≠ runnable`, confirmed independently

The harness found two supposedly hole-free `cachetools` functions that hit unresolvable
calls at runtime — `call:_CacheInfo`, `call:info`. This is §17's finding arrived at from
the other direction, by execution rather than by static analysis, and it is why the ledger
now reports call-closure separately.

### The oracle was lying, silently

The single most important process finding of this pass: **a stale `.olean` was answering
with the previous semantics.** It produced 10 fictitious divergences and 22 fake
inconclusives before being noticed. The harness now runs `lake build` on the generated
module before comparing.

Generalize it: this project's entire trust story rests on oracles that do not share the
artifact's assumptions (§17). An oracle reading a stale cache shares the *old* artifact's
assumptions, which is worse than having no oracle — it produces confident, specific,
wrong findings. **Any oracle must establish that it is reading the current artifact
before it reports anything.** That check belongs in the oracle, not in the caller.

### Measured conformance after Tier 2

| Corpus | functions (total / hole-free / exercised) | compared | agree | diverge | inconclusive |
|---|---|--:|--:|--:|--:|
| cachetools (test-suite driven) | 233 / 166 / 7 | 58 | **42/42 (100%)** | 0 | 16 |
| stress | 6 / 5 / 5 | 25 | 25/25 | 0 | 0 |
| sample | 5 / 2 / 2 | 10 | 10/10 | 0 | 0 |
| ctest (`cc`) | 7 / 6 / 6 | 25 | 25/25 | 0 | 0 |
| shortcircuit | 1 / 1 / 1 | 6 | 6/6 | 0 | 0 |

`cachetools` went from **zero** comparable cases to 42 compared and agreeing, including
method calls against reconstructed receivers — because the harness now drives from the
repository's own test suite (§3's "every repo ships its own conformance suite"), snapshots
the receiver into a Lean `Heap` literal, and compares structured values and exceptions
rather than only integers.

Honest coverage limits, reported rather than smoothed: 109 calls skipped because the
receiver is a `tuple` subclass (a value, not an object with fields — Core cannot represent
it), 34 skipped for `float` arguments, 2 hole-free methods never reached by the suite.

### Tier 2 status

| item | status |
|---|---|
| 1. integer width | **closed** — `Numeric.lean` wired; `ub ↦ hole` |
| 2. short-circuit | **closed** |
| 3. differential coverage | **closed** — test-suite driven, structured values, exceptions, methods |
| 4. heap / aliasing / mutation | **closed** — done as part of Tier 1 |
| 5. naive scoping | open — no closures, globals, `nonlocal` (8 holes on cachetools) |
| 6. strings conflated | open — Python `str` and C `char*` are one `Val.str` |

## 20. Refinement: the debt that mattered most

§13 called the missing deep≈shallow refinement "the single largest architectural debt",
because proving anything against `execStmt` applied to a concrete AST does not scale.
`Autoform/Refine.lean` closes it.

```lean
inductive Outcome | ret : Val → Outcome | raise : Val → Outcome
def Refines p name N dom spec : Prop :=
  ∀ args, dom args → ∀ fuel, N ≤ fuel → runFunc p fuel name args = (spec args).toEResult
```

Three design choices make it non-vacuous, each backed by a theorem rather than a comment:

* **`Outcome` has no `hole` and no `outOfFuel` constructor.** A refined function provably
  never reports either (`refines_not_hole`, `refines_terminates`). Exceptions *are*
  refinable — "raises `ZeroDivisionError`" is a specification — but hole and outOfFuel are
  statements about our ignorance, so a spec cannot quietly absorb them.
* **Fuel is universally quantified above a concrete bound**, not existential, so the answer
  must be fuel-stable.
* **`refines_unique`**: two shallow specs refining the same entry point agree on the domain.

Proved on real translated functions: `poly`, `clamp`, `cdiv` (C) and `add`, `absval`,
`cmpchain`, `fmod` (Python). `cdiv`/`fmod` are the dialect-sensitive pair — same shape,
`.cLike ↦ Int.tdiv`, `.python ↦ Int.fmod` — both now proved.

### The two negative results are the real evidence

* `fdiv_not_refinable` — `ops.py:fdiv` contains `Expr.hole "op:floorDiv"`, and **no**
  shallow spec, at any fuel bound, on any domain containing a nonzero divisor, refines it.
  Holes are not merely inconvenient; they are provably unspecifiable.
* `poly_not_refinable` — with fixed-width arithmetic wired in, `poly` does **not** refine
  `a*b + c - a` on the unrestricted domain. The witness is `a = b = 100000`, the same
  value that produced the original `1410065408` divergence against `cc`.

That is the loop closing on itself: a bug found by the differential oracle, fixed by
parameterizing the semantics, and now permanently recorded as a machine-checked
impossibility theorem. `poly_refines` holds only under `Fits32 (a*b) ∧ Fits32 (a*b+c) ∧
Fits32 (a*b+c-a)` — which is what the `dom` parameter was for, and why it is not decoration.

`clamp_deep_idem` shows the payoff: idempotence is proved by `omega` on the plain Lean
function, then transferred to the deep term with no interpreter in sight.

All headline theorems: `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

Open obligations, stated rather than admitted: general fuel monotonicity for the full
language; loop invariants (`sumto`, `gcdish` are hole-free but need an invariant rule);
heap-mutating methods (need a representation predicate).
