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
- `lake` + `reservoir` for builds; `leanchecker` (ships with the toolchain since v4.28.0;
  the standalone `lean4checker` is deprecated) for external re-verification of `.olean`s;
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
             Lean kernel · leanchecker --fresh · differential fuzzing vs real runtime
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
re-verifies all `.olean`s with `leanchecker --fresh` in a clean environment. Produces the
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
theorem/obligation database (SQLite), `#print axioms` + `leanchecker` gate in CI, trust
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
| Build, cache, kernel re-check | BUY | lake, Reservoir, `leanchecker` (in-toolchain), `#print axioms` |
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
- **Axiom/trust audit** — `#print axioms`, `leanchecker`, environment diffing: all
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

No CI; kernel re-check not in the loop; Cartographer scoring weights uncalibrated
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
  (the audit tool's own walker is unproven-terminating), and at the time **`lean4checker`
  was not installed** — since closed, see §23.
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

## 21. One more silent wrong number, found by the refinement layer

Wiring `Numeric` into `applyBinop` left `applyUnop` untouched, so unary minus still
returned mathematical negation unconditionally. Under `.cLike` that made `-INT_MIN`
evaluate to `2147483648` — a value that does not exist in a 32-bit signed integer.

Exactly the defect class `Numeric.lean` was built to eliminate, surviving on the path
nobody thought to check. Found not by the differential oracle (no test negated `INT_MIN`)
but by the **refinement layer**, which had to state `applyUnop_int_neg` as an unconditional
`rfl` and noticed that the unconditionality was itself the bug.

Now: negation routes through `NumConfig.neg`, and the C equation carries a `Fits32`
hypothesis like every other operator.

```
applyUnop .cLike  "-" (-2147483648)  ==>  -2147483648   (wraps, matching cc -fwrapv)
applyUnop .python "-" (-2147483648)  ==>   2147483648   (bignum, correct)
```

Third distinct oracle, third class of finding: differential testing catches semantics that
disagree with reality, mutation catches specifications that constrain nothing, and
**proof catches operations that were never given a specification at all.** They are not
redundant — each sees a failure mode the others are blind to, which is the argument for
paying for all three.

## 22. Tier 2 items 5 and 6

### Item 6 — C strings are not Python strings

`Val.str` served both, and `applyBinop` applied Python semantics to both. In C:

* `+` on `char*` is **pointer arithmetic**, not concatenation.
* `<` / `>` compare **addresses**, not contents.
* `==` compares **addresses**, not contents — and `Val.beq` is structural, so this was
  silently returning the Python answer for C programs.

All three are now dialect-split: correct under `.python`, precise holes under `.cLike`
(`str:pointer-arithmetic-not-modelled`, `str:pointer-compare-not-modelled`,
`str:pointer-equality-not-modelled`). Third instance of the §12 pattern — the constructs
that *look* identical across languages are the ones that mistranslate silently.

### Item 5 — scoping: closures and function values

Two additions:

* `Expr.closure f` builds `Val.clos f ρ`, capturing the enclosing bindings **by value**.
  `applyClosure` uses the captured bindings as the base environment, with parameters
  shadowing them.
* `Expr.name x` now falls back to the function table when `x` is not local, so a
  module-level function referenced as a value resolves to `Val.fn x` instead of `unit`.
  `Expr.call` dispatches through `Val.fn` / `Val.clos` held in variables.

Together these make decorators, factories, callbacks and other higher-order code
translatable rather than holed:

```
def make_adder(n): return inner     # inner(x) = x + n
use() = apply2(make_adder(10), 5)   ==>  15
```

**What is deliberately NOT done, and why.** `nonlocal` *writes* remain a hole
(`scope:nonlocal-write`). Capture is by value, so a closure cannot mutate a binding in its
enclosing frame. Making that work requires variables to be shared mutable cells — every
scope a heap frame, `Env` becoming a `Ref` — which is a correct design and a genuinely
large refactor of the interpreter, and would require re-repairing the 74-theorem
refinement layer. Global *rebinding* (`global x; x = 5`) is unsupported for the same
reason.

This is the honest boundary: reads across scopes work and are correct; writes across
scopes are a hole. Implementing writes by copying values back would appear to work on
simple cases and be silently wrong on aliased ones, which is the failure mode this project
exists to prevent.

### Revised Tier 2 status

| item | status |
|---|---|
| 1. integer width | **closed** — including unary minus (§21) |
| 2. short-circuit | **closed** |
| 3. differential coverage | **closed** |
| 4. heap / aliasing / mutation | **closed** |
| 5. scoping | **closed for reads** — closures, function values, higher-order calls; cross-scope *writes* remain an explicit hole with a stated design for closing them |
| 6. strings conflated | **closed** |

## 23. Kernel re-verification — closed, and a trap avoided

Tier 4's last open gap was that the `.olean` files had never been re-checked by an
independent kernel. It is now closed, and the way it closed is instructive.

**There was nothing to install.** `lean4checker` is deprecated: it was merged into the
Lean repository and ships as **`leanchecker`** with every toolchain from v4.28.0. We are
on v4.30.0-rc1, so it was already present at
`~/.elan/toolchains/*/bin/leanchecker`. There is no Homebrew formula, and none is needed.

```
lake env leanchecker --fresh Autoform     exit 0,  ~92s,  status VERIFIED
```

### The trap: non-fresh mode can silently pass

`leanchecker <Module>` without `--fresh` **can no-op on a module that has only imports and
no declarations of its own** — which is exactly the shape of `Autoform.lean`. Demonstrated
directly: a scratch `Bad` module with an env-hacked bogus declaration plus a `Root` module
importing it — `leanchecker Root` exits 0 silently, while `leanchecker Bad` and
`leanchecker --fresh Root` both reject it.

So the naive invocation would have produced a confident VERIFIED that checked nothing.
This is §19's lesson recurring at the very last link in the chain: **an oracle that
silently passes is worse than no oracle.** The audit therefore uses `--fresh` by default
and records *which mode ran* in `audit.json`, because the two are not equally strong.

### Proof the checker actually rejects bad input

Two independent demonstrations, since "exit 0" is exactly the shape a no-op takes:

1. **Environment hacking** — `Environment.addDeclCore (doCheck := false)` installing
   `bogusFalse : False := False`. The elaborator writes the `.olean` happily; `leanchecker`
   exits 1 with `(kernel) declaration type mismatch`.
2. **Tampering this project's own build tree** — a copy of `Autoform/Refine.olean`
   recompiled with an injected bogus declaration. `leanchecker --fresh Autoform` exits 1
   with `while replaying declaration 'Autoform.tamperedFalse': (kernel) declaration type
   mismatch`. The untampered copy of the same scratch setup passes, so the failure is
   caused by the tamper and not by the harness.

Also verified: `LEANCHECKER=/usr/bin/false` → FAILED → VERDICT FAIL; a genuinely absent
binary → UNVERIFIED (never a pass), and `--strict` turns that into a failure. CI now runs
`audit_all.py --strict`, so a missing checker fails the build rather than quietly
downgrading.

Current audit state: **PASS**, axiom sweep clean over 1,696 declarations
(`propext`, `Quot.sound`, `Classical.choice` only), kernel re-verification **VERIFIED**.

## 24. Globals, closures, and a coverage number that moved the honest way

The CPG side of item 5 landed, and the exporter's findings sharpened the design.

### What the CPG actually says

* **`Method.local` is a *reference*, not a binding.** pysrc2cpg emits a `LOCAL` in the
  *inner* method for every name it closes over and for every module global it reads. A
  free-variable analysis that treats `LOCAL` as a binder concludes nothing ever captures —
  it reported 0 closures on cachetools. Bindings must come from parameters and assignment
  targets, which is Python's own rule.
* **`fullName` is the lexical nesting path**, so the scope chain is recoverable by prefix
  — but it **cannot be split on `.`**, because `cachetools/keys.py:<module>` itself ends in
  the dot-segment `py:<module>`. String surgery classifies module scope as an ordinary
  function and concludes every module-level `def` captures the module.
* **Module-level `def`/`class` are assignments**: `hashkey = def hashkey(...)`,
  `Cache = class Cache<meta>(...)`. So one rewrite of module-scope assignment to
  `setGlobal` makes constants, classes and functions resolvable together.
* **C `typeFullName` gives `char*` directly**, including on literals, so item 6 needed no
  inference.

### The numbers moved down, and that is the finding

| | before | after |
|---|--:|--:|
| real functions hole-free | 166 | **148** |
| holes on real functions | 102 | **120** |

The 18 new holes are `scope:class-closure`. `cachetools/_cachedmethod.py` defines classes
*inside* functions, and their methods read the enclosing function's parameters. Those six
functions previously counted as hole-free while returning a class whose methods reference
names that exist nowhere in the translated program. `Expr.closure` names a *function*;
there is no constructor for a class-valued closure, and `fnref` would have been the
silently-wrong answer.

The C string result is starker: on a purpose-built C corpus, **5/5 functions were reported
hole-free before and 1/5 after** — because four of the five were being mistranslated,
`s + n` concatenating a pointer and `a < b` comparing contents instead of addresses.

Both movements are the metric getting *more honest*, not the tool getting worse. This is
now the fourth instance of §17's rule: a number computed without an oracle that disagrees
with the artifact will flatter itself.

### Open, and deliberately not guessed

* **Cross-file initializer ordering.** The transpiler emits one zero-argument `Func` per
  source module and `runMain` executes them in list order. The CPG does not give a
  cross-file dependency order, so a module reading another module's globals depends on
  list order. Recorded rather than resolved by a guessed topological sort.
* **`Expr.classClosure`** — the constructor that would close the 18 `scope:class-closure`
  holes.
* **`<metaClassCallHandler>` synthetics** pad the function count; the `synthetic` filter
  excludes `<metaClassAdapter>` but not these. Left alone so that this pass's numbers move
  for one reason only.

## 25. The oracle recovered, and found the next silent mistranslation

Adding globals regressed the differential harness to 0/0 — it started from an empty heap,
so every global read resolved to `unit`. Re-integrated via `initGlobals`, with two details
worth recording:

* **Receiver addresses are computed Lean-side.** The globals frame occupies ref 0, so
  receiver objects must be allocated from `h₀.length` onward. Rather than trust Python
  arithmetic to get that offset right, the harness emits `Val.ref (base + k)` with
  `base := h₀.length` evaluated in Lean.
* **The harness checks its own setup before reporting.** Each case carries the class name
  Python recorded for every receiver; the runner refuses to compare unless the object at
  `gref` is still `<globals>` and each receiver's class matches, returning
  `harness:receiver-alias` / `harness:globals-frame-clobbered` as INCONCLUSIVE. Verified by
  fault injection: with `base - 1` — the exact off-by-one that would alias the globals
  frame — it reports the alias rather than a false agreement.

That is §19's rule applied to the oracle itself: an oracle must establish it is measuring
what it thinks it is measuring before it reports anything.

Reach went from 42 compared cases across 7 functions to **87 across 61**.

### The finding: Python private name mangling

All 16 divergences share one root cause. Inside a class body, CPython rewrites `__name` to
`_ClassName__name` at compile time. We emit

    .field (.name "self") "__maxsize"

while CPython stores `_Cache__maxsize`. The read misses and returns `unit`:

    Cache.maxsize():  cpython = 2,  lean = unit

Silently wrong, not absent — the same category as `floorDiv` and the bitwise `and`/`or`
mapping. Notably the harness author declined to make the *value encoder* also expose
unmangled aliases, which would have made the numbers agree while leaving the transpiler
wrong. Fixing the measurement to match a broken artifact is the most tempting failure mode
in this whole design, and refusing it is what keeps the conformance number meaningful.

### Honest ceilings on this corpus

The structural losses are now larger than the fixable ones: `skip_self_not_object` 1,527
(receivers that are `tuple`/`dict` subclasses, which Core cannot represent as objects),
`skip_unencodable_args` 534 (floats, locks, sets), `skip_varargs` 340. The 57 "no instance
reached by the test suite" skips are unrelated to globals and did not move.

Dominant inconclusive labels, i.e. what would buy the most oracle reach next:
`setField:non-object` (49), `call:set` (25), `mcall:__init__:non-object` (20),
`in:non-container` (15).

## 26. Name mangling, and a fix that paid for itself twice

CPython rewrites `__name` to `_ClassName__name` inside a class body, at compile time. The
transpiler did not, so `Cache.maxsize` read a field that does not exist and returned
`unit` where CPython returned `2`. Sixteen divergences, one root cause.

The fix hooks in at exactly two places — `asField` (the single source of the attribute
name for `field`, `setField` *and* `mcall`) and `mangledFullName` (the last segment of a
method's `fullName`) — so **references and definitions move together**. Getting only one
side would have converted a silent wrong answer into a silent unresolvable call, which is
not obviously an improvement. Verified against CPython `__dict__` on a purpose-built
corpus: `__priv`, `___three`, `__trail_` mangle; `__dun__` and `_one` do not; the
mangling class is the *lexically enclosing* class, not the receiver's, which is what makes
`Cache.__getitem__` reach `_Cache__data` even when `self` is an `LRUCache`.

Hole counts are **completely unchanged** — mangling is a renaming, not a coverage change.
Divergences went to **zero**.

### The second payoff

The harness recovers qualified names from the source AST (Python 3.9 has no
`co_qualname`), and it was not mangling them — so a traced call to `LFUCache.__touch`
never matched the translated `LFUCache._LFUCache__touch`, and two functions were silently
dropped from the oracle's reach. Applying the same rule there restored them, and one of
the two restored functions **immediately produced a new divergence**:

    LFUCache._LFUCache__touch(tuple[ref 6]): cpython = unit, lean raised KeyError

So the coverage fix and the bug it found were the same change. That is the general shape
worth noticing: *the oracle's blind spots and the artifact's bugs are correlated, because
both come from the same unmodelled language rule.* Fixing reach is not separate from
finding defects; it is how you find them.

### That last divergence is the apparatus, not the artifact

`__touch` begins `link = self.__links[key]`. The `key` argument arrives encoded as an
object reference (a `_HashedTuple` — a tuple subclass — snapshotted as a heap object),
while the keys stored inside the receiver's `__links` dict were encoded as tuple *values*.
`Val.beq` cannot equate `.ref n` with `.tuple [...]`, the lookup misses, and Core raises
`KeyError` where CPython succeeds.

The deeper defect is that the representability check applies to top-level arguments but
not to values nested inside a receiver's fields, so an unrepresentable nested value can
surface as a *confident divergence*. **An oracle must not report a disagreement it caused
itself** — the same discipline as §19's stale `.olean` and the receiver-alias guard of
§25, one level further in.

### Ceilings, restated with current numbers

`skip_self_not_object` 1,527 · `skip_unencodable_args` 521 · `skip_varargs` 340 ·
`skip_no_instance` 57. These now dominate, and they bound how much of a real Python
codebase this oracle can reach *regardless* of translation coverage.

One practical note: `find_tests` did not locate `tests/` when given the repo root, because
the AST paths are relative to `src/`. The `src/`-layout-with-sibling-tests arrangement is
the modern default, so discovery needs to walk up from `src_root`.

## 27. The last divergence was the apparatus — and the diagnosis is a scope boundary

Resolved, with a sharper cause than the encoding inconsistency I guessed at in §26.

The failing case is `LFUCache.__touch` driven by `test_func.py`, whose helper is:

```python
class RecursiveEquals:
    def __hash__(self):      return hash(self._use_cache)
    def __eq__(self, other): return self._use_cache == other._use_cache
```

The test primes the cache with one instance and then looks up a **different instance that
compares equal**. CPython's dict lookup succeeds through `__hash__`/`__eq__`; Core compares
`Val`s structurally with `.ref` identity, misses, and raises `KeyError`.

**This is a scope boundary, not a bug.** A Python dict keyed by objects with user-defined
equality is outside what a structural `Val` comparison can model at all. 27 cases are now
refused on that ground and appear in `conformance.json` under `unencodable_reasons`
rather than being compared. Naming the boundary is the deliverable; pretending the
comparison is meaningful would not be.

A second, independent silent-wrongness source was live in the same case: the encoder
**swallowed** nested representability failures, counting `dropped_fields` and continuing.
A dropped `__links` field reads back as `unit` in Core — which is exactly how an apparatus
artifact becomes a confident divergence. Representability is now recursive and fatal: an
unrepresentable value at any depth aborts the case, which is counted by reason rather than
compared.

Three further apparatus defects surfaced once refusal stopped hiding them:

* The return value was encoded with a **fresh** encoder, so a returned object got a
  colliding `ref`. One memo now spans the whole case, so a given Python object gets the
  same `Val` as receiver, nested field, argument and result.
* `Val.fn` spellings disagreed — CPython says `TTLCache._Link`, Joern says
  `cachetools/__init__.py:<module>.TTLCache._Link`. Now matched by dotted suffix and
  nothing looser, mirroring `Ctx.resolve`. Six more apparatus divergences.
* Callable *instances* were being encoded as `Val.fn`. Only routines, classes, `partial`
  and descriptors are functions; an instance with `__call__` has fields and is an object.
  Recovered 274 previously-refused cases.

### Result

| | before | after |
|---|--:|--:|
| compared cases | 67 | **99** |
| functions exercised | 61 | **79** |
| divergences | 1 | **0** |
| "no instance" skips | 57 | **40** |

Independently re-verified: **99/99 agree (100%), 0 divergences**, and passing the bare
repo root now works — `resolve_src_root` corrects to `<repo>/src` and finds
`<repo>/tests`. Regressions green: stress 30/30, sample 10/10, ctest 25/25 vs `cc`.

### The pattern, stated once more

Every divergence in this episode was the measurement, not the artifact — and each was
found only because refusing to compare exposed what dropping had hidden. **Strictness in
an oracle buys accuracy, not just safety**: the stricter the refusal, the more of the
remaining agreements mean something. `MAX_DEPTH` and `MAX_ELEMS` were raised to pay back
the coverage that stricter refusal cost, which is the right trade — reach bought by
honesty, not by leniency.

### Ceilings, current

`skip_unencodable_args` — dominated by caches wider than 256 entries (15,487) and floats
(6,995, which Core has no type for); `skip_varargs` 13,188; `skip_self_not_object` 1,361.
Top inconclusive labels: `setField:cache_clear:non-object` 49, `mcall:__init__:non-object`
36, `call:super` 30, `call:set` 22.

## 28. Refinement reaches real code shapes

§13 called the missing deep≈shallow refinement "the single largest architectural debt", and
§20 closed the straight-line case. Two obligations remained, and they were the ones that
mattered: refinement could not touch a loop or a mutated object — i.e. not what programs
are made of. Both are now closed.

### The loop rule

`execStmt_loop_rule` is a Hoare while-rule adapted to the fuel-indexed interpreter, with
one design choice doing the work: the invariant `I : Nat → Heap → Env → Prop` is **indexed
by a termination measure that must strictly decrease**, and the fuel bound is derived from
it. Partial correctness and termination are therefore proved *together* — at measure `0`
the step obligation would have to produce `m' < 0`, so the invariant can only exit.
`execFor_rule` is the `for` counterpart with the remaining sequence as the measure.

Proved on real translated functions, not toys:

* `sumto_refines` (C, from `math.c`): `sumto n = n*(n+1)/2`. The per-iteration `Fits32`
  obligations are discharged from a **closed-form** domain via monotonicity of the
  triangular-number function, so the domain reads `0 ≤ n ∧ n ≤ 65535 ∧ Fits32 (n*(n+1)/2)`
  rather than a quantified per-step mess.
* `gcdish_refines` (Python, from `ops.py`): `gcdish a b = Int.gcd a b`. The measure is
  `b.natAbs`; correctness rests on `gcd a b = gcd b (a % b)`, and `%` here is `.python`
  (`Int.fmod`), which agrees with `Int.emod` only because both operands are nonnegative.
  **The dialect split reappearing inside a loop invariant** — §16's parameterization is not
  a peripheral concern, it reaches into the proof obligations themselves.

### The representation predicate

`HeapRep α` pairs a class name with a **partial** abstraction function, and
`Represents R h r a` says heap object `r` represents abstract value `a`. Two lemmas make it
usable: `Represents.frame` (a write to another address preserves it) and
`Represents.update` (a write to this address re-establishes it), both proved against the
real `Heap.setField` (`List.mapIdx`).

`abs` being partial is the load-bearing choice: an ill-formed object represents *nothing*
rather than something wrong. Concretely, an instance of a function-local class (one with a
captured frame) returns `none`, so it is not represented rather than silently
mis-represented.

Proved end to end on a `Counter` class: `bump_step` is a full dispatch of a method that
**mutates its receiver** — receiver evaluation, argument evaluation, `resolveMethod`
dispatch, field read, field write, return — ending in a heap that still represents, now at
`a + k`. `total_run` carries an invariant through `execFor_rule` over an arbitrary list,
through object construction and `__init__`; `total_refines` lands in `Refines` proper, so
§20's non-vacuity theorems apply (no hole, terminates in `|ys| + 13` fuel).

### An incidental finding worth knowing

**`String.endsWith` does not reduce definitionally** — it goes through `String.Slice`
pattern matching. So `Ctx.resolveMethod`, which resolves by suffix, cannot be discharged by
`rfl` the way `Ctx.resolve` can on an exact name; it needs `simp [String.endsWith]; decide`
per name. Any proof touching method dispatch will hit this.

### Still open, stated not admitted

**Loop cost is input-dependent, but `Refines` carries a constant fuel bound.** So the
`Refines` instances need bounded domains (`n ≤ 65535`, `b ≤ 1000000`) while the parametric
`_run` theorems are the sharp statements. Making `Refines` carry an argument-dependent
bound is the honest fix and is not done — this is a real limitation of the refinement
relation, not of these proofs.

Also: `n ≤ 65535` in `sumto`'s domain is *implied* by `Fits32 (n*(n+1)/2)` but stated
rather than derived, because deriving it needs nonlinear arithmetic unavailable without
Mathlib. And representation covers field-mutating objects only; container classes need
boxed containers first.

All headline theorems: `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

## 29. "Universal" is aspirational: the front end generalizes, the back end does not

Five new languages were run through the unmodified pipeline. The architectural bet is
half-vindicated and half-refuted, and the split is clean.

| language | corpus | parses | compiles | hole-free | verifiable core | oracle |
|---|---|:--:|:--:|--:|--:|---|
| Python | cachetools | ✅ | ✅ | 76% | 19% | **CPython** |
| Java | gson | ✅ | ✅ | **52%** | 28% | **none** |
| TypeScript | p-queue | ✅ | ✅ | 51% | 21% | none |
| JavaScript | p-map | ✅ | ✅ | 35% | 7% | none |
| C | antirez/sds | ✅ | ✅ | 29% | 13% | crashed |
| Go | envconfig | ✅ | ✅ | 25% | 7% | none |

**The front end is real.** Five languages parsed, exported and type-checked with *zero*
exporter or semantics changes, and Java gave the best hole-free rate measured anywhere.
That is the CPG-as-universal-AST bet paying off.

**The back end is not.** There are two dialects for six languages, `.cLike` means
"32-bit truncating C", and `differential.py` picks its runtime with one line —
`runtime = "cc" if is_c else "cpython"` — so Java, Go, JS, TS and Kotlin are all handed
to CPython, produce zero cases, and print "no comparable cases". **The oracle that found
every dialect bug in this project's history does not exist for four of six languages**,
which is why the findings below had to be found by hand.

### Six silent mistranslations, one of which was in the flagship corpus

1. **`and`/`or` return an operand, not a bool — including Python.** `pick(0,5)` is `0` in
   CPython and was `True` in Core; `both(2,3)` is `3` and was `True`. It survived because
   cachetools only uses them in *conditions*, where truthiness makes the two
   indistinguishable — lodash uses 551 of them in *value* position. **Fixed**, and
   dialect-split: C's `&&`/`||` genuinely do yield 0/1.
2. **Unknown extensions silently got the Python dialect.** `infer_dialect` returned
   `.python` when nothing voted, so a `.tsx` file was translated with floored division:
   `-7 % 3` gave `2` where TypeScript gives `-1`. The §12 modulo bug re-entering through
   the extension table. **Fixed** — it now refuses.
3. **JS numbers are doubles; Core gave 32-bit ints.** `2147483647+1` → `-2147483648`
   (JS: 2147483648); `7/2` → `3` (JS: 3.5); `5/0` → `ZeroDivisionError` (JS: Infinity).
4. **JS `==` and `===` are the same Core operator** — `jssrc2cpg` emits
   `<operator>.equals` for both, so the distinction is erased *before* Core sees it.
   Not fixable in the semantics.
5. **Java `long` and Go `int` are 64-bit; Core models 32.** `100000L*100000L` → 1410065408.
   `Numeric.lean` already defines `java32`/`java64`/`go64` — but `Dialect` has only
   `python | cLike`, so they are unreachable dead code.
6. **`.cLike` string rules are C's, applied to Java/JS/TS.** `"a"+"b"` becomes a pointer
   hole instead of `"ab"` — safe, but the exact inverse of the case §22 fixed.

### The lesson

§22 split strings by dialect and called item 6 closed. It was closed *for C versus
Python* — and then applied C's rules to three languages that are neither. **A two-valued
parameter cannot express a six-way distinction**, and every time this project has added a
dialect axis it has under-provisioned it: one for integer division, then unary minus, then
strings, now widths and boolean-operator semantics. The right shape is a dialect per
*language*, wired to the `NumConfig`s that already exist, with `infer_dialect` refusing
rather than guessing — not another boolean.

## §30 — The verifiable core survives execution about 40% of the time

`scripts/core_oracle.py` ran the claimed verifiable core and refuted it. The claim was
74 of 238 `cachetools` functions hole-free *and* call-closed. Executed over 1,056 cases
with 100% of the claimed core exercised — 46 of them on arguments recorded from
cachetools' own pytest suite under `sys.settrace` — **30 of 74 never holed**, and **21
were refuted on a real input a CPython test actually passed**. Against the earlier
45-function claim the same harness gave 24/45. The ratio is stable at roughly 40%.

This is §17 again, measured. §17 said static hole-freedom is an upper bound on runtime
hole-freedom. It is, and the factor is about 2.5x.

Two distinct errors were tangled together, and separating them mattered:

1. **A real bug in the ledger, now fixed.** `Ctx.resolvable` was widened to mirror
   `Ctx.resolveMethod`'s first-match rule — correct for method calls, where `clear` has
   9 candidates and the interpreter dispatches fine. But `Analysis.eCalls` flattened
   `.call` and `.mcall` into one untagged `List String`, so the method rule was applied
   to **free** calls too, which really use `Ctx.resolve` and its *unique*-match
   requirement. `_wrapper` and `cache_clear` have several definitions each: the ledger
   called them resolvable, `Ctx.resolve` returns `none` on the ambiguity, and the
   interpreter holes. Calls are now tagged with their dispatch path and answered per
   path. Cachetools' core: **74 → 69**.

   Note the shape. The first version was too strict, understating the core by 14. The
   fix for that overshot into too loose. Both were single-rule answers to a two-path
   question, and a flat `List String` made the second error unstatable rather than
   merely unnoticed.

2. **Not a bug — the remaining gap.** The ambiguity fix accounts for 5 functions; the
   oracle's 44 refutations are mostly something else. `setField:<f>:non-object` (89),
   `mcall:clear:non-object` (90), `in:non-container` (80): setting an attribute on a
   `Val.fn` (decorating a function) is not modelled, and `key in self` has no object
   receiver. These are gaps in the *semantics*, not in the ledger's description of it,
   and no amount of care in `Ledger.lean` would have found them. Only execution did.

The recurring rule holds a fourth time: a metric computed from the same artifact it
describes will flatter itself. `verifiableCore` is computed from the AST and the program
table; the only thing that refuted it was running the program.

Two apparatus defects the oracle's author caught in their own harness, worth recording
because both would have produced a *better-looking* number: `differential.py`'s
`parse_result` rejects `Val.clos`, which would have turned three genuine closure results
into fake INCONCLUSIVEs; and a synthetic receiver with no fields makes every attribute
access hole for reasons that are ours, not the program's, so `harness:` holes are
excluded from the evidence entirely. §27 said the last divergence was the apparatus. It
keeps being the apparatus.

## 20. Fuel monotonicity (`Autoform/FuelMono.lean`)

Open obligation #1 of `Refine.lean` §5 is closed, with one exclusion that is not a proof
artefact. All seven mutually recursive interpreter functions (`evalExpr`, `applyFunc`,
`applyClosure`, `evalList`, `evalPairs`, `execStmt`, `execFor`) satisfy
`f k … = (h', r) → r ≠ outOfFuel → f (k+1) … = (h', r)`, and the `k ≤ k'` form follows;
the proof is one induction on fuel over a seven-way conjunction, since every recursive
call in the interpreter is at `k`.

The exclusion is `Stmt.tryFinally`, the only construct that does **not** propagate an
out-of-fuel sub-result: when the body exhausts fuel and the finalizer exits abnormally,
the finalizer's outcome discards the body's, so the statement returns an ordinary result
computed from a partially-mutated heap, and more fuel mutates that heap further.
`tryFinally_breaks_fuel_mono` is a machine-checked counterexample (`return 1` at fuel 4,
`return 2` at fuel 5, neither `outOfFuel`). The theorems therefore carry `tfFreeS`
side conditions; `tfFree_of_table` discharges them from a table-wide check, and
`(Generated.program.table.all fun p => tfFreeS p.2.body) = true` holds by `rfl`, so the
cachetools corpus is inside the covered fragment.

### §30.1 — Naming the language, so the approximation can be read

Four of six supported languages have no conformance oracle, and commissioning one
surfaced a prerequisite: nothing in the build ever named a language. `Dialect` has two
constructors, so Java, Go, JavaScript, TypeScript and Kotlin were all run as `.cLike`.
That is right about `and`/`or` for Java, Go and Kotlin — they yield a bool — and **wrong**
for JavaScript and TypeScript, where `0 || 5` is `5`, exactly as in Python.

`Lang` (in `Numeric.lean`) names the language and states, per language, the dialect it is
evaluated under, its `NumConfig`, its file extensions, and whether that pairing is
`approximated` — known-wrong rather than unknown. `Lang.known_wrong` currently evaluates
to `[javascript, typescript]`. This also wires `java64` and `go64`, written months ago
and never connected to anything, because nothing named a language.

This is deliberately *not* the constructor-per-language split §29 calls for. About 110
sites still `match` on `Dialect` directly, so adding constructors makes all of them
non-exhaustive simultaneously — and four agents are mid-build. The split is the right end
state; it is blocked on those sites, not on this type. What `Lang` buys now is that a
divergence found by the new oracle can be attributed: caused by the transpiler, or caused
by an approximation the build already admits to.

## §31 — Silently wrong beats absent, and 104 nodes were silently wrong

The exporter pass that closed `control:TRY-finally-escaping` (31 → 0) and
`scope:class-closure` (18 → 0) found something worse than either: **104 call nodes with an
empty callee name**. `{"k":"call","f":""}` is well-typed. It rendered, it type-checked, it
counted as *translated* — and at run time it resolved to nothing. Every hole in this
project is an admission of ignorance the ledger can count. These were not holes. They were
translated code that did nothing, inflating the coverage number in the one direction the
ledger cannot detect, because a hole-free function is exactly what the ledger looks for.

Ninety of them were the `with` statement. `pysrc2cpg` lowers `with cm as x:` into
`manager_tmp0 = cm; enter_tmp0 = manager_tmp0.__enter__; value_tmp0 = enter_tmp0()`, so
the invocation carries no name — but both halves of the method's identity are present,
split across two statements: the receiver on the call, the attribute name on the
assignment that made the temporary. Rejoining them is what made `with` translatable at
all, and it is why the `_TimedCache`/`TTLCache`/`TLRUCache` timer methods stopped being
calls into nothing.

Six were genuinely inexpressible — `cached(...)(func)`, a *computed* callee, where
`Expr.call` is by name and Core has no "apply this value". Those six functions were
counted hole-free and are not. Coverage went down for the right reason, the third time
on this project.

Two further results from the same pass:

* **Verifiable core 74 → 97, with no Lean change.** The exporter was discarding Joern's
  resolved `fullName` and emitting the short name, so `Ctx.resolve`'s unique-suffix
  fallback could not separate `_cached.py:_wrapper` from `_cachedmethod.py:_wrapper`.
  Emitting the `fullName` makes the *exact* match fire. Note this interacts with §30: the
  ledger fix made the free-call path correctly strict, and this makes the exporter supply
  the name that strictness needs. Neither alone was enough.

* **18 "hole-free" functions were padding.** `<metaClassCallHandler>` synthetics: 30
  functions removed, of which 18 had counted as hole-free. Denominator and numerator both
  fell, and none of it was coverage. On the common 208-function basis the real movement is
  hole-free **147 → 159**, holes **106 → 78**.

### The decision this leaves me: no inheritance from builtin types

`class _HashedTuple(tuple)` translates to an ordinary class, so instances are opaque
`Val.ref`s. CPython's instance *is* a tuple: `hashkey(0) == (0,)` is `True`. `Val.beq`
cannot equate a `.ref` with a `.tuple`, and `hashkey` is cachetools' cache-key function —
so this is a behavioural gap, not an encoding artifact. It was verified against the
*pre-change* 238-function program, which returns the same `ref 1`, so it predates the
exporter work and was merely exposed when the harness stopped skipping varargs.

**Decision: it stays a DIVERGENCE.** The tempting move is an oracle-side representability
rule that reclassifies it INCONCLUSIVE — "we cannot encode this comparison". That would be
false. The semantics genuinely computes a different answer from CPython, and calling that
"unrepresentable" would convert a known-wrong result into a not-measured one, which is the
§17/§30 failure in its most seductive form: the artifact that makes a metric look better
by narrowing what it measures. A real fix is a Core notion of builtin base classes, or
`alloc` producing a tagged value for such classes. Until then the divergence is the honest
output.

### An apparatus hazard that generated phantom results

`scripts/differential.py` writes its harness to a fixed `/tmp/autoform_diff.lean`. With
several agents running it concurrently they overwrite each other mid-run, so a run can
report conformance for *another agent's program*. This was live for every concurrent run
today. §27 said the last divergence was the apparatus; here the apparatus was not even
measuring the right artifact.

## §32 — Velvet/Loom: take the DSL, refuse the oracle

`verse-lab/velvet` is a Dafny-style auto-active verifier for Lean 4, built on `verse-lab/loom`,
with `requires`/`ensures`/`invariant`/`decreasing` macros, cvc5 and z3 wired in, and
property-based testing in the same environment. On the surface it is exactly the tier-2
hammer §5 asks for and this build does not have.

It is not, and the reason is one line — `Loom/SMT.lean:215`:

```lean
axiom trust_smt : ∀ (p : Prop), p
```

closed by `mkApp (mkConst ``trust_smt) goalType`. This is not "assume the solver is
right about this formula". It is a proof of every proposition. Checked directly in this
build:

```
'two_eq_three' depends on axioms: [trust_smt]     -- (2 : Nat) = 3
'false_holds'  depends on axioms: [trust_smt]     -- False
```

Adopting it would let `portfolio` close all 89 open obligations immediately, and every
one would be worthless. `scripts/audit_all.py` allows exactly
`{propext, Quot.sound, Classical.choice}`, so the sweep rejects it on sight — the gate
works, and this is the first time it has been tested against a real external tool rather
than a hypothetical.

This vindicates `#smt_evidence`. §5 wanted SMT at tier 2; the design instead reaches
cvc5/z3 through `scripts/prover/smt.py` and records the verdict as an **open obligation
carrying the solver's answer as evidence**, because no Lean proof can be reconstructed
from it. Velvet shows the alternative and what it costs: an axiom that makes the logic
inconsistent, in exchange for a green checkmark. `bv_decide` remains the counterexample
that proves the rule — SAT-backed *and* LRAT-replayed in the kernel, hence a real rung.

What is worth taking, none of which costs trust:

* **The specification DSL.** `requires`/`ensures`/`invariant`/`decreasing` as syntax over
  an existing semantics. `Autoform/Contracts.lean` builds `Contract` values by hand and
  `execStmt_loop_rule` takes its invariant and decreasing measure as explicit arguments;
  both would read better as macros, and macros carry no soundness weight.
* **Angelic vs demonic non-determinism.** This is the vocabulary for something already
  built: `RefinesUnder` quantifies over *every* implementation consistent with the
  contract, which is precisely demonic non-determinism, and `refinesUnder_of_unsatisfiable`
  is the degenerate angelic case. Naming it connects the hole mechanism to existing
  literature instead of inventing terms.
* **Partial vs total correctness kept apart, with termination separate.** The fuel-indexed
  interpreter already draws this line — `outOfFuel` is ignorance, not divergence — but the
  ledger reports one number. Velvet's separation is the cleaner presentation.

What Velvet does **not** help with: the remaining holes. `op:starredUnpack` (36),
`import:module-value` (15), `scope:nonlocal-write` (8), `op:delete-index`/`-slice` (8),
`call:computed-callee` (6) and the `_HashedTuple` builtin-base gap are all missing
*language modelling* in Core, not missing proof automation. No verifier closes them.

## §33 — Correction to §31: the apparatus lied again, and I repeated it

§31 attributed five `cachetools` conformance divergences to `class _HashedTuple(tuple)`
and Core's lack of inheritance from builtin types. **That attribution was wrong**, and it
reached the README before it was checked.

All five were contamination. A **concurrent mutation run** held
`Autoform/Generated/Cachetools.lean` while the differential harness read it, and
`_DefaultSize.pop` was a live mutant returning `0` instead of `1`. Corroborated by an
independent artifact rather than by the same agent that found it:
`f_cachetools___init___py__module___DefaultSize_pop` appears in `mutation-Cachetools.json`'s
`decls` list. Reproducing against a rebuilt module returns `1`. Two earlier divergences
(`Cache.__contains__` inverted) were the same thing.

The oracle was measuring a program nobody had written.

What makes this worth a section rather than a fix: §27 concluded the last divergence was
the apparatus, and §31 quoted that rule while committing the same error one level down.
The exporter agent's reasoning was careful and its evidence was real — it evaluated
`hashkey` on the pre-change build and got `ref 1` — but "this gap exists" and "this gap
caused those five divergences" are different claims, and only the first was established.
A true fact adjacent to the failure is the most convincing wrong explanation available.

Three defences now exist, and none of them existed this morning:

* `scripts/differential.py` detects the `.mutate-backup` sentinel, warns loudly, and sets
  `build_stable: false` / `mutation_in_progress: true`. A measurement taken over a mutant
  is now labelled as one.
* The harness copies the compiled `Autoform/Lang` tree and the generated `.olean` into a
  private directory and points `LEAN_PATH` at it, so a concurrent rebuild cannot change
  the program mid-run.
* Every scratch path is under one `mkdtemp`. The fixed `/tmp/autoform_diff.lean` meant
  concurrent agents overwrote each other's harness and could report conformance for
  *another agent's program*.

### The `_HashedTuple` gap, restated correctly

It is real and it is not a divergence. Core has no inheritance from builtin types, so
`_HashedTuple` instances are opaque `Val.ref`s while CPython's instance *is* a tuple. The
harness rules this a counted `representation:value-vs-object` INCONCLUSIVE.

§31 argued that reclassifying a divergence as "unrepresentable" would be the flattering
lie. That argument stands as a principle and was applied to the wrong facts: there was no
divergence to reclassify. The distinction that matters is whether the class is **counted
and named** — an INCONCLUSIVE bucket with a label and a number is an admission, while one
that quietly absorbs disagreements is laundering. This one is counted.

### And the headline was overstated in the other direction

`0 divergences` on `cachetools` is true and nearly uninformative: **30 of 208 functions**
are compared. The rest are INCONCLUSIVE. Reach is the binding constraint, not agreement,
and a conformance rate quoted without its coverage is exactly the metric shape §17, §30
and §31 keep catching.

## §34 — Correction to §33: I made the same inferential error twice

§31 attributed five conformance divergences to `_HashedTuple` and Core's lack of builtin
inheritance. §33 "corrected" that, saying all five were mutation contamination. **§33 was
an over-correction, and it was reached by exactly the reasoning §33 itself condemned.**

The evidence offered for §33 was that `f_..._DefaultSize_pop` appears in
`mutation-Cachetools.json`'s `decls` list. That establishes `_DefaultSize.pop` *was being
mutated*. It does not establish that it *caused those divergences* — the identical
"true fact adjacent to the failure" error §33 was written to record.

Settled first-hand rather than by agent report. `hashkey` is **not** in the mutation
`decls` list and its body is untouched by the live mutant, so it can be evaluated even
with the gate running:

```
Lean:    hashkey (tuple [int 0])  =  Val.ref 0          -- an opaque reference
CPython: hashkey((0,))            =  ((0,),)            -- type _HashedTuple
         isinstance(r, tuple)     =  True
         r == ((0,),)             =  True
```

So the `_HashedTuple` divergence is **real, and independent of mutation**. §31 was right.

And the contamination is *also* real — in the current tree
`_DefaultSize.__getitem__` evaluates to `int 1` where the pristine body returns `int 0`,
because that decl is live-mutated right now.

Both are true because they are **different runs**. Two agents each reported "5
divergences" from separate invocations at separate times, one against a pristine subject
in an isolated copy and one against the main repo mid-mutation. Neither was lying and
neither was wrong about its own run; the error was mine, in assuming two reports of the
same *count* were reports of the same *event*.

The standing rule needs a clause. "The last divergence was the apparatus" (§27) is a
prior, not a verdict — and applying it reflexively produced a wrong correction to a right
finding. A report is evidence about the run that produced it, and two runs are not
comparable unless something ties them together. `conformance.json` now carries
`measurement_basis`, `build_stable` and `mutation_in_progress` precisely so that a
future comparison can check whether it is entitled to compare.

### Standing hazard while agents run concurrently

`Autoform/Generated/Cachetools.lean` currently has **238** functions while
`ast-Cachetools.json` has **208**: a concurrent pipeline re-rendered the module from an
AST that is not the checked-in one, three separate times. Any `cachetools` conformance or
ledger number produced right now describes a build that does not correspond to the
committed AST. `scripts/check_docs.py` reports this as STALE and should keep failing
until the module is re-rendered from the AST and both are committed together.

## §35 — Closing the `_HashedTuple` gap: the payload has to be in the value

§34 settled that the divergence is real: `hashkey (tuple [int 0])` was `Val.ref 0` where
CPython's `hashkey(0)` is `(0,)`, of type `_HashedTuple`, and `== (0,)` is `True`. This
section is the fix and, more usefully, why the cheap version of the fix does not exist.

### The representation, and why the other one is not available

The obvious cheap move is `Obj.builtin : Option Val` — leave the instance a `Val.ref` and
have equality consult the heap. **It is not implementable without a much larger change
than the alternative**, and the reason is structural rather than aesthetic: `Val.beq`,
`applyBinop`, `valIn` and `Val.truthy` are pure functions of values and do not take a
`Heap`. They are also precisely the functions that have to agree with the builtin. Making
an `Obj` payload visible to them means threading a heap through `Val.beq` — which is the
`BEq Val` instance, is called from `Val.beqL`/`beqP`, from `Stdlib`'s association-list
helpers, and from dozens of `Refine.lean` theorems — and it leaves every one of those call
sites able to *forget* to consult the heap. That is the silent-wrong shape this project
keeps finding, bought at a higher price than the alternative.

So the payload lives in the value: `Val.bobj : String → Val → Val`, the class name plus
the underlying `tuple`/`list`/`dict`/`str`. There is exactly one copy of the state and no
way for a value and a heap object to disagree about it.

The predicted cost of a new `Val` constructor — "every existing match goes non-exhaustive
at once" — was **not** what the change cost. Lean flagged four matchers, all of which had
catch-alls that were already honest. What it did cost was two things nobody would have
predicted:

* Making `Val.truthy`, `Val.iterable` and `Stdlib.elems` *recursive* (`| .bobj _ v => f v`)
  compiles them through `brecOn`, and that broke ~30 `Refine.lean` proofs and the
  `whnf`-based proof of `Stdlib.builtin_heap_unchanged`. Writing the four base cases out
  by hand keeps them plain matchers that reduce by `rfl`. The same constraint forced
  `Val.beq`'s twelve explicit `bobj` cases: every recursive call has to be on a subterm of
  the *first* argument or the definition falls off structural recursion into well-founded
  recursion, and a well-founded `Val.beq` is not reducible by `decide` — which
  `beq_float_nan_self` and much of `Refine.lean` depend on.
* One case genuinely did not fit: `len` of a builtin-based instance. Adding it to
  `Stdlib.builtinCore` defeats the brute-force branch enumeration in
  `builtin_heap_unchanged`, and raising `maxHeartbeats` does not help. It is a **hole**
  with a test pinning it (`excluded_len`), not a silent `none`. `list`, `tuple`, `sorted`,
  `sum`, `min` and `max` all reach the base through `Stdlib.elems` and do work.

`FuelMono.lean` needed two new cases and no weakening: `alloc` splits on
`Ctx.builtinBase` before the existing proof (the builtin branch is a fuel-free
computation, so there is nothing to induct on), and `mcall` gains a `bobj` receiver case
mirroring the `ref` one. `fuelMonoExclusions` is unchanged at `["Stmt.tryFinally"]`.

### The refusals are the load-bearing part

`Val.beq` compares a `bobj` by contents and **ignores the class**, because CPython does:
`A((0,)) == B((0,))` is `True` for two distinct subclasses of `tuple`. That is only sound
for a class that does not override `__eq__`, so `allocBuiltin` **refuses** to build a
`bobj` for a class that defines its own `__eq__` or `__init__`, emitting
`alloc:builtin-base:<cls>:own-__eq__`. A refusal is a counted hole; honouring the class
while ignoring the override would be a silent wrong answer of the exact kind this whole
mechanism exists to remove. Same for `str(x)` of a non-string, `dict(pairs)`, a
non-iterable argument, and more than one constructor argument.

The feature is also **opt-in per class**: `Program.builtinBases` is empty by default, so a
class the exporter did not record behaves exactly as before — an opaque `Val.ref`. Every
existing corpus is byte-for-byte unaffected, which is what makes the 113 `Refine.lean` and
79 `SpecsGen` theorems a meaningful regression check rather than a coincidence.

### What is still open, and it is the exporter

`cartographer/export_ast.sc` now reads `TypeDecl.inheritsFromTypeFullName` and emits a
`classBases` map on the module initializer; `render_lean.py` turns it into
`Program.builtinBases`. **Neither has been run**: this environment has no Joern and no
corpus source, so `ast-Cachetools.json` still carries no `classBases` and the shipped
`Autoform/Generated/Cachetools.lean` therefore still has an empty `builtinBases`. The Lean
side is demonstrated against the *committed* `hashkey` body with the one base supplied at
the test site (`Autoform/BuiltinBase.lean`). That is a real gap and it is named rather
than papered over: until the exporter is re-run, the capability exists and the corpus does
not use it.

`Autoform/Generated/Cachetools.lean` is also still stale against its AST (238 functions
against 208, §34's standing hazard). Re-rendering it would delete declarations
`Autoform/SpecsGen/Cachetools.lean` depends on, so it stays a separate change and
`scripts/check_render.py` keeps failing on exactly that one module, as it did before.
