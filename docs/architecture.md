# Architecture

How the pieces fit together. `STRATEGY.md` holds the full design record; this document is
the map.

## The approach

Programs are not translated into Lean definitions with theorems then guessed about them.
In that arrangement the translation is unfaithful, nothing checks the faithfulness, and
the resulting theorems are vacuous.

Instead the language is formalized, not the program.

1. A definitional interpreter for the source language is written *inside Lean*
   (`Autoform/Lang/Core/Semantics.lean`). It is written once and reused for every program.
2. The codebase is mechanically transpiled into a **term** of that interpreter's syntax
   type — a deep embedding. This step is a parser plus a printer, not a model: total,
   deterministic, diff-testable.
3. Every property of the program is then a theorem about `eval` applied to a concrete AST.
   The semantics is checkable against reality by differential-testing `eval` against the
   real runtime, so the trust story does not begin with "assume the translation is right".
4. A shallow embedding is layered on top (`Autoform/Refine.lean`): prove once that the
   deep term is observationally equivalent to a clean Lean function, then reason in the
   clean world. This is the Aeneas/`hax` playbook.

The artefact under proof is *data*. A program is a `Autoform.Core.Program` value, a
coverage metric is a fold over that value, and a "specification" is a statement about
`runFunc` applied to it.

## The CPG as a universal AST

Step 2 is normally per-language: one front end, one syntax type and one transpiler per
supported language. Joern's **code property graph** collapses that. C, C++, Java,
JavaScript, Python, Kotlin and compiled binaries all normalize into a single node
vocabulary — `CALL`, `IDENTIFIER`, `LITERAL`, `CONTROL_STRUCTURE`, `RETURN`, `BLOCK`,
`FIELD_IDENTIFIER`, `METHOD_REF`, `TYPE_REF` — with operators appearing as `<operator>.*`
calls. The system therefore writes:

* **one** semantics for that vocabulary (`Autoform/Lang/Core/*`),
* **one** CPG → JSON exporter (`cartographer/export_ast.sc`),
* **one** JSON → Lean printer (`cartographer/render_lean.py`),

and every Joern-supported front end is covered. Compared with the alternative (compile
everything to Wasm and write one Wasm semantics), source-level structure survives, which
keeps the deep≈shallow refinement tractable.

The cost falls in one place: **constructs that look alike across languages are the
dangerous ones.** Integer division rounds toward negative infinity in Python and toward
zero in C. `char*` arithmetic is not string concatenation. `<operator>.and` is bitwise,
not logical. Each such construct is a latent *dialect parameter*, and the semantics
carries `Core.Dialect` explicitly rather than picking a winner. See
`docs/core-language.md`.

## The pipeline

```
source tree
   │  joern-parse
   ▼
CPG (cpg.bin)
   ├── cartographer/formalization_graph.sc ─▶ formalization-graph.json
   │        call graph, effect classes, formalizability score
   │
   │  cartographer/export_ast.sc
   ▼
language-neutral JSON AST  (ast-<Module>.json)
   │  cartographer/render_lean.py
   ▼
Autoform/Generated/<Module>.lean   :  Autoform.Core.Program
   │  lake build            ── type-checks
   ├── scripts/differential.py     ─▶ conformance.json   (vs CPython / cc)
   ├── scripts/core_oracle.py      ─▶ core-oracle.json   (execution vs coverage claim)
   ├── scripts/audit_all.py        ─▶ audit.json         (axioms + escapes + leanchecker)
   ├── scripts/mutate.py           ─▶ mutation.json      (specification teeth)
   ├── Autoform/Ledger.lean        ─▶ ledger-<Module>.json
   └── scripts/sacm.py             ─▶ sacm-<Module>.json (SACM assurance case)
```

`./autoform.sh <src> <Name>` runs the top half (through the ledger).
`./assure.sh <src> <Name>` runs all of it. See `docs/running.md`.

Two properties of this arrangement are load-bearing:

* **Nothing is silently dropped.** A construct the exporter cannot translate faithfully
  becomes an `Expr.hole` / `Stmt.hole` tagged with the CPG node label that produced it.
  The ledger counts holes by cause; `scripts/sacm.py` turns each hole label into a named
  SACM `Assumption` node, so an untranslated construct appears in the argument rather
  than vanishing from it.
* **Every number has an oracle that does not share the artefact's assumptions.** Static
  hole counting is computed from the same AST it describes. The execution oracle
  (`core_oracle.py`) and the differential oracle (`differential.py`) exist to disagree
  with it. See `docs/trust-model.md`.

## Module layout

### `Autoform/Lang/Core/` — the semantic kernel

| File | Role |
|---|---|
| `Syntax.lean` | The universal deep embedding: `Val`, `Obj`/`Heap`, `Lit`, `Expr`, `Stmt`, `Func`, `Program`, `Dialect`, `EResult`, plus the hole/size folds the ledger is built on. |
| `Semantics.lean` | The fuel-indexed total interpreter: `Env`, `Ctx`, `evalExpr`/`execStmt`/`applyFunc`/`applyClosure`, operator application, name resolution, `runFunc`/`runMain`. No `partial`, no `sorry`. |
| `Numeric.lean` | Machine integers as a dialect parameter: `Width`, `IntType`, `NumConfig` (Python / C32 / C64 / unsigned / Java / Go presets), and `NumResult` with `ok`/`divZero`/`trap`/`ub`. Undefined behaviour becomes a hole, never a number. |
| `Stdlib.lean` | A modelled Python standard library and builtins, consulted *after* user functions. Every entry returns `none` — falling through to a visible hole — on any argument shape it cannot model faithfully. Under `.cLike` it returns `none` for everything. |
| `Float.lean` | IEEE-754 binary32/binary64 as an explicit bit pattern (`Fl`) with exact-rational rounding, plus Python's float semantics (`pyMod`, int/float comparison without coercion, `OverflowError`). Chosen over Lean's `Float` because `Float` is an opaque `@[extern]` type the kernel cannot reduce. As of this writing it is a standalone development: `Val` has no `float` constructor and `Semantics.lean` does not import it, so floats still reach the interpreter as holes. Check with `grep -n float Autoform/Lang/Core/Syntax.lean`. |

### `Autoform/Lang/Imp/` — the worked example

`Syntax.lean` and `Semantics.lean` define a minimal imperative language with two
presentations kept apart: `BigStep`, an inductive relation that *is* the specification,
and `eval`, a computable fuel-indexed interpreter. `evalStmt_sound` bridges them. Imp
exists to exercise the harness end to end, including the mutation gate, on a small
subject.

### `Autoform/` — the verification and accounting layer

| File | Role |
|---|---|
| `Refine.lean` | Deep ≈ shallow. `Refines p name N dom spec` says the interpreter applied to the translated AST equals a clean Lean function, for every fuel budget above a stated bound, on a stated domain. `Outcome` deliberately has no `hole` and no `outOfFuel` constructor. |
| `Ledger.lean` | Coverage arithmetic and the trust ledger: hole-free, call-closed, dynamic-hole risk, holes-by-cause; `Program.ledger` (human) and `Program.ledgerJson` (evidence for the assurance case, tagged with module and dialect). |
| `Overflow.lean` | Derives representability obligations (`Fits32`-style side conditions) mechanically from the AST, with a soundness theorem: if the generated obligations hold, evaluation agrees with the exact mathematical value and in particular is never `hole "ub:…"`. |
| `Contracts.lean` | Boundary contracts for code outside the verified core. Being written concurrently — see `docs/contracts.md`. |
| `Harness/Audit.lean` | `#audit_axioms`, `#audit_depends`, `#audit_ledger`, implemented as Lean metaprogramming over `Lean.Environment`. |
| `Harness/Conformance.lean` | Specimen-derived generators and checkers over the `BigStep` relation; `plausible` used as a **refutation** gate before a prover is allowed to spend time. |
| `Tactics/Portfolio.lean` | The tiered proof portfolio, with the guard that a rung counts as success only if the resulting term passes `hasSorry`/`hasExprMVar` screening. Exhaustion records an `Obligation` as data; it never admits a theorem. |
| `Specs/*.lean` | Hand-written specifications *about generated modules*, stated by import so that mutating the generated file mutates the subject of the theorems. |
| `SpecsGen/*.lean` | The hand-written vocabulary (`Case`, `Obs`, the `law*` predicates, `MRefines`) that machine-synthesized specifications are generated in, plus the generated specs themselves. |
| `Generated/*.lean` | Transpiler output. Data literals; never hand-edited. |

### `cartographer/` — the front end

| File | Role |
|---|---|
| `formalization_graph.sc` | Joern query producing the formalization graph: call graph, effect classification (io / ffi / reflection / concurrency / nondeterminism), and a formalizability score. The scoring weights are the policy. |
| `export_ast.sc` | CPG → language-neutral JSON AST. Deterministic, no model on this path. Also answers the whole-program questions the node vocabulary cannot: module-level bindings, which function values capture an enclosing scope, and which operators change meaning under the dialect. |
| `render_lean.py` | JSON AST → Lean `Program`. A pure function of the JSON: no timestamps, no dict-order dependence, byte-identical output for identical input. Infers the dialect from the file extension. |
| `run.sh` | Cartographer-only driver (source tree → formalization graph). |

### `scripts/` — orchestration and oracles

| File | Role |
|---|---|
| `differential.py` | The conformance oracle. Drives from the repository's own test suite via a `sys.settrace` hook, snapshots receivers into a Lean `Heap` literal, and compares structured values and exceptions against the Lean interpreter. Three-valued: agree / diverge / INCONCLUSIVE. |
| `core_oracle.py` | The execution oracle for the ledger's verifiable-core claim: runs every function in the claimed core over many inputs instead of analysing the AST that produced the claim. |
| `audit_all.py` | Axiom sweep over every declaration, source sweep for escape hatches (`sorry`, `partial`, `unsafe`, `native_decide`, `@[implemented_by]`, `axiom`), and `leanchecker --fresh` kernel replay. Gates CI with `--strict`. |
| `mutate.py` | Source-level mutation gate — the *sufficient* anti-vacuity test. Two modes: hand-written Lean, and generated modules (where the file mutated and the file rebuilt are different). |
| `sacm.py` | Builds the SACM assurance case (G1–G5, status lattice, coverage caps) and wraps it in an in-toto Statement. |
| `synth_specs.py` | Layer 4: specification synthesis working *down* the trustworthiness ordering — existing artefacts, structural/safety specs, mined algebraic laws, cross-implementation equivalence. |
| `fvspec.py` | Runs the anti-vacuity screen over the FVSpec benchmark. See `docs/fvspec.md`. |
| `scale_test.py` | Runs the pipeline stage by stage on arbitrary source trees, recording wall-clock, peak RSS and artefact sizes per stage. See `docs/scale.md`. |
| `prover/smt.py` | External solver driver. Produces **evidence**, never a proof: an `unsat` verdict is recorded on an open obligation because no Lean proof is reconstructed from it. |
| `prover/propose.py` | Local (ollama) neural whole-proof proposer, off unless `AUTOFORM_NEURAL=1`. Output is untrusted text; every candidate is re-elaborated and screened. |
| `ledger.lean.tmpl` | The `#eval` script `autoform.sh` instantiates per module to print the ledger and write `ledger-<Module>.json`. |

## Out of scope by design

* Whole-repo formalization is not attempted. The output is a verified core plus declared
  assumptions for everything else. This is a product decision, not a limitation to be
  fixed later.
* An agent cannot close a goal. The Lean kernel is the only thing that decides whether
  something is proved, which is what makes unattended operation safe.
* The transpiler is not proved correct. Transpiler faithfulness is *tested* — see
  `docs/trust-model.md`, which states where that boundary sits.
