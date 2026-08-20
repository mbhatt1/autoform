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

### The CPG front end is a pinned dependency

Because the whole system is downstream of the CPG, **the neutral AST is a function of the
Joern version**. The node vocabulary, the resolved `fullName`s, whether `IS_VARIADIC` is
set on a parameter, whether an absent `for` clause is elided rather than empty — all of it
is the front end's choice, and all of it changes what the generated Lean means. Two
machines with different Joern builds can produce different `ast-*.json` from identical
source.

`lake-manifest.json` pins every Lean dependency to a revision and `lean-toolchain` pins
the compiler. **`joern-version` does the same job for the front end**, and
`scripts/provenance.py joern-version --check` compares it to what is installed. See
"Provenance" below.

### The exporter requires the source tree, not only the CPG

`cartographer/export_ast.sc` reads the original source text. This is a **precondition, not
an optimization**: CPG-only analysis is no longer possible, and a CPG whose source tree
has moved away cannot be exported.

The reason is `*args` / `**kwargs`. Joern's `pysrc2cpg` sets `IS_VARIADIC` on `*args` and
sets **nothing** on `**kwargs` — by every graph property, `**kwargs` is indistinguishable
from an ordinary positional parameter. No CPG property records the stars. What the CPG
does carry is `OFFSET`, the parameter name's byte offset in its file, so the exporter
reads the source at that offset and counts the `*`s immediately before the name.

The alternative was to treat `**kwargs` as positional, which is a silent mistranslation of
exactly the kind the hole mechanism exists to prevent. So the exporter **aborts** when it
cannot read a source file it needs, naming the file, the CPG's recorded root and the
parameter, rather than guessing. `docs/running.md` §1 states the operational consequence.

Two details worth knowing:

* The star-count is **gated to `.py` files**. In C and C++ a `*` before a parameter name is
  a pointer, and reading it as a splat would be a mistranslation rather than a hole. It is
  also why the gate must come first: because the source read is a hard error by design, an
  ungated version aborted the export of every non-Python corpus.
* The path it reads is `cpg.metaData.root` joined with the file's relative path. Move or
  delete the tree after `joern-parse` and the export fails — which is why
  `scripts/provenance.py` records `source_path` and `source_revision` alongside every
  artifact.

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

## Provenance

An artifact that cannot be traced to what produced it is not evidence. Three gaps had the
same root, and one mechanism closes them.

**The `.cpg` files are not tracked.** They are hundreds of megabytes; tracking them is not
on the table. But `ast-*.json` **is** tracked, which used to mean a committed AST could
drift arbitrarily far from the exporter committed beside it with nothing complaining —
the only thing that compares them is a Lean module rendered from the same AST at the same
time, which agrees with it by construction.

The fix is to record what a regeneration needs, and then to check the record:

```
provenance/<artifact>.prov.json
    artifact_sha256    the artifact this record describes
    joern_version      the front end, checked against ./joern-version
    exporter           + exporter_sha256 of the .sc that produced it
    source_path        + source_revision (git commit, or `tree-sha256:…` content
                       digest for a tree that is not a checkout)
    command            the exact command line
```

Sidecar files rather than a field inside the artifact, because `export_ast.sc` writes a
bare JSON array and `render_lean.py`, `check_docs.py` and `differential.py` all index it as
one. An envelope is the better end state; see "Merge-phase changes this asks for
elsewhere".

Two checks, one cheap and one expensive:

* **`scripts/check_provenance.py`** runs on a clean clone with **no Joern installed and no
  CPG anywhere**, because every question it asks is answerable from tracked bytes:
  coverage (every artifact has a record or is a named entry in the backlog), integrity
  (the record's digest is the file's digest), the Joern pin, required fields, orphans, and
  — the one that closes the "cannot re-verify without the CPG" gap — **exporter drift**.
  The moment `export_ast.sc` changes, every AST that predates the change is mechanically
  known to be stale, and the record holds the command that regenerates it.
* **`scripts/reproduce_ast.py`** is the independent recomputation: rebuild the CPG from the
  recorded source tree with the pinned Joern, re-run the committed exporter, diff. It does
  not read the committed AST to decide what to expect. Minutes per corpus, so it is a
  command rather than a build step.

`provenance/unattributed.json` is a **named backlog**, not an exemption. The eleven
`ast-*.json` files that predate this mechanism are listed there with a reason, printed by
name on every run of the checker, and an entry expires the moment its artifact's digest
changes — regenerate one and you must record real provenance. `--strict` refuses the
backlog entirely. Three of the eleven were re-exported to find out rather than assumed;
all three differ from a fresh export (module-initializer entries and integer-literal
representation postdate them), which is recorded as the finding it is.

### Merge-phase changes this asks for elsewhere

Neither is made here — `cartographer/export_ast.sc` and `autoform.sh` are owned elsewhere
this round — and until they are, an AST produced by `./autoform.sh` is unattributed and
the checker says so by name. Use `scripts/export_with_provenance.sh` to produce an
attributed one.

1. **`autoform.sh`**: call `python3 scripts/provenance.py joern-version --check` before
   stage 1, and `python3 scripts/provenance.py record --artifact ast-$MOD.json --source
   "$SRC" --exporter cartographer/export_ast.sc --command "…"` after stage 3.
2. **`cartographer/export_ast.sc`**: emit `joern.metaData.version` and the CPG root into
   the artifact itself, so provenance survives a file copied out of the repository. This
   requires changing the top-level JSON from an array to
   `{"provenance": {...}, "functions": [...]}` and updating the three readers; the sidecar
   is the interim.

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
| `provenance.py` | The CPG front end's pin (`joern-version`, read from the distribution's jar names rather than by booting a JVM) and the writer of `provenance/<artifact>.prov.json`. Refuses to record an artifact whose Joern version or source revision it cannot determine. |
| `check_provenance.py` | The enforcement half: coverage, integrity, pin, exporter drift, required fields, orphans, backlog expiry. Runs on a clean clone with no Joern and no CPG. |
| `reproduce_ast.py` | Rebuilds an artifact's CPG from its recorded source tree and re-exports it, diffing against the committed file. The independent recomputation that makes discarding the CPG acceptable. |
| `export_with_provenance.sh` | `joern-parse` → `export_ast.sc` → `provenance.py record`, refusing to start on an unpinned Joern. The way to produce an attributed AST until `autoform.sh` does it itself. |
| `ledger.lean.tmpl` | The `#eval` script `autoform.sh` instantiates per module to print the ledger and write `ledger-<Module>.json`. |

## Out of scope by design

* Whole-repo formalization is not attempted. The output is a verified core plus declared
  assumptions for everything else. This is a product decision, not a limitation to be
  fixed later.
* An agent cannot close a goal. The Lean kernel is the only thing that decides whether
  something is proved, which is what makes unattended operation safe.
* The transpiler is not proved correct. Transpiler faithfulness is *tested* — see
  `docs/trust-model.md`, which states where that boundary sits.
