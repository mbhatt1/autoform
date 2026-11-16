# Architecture

How the pieces fit together. `STRATEGY.md` holds the full design record; this document is
the map.

The source pipeline below now has a separate machine-level companion:
binary/assembled bytes → SLEIGH raw p-code → `Autoform.PCode.Program` → a total Lean
interpreter. This path keeps machine widths, address spaces, registers, and control
flow instead of assigning a source dialect to disassembly. See
[machine-code.md](machine-code.md) for its interface, trust boundary, and gaps.

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
JavaScript, TypeScript, Go, Python and Kotlin normalize into a single node
vocabulary — `CALL`, `IDENTIFIER`, `LITERAL`, `CONTROL_STRUCTURE`, `RETURN`, `BLOCK`,
`FIELD_IDENTIFIER`, `METHOD_REF`, `TYPE_REF` — with operators appearing as `<operator>.*`
calls. The system therefore writes:

* **one** semantics for that vocabulary (`Autoform/Lang/Core/*`),
* **one** CPG → JSON exporter (`cartographer/export_ast.sc`, backed by
  `cartographer/compiler/SourceCompiler.scala`),
* **one** JSON → Lean printer (`cartographer/render_lean.py`),

shared by the supported source front ends. Sharing a vocabulary does not establish
support for every Joern language or construct; the native fixture tests and explicit
holes define the checked boundary. Compared with the alternative (compile
everything to Wasm and write one Wasm semantics), source-level structure survives, which
keeps the deep≈shallow refinement tractable.

The exporter entry point loads the CPG and creates one compilation instance. JSON
encoding and typed numeric operations live in `compiler/Json.scala` and
`compiler/Numeric.scala`; source analysis and lowering remain in `SourceCompiler.scala`.
Its analysis priming, module initialization and method emission retain their order.
The Python lowering passes share iterative JSON traversal in `cartographer/ast_tools.py`,
while the Lean printer uses one measured document engine for both flat and multiline
output. See [compiler-rewrite.md](compiler-rewrite.md) for the compatibility boundary
and validation commands.

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
    exporter_sources   relative compile-unit paths and their SHA-256 digests,
                       following every transitive Joern `using file` directive
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
  The moment any exporter compile unit changes, every AST that predates the change is mechanically
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

1. **`autoform.sh`** — **done, in part.** Stage 3 now calls `provenance.py record`
   after writing `ast-$MOD.json`, so a run of `./autoform.sh` produces an attributed
   AST carrying `joern_version`, `exporter_sha256`, the artifact digest and the source
   revision. `scripts/export_with_provenance.sh` is no longer the only way to get one.

   The `joern-version --check` half is deliberately **not** wired in, and is not
   pending either. Refusing to analyze a repository because the installed Joern differs
   from the pin is the wrong place for that verdict: the pipeline records the mismatch
   and announces it, while `autoform doctor` returns `1` on it, so the strict gate is
   the command you run to ask "is this machine right?" rather than a trap inside an
   analysis run. Recording is also non-fatal — an unattributed AST warns, it does not
   fail the run, because a missing attribution is a weaker problem than a missing
   analysis.
2. **`cartographer/export_ast.sc`** — still open. Emit `joern.metaData.version` and the CPG root into
   the artifact itself, so provenance survives a file copied out of the repository. This
   requires changing the top-level JSON from an array to
   `{"provenance": {...}, "functions": [...]}` and updating the three readers; the sidecar
   is the interim.

## Module layout

### `Autoform/Lang/Core/` — the semantic kernel

| File | Role |
|---|---|
| `Syntax.lean` | The universal deep embedding: `Val`, `Obj`/`Heap`, `Lit`, `Expr`, `Stmt`, `Func`, `Program`, `Dialect`, `EResult`, plus the hole/size folds the ledger is built on. |
| `Semantics.lean` | The fuel-indexed total interpreter: `Env`, `Ctx`, `evalExpr`/`execStmt`/`applyFunc`/`applyClosure`, operator application, name resolution, `runFunc`/`runMain`. No `partial`, no `sorry`. **Name resolution is structurally recursive on purpose** (`strEndsWith`, `lastDotSegment`, `dropLastDotSegment`): `String.endsWith`/`splitOn` are well-founded recursions over byte positions, which the kernel does not unfold, so a proof *by computation* that reached a resolve miss or a class value's short name never terminated — three cachetools constructors had to be excluded from the generated conformance module for exactly that. Suffix matching on `List Char` reduces; `strEndsWith_eq_endsWith` proves it is the same predicate. Anything added to the resolution path must keep that property. |
| `Numeric.lean` | Machine integers as a dialect parameter: `Width`, `IntType`, `NumConfig` (Python / C32 / C64 / unsigned / Java / Go presets), and `NumResult` with `ok`/`divZero`/`trap`/`ub`. Undefined behaviour becomes a hole, never a number. |
| `Stdlib.lean` | A modelled Python standard library and builtins, consulted *after* user functions. Every entry returns `none` — falling through to a visible hole — on any argument shape it cannot model faithfully. Under `.cLike` it returns `none` for everything. |
| `ClassHierarchy.lean` | Python class namespaces: C3 linearization over the exporter's class declarations, descriptor kinds (method, property, stored, slot, opaque), the barriers a dynamic class body raises, and lookup through a contracted external base. |
| `ExternalBases.lean` | Generated from `scripts/external_bases.py`: for each storage-free `collections.abc` ABC, the names it defines beyond `object` and its abstract methods. A contracted base is one node of a complete MRO; the oracle verifies each contract against the live class before trusting it (`docs/contracts.md`). |
| `Float.lean` | IEEE-754 binary32/binary64 as an explicit bit pattern (`Fl`) with exact-rational rounding, plus Python's float semantics (`pyMod`, int/float comparison without coercion, `OverflowError`). Chosen over Lean's `Float` because `Float` is an opaque `@[extern]` type the kernel cannot reduce. Wired in: `Syntax.lean` imports it and carries `Val.float : Fl → Val` and `Lit.float` (`grep -n float Autoform/Lang/Core/Syntax.lean`). Unsupported literal forms and conversions still hole (`lit:float`; `docs/typed-numerics.md`). |
| `Numeric.lean` → `TypedNumeric.lean` | Numeric operators whose language and promoted operand type survive CPG export, encoded `num:<c\|java\|go\|js>:<i\|u><width>:<operator>`; untyped legacy operators keep their semantics and unknown encodings remain holes. A structural parser keeps tagged operations cheap to reduce in the kernel. |
| `Iteration.lean` | Python iterator objects as heap state: positions and exhaustion live on the heap, container iterators retain their source reference so mutations stay visible, and the protocol methods are ordinary Core functions run through the same fuel-bounded interpreter. Value replacement in a dict is supported; a changed key layout at unchanged size is an explicit hole. |
| `ExcSafe.lean` | The theorem that every `.exn v` the Python interpreter can produce has `v` a represented exception class name (`Stdlib.ExcSafe`) — one simultaneous induction over the mutually recursive interpreter functions. It is why the `try`/`except` dispatch no longer needs a `control:TRY-exception-representation` guard. |
| `ExternalMethods.lean` | Generated by `scripts/external_bases.py --emit-lean`: the exporter's translation of the pinned CPython 3.11 source of each contracted external base method (`collections.abc.MutableMapping.popitem`, …), which `verify` compares with the live stdlib before the oracle encodes a receiver through the base. Never hand-edited. |
| `Observation.lean` | `HeapObservation`: native observations as a rooted heap graph, not allocator addresses. Input objects keep their addresses, freshly reachable objects are related bijectively; the checker is total and kernel-reducible, and exhausting its budget is never agreement. `docs/native-heap-observations.md`. |

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
| `Contracts.lean` | Contracts at holes: an opt-in assumption about one labelled hole, so a function containing it can be proved correct *relative to* that assumption with the assumption surfaced rather than discharged. `scripts/emit_contracts.py` renders `contractRecords` to JSON; `docs/contracts.md`. |
| `FuelMono.lean` | General fuel monotonicity: for every function of the interpreter's `mutual` block, raising the budget preserves any result that is not `outOfFuel`, heap and locals included — one induction over the eight-way `FuelStep` statement. The `_all` entry points cover every statement constructor; the older `TFFreeCtx`/`tfFreeS` forms are kept so previously generated proofs still elaborate. `docs/fuel.md`. |
| `CallingConvention.lean` | Anti-vacuity evidence for the calling convention that closed `op:starredUnpack`: five `Func`s written directly in Core, each `#eval` paired with the value CPython 3.9.6 printed. |
| `BuiltinBase.lean` | Classes with a builtin base type (`class _HashedTuple(tuple)`), the `Val.bobj` constructor and the CPython-measured equalities (`hashkey(0) == (0,)`) that motivated it — STRATEGY.md §31/§33/§34's one confirmed behavioural divergence, closed. |
| `Runtime.lean` | The reusable pipeline library: the import closure a consumer needs (Core semantics, p-code, ledger, audit, conformance, portfolio, refinement, fuel monotonicity, contracts, the SpecsGen basis), independent of the historical corpus proofs (its own header comment). |
| `CI.lean` | The CI umbrella: `Autoform.lean` minus `Autoform.SpecsGen.V8Base` (`.github/workflows/ci.yml`), importing every library module plus the hand-written and generated spec modules CI must elaborate. `lake build Autoform.CI` and `scripts/audit_all.py --strict --module Autoform.CI` are the workflow's build and audit steps. |
| `NL/Basis.lean` | Structural `DecidableEq` for `Val`, `Payload`, `Obj`, `Heap` and `EResult` (`Val.seq`, with soundness and reflexivity), so the natural-language pipeline can *decide* "this frozen heap literal is what the initializers produce". Deliberately not `Val.beq`, which is the interpreter's Python equality. |
| `NLModel/*.lean` | Per-run build products of `autoform.nl.model` (`docs/autoformalize.md`): plain Lean models of Python functions written by a language model and validated against the deep translation. Gitignored (`Autoform/NLModel/*.lean`) except the tracked `TestFixturePython.lean`. |
| `Lang/PCode/{Syntax,Semantics,Properties}.lean` | The machine-level companion (`docs/machine-code.md`): SLEIGH raw p-code as a target independent of source language and ISA, a total fuel-indexed executor that never silently runs a syscall, float op, unknown byte or external destination, and `rfl`-checked width properties. |
| `Harness/Audit.lean` | `#audit_axioms`, `#audit_depends`, `#audit_ledger`, implemented as Lean metaprogramming over `Lean.Environment`. |
| `Harness/Conformance.lean` | Specimen-derived generators and checkers over the `BigStep` relation; the Plausible library as a **refutation** gate before a prover is allowed to spend time. Candidates are fuzzed with `Testable.check`, **not** the `plausible` tactic, because the tactic closes the goal with `sorry` (Conformance.lean's own note; CONTRIBUTING.md rule 2). |
| `Tactics/Portfolio.lean` | The tiered proof portfolio, with the guard that a rung counts as success only if the resulting term passes `hasSorry`/`hasExprMVar` screening. Exhaustion records an `Obligation` as data; it never admits a theorem. |
| `Specs/*.lean` | Hand-written specifications *about generated modules*, stated by import so that mutating the generated file mutates the subject of the theorems. |
| `SpecsGen/*.lean` | The hand-written vocabulary (`Case`, `Obs`, the `law*` predicates, `MRefines`) that machine-synthesized specifications are generated in, plus the generated specs themselves. |
| `Generated/*.lean` | Transpiler output. Data literals; never hand-edited. |

### `cartographer/` — the front end

| File | Role |
|---|---|
| `formalization_graph.sc` | Joern query producing the formalization graph: call graph, effect classification (io / ffi / reflection / concurrency / nondeterminism), and a formalizability score. The scoring weights are the policy. |
| `export_ast.sc` | The Joern entry point: CPG → language-neutral JSON AST. It loads `compiler/SourceCompiler.scala`, which owns a fresh compilation's analysis state (`docs/compiler-rewrite.md`). Deterministic, no model on this path. Also answers the whole-program questions the node vocabulary cannot: module-level bindings, which function values capture an enclosing scope, and which operators change meaning under the dialect. |
| `compiler/SourceCompiler.scala`, `compiler/Json.scala`, `compiler/Numeric.scala` | The source compiler proper — every lowering rule and every static hole label in `docs/core-language.md` §8 is emitted here — plus its JSON writer and the typed-numeric encoder. A `SourceCompiler` may be reused; each run owns fresh analysis and lowering state and writes the neutral AST and the census sidecar. Pinned by every provenance record, which is why the Python passes below are separate files rather than exporter options. |
| `prepare_cpg.sc` | Fallback for a CPG parsed with `--nooverlays`: applies the overlays the exporter reads without the `dataflowOss` pass that crashes `joern-parse` on some real Kotlin repositories (measured: three of five packages). |
| `ast_tools.py` | Stack-safe traversal and rewriting of the compiler's JSON trees, shared by the passes below; AST depth follows the program, not Python's recursion limit. |
| `generator_lowering.py` | Compiles suspended Python generator frames to ordinary Core heap operations — a translation pass, not a host-language generator: every resume runs the same fuel-bounded Core semantics. Frame helpers are auxiliary definitions excluded from the source-function population. |
| `python_truth_lowering.py`, `python_truth_values.py` | Preserve CPython's jump-based truth contexts in the value-based AST (so `if not (a and b)` never tests a short-circuit operand twice), and retain an evaluated truth result across nested Boolean value operators (`pythonTruthCache`, `docs/core-language.md` §1). |
| `plain_class_values.py` | Post-export pass: a class-body `NAME = Cls()` whose class is a plain module-level class becomes a `stored` attribute allocated in the module initializer, instead of an opaque `class-attribute:unmodeled-value` that holes every read. |
| `render_lean.py` | JSON AST → Lean `Program`. A pure function of the JSON: no timestamps, no dict-order dependence, byte-identical output for identical input. Infers the dialect from the file extension. `--shard-functions N` writes the definitions into `Autoform/Generated/<M>/PartNNNN.lean` modules (each with its slice of the function list) that build in parallel; the root module appends the slices into `program`. Tracked corpora are rendered unsharded. |
| `run.sh` | Cartographer-only driver (source tree → formalization graph). |

### `scripts/` — orchestration and oracles

| File | Role |
|---|---|
| `generated_module.py` | The files that make up a rendered model — root plus the parts it imports — and the digest evidence is bound to. Everything that hashes, snapshots or mutates "the model" goes through it. |
| `external_bases.py` | The external base-class contracts (source of truth), `verify(cls)` for the oracle, `--emit-lean` for `ExternalBases.lean`, `--check` against the running interpreter. |
| `differential.py` | The conformance oracle. Drives from the repository's own test suite via a `sys.settrace` hook, snapshots receivers into a Lean `Heap` literal, and compares structured values and exceptions against the Lean interpreter. Three-valued: agree / diverge / INCONCLUSIVE. |
| `core_oracle.py` | The execution oracle for the ledger's verifiable-core claim: runs every function in the claimed core over many inputs instead of analysing the AST that produced the claim. |
| `audit_all.py` | Axiom sweep over every declaration, source sweep for escape hatches (`sorry`, `partial`, `unsafe`, `native_decide`, `@[implemented_by]`, `axiom`), and `leanchecker --fresh` kernel replay. Gates CI with `--strict`. |
| `mutate.py` | Source-level mutation gate — the *sufficient* anti-vacuity test. Two modes: hand-written Lean, and generated modules (where the file mutated and the file rebuilt are different). |
| `sacm.py` | Builds the SACM assurance case (G1–G5, status lattice, coverage caps) and wraps it in an in-toto Statement. |
| `synth_specs.py` | Layer 4: specification synthesis working *down* the trustworthiness ordering — existing artefacts, structural/safety specs, mined algebraic laws, cross-implementation equivalence. Each candidate is compiled alone under a wall-clock and memory budget first (`budget_probe`); an over-budget one is excluded by name in the module and the report. |
| `assure.py`, `repository_assurance.py`, `guarantee.py` | The `assure` orchestration: stage deadlines, per-language child modules, the gates in order, and the guarantee whose claims are bound to artifact hashes. |
| `check_docs.py`, `check_render.py`, `check_specs_fresh.py` | Integrity gates: documented figures equal their artifacts; committed renders are renders of committed ASTs; spec modules describe the corpus in the tree. |
| `fvspec.py` | Runs the anti-vacuity screen over the FVSpec benchmark. See `docs/fvspec.md`. |
| `scale_test.py` | Runs the pipeline stage by stage on arbitrary source trees, recording wall-clock, peak RSS and artefact sizes per stage. See `docs/scale.md`. |
| `prover/smt.py` | External solver driver (`cvc5` binary, `z3` binary, then the `z3` Python module). Produces **evidence**, never a proof: an `unsat` verdict is recorded on an open obligation because no Lean proof is reconstructed from it. Each solver gets `AUTOFORM_SMT_TIMEOUT` seconds (default 30); a solver that exists but exceeds it reports `timed out`, kept distinct from `unavailable` (no solver was tried at all) and `no verdict` (a solver crashed or printed none). |
| `prover/propose.py` | Neural whole-proof proposer, off unless `AUTOFORM_NEURAL=1`. Backends via `AUTOFORM_NEURAL_BACKEND`: `ollama` (default; local, no egress beyond localhost), `anthropic` and `openai` (API keys read from the environment; `AUTOFORM_LLM_ALLOWED_BACKENDS` can refuse them before anything is sent). The model is `AUTOFORM_NEURAL_MODEL_<BACKEND>`, else `AUTOFORM_NEURAL_MODEL`, else the backend's default. Output is untrusted text; every candidate is re-elaborated and screened. |
| `provenance.py` | The CPG front end's pin (`joern-version`, read from the distribution's jar names rather than by booting a JVM) and the writer of `provenance/<artifact>.prov.json`. Refuses to record an artifact whose Joern version or source revision it cannot determine. |
| `check_provenance.py` | The enforcement half: coverage, integrity, pin, exporter drift, required fields, orphans, backlog expiry. Runs on a clean clone with no Joern and no CPG. |
| `reproduce_ast.py` | Rebuilds an artifact's CPG from its recorded source tree and re-exports it, diffing against the committed file. The independent recomputation that makes discarding the CPG acceptable. |
| `export_with_provenance.sh` | `joern-parse` → `export_ast.sc` → `provenance.py record`, refusing to start on an unpinned Joern. The way to produce an attributed AST until `autoform.sh` does it itself. |
| `ledger.lean.tmpl` | The `#eval` script `autoform.sh` instantiates per module to print the ledger and write `ledger-<Module>.json`. |
| `ledger.py`, `ledger_fixture.py`, `ledger_corpus.sh` | The trust ledger computed from the neutral AST without elaborating Lean; a pinned Lean-produced ledger for `tests/test_ledger_py.py`; and export → render → ledger with each stage timed and no `lake build`. |
| `check_specs.py`, `check_distribution.py`, `release_check.sh` | More integrity gates: the synthesised spec modules still elaborate; the actual wheel and sdist match this checkout; the preconditions for a release, checked, with the exact commands printed and nothing tagged or uploaded (`docs/releasing.md`). |
| `pr_mode.py`, `pr_fixture.py`, `regression.py` | Per-function evidence for the functions a change touched (`autoform pr`, `docs/evidence-levels.md`); a two-commit Git fixture for exercising it offline; and what could be proven at one commit that cannot at another. |
| `runtime_backends.py`, `native_c.py`, `native_c_worker.py`, `wasm_backend.py`, `sandbox.py` | The conformance oracle's native legs: Node/JVM/Go drivers that consume exported function identities and never re-parse source; scalar C entry points compiled in their original translation units (the worker runs under `python -I`); a WASM sandbox for the C backend; and the one sandbox every process that runs code under test goes through. |
| `native_heap.py`, `oracle_cache.py`, `work_cache.py`, `boundary_values.py` | CPython rooted object-graph snapshots with strict function-state encoding (`docs/native-heap-observations.md`); the per-function result cache keyed by AST digest that makes a one-function change cost less than a full run; the `.autoform-work/cache` of translations and verdicts a re-land replays; and the typed boundary inputs shared by the oracle and the machine regression search. |
| `formalize_machine.py`, `binary_loader.py`, `dwarf_signature.py`, `machine_regress.py` | The machine-code path (`docs/machine-code.md`): bytes → SLEIGH raw p-code → executable Lean model with a coverage report; loading executables without running them or guessing an ISA; parameter and return shapes read from DWARF; and whether two commits' compiled functions compute the same thing. |
| `rust_aeneas.py`, `rust_regress.py`, `rust_setup.sh` | The Rust path (`docs/rust.md`): Charon + Aeneas model, ledger, differential oracle and kernel-checked case theorems for one Cargo crate; behaviour regressions between two revisions; and the scratch Lake project Aeneas' pinned Lean needs. |
| `security_specs.py`, `proof_artifacts.py`, `emit_contracts.py` | Independently supplied Lean properties proved of a generated model — statements are inputs, never inferred from the implementation (`docs/security.md`); replay evidence bound to the source, modules and reports it checked; and `Contracts.contractRecords` rendered to JSON. |
| `repository_inventory.py`, `repository_scope.py`, `source_context.py`, `strip_kernel_attrs.py`, `compiler_sources.py` | Accounting for a repository's files without claiming unsupported languages (never follows symlinks or opens devices); a source-file population independent of any frontend's AST; the build context shared by Joern and the native C oracle (an unconfigured kernel tree is a portable userspace experiment, never a configured kernel); the GCC/kernel attributes that defeat Joern's preprocessor-free C parser; and the `using file` closure of a Joern script that provenance pins. |
| `lang_matrix.py`, `label_function_counts.py`, `external_callees.py`, `vacuity_rank.py`, `extract_sample_ast.py`, `deep_json.py` | Measurement helpers: the per-language coverage behind `docs/languages.md`; how many functions each hole label alone keeps from being hole-free; which calls leave the translated program, ranked; Ben-David–Kupferman ranking of surviving mutants; byte-identical sample corpora cut from a parent AST; and nested JSON reads that do not spend one stack frame per container. |
| `bootstrap.sh`, `reland_corpus.sh`, `integrity_guard.sh` | A fresh clone to `VERDICT: PASS` in one command (`docs/running.md` §1); re-landing a tracked corpus from its identified source revision; and the guard against the two concurrency hazards `docs/integrity.md` records (a `mutate.py` rewrite racing a build among them). |
| `kernel_shim/include/` | Replacement kernel headers (`linux/math64.h`, `linux/lcm.h`, `linux/bitops.h`, …) that `machine_regress.py` compiles kernel sources against in place of a configured tree; the comparison records that the real headers were replaced. |

## Out of scope by design

* Whole-repo formalization is not attempted. The output is a verified core plus declared
  assumptions for everything else. This is a product decision, not a limitation to be
  fixed later.
* An agent cannot close a goal. The Lean kernel is the only thing that decides whether
  something is proved, which is what makes unattended operation safe.
* The transpiler is not proved correct. Transpiler faithfulness is *tested* — see
  `docs/trust-model.md`, which states where that boundary sits.
