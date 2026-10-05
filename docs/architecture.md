# Architecture

How the pieces fit together. `STRATEGY.md` holds the full design record; this document is
the map. Last checked against the tree at `9639df0` (2026-10-02): the module and script
tables were compared with the directory listings, the CI and trust descriptions with
`.github/workflows/ci.yml` and `scripts/audit_all.py`.

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
calls. (Exercised in this repository, each with a tracked AST or fixture: Python, C, C++,
Java, Go, JavaScript, TypeScript and Kotlin; `docs/languages.md` says how far each goes.)
The system therefore writes:

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
carries `Core.Dialect` explicitly rather than picking a winner. There are three dialects:
`.python`, `.cLike` (C, C++, Java, Go, Kotlin) and `.javascript` (`.js`, `.ts`, `.tsx`,
`.jsx`, `.mjs`, `.cjs`; `render_lean.py` infers it from the file extension). Within `.cLike`,
integer operators the exporter has typed (`"*:i64"`, `"+:j64"`, Go `"*:g64"`, Kotlin
`"*:k64"`, ...) compute at that width, an operator whose type does not resolve is the hole
`op:int:unresolved-type`, and an untyped operator still means 32-bit wrapping
(`Autoform/Lang/Core/TypedInt.lean`). See `docs/core-language.md`.

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
   ├── scripts/audit_all.py        ─▶ audit.json         (axioms + escapes; kernel replay is hours, its own CI job)
   ├── scripts/mutate.py           ─▶ mutation.json      (specification teeth)
   ├── Autoform/Ledger.lean        ─▶ ledger-<Module>.json
   └── scripts/sacm.py             ─▶ sacm-<Module>.json (SACM assurance case)
```

`./autoform.sh <src> <Name>` runs the top half (through the ledger).
`./assure.sh <src> <Name>` runs all of it. See `docs/running.md`.

Beside the pipeline, a second set of scripts checks that the artifacts it produces are the
ones the claims are about; none of them appears in the diagram because none consumes the
pipeline's output:

```
ast-<M>.json ──▶ scripts/check_render.py       render hash + AST hash vs artifact-manifest.json
                                               (Ansible / LinuxCrypto / LinuxLib: NOT-TRACKED by
                                                reviewed policy, never counted as verified)
             ──▶ scripts/check_provenance.py   record or named baseline entry; Joern pin;
                                               exporter digest (fixtures: tests/test_fixture_exporter_fresh.py)
             ──▶ scripts/check_specs_fresh.py  specs vs the corpus AST they were generated from
ledger-<M>.json ▶ scripts/check_docs.py        documented figures vs artifact fields
```

CI runs these (and the audit with `--skip-kernel`) in `build-and-audit`, `check_provenance.py`
and pytest in `python-tests`, and the kernel replay in its own `kernel-replay` job; the Joern
pipeline is manual. `docs/running.md` §1b lists the jobs, `docs/integrity.md` the incident
behind each check.

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
one. An envelope is the better end state; see "Remaining provenance hardening" below.

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

`provenance/unattributed.json` is a **named backlog**, not an exemption. On the final tree
nine `ast-*.json` files are listed there (`CMath`, `LangC`, `LangJava`, `LinuxLibSample`,
`Sample`, `Stress`, `V8Base`, `V8BaseSample`, `V8Numbers`) with a reason each, printed by
name on every run of the checker, and an entry expires the moment its artifact's digest
changes — regenerate one and you must record real provenance. `--strict` refuses the
backlog entirely. Six artifacts now carry a real record (`CAddr`, `Cachetools`, `LangGo`,
`LangJS`, `LangKt`, `LangTS`), so the checker's summary is `6/15 in-repository artifacts
fully attributed ... 9 unattributed (baselined) ... 0 violation(s)`. Three of the baselined ones
were re-exported to find out rather than assumed; all three differ from a fresh export
(module-initializer entries and integer-literal representation postdate them), which is
recorded as the finding it is. A fixture's `provenance.json` under `tests/` is held to a
stricter standard: its `exporter_sha256` must equal the current exporter
(`tests/test_fixture_exporter_fresh.py`).

### Remaining provenance hardening

The CLI pipeline now enforces the Joern pin before parsing and records
`provenance/ast-<Module>.json.prov.json` after `export_ast.sc` emits a tracked AST; the
legacy `./autoform.sh` and `./assure.sh` wrappers delegate to that shared path. The
standalone `scripts/export_with_provenance.sh` helper remains useful when a team only
needs an attributed neutral AST without rendering Lean or running assurance checks.

The remaining hardening item is inside **`cartographer/export_ast.sc`**: emit
`joern.metaData.version` and the CPG root into the artifact itself, so provenance survives
a file copied out of the repository. This requires changing the top-level JSON from an
array to `{"provenance": {...}, "functions": [...]}` and updating the readers; the
sidecar is the interim.

## Module layout

### `Autoform/Lang/Core/` — the semantic kernel

| File | Role |
|---|---|
| `Syntax.lean` | The universal deep embedding: `Val`, `Obj`/`Heap`, `Lit`, `Expr`, `Stmt`, `Func`, `Program`, `Dialect`, `EResult`, plus the hole/size folds the ledger is built on. |
| `Semantics.lean` | The fuel-indexed total interpreter: `Env`, `Ctx`, `evalExpr`/`execStmt`/`applyFunc`/`applyClosure`, operator application, name resolution, `runFunc`/`runMain`. No `partial`, no `sorry`. |
| `Numeric.lean` | Machine integers as a dialect parameter: `Width`, `IntType`, `NumConfig` (presets `python`, `c32`, `c32Wrapv`, `c64Wrapv`, `u32`, `java32`, `java64`, `go64`), and `NumResult` with `ok`/`divZero`/`trap`/`ub`. Undefined behaviour becomes a hole, never a number. |
| `TypedInt.lean` | Width-typed integer operators: the exporter names the operand type inside the operator (`"*:i64"`, `"+:j64"`, Go `"*:g64"`, Kotlin `"*:k64"`), the operator converts its operands to that type and computes through `NumConfig`; an unresolved type is a hole. Untyped `.cLike` operators keep their 32-bit meaning. |
| `Address.lean` | The C address model: a pointer is a block (heap `Ref`) plus an offset (`Val.iref`), so comparison, `&p[i]` and pointer arithmetic within one array are defined and anything across objects is a hole. |
| `Boxed.lean` | The heap-free half of Python's boxed containers: what a write does to a list/dict payload, what membership and the builtins may see (`docs/boxed-containers.md`). |
| `Stdlib.lean` | A modelled Python standard library and builtins, consulted *after* user functions. Every entry returns `none` — falling through to a visible hole — on any argument shape it cannot model faithfully. Under `.cLike` and `.javascript` it returns `none` for everything. |
| `Float.lean` | IEEE-754 binary32/binary64 as an explicit bit pattern (`Fl`) with exact-rational rounding, plus Python's float semantics (`pyMod`, int/float comparison without coercion, `OverflowError`). Chosen over Lean's `Float` because `Float` is an opaque `@[extern]` type the kernel cannot reduce. Wired in: `Syntax.lean` imports it for `Val.float`/`Lit.float`, and `Semantics.lean`'s "Floating point" section evaluates float literals, arithmetic, comparison and unary minus. What still holes is listed in `docs/core-language.md` §1. |

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
| `PyArith.lean`, `PyScoping.lean`, `PyMro.lean`, `CBoolInt.lean`, `CIntWidth.lean`, `JavaIntWidth.lean`, `GoIntWidth.lean`, `KotlinIntWidth.lean`, `JsNode.lean`, `BoxedContainers.lean` (+ the `*Program.lean` data they run) | Fixtures pinned by evaluation: each runs an exported-and-rendered program through the Core interpreter, `#guard_msgs`-pins the answers, and a pytest compares the same cases with the real runtime (CPython, `cc`, `java`, `go`, Kotlin, Node). They are in the root import graph, so `lake build` re-checks every pin. |
| `HoleContracts.lean` | Contracts at *statement* holes, scoped to a site (the statement-level counterpart of `Contracts.lean`); the ledger's "conditionally verifiable" count rests on it (`docs/contracts.md`). |
| `Overflow.lean` | Derives representability obligations (`Fits32`-style side conditions) mechanically from the AST, with a soundness theorem: if the generated obligations hold, evaluation agrees with the exact mathematical value and in particular is never `hole "ub:…"`. |
| `Contracts.lean` | Contracts at holes: `RefinesUnder Γ`, refinement relative to stated assumptions about named holes, with the unsatisfiable-assumption failure mode stated as a theorem. See `docs/contracts.md`. |
| `FuelMono.lean` | General fuel monotonicity for all seven mutually recursive interpreter functions, excluding `Stmt.tryFinally` (stated why in the file). |
| `CallingConvention.lean` | Anti-vacuity evidence for `starred`/`kwargE`/`dstarred` and `vararg`/`kwarg`: `#eval`s paired with the values CPython printed. |
| `BuiltinBase.lean` | Classes with a builtin base type (`class X(tuple)`): the `Val.bobj` model and its checks against CPython. |
| `Harness/Audit.lean` | `#audit_axioms`, `#audit_depends`, `#audit_ledger`, implemented as Lean metaprogramming over `Lean.Environment`. |
| `Harness/Conformance.lean` | Specimen-derived generators and checkers over the `BigStep` relation; `plausible` used as a **refutation** gate before a prover is allowed to spend time. |
| `Tactics/Portfolio.lean` | The tiered proof portfolio, with the guard that a rung counts as success only if the resulting term passes `hasSorry`/`hasExprMVar` screening. Exhaustion records an `Obligation` as data; it never admits a theorem. |
| `Specs/*.lean` | Hand-written specifications *about generated modules*, stated by import so that mutating the generated file mutates the subject of the theorems (`CachetoolsSpec`, `V8Spec`, `CppCastSpec`, `DoWhileSpec`, `AddressSpec`). |
| `SpecsGen/*.lean` | The hand-written vocabulary (`Case`, `Obs`, the `law*` predicates, `MRefines`) that machine-synthesized specifications are generated in, plus the generated specs themselves. |
| `Generated/*.lean` | Transpiler output. Data literals; never hand-edited. Mostly untracked build products (`docs/integrity.md` says which six are tracked); `render_lean.py` emits `set_option maxRecDepth` scaled to the function count at the top of each. |

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
| `audit_all.py` | Axiom sweep over every declaration, source sweep for escape hatches (`sorry`, `partial`, `unsafe`, `native_decide`, `@[implemented_by]`, `axiom`, `@[extern]`), and `leanchecker --fresh` kernel replay. `--skip-kernel` reports the replay as `DELEGATED` (not a pass); `--kernel-only` runs just the replay. CI runs the sweep with `--strict --skip-kernel` in the build job and the replay (hours) in its own `kernel-replay` job. |
| `check_render.py` | Render-integrity gate: each AST and its render against `artifact-manifest.json`; corpora whose AST is in no clone are `NOT-TRACKED` by a reviewed allowlist (never counted verified). `--strict` ignores the allowlist. |
| `check_docs.py`, `check_specs.py`, `check_specs_fresh.py` | Documented figures vs artifact fields; the SpecsGen modules elaborate; each spec is bound to the AST hash of its corpus. |
| `lang_matrix.py` | Per-language coverage measurement over exported ASTs; its language table equals `render_lean.py`'s (tested). |
| `emit_contracts.py` | Renders `Autoform.Contracts.Demo.contractRecords` to JSON for the assurance case. |
| `wasm_backend.py` / `wasm_run.mjs` | `--wasm` mode of the differential harness's C backend: runs the C side compiled to wasm32 so a wild pointer is a recorded trap rather than a crashed harness. |
| `strip_kernel_attrs.py`, `label_function_counts.py`, `arity_blast.lean.tmpl` | Measurement helpers: strip GCC/kernel attributes that defeat Joern's C parser; count how many functions one hole label alone would unblock; count call sites passing too many positional arguments. Not on the gating path. |
| `sqlite_corpus.sh`, `sqlite_sample.py` | The SQLite full-tree setup (generated `sqlite3.h`, parse, export) and the selector for the typed C conformance sample (`docs/scale.md`). |
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
