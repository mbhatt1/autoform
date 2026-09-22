# Interpreter recovery

The completion target remains [the arbitrary-codebase goal](GOAL-arbitrary-codebases.md),
including the corpus comparisons, kernel proofs and provenance gates. This is a
recovery record, not a completion claim.

The latest Claude session stopped during its second interpreter round. Inspection on
2026-09-22 found the main checkout at `40c9a8e`, with several uncommitted worktrees.
The original worktrees have been preserved. Their contents require review and live
source tests; earlier successful build messages do not establish semantic fidelity.

| Slice | Existing work under `.claude/worktrees/` | Next work |
|---|---|---|
| Decorators | `agent-a01d6352dbddae745` | Joern already emits nested applications in the defining scope; preserve these rather than applying decorators in the module-object initializer. Separate the original body from the bound decorated value, including direct oracle entry points and method descriptors. |
| Generators | `agent-a80201a5d8016fae2`, commit `bb6d0f0` | The main checkout now compiles ordinary generator functions to suspended heap frames. The eager consumer substitution from this worktree remains unmerged. Complete the explicit protocol and iterator gaps below. |
| Exception handlers | `agent-a2612eb7fc5911288` | Validate imported names, aliases, shadowing and multiple inheritance against real CPGs and CPython. |
| Expression statements | `agent-accbd26162643b16c` | Recovered and extended in the main checkout; see languages §17.R4 and the source numeric tests. |
| Bytes and related syntax | `agent-a624c48684ae2a813` | Complete the new value representation, proofs, exporter and runtime comparisons. |
| Class hierarchy / JavaScript | `agent-a3a175605a06c962b` | Complete consistent name normalization, hierarchy export/rendering, inherited dispatch and comparisons. |
| Java | `agent-a95ece4fbb2788b31` | Repair failed guards, review constructors/catches/loops, then compare with Java. |
| Go pointers | `agent-a9c28543f59d067ab` | Already merged at `40c9a8e`; composite literals and range still need real frontend shapes. |
| Proof cost | `agent-a64f359a43f9cc15f` | Review unfinished proof refactoring without weakening statements; benchmark kernel computation. |
| Python library models | `agent-a584b9bb999543f40` | No working-tree changes were present; resume from external-callee measurements. |

The expression work additionally exposed missing boxed-input support for `tuple`,
and empty-name context-manager calls misclassified as allocations. Both have runtime
regressions now. General context-manager exception suppression, stored generators,
function/method name collisions and the other slices still need work.

Decorator inspection used a fresh CPG in `/tmp/autoform-decorator-recovery/`.
Joern emits `target = decorate(2)(decorate(3)(def target(...)))` at the definition,
including nested definitions inside functions. Core's `callValue` already evaluates
the callee before its arguments. The recovered exporter now also carries statements
through computed callees and snapshots them before later argument statements. This
is a prerequisite for decorators, not a completed decorator implementation: named
calls can still bypass a rebound callable through static resolution, and the pipeline
must distinguish a raw function body from the decorated source entry point.

The generator implementation needs a resumable interpreter state. Python saves
locals, the instruction position and pending exception handling across a yield, while
the leftmost iterable of a generator expression is evaluated at creation. See the
[generator and yield reference](https://docs.python.org/3/reference/expressions.html#yield-expressions).
Joern represents both `yield` and `return` as RETURN nodes. The exporter now distinguishes
them and records lexical generator metadata. `cartographer/generator_lowering.py`
compiles the suspension markers to ordinary Core operations: a heap object carries the
locals dictionary, instruction position, lifecycle state and pending exception. Its
auxiliary methods implement `__iter__`, `__next__` and `send`. Creation does not execute
the body. Loops, exception handlers and pending `finally` work retain their continuation
across suspension, including a yield inside the finalizer itself.
Protocol methods are shared across frames; only the resume body is specific to a source
function. Straight-line statement chains are lowered iteratively. Excessively large or
nested control graphs retain named resource-limit holes.

The regression source is `examples/python_control/generators.py`, exercised by
`tests/test_source_generators.py`. The opt-in test parses that source with Joern, compares
the resulting Core execution with CPython, then proves the observed results by kernel
computation. Run it with `AUTOFORM_TEST_JOERN=1 JOERN_HOME=<joern-cli-directory>
pytest tests/test_source_generators.py -q` with `lake` on PATH.

Remaining gaps are explicit: `generator:yieldFromS`, `generator:close`,
`generator:throw`, `generator:return-value`, `generator:free-variable-cells`,
`generator:closure-frame` and `generator:async`. Return values need exception payloads;
free variables need shared cells. Suspended `for` uses the existing `iter`/`next`
protocol: user iterators and other translated generators can run, but ordinary container
iterator objects are still missing from Core. Existing eager generator-expression
consumer recognition also needs correction: `any`/`all` can stop early,
`enumerate`/`zip` are lazy, and `len` does not consume a generator. Even `sum` interleaves
accumulation with item production.

Frame methods reside in `Program.auxiliaryFuncs`, outside the source-function coverage
denominator. The original operations and explicit translation refusals remain in the
owning function's `analysisBody`; the interpreter executes `body`. Contract substitution
updates both bodies and the auxiliary methods. The source-to-Core translation remains
tested code, not a proved compiler.

Validation of this generator slice on 2026-09-22 passed the source comparison and kernel
proofs, the long-body lowering regression, `lake build`, the full Python test suite,
the render round-trip tests, and the strict `Autoform.Runtime` audit with fresh kernel
replay. The existing tracked renders remain byte-identical. A repository-wide fresh
kernel audit is a separate gate and must finish before being reported as passed.

Keep execution structurally recursive on explicit fuel. Lean's
[recursion reference](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)
explains that `partial` definitions are opaque to kernel reduction and that well-founded
recursion may impose additional kernel reduction cost. A continuation datatype with a
fuel-bounded step function fits the existing trusted interpreter and its computation
proofs. The frame compiler reuses the existing fuel-bounded interpreter rather than
introducing host-language coroutines or opaque execution. This does not establish that
the existing eager generator-expression cases are sound.

The exploratory Click comparison is recorded in
[`click-prelude-export.json`](../artifacts/interpreter-recovery/click-prelude-export.json).
Both exports use the same freshly parsed CPG. It records static translation changes
only; it is not replacement evidence for the tracked corpus or a conformance claim.
The underlying scratch exports and logs are in `/tmp/autoform-r4-evidence/`.

Validation of the recovered expression slice on 2026-09-22:

* `lake build` completed successfully, including the generated corpus specifications.
* `scripts/audit_all.py --module Autoform.Runtime --strict` passed, including fresh
  kernel replay. This scoped audit does not replace the completion target's full audit.
* `pytest tests/ -q` passed; the opt-in Python and C source numeric comparisons also
  passed, with kernel proofs of the Python observations.
* The public CLI assurance run for the temporary `PreludeRecovery` corpus completed
  its source, core-oracle, audit and contracts stages. Its mutation gate had survivors,
  so the final status is `completed_with_gaps`, not complete verification. Reproduce
  with `PYTHONPATH=src AUTOFORM_CASES=5 python -m autoform --workspace
  /tmp/autoform-prelude-validation assure /tmp/autoform-prelude-source PreludeRecovery
  --stage-timeout 600`; reports are under that workspace's
  `artifacts/pipeline/PreludeRecovery/`.

The computed-callee extension was subsequently checked with the expanded Python
source comparison (including kernel proofs), the production-gap tests, and a fresh
Click export that was byte-identical to the recorded `after.json`. A second CLI run,
`ValueCallRecovery`, passed its source, core-oracle, mutation, audit and contracts
stages. It still reports `completed_with_gaps`: some functions are unexercised and
sampled agreement is not a proof of transpiler faithfulness. Its reproducible source
is `/tmp/autoform-valuecall-source/valuecall.py`; use the same CLI command above with
workspace `/tmp/autoform-valuecall-validation` and module `ValueCallRecovery`.

Current integrity checks must continue to distinguish stale and missing evidence.
`check_provenance.py` rejects the four tracked Python corpora whose exporter pin is
stale; regenerate their complete evidence with `scripts/reland_corpus.sh`. Do not
update only their hashes. The re-land script now validates the selected artifact with
`check_provenance.py --strict --artifact ast-<Module>.json`, so unrelated stale corpora
do not interrupt that corpus's regeneration. It records specification pins only with
`check_specs_fresh.py --record --corpus <Module>`. Default checks remain repository-wide;
the selected checks explicitly report their scope and cannot establish the full gate.
Regression checks live in `tests/test_reland_scope.py`.

Local scratch ASTs without manifest entries are reported
as unverifiable by `check_render.py`. The docs/spec freshness checks do not establish
that the current interpreter agrees with every source corpus.
