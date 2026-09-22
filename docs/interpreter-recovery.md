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
regressions now. General context-manager exception suppression, generator expressions,
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
free variables need shared cells. Suspended `for` uses the `iter`/`next`
protocol. `Autoform/Lang/Core/Iteration.lean` now provides heap-backed list, tuple,
string and dictionary iterators, sequence fallback through `__getitem__`, and
callable/sentinel iteration. Positions and exhaustion survive across calls; list
mutations remain visible. Dictionary value replacement is allowed, size errors remain
sticky, and same-size key-layout changes retain `iterator:dict-keys-changed` because
Core does not represent CPython's dictionary slots. An `__iter__` method that returns
a list now raises `TypeError`, as Python requires an iterator result.
Synthetic loops retain their own iterator references; nested dictionary, iterator and
sequence-protocol loops cannot overwrite an enclosing loop's hidden state.

The synthetic protocol methods execute through ordinary Core calls without entering
the source function table. Callable/sentinel iteration follows CPython's
[iterator implementation](https://github.com/python/cpython/blob/3.14/Objects/iterobject.c):
compare sentinel first, skip equality for identical objects, and preserve exhaustion
if a callback re-enters the iterator. Unknown identity that can affect equality retains
`iterator:sentinel-identity`; unknown custom exception ancestry retains
`iterator:exception-hierarchy`. Runtime frame fields are not exposed by the pure
`getattr`/`hasattr` models. Source comparisons and kernel proofs live in
`tests/test_source_iterators.py` using `examples/python_control/iterators.py`.

Passing an ordinary bound method as a callback also now preserves its receiver.
The source tests exposed Joern type-recovery reference nodes appended alongside real
arguments; the exporter excludes those duplicate metadata nodes while retaining the
source expression and its effects. Source methods read from instances become callable
values with the receiver captured, following Python's
[instance-method rules](https://docs.python.org/3/reference/datamodel.html#instance-methods).
Taking a builtin iterator's synthetic method as a value remains the explicit
`field:runtime-method` gap; calling that method directly is supported.

Validation of the iterator extension on 2026-09-22 passed the source-to-CPython
comparisons and kernel proofs, the nested-loop kernel regression, the full Python
test suite and `lake build`. The strict `Autoform.Runtime` audit passed with stable
source and compiled artifacts throughout its fresh kernel replay. The docs and spec
freshness checks passed; tracked renders remained byte-identical. The full strict audit
then passed on an independent frozen copy of commit `bbe15f03c0e9596ff68b197dab4aab90390ffbab`,
with stable artifacts and fresh kernel replay of the complete `Autoform` import closure.
The [audit record](../artifacts/interpreter-recovery/iterator-audit.json) identifies that
revision and the complete local report. It excludes subsequent generator-expression
changes. Stale corpus provenance remains a separate gate, and this extension does not
meet the arbitrary-codebase goal.

Generator expressions now use the same frame compiler. Following Python's
[expression rules](https://docs.python.org/3/reference/expressions.html#generator-expressions),
creation evaluates the leftmost iterable and prepares its iterator; the body and
later clauses stay suspended. The exporter no longer chooses eagerness from a consumer
name. Core consumers resume through the ordinary interpreter, including short-circuit
truth tests for `any`/`all` and exact integer accumulation for `sum`. A custom length hint
retains `iterator:length-hint`; non-integer sums retain `iterator:sum-type`. Shared
free-variable cells retain `genexpr:free-variable-cells`, and async expressions retain
`genexpr:async`. Historical ASTs must be re-exported to remove eager lowering.
Implicit protocol calls use reserved names so source bindings of `iter`/`next` cannot
replace them. Source and kernel regressions live in
`tests/test_source_generator_expressions.py`.

Frame methods reside in `Program.auxiliaryFuncs`, outside the source-function coverage
denominator. The original operations and explicit translation refusals remain in the
owning function's `analysisBody`; the interpreter executes `body`. Contract substitution
updates both bodies and the auxiliary methods. The source-to-Core translation remains
tested code, not a proved compiler.
The language coverage report, external-call ranking and differential harness use this
same source analysis. Generated helpers participate in call resolution without entering
the source population, and lowering refusals cannot disappear from hole counts.

Validation of the generator-expression extension on 2026-09-22 passed `lake build`,
the full Python suite, the opt-in source comparisons and kernel proofs for generator
expressions, the existing generator/iterator source regressions, and the Python numeric
source comparison. The strict `Autoform.Runtime` audit passed with fresh replay and
stable artifacts. The final expression test proves a sufficient smaller fuel budget in
the kernel and transports that result to the native run's fuel using the proved
monotonicity theorem; no native observation is accepted as a proof. Reporting regressions
also check suspended-body calls, lowering refusals and deeply nested ASTs. A separate
full strict audit of this checkpoint is still required; the passing iterator audit above
does not cover this extension.

Validation of this generator slice on 2026-09-22 passed the source comparison and kernel
proofs, the long-body lowering regression, `lake build`, the full Python test suite,
the render round-trip tests, and the strict `Autoform.Runtime` audit with fresh kernel
replay. The existing tracked renders remain byte-identical. A repository-wide fresh
kernel audit is a separate gate and must finish before being reported as passed.
The full audit started before the iterator work completed its fresh kernel replay,
but its final verdict was `FAIL`: it correctly detected that the checked source and
compiled artifacts changed during that run. That audit cannot establish the current
tree's integrity; the replacement run must use a stable build.

Keep execution structurally recursive on explicit fuel. Lean's
[recursion reference](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)
explains that `partial` definitions are opaque to kernel reduction and that well-founded
recursion may impose additional kernel reduction cost. A continuation datatype with a
fuel-bounded step function fits the existing trusted interpreter and its computation
proofs. The frame compiler reuses the existing fuel-bounded interpreter rather than
introducing host-language coroutines or opaque execution. Generated-expression factories
remain auxiliary functions, and their source bodies remain visible in coverage analysis.

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
