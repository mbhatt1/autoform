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
| Decorators | `agent-a01d6352dbddae745` | Applied at definition time for in-program decorators (languages §16.J): raw bodies are `<name><undecorated>`, source entries are auxiliary forwarding functions, class-body methods bind through stored class attributes, and traced frames compare against the raw body. External decorators remain `decorator:external:*` for Milestone 3. |
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
was the prerequisite. The decorator work now reads each decorator expression as a value
rather than a static callee, renames the raw body so no static or suffix resolution can
bypass the rebound name, and records `undecoratedOf`/`decoratedEntries` so the pipeline
distinguishes the raw body from the decorated source entry point.

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
The truth consumers now run declared `__bool__`/`__len__` methods between resumptions,
including their mutations, exceptions and short-circuit behavior. The same consumer
handles plain lists, tuples, dictionaries and strings. Internal truth calls cannot be
replaced by a source binding named `bool`. Unknown truth protocols retain
`truth:unresolved-protocol`; lengths above the portable signed 32-bit bound retain
`truth:length-platform` until the target's `Py_ssize_t` width is represented. These
consumer changes do not establish protocol-correct truth testing for every other Core
condition or operator. Source regressions live in `tests/test_source_truth_consumers.py`.
Implicit protocol calls use reserved names so source bindings of `iter`/`next` cannot
replace them. Source and kernel regressions live in
`tests/test_source_generator_expressions.py`.

The subsequent condition extension routes `if`, `while`, conditional expressions,
negation, Boolean operators, `__contains__` results, and the `__eq__` fallback for `!=`
through effectful truth testing. Refinement rules include its resulting heap, and the
fuel-monotonicity and exception-safety proofs cover the additional calls. The renderer
uses separate value and branch forms, following CPython's
[`codegen_jump_if`](https://github.com/python/cpython/blob/3.14/Python/codegen.c).
A cached short-circuit answer survives temporary assignments and generator suspension;
a later independent test of the materialized value calls the protocol again.
The auxiliary helper functions retain source operations in `analysisBody` and do not
increase the source-function denominator. Source regressions are in
`tests/test_source_truth_conditions.py`.

The condition extension passed the full Lean build (478 jobs), the full Python suite
(804 passed, 54 skipped, one expected failure), and all 18 generator, iterator, truth
consumer and scope source regressions. Its new source test compared 31 CPython results
and proved each in the kernel, together with two named-gap results. The strict
`Autoform.Runtime` audit passed with stable artifacts and fresh replay. Input hashes
and validation commands are recorded in
[`truth-conditions-validation.json`](../artifacts/interpreter-recovery/truth-conditions-validation.json).
The full strict audit of commit `4bc664a` subsequently passed on a stable independent
snapshot, including fresh replay of the complete `Autoform` import closure; see
[`truth-conditions-audit.json`](../artifacts/interpreter-recovery/truth-conditions-audit.json).
Complete regeneration of the four affected Python corpora remains a separate gate;
their older renders differ from the current renderer.

Validation of the truth-consumer correction passed the full Lean build (478 jobs),
the full Python suite (801 passed, 53 skipped, one expected failure), and all 12 existing
generator/iterator source regressions. The new source comparison checked 14 CPython
observations and their kernel proofs, plus two named-gap proofs. The strict
`Autoform.Runtime` audit passed with stable artifacts and fresh replay. This scoped
audit does not establish a full audit of the correction. A subsequent full strict
audit of commit `2a431df` passed on an independent, stable snapshot, including fresh
kernel replay of `Autoform`; see
[`truth-consumer-audit.json`](../artifacts/interpreter-recovery/truth-consumer-audit.json).
That result excludes the later condition extension.

Source metadata also distinguishes lambdas and comprehensions that share a line.
When Python's public symbol table lacks a distinguishing column, the decoder gives
those expressions separate lines in a temporary source copy and checks that its parsed
AST is identical before using its scope positions. The CPG and translated program still
use the original source. Metadata lookup converts Joern's UTF-16 columns to Python AST
UTF-8 byte columns, including supplementary Unicode characters. The source regressions
are `examples/python_control/scope_collisions.py` and `tests/test_python_scope_metadata.py`.
Ambiguity that cannot be removed without changing the AST remains a refusal; in
particular, older Python parsers restrict newlines inside f-string expressions.
This extension passed the opt-in Joern/CPython comparison and kernel proofs, the
signature/handler regressions, and the full Python suite. Metadata remained identical
for the earlier example files and the sampled largest files from the four existing
Python corpus checkouts. These metadata comparisons do not replace corpus re-landing.

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
also check suspended-body calls, lowering refusals and deeply nested ASTs. The separate full strict audit of commit `24bf6d0` passed on a stable, independent
snapshot, including fresh kernel replay of the complete `Autoform` import closure.
Its report is recorded in
[`generator-expression-audit.json`](../artifacts/interpreter-recovery/generator-expression-audit.json).
That result does not cover later scope metadata or truth-protocol changes.

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

The differential driver, core oracle and generated specification context must carry
`Program.properties` and `Program.excClasses`, as well as the dialect, functions,
builtin bases and globals address. Omitting those fields caused the oracle to bypass
property getters and reject represented user exceptions. The generated-driver tests in
`tests/test_oracle_context_metadata.py` execute property reads and custom exceptions,
including kernel proofs of both results. The native sampler also loads files containing
only classes before attempting their methods; those files need no free function or test
suite to become visible to the sampler.
The correction passed the three generated-driver tests, the full Python suite
(806 passed, 55 skipped, one expected failure), and the 478-job Lean build. Commands
and input hashes are recorded in
[`oracle-context-validation.json`](../artifacts/interpreter-recovery/oracle-context-validation.json).
The first regenerated Cachetools and Click comparisons failed and stopped before
specification regeneration. Their diagnostic reports and the Click comparison with the
corrected contexts are indexed in
[`corpus-reland-diagnostics.json`](../artifacts/interpreter-recovery/corpus-reland-diagnostics.json).
These attempts are not completed re-lands. Native module state, callback encoding and
class attributes still need investigation before the remaining mismatches can be
classified as interpreter defects or mismatched inputs.

Python attribute calls now look up and save an ordinary callable attribute before
executing its arguments. Instance fields can shadow ordinary methods, properties run
before instance-field reads, and bound methods and getters retain the lexical captures
of local classes. Missing Python methods no longer resolve to unrelated functions or
constructors with the same suffix. Container methods keep their dedicated path; a
user-defined method on a represented container subclass uses attribute lookup.

The exporter preserves the source attribute expression when Joern adds a synthetic
`METHOD_REF` beside it. Such an annotation previously replaced a property read with
an inferred function value. Attribute lookup and legacy method-name classification use
structural character-list helpers so the new paths reduce in kernel proofs.

The Counter representation now excludes extra instance fields and container payloads.
Its method-call rule also requires that the globals frame does not override the class
method. These conditions prevent field shadowing from invalidating the proof; the
end-to-end `total` result and its fuel bound are unchanged. Generic accessor rules
require the accessed name to be absent from the program's property table, since a
property can run arbitrary code even when an instance field exists.

`tests/test_source_object_lookup.py` checks source execution against CPython and proves
those observations in the kernel. Separate heap probes cover an instance dictionary
entry shadowed by a property and a represented container subclass method. This work
does not establish inheritance/MRO, qualified class identity, dynamic descriptors,
custom attribute hooks, or general class metadata. Calls with arguments lifted into
compiler statement preludes still need a separate lookup-order review.


The object-lookup checkpoint passed the full Python suite, the source and kernel
probes, the protocol regressions, and the 478-job Lean build. A strict fresh-kernel
replay of the complete `Autoform` import closure accepted 7,153 declarations with
stable inputs. Commands, input hashes, failed attempts, and the end-to-end pipeline
status are recorded in
[`object-lookup-validation.json`](../artifacts/interpreter-recovery/object-lookup-validation.json)
and [`object-lookup-audit.json`](../artifacts/interpreter-recovery/object-lookup-audit.json).
The existing corpus render and provenance gates still fail; this checkpoint does not
claim a completed re-land or completion of the arbitrary-codebase goal.
The packaged `ObjectLookupRecovery` pipeline completed its native comparison,
generated proofs, core oracle, restored build and strict scoped kernel audit. Its
mutation run found survivors and untested subjects, including field writes that
return-value-only observations do not distinguish, so the final status remains
`completed_with_gaps`. The earlier mutation timeout and its completed rerun are
both recorded in the validation artifact.

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

The native sampler now runs on the main thread, where its signal deadlines can
interrupt synthesized calls. The old large-stack worker was obsolete after AST
decoding and traversal became iterative. Random free-function sampling now uses
the same deadline as constructed calls; a timeout or unavailable deadline is a
recorded skip, never a source exception. Reports identify the changed sample as
`python-deadlines-v4`. These signal deadlines do not replace the pipeline's external
process timeout. `tests/test_native_deadlines.py` checks a blocking native call
through the CLI while reading an AST deeper than Python's recursion limit. The
[validation report](../artifacts/interpreter-recovery/native-deadline-validation.json)
records the focused checks and full Python suite.

A fresh Cachetools export under the first object-lookup change still fails its
existing `Cache.__init__` conformance theorem. Its class-value read of
`Cache.getsizeof` reaches an unmodeled field branch. A separate diagnostic sample
also reports inherited-attribute divergences; this has not completed a corpus
re-land. The [diagnostic report](../artifacts/interpreter-recovery/cachetools-object-lookup-diagnostic.json)
preserves the failing theorem, sample size, per-function divergences and input hashes.

Minimal [inherited-lookup probes](../artifacts/interpreter-recovery/inherited-lookup-diagnostic.json)
confirm two missing behaviors on the fresh Cachetools model: the base classes
resolve `getsizeof` and `timer`, while `FIFOCache` and `TTLCache` incorrectly raise
`AttributeError` for the corresponding inherited reads. Correcting this requires
class identity, ordered base metadata and descriptor lookup together; a global
method-name fallback would bind unrelated functions. These probes do not claim
to explain every divergent corpus call. Without class metadata that exception is
now the named gap `field:<attr>:unresolved-inheritance` (docs/languages.md §16.A), so
a legacy model reports the missing hierarchy instead of asserting an exception.

Python method calls with compiler-lifted argument statements now save the callable
attribute before those statements. Saved methods on modeled builtin containers and
runtime iterators retain their receiver. The
[bound-call validation](../artifacts/interpreter-recovery/bound-call-validation.json)
records source comparisons, kernel observations, a full Lean build and a fresh full
kernel audit. Its packaged pipeline completes with mutation and assurance gaps;
constructor post-state and untested theorem subjects remain limitations. Inherited
builtin descriptors on user subclasses and general attribute hooks remain open.

Class values now expose their own translated callable attributes through exact
qualified owners. Saved static methods, unbound methods, classmethods and captured
local static methods pass the source and kernel probes. The
[class-attribute validation](../artifacts/interpreter-recovery/class-attribute-validation.json)
records the full Python suite, full Lean build, fresh full kernel audit, and main
checkout verification. The unchanged stored `Cache.__init__` observations also
replay and prove with this reader; the earlier failed corpus re-land has not been
promoted. The packaged class-attribute pipeline still has mutation and assurance
gaps. Inheritance, descriptor objects and captured unbound methods remain outside
this validated change.

Corpus identities now distinguish a clean tracked source subtree from an ignored,
untracked, or changed tree inside a surrounding checkout. The latter receives a
content digest, and a missing source root is refused. The
[source-identity validation](../artifacts/interpreter-recovery/source-identity-validation.json)
records the Git and native-report regression checks. Existing provenance records
have not been re-pinned; affected corpora need regeneration.

Native tracing now distinguishes an executed return instruction from an exception
unwind, so a handled exception followed by `return None` is recorded as a return.
Ambiguous unwind types and suspended generator/coroutine frames remain counted
gaps. Python reports append `+trace-returns-v1` to their measurement basis. The
[trace validation](../artifacts/interpreter-recovery/native-trace-validation.json)
records actual CPython trace-event checks. Receiver post-state observations remain
necessary to detect constructor mutations that preserve the return value.

The integrated inheritance and slots implementation is now in the main worktree.
Qualified classes use C3 lookup, slot storage follows declaring-class identity, and
saved local callables retain their runtime binding. Class-valued outcomes are
compared by exact qualified declaration. The
[integration validation](../artifacts/interpreter-recovery/integration-validation.json)
records the full Python suite, source regressions, completed full builds and fresh
kernel audits. The packaged pipeline has no native divergences or open conformance
proof obligations, while mutation and assurance gaps remain recorded. The native heap-observation extension is now also in the main worktree.


Native conformance observations now compare the complete rooted input and final
object graphs alongside the result. This detects lost mutations even when the
return value is unchanged, and preserves aliases, cycles, detached input objects
and newly reachable allocations. Function values require unique source identities
and representable, unchanged metadata; unsupported state remains an explicit gap.
The [observation model](native-heap-observations.md) defines the exact scope.

The [final graph validation](../artifacts/interpreter-recovery/native-heap-final-validation.json)
records the full Python suite, source comparisons and kernel proofs, mutation
checks, completed full Lean build, and fresh strict audit of the complete Autoform
import closure. The main worktree's source and compiled artifacts were verified
against that audit after promotion and its local build. This does not establish the
arbitrary-codebase goal or repair stale corpus evidence.

A separate [module namespace diagnostic](../artifacts/interpreter-recovery/module-namespace-diagnostic.json)
confirmed that unqualified globals from different modules could collide. The
[namespace repair](python-module-namespaces.md) now accompanies the shared
[compiler simplification](compiler-rewrite.md). Their
[validation report](../artifacts/compiler-rewrite/validation.json) records source
regressions, the complete tooling test suite, all supported language fixture
pipelines, package checks and a fresh scoped kernel audit. The earlier
heap-observation audit remains evidence for its unchanged Lean source and compiled
artifacts; it does not include these later compiler checks.
