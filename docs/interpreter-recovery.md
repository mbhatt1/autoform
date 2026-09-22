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
| Generators | `agent-a80201a5d8016fae2`, commit `bb6d0f0` | Suspended generators were not implemented. Do not merge eager method-consumer substitution as a lazy-generator implementation. Review the independent string-join model separately. |
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

The next generator implementation needs a resumable interpreter state. Python saves
locals, the instruction position and pending exception handling across a yield, while
the leftmost iterable of a generator expression is evaluated at creation. See the
[generator and yield reference](https://docs.python.org/3/reference/expressions.html#yield-expressions).
The proposed Core design is a heap object carrying locals, continuation frames and a
lifecycle state, resumed by iterator operations. Continuations must preserve loops and
pending `finally` work; `send`, `throw`, `close` and delegated yields must either follow
their source protocol or remain explicit holes. Existing eager consumer recognition
also needs correction: `any`/`all` can stop early, `enumerate`/`zip` are lazy, and `len`
does not consume a generator. Even `sum` interleaves accumulation with item production.

Keep execution structurally recursive on explicit fuel. Lean's
[recursion reference](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)
explains that `partial` definitions are opaque to kernel reduction and that well-founded
recursion may impose additional kernel reduction cost. A continuation datatype with a
fuel-bounded step function fits the existing trusted interpreter and its computation
proofs. This is an implementation direction, not a claim that the current Core has
suspended frames or that its eager generator cases are generally sound.

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
update only their hashes. Local scratch ASTs without manifest entries are reported
as unverifiable by `check_render.py`. The docs/spec freshness checks do not establish
that the current interpreter agrees with every source corpus.
