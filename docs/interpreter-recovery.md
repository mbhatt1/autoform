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
| Decorators | `agent-a01d6352dbddae745` | Review definition-time evaluation order, binding and method descriptors; finish source comparisons. |
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

Current integrity checks must continue to distinguish stale and missing evidence.
`check_provenance.py` rejects the four tracked Python corpora whose exporter pin is
stale; regenerate their complete evidence with `scripts/reland_corpus.sh`. Do not
update only their hashes. Local scratch ASTs without manifest entries are reported
as unverifiable by `check_render.py`. The docs/spec freshness checks do not establish
that the current interpreter agrees with every source corpus.
