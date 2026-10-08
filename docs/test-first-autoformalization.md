# Test-first autoformalization

Autoform should use a target codebase's tests as the fastest route to useful formal artifacts, but it should not copy test syntax into Lean and call that a proof. The tests are evidence about the behavior the team already relies on. Autoform should run them on the real runtime, record what they prove by observation, and then emit Lean examples and contracts that constrain the translated program.

The working model is:

```text
source tree ──Joern──▶ neutral AST ──▶ generated Lean program
    │                                               ▲
    └─ tests ──real runtime trace──▶ behavior specs ┘
```

A test-first run has seven phases:

1. **Seed characterization tests.** Write or review executable tests for behavior that matters. Autoform can scaffold Python pytest characterization tests from sample inputs and zero-argument functions; anything needing human input becomes a skipped TODO.
2. **Discover tests.** Find the command that exercises the service or library in its real runtime: `pytest`, `npm test`, `go test`, Maven, a project shell script, or a service-specific smoke suite. A missing or non-runnable suite is an explicit gap, not a green result.
3. **Trace runtime behavior.** Run those tests and record concrete observations: function, receiver state, arguments, return value or exception, side effects that can be represented, and covered call paths. Values that cannot be encoded must produce named skip reasons.
4. **Translate the same source.** Run the normal Joern → neutral AST → Lean rendering path and record provenance for the AST.
5. **Emit Lean behavior specs.** Convert observations into Lean examples or contracts over Autoform's evaluator. The generated theorem should say what the runtime did, not merely reproduce the shape of the original test.
6. **Check conformance.** Compare Lean execution with the recorded runtime behavior. A run with zero compared cases fails because it established nothing.
7. **Reject vacuity.** Run mutation and coverage checks so generated specs must break when relevant behavior changes.

This design makes tests a source of behavioral contracts. It does not make tests sound by themselves. A source test such as `f(x) == f(x)` is weak in the original language and becomes worse in Lean, where purity can make it reflexive. The translator must reject or down-rank tests that only assert determinism, implementation echoes, or branch-free smoke behavior.

`autoform spec-plan` records this strategy as JSON before a runtime-specific tracer runs:

```sh
autoform --json spec-plan /repo/service Service \
  --test-command 'pytest tests' \
  --test-framework pytest
```

The output names the required artifacts, the phase ordering, and the anti-vacuity gates. CI can review that plan the same way it reviews `autoform plan`: before a team spends a long Joern/Lean run, it can see whether the target has a real test command, where traces will be written, and what Lean spec module will be produced.

The trace-to-Lean conversion step is executable now:

```sh
autoform seed-python-tests /repo/service Service \
  --sample-cases autoform-samples.json \
  --output /repo/service/tests/test_autoform_characterization.py

autoform trace-python-tests /repo/service Service \
  --test-command 'python -m pytest tests' \
  --trace-output .autoform-runs/Service/behavior-trace.jsonl \
  --spec-output Autoform/Specs/ServiceBehaviorSpec.lean

autoform spec-from-trace .autoform-runs/Service/behavior-trace.jsonl Service \
  --output Autoform/Specs/ServiceBehaviorSpec.lean
```

For Python projects, the same executable path is available as one command:

```sh
autoform test-first-python /repo/service Service \
  --sample-cases autoform-samples.json \
  --generated-tests /repo/service/tests/test_autoform_characterization.py \
  --trace-output .autoform-runs/Service/behavior-trace.jsonl \
  --spec-output Autoform/Specs/ServiceBehaviorSpec.lean \
  --manifest-output .autoform-runs/Service/test-first-python.json
```

`seed-python-tests` writes pytest characterization tests from sample inputs and from zero-argument functions it can execute safely enough to snapshot. Functions that need inputs become skipped TODO cases rather than silent omissions. `trace-python-tests` installs a temporary Python trace hook, runs the real test command from the source tree, records project function calls, and then renders the trace. `test-first-python` runs both steps as one workflow and writes a manifest that lists the generated tests, trace and Lean spec for CI evidence. `spec-from-trace` is the lower-level renderer for traces produced elsewhere. The trace commands refuse an empty trace, import `Autoform.Generated.<Module>` by default, and emit a Lean inventory of the observed calls. That inventory is not a semantic proof yet. It makes the test evidence reviewable and kernel-checkable while keeping conformance, mutation, and coverage gates responsible for deciding whether the translated program really matches the runtime.

The remaining implementation step is a tracer for non-Python runtime families. The trace format is JSONL with one observation per call:

```json
{"function":"pkg.mod.normalize","args":[" A "],"kwargs":{},"result":"a","exception":null,"coverage":["pkg/mod.py:12","pkg/mod.py:13"]}
```

That trace is rendered into a Lean behavior module such as `Autoform/Specs/ServiceBehaviorSpec.lean`. Each generated spec carries the observation id, the source test that produced it, and the skip or encoding reason if a value cannot yet be represented. This keeps Autoform honest: tests broaden reach, while provenance, conformance and mutation decide how much assurance the generated Lean actually provides.
