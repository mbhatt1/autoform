# tests/ — the Python tooling's own test suite

```sh
python3 -m pytest tests/ -q          # optional machine checks skip without their tools
python3 -m pytest tests/ -q -rx      # ...and print the reason for each strict xfail
python3 -m pytest tests/test_regressions.py -q     # the five silent failures
```

The source-tooling tests require no plugins, fixtures directory, network, or `lake`.
They run a script from `scripts/`/`cartographer/` in a throwaway directory or import it by path
(`tests/conftest.py::load`).

`test_source_numeric.py` additionally checks typed operators in the Lean kernel.
Set `AUTOFORM_TEST_JOERN=1` to run its source → Joern → Lean comparisons against
CPython, Java, Go, C, and Node; these require the corresponding runtimes and Joern.
The corpus covers lifted assignment effects, operand/call/index ordering, primitive
casts, and object aliases. Strict expected failures record unsupported JavaScript
array construction and string indexing; they are not native agreements.
See [typed-numerics.md](../docs/typed-numerics.md) for scope and commands.

`AUTOFORM_TEST_JOERN=1 python -m pytest tests/test_source_pipeline.py -q` runs all
eight source fixtures through the public CLI, including native comparisons and
generated kernel proofs. `test_spec_synthesis.py` checks that large-shift proofs
terminate and incorrect expected values are rejected. `test_package.py` installs
the wheel named by `AUTOFORM_TEST_WHEEL` into a clean environment and exercises it
outside the checkout.

`test_security_specs.py` checks independent quantified properties in Lean and rejects
false, vacuous, admitted or compiler-trusted proofs. It also checks property-input
validation, stale evidence, wrong mutation subjects and bounded proof-worker cleanup.
`test_control_flow.py` compares exception/finalizer state with CPython and checks
that holes and exhausted fuel cannot be masked by cleanup. Its Joern source tests
also run in the source-runtime CI workflow.
`test_python_handlers.py` checks typed handler selection against CPython, then proves
the recorded outcomes in Lean's kernel. It covers inheritance, ordered and tuple
handlers, unmatched exceptions, else/finally, synthetic-name collisions and explicit
gaps for dynamic handler types and exception payload bindings. It runs with Joern in
the same CI workflow.
`test_python_raises.py` compares builtin exception-constructor outcomes and source
raise behavior with CPython, then checks the expected outcomes in Lean's kernel.
It covers invalid raise values, operand evaluation before validation, bare builtin
classes and SyntaxError details. Ambiguous exception instances and explicit causes
must remain holes until their representation and evaluation are supported.
`test_python_signatures.py` records native default, keyword-only and positional-only
behavior and requires explicit gaps where Core cannot represent it. It checks both
calls and function creation, including an unused definition whose default raises,
and retains an ordinary-signature control which must still match the native result.
The Python sampler also attempts functions whose only static holes are exception
representation fallbacks. The hole-free ledger remains unchanged; reaching a hole
is inconclusive. Coverage reports separate compared functions with and without holes.
Conformance proof generation retains observed subjects outside the static call-closed
core. Kernel regressions check that an unused hole does not block a recorded execution,
while a reached hole cannot become a proved observation.
`test_source_resolution.py` prevents test discovery from escaping the selected source
scope into ancestor projects.

`test_linux_pipeline.py` exercises translation-unit isolation, static C helpers,
cross-file dependencies, native build definitions, and final reports after a failed
run. With `AUTOFORM_TEST_JOERN=1`, it also checks kernel annotations, conditional
bodies that must remain visible, and synchronization effects that must remain holes.
`test_runtime_backends.py` rejects observations after source or included headers change.
`test_repository.py` acquires real Git URLs against temporary local remotes, pins
revisions, checks checkout scope and concurrent-run exclusion. The assurance tests
also enforce finite stage deadlines and verify that descendant file locks are
released after timeout or parent completion. CLI tests check deadline forwarding
and reject invalid limits before source acquisition. This tests process-group
cleanup, not containment of processes that detach into another session.
The real mutation driver is also interrupted during its baseline and mutant builds;
both must restore the source, remove their own backup marker and release compiler locks.
The assurance tests
require current native evidence and a scoped independent audit before issuing a
guarantee. The installed-wheel test also checks URL acquisition failure and stale
guarantee invalidation.

Exception: `test_machine_frontend.py` tests the optional binary/assembly path. Install
`requirements-machine.txt` and run it with `.venv/bin/python -m pytest`; its execution
and proof tests require Lean, and the native oracle requires clang. These tests skip
when optional tools are absent. The dedicated machine CI job installs them and sets
`AUTOFORM_REQUIRE_LEAN=1` so missing Lean cannot become a silent skip.

## What this suite is for

Roughly 8,000 lines of Python decide what this repository claims. Each of those lines has
had a chance to fail *quietly*, and five of them took it:

| # | Failure | Test |
|---|---------|------|
| 1 | `mutate.py`'s `error_lines` matched only the pre-4.x Lean diagnostic shape, so on this toolchain nothing was ever attributed and every "kill" came from the coarse whole-build fallback | `test_regressions.py::TestMutateErrorAttribution` |
| 2 | `check_docs.py` passed 5/5 while the ledger it compared against was stale (238 functions vs. the AST's 208) | `TestCheckDocsStaleArtifact` |
| 3 | ...and its cross-artifact check `continue`d silently when an input was absent | `TestCheckDocsMissingInput` |
| 4 | `render_lean.py` never raised the recursion limit, so every direct run used 1000 frames and died at 247 consecutive statements | `TestRenderRecursionDepth` |
| 5 | `paramStars` ran for every language; in C a `*` before a parameter is a pointer, and the helper hard-errors by design, so every non-Python corpus stopped exporting | `TestVarargContract` |

Each of those classes contains a `test_old_behaviour_*` that **reconstructs the broken
code and asserts it is broken**, next to a `test_fixed_*` on the same input. That pairing
is the point: a test that only pins today's behaviour cannot tell you it would have caught
yesterday's bug.

The rest covers what is load-bearing downstream: Lean literal escaping and big integers,
total parenthesisation, renderer determinism (including under `PYTHONHASHSEED`) and linear
output size, dialect inference refusing to guess, the JSON contract with the Scala
exporter, `check_render` in both directions, and source-root resolution. Trust-audit
regressions inject escape hatches into both Core and p-code semantics and require a
failing verdict; printing a failed claim while returning success is insufficient.

## House rules for tests added here

* **Nothing-to-check is a failure.** Every test that iterates over artifacts asserts it
  found some. `assert not violations` over an empty list is the bug this repo keeps
  shipping.
* **Known gaps get a strict `xfail` with a reason, never a deletion or a loosened
  assertion.** `pytest -rx` prints them; `strict=True` means the test fails the moment
  someone fixes the gap and forgets to remove the marker. The remaining strict xfail
  records small integers encoded as strings in `ast-V8Numbers.json`.
* **Test the shipped script, not a copy of its logic.** `conftest.make_repo` copies the
  real `check_render.py` and `render_lean.py` into a temp tree.
* `scripts/differential.py` re-execs the whole process at import time unless
  `AUTOFORM_NO_REEXEC` is set — importing it unguarded makes `pytest` exit 0 with no
  output. Use the `differential` fixture.
