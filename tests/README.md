# tests/ — the Python tooling's own test suite

```sh
python3 -m pytest tests/ -q          # whole suite, ~30 s, no Lean toolchain needed
python3 -m pytest tests/ -q -rx      # ...and print the reason for each strict xfail
python3 -m pytest tests/test_regressions.py -q     # the five silent failures
```

No plugins, no fixtures directory, no network, no `lake`. Every test either runs a script
from `scripts/`/`cartographer/` in a throwaway directory or imports it by path
(`tests/conftest.py::load`).

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
exporter, `check_render` in both directions, and source-root resolution.

## House rules for tests added here

* **Nothing-to-check is a failure.** Every test that iterates over artifacts asserts it
  found some. `assert not violations` over an empty list is the bug this repo keeps
  shipping.
* **Known gaps get a strict `xfail` with a reason, never a deletion or a loosened
  assertion.** `pytest -rx` prints them; `strict=True` means the test fails the moment
  someone fixes the gap and forgets to remove the marker. Two are open today (`.cc` is
  missing from `render_lean.DIALECT`; `ast-V8Numbers.json` encodes small integers as
  strings).
* **Test the shipped script, not a copy of its logic.** `conftest.make_repo` copies the
  real `check_render.py` and `render_lean.py` into a temp tree.
* `scripts/differential.py` re-execs the whole process at import time unless
  `AUTOFORM_NO_REEXEC` is set — importing it unguarded makes `pytest` exit 0 with no
  output. Use the `differential` fixture.
