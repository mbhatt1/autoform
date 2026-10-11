# Example: `autoform pr` on cachetools v7.1.4 → v7.1.5

A real run on a real change in a library teams ship. Nothing was posted anywhere; the
files here are what the command wrote, with absolute paths replaced by `<workspace>`,
`<repo>`, `<clone>` and `<tmp>`.

| file | what it is |
|---|---|
| `pr.md` | the review comment (`--markdown`) |
| `pr.sarif` | SARIF 2.1.0 (`--sarif`); `validate_sarif()` in `scripts/pr_mode.py` returned no problems |
| `pr.json` | the full record: per function level, reason, artifacts, oracle status; stages; exporter digest |
| `README.md` | this reading |

The change is cachetools `v7.1.4` (`48284d73d0a8`) to `v7.1.5` (`0d2a6ea17b36`), cloned
from `https://github.com/tkem/cachetools`. Its changelog entry is "Reject negative cache
item `getsizeof` values": two lines in `Cache.__setitem__`
(`docs/evidence-cachetools-negative-size.md` has the diff and the cross-revision oracle
result for the same change). The tests are the head revision's own `tests/` directory.

## Command

```sh
git clone https://github.com/tkem/cachetools <clone>
python scripts/pr_mode.py <clone> --base v7.1.4 --head v7.1.5 --module CachetoolsPR \
    --out <workspace>/artifacts/pr/CachetoolsPR --sarif pr.sarif --markdown pr.md
```

This is the script `autoform pr` runs (`src/autoform/cli.py`, `_pr`). I invoked the script
from the repository checkout rather than through an installed `autoform` plus an `init`
workspace, because the workspace payload needs a built wheel; the arguments are the ones
the CLI passes, except `--cases` (the script default of 5) and `--mutants` (0, so the
mutation gate was **skipped**, as the report says). Joern came from `~/joern`.

Cost, from `/usr/bin/time -l` around that command: **75.41 s wall** (97.45 s user,
20.65 s sys) with Lean already built (`Autoform.Runtime`, so the build stage was seconds)
and **1.67 GB maximum resident set size**. macOS reports the largest single process in
the tree there (not the sum of concurrent children). The stage times are in `pr.md`;
the Joern export is the longest.

## What was found

Five functions, in one source file and two test files (the markdown
report has the table; lines are in `pr.json`):

| function | change | level | why |
|---|---|---|---|
| `Cache.__setitem__` (`src/cachetools/__init__.py:75`) | modified | `translated` | type-checks in Lean; the oracle built no case: `blocked (unexercised): unencodable receiver/arguments: callable-source-identity-unresolved` |
| `TLRUCache.__setitem__` (`src/cachetools/__init__.py:630`) | modified | `translated` | same blocker |
| `CacheTestMixin.test_getsizeof_negative` (`tests/__init__.py:287`) | added | `hole` | `class-construction:unresolved-lexical-identity:Cache` |
| `TLRUCacheTest.test_overwrite_existing_with_expired` (`tests/test_tlru.py:147`) | added | `translated` | blocked: `unittest.case.TestCase` has no contract |
| `...test_overwrite_existing_with_expired.ttu` (`tests/test_tlru.py:151`) | added | `proved` | a kernel theorem over 2 recorded cases |

Also reported: `docs/conf.py:get_version` removed (nothing to verify), and the non-code
files (`CHANGELOG.rst`, `tox.ini`, CI files) not analysed. No function is `oracle-agreed`
or `refuted`; the exit code was 0.

## What each level means here

* `hole` (the new regression test): the model of that function contains a construct the
  translation does not handle, so the report says nothing about its behaviour.
* `translated` (both `__setitem__` methods): the function was turned into a total Lean
  definition that the Lean kernel type-checked. The oracle, which runs the real code and
  the model on the same inputs, could not construct a receiver for it (a `Cache` whose
  `getsizeof` is a callable it cannot identify in the model), so no input was compared.
  It claims that the model exists and type-checks; it does not claim the model matches
  the runtime.
* `proved` (the nested `ttu` function in a new test): the oracle recorded two inputs, both
  agreed, and the kernel proves the model reproduces them. This is a theorem about two
  recorded cases of a helper in a test; it says nothing about the library fix.

## What the report does and does not tell a reviewer about the fix

* **It does flag that `Cache.__setitem__` changed**, and lists it first. That is the
  value: the reviewer is pointed at the changed function and its added test.
* **It does not flag the defect or the fix.** The level of `Cache.__setitem__` is
  `translated`, not `refuted` and not even `oracle-agreed`: the oracle compared nothing
  on it. A reviewer must not read `translated` as "the new check is right".
* **It says nothing about negative sizes.** The only test that exercises them,
  `test_getsizeof_negative`, is itself a `hole` and was not modelled.
* **Even a successful oracle run would not have caught this bug.** `autoform pr` compares
  the model and the runtime of one revision (the head). The head is the fixed code, so
  model and runtime agree on it by construction; the behaviour that changed (rejecting
  size below zero) is a difference between two revisions, which a single-revision
  comparison cannot see.
* **What would flag it** is the cross-revision run: the model of `v7.1.4` against the
  runtime of `v7.1.5` with the `v7.1.5` tests, which
  `docs/evidence-cachetools-negative-size.md` records as one divergence on
  `Cache.__setitem__`. `autoform regress --base v7.1.4 --head v7.1.5` compares the
  pipeline at two commits by what each proved; it is the nearest shipped command, but
  this example did not run it and makes no claim about its result on this change.

In short: `pr` gave a correct map of what changed and an honest "not adjudicated" for the
function that mattered. It is a triage aid for the change, not evidence that the fix is
correct or that the previous revision was buggy.
