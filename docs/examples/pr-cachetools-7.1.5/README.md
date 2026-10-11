# Example: `autoform pr` on cachetools v7.1.4 → v7.1.5

A real run on a real change in a library teams ship. Nothing was posted anywhere; the
files here are what the command wrote, with absolute paths replaced by `<workspace>`,
`<repo>`, `<clone>` and `<tmp>`.

| file | what it is |
|---|---|
| `pr.md` | the review comment (`--markdown`) |
| `pr.sarif` | SARIF 2.1.0 (`--sarif`); `validate_sarif()` in `scripts/pr_mode.py` returned no problems |
| `pr.json` | the full record: per function level, reason, artifacts, oracle status, `behaviour`; stages; exporter digest |
| `control-7.1.5-7.1.6.pr.md`, `.pr.json` | the control: v7.1.5 to v7.1.6, a change that must not read as a behaviour change |
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

Cost, from `/usr/bin/time -l` around that command: **235.48 s wall** (248.76 s user,
66.23 s sys) and **1.67 GB maximum resident set size** (macOS reports the largest single
process in the tree, not the sum of concurrent children), with Lean already built. The
behaviour comparison added about 160 s to the 75 s the levels alone took before: a second
Joern export of the base tree (37 s), the base model's render and build, and two oracle
runs (cross-revision and same-base control, about 50 s each). The control run only happens
when the cross-revision run has divergences. The stage times are in `pr.json`
(`behaviour.stages`).

## What was found

Five functions, in one source file and two test files (the markdown
report has the table; lines are in `pr.json`):

| function | change | level | why |
|---|---|---|---|
| `Cache.__setitem__` (`src/cachetools/__init__.py:75`) | modified | `translated` | type-checks in Lean; the oracle built no case: `blocked (unexercised): unencodable receiver/arguments: callable-source-identity-unresolved` |
| `TLRUCache.__setitem__` (`src/cachetools/__init__.py:630`) | modified | `translated` | same blocker |
| `CacheTestMixin.test_getsizeof_negative` (`tests/__init__.py:287`) | added | `hole` | `class-construction:unresolved-lexical-identity:Cache` |
| `TLRUCacheTest.test_overwrite_existing_with_expired` (`tests/test_tlru.py:147`) | added | `translated` | blocked: `unittest.case.TestCase` has no contract |
| `...test_overwrite_existing_with_expired.ttu` (`tests/test_tlru.py:151`) | added | `translated` | the oracle's verdict was replayed from its cache (`compared: cached from ...`), which this tool does not level above `translated`; the first run of this example computed it fresh and reached `proved` (a kernel theorem over 2 recorded cases) |

Also reported: `docs/conf.py:get_version` removed (nothing to verify), and the non-code
files (`CHANGELOG.rst`, `tox.ini`, CI files) not analysed. No function is `oracle-agreed`
or `refuted`; the exit code was 0 (a behaviour change does not change it).

## What each level means here

* `hole` (the new regression test): the model of that function contains a construct the
  translation does not handle, so the report says nothing about its behaviour.
* `translated` (both `__setitem__` methods): the function was turned into a total Lean
  definition that the Lean kernel type-checked. The oracle, which runs the real code and
  the model on the same inputs, could not construct a receiver for it (a `Cache` whose
  `getsizeof` is a callable it cannot identify in the model), so no input was compared.
  It claims that the model exists and type-checks; it does not claim the model matches
  the runtime.
* `proved` (the nested `ttu` function in a new test, in the first run of this example): the oracle recorded two inputs, both
  agreed, and the kernel proves the model reproduces them. This is a theorem about two
  recorded cases of a helper in a test; it says nothing about the library fix.

## Behaviour: what the new section says

`pr.md` now has a section "Behaviour changes in this PR", `pr.sarif` a result of rule
`autoform/behaviour-changed` (level `warning`) and `pr.json` a `behaviour` object per
function. For this change:

```
Cache.__setitem__(int 1, int 1) on Cache{getsizeof=<lambda>2, size=dict, data=dict,
    currsize=int 0, maxsize=int 3}: base model returns unit; head runtime raises ValueError
```

That is `cache[1] = 1` in `test_getsizeof_negative`, whose `getsizeof` returns -1: the v7.1.4
model stores the item and returns; the v7.1.5 runtime raises `ValueError`. `Cache.__setitem__`
is `behaviour: changed`, with one diverging input of 93 compared
(`behaviour/cross/conformance.json` in the workspace, not copied here); the same function
under the same-base control (v7.1.4 model against the v7.1.4 runtime on the same inputs)
has 0 divergences, so the difference is the revision and not the harness. The other four
functions are `not-compared`, each with its reason: `TLRUCache.__setitem__` ("parameter
list disagrees with the AST": the oracle refuses the call), and three functions added at
head, which have no base behaviour to compare. Suppressed-as-model-noise: 0.

How it is computed (`scripts/pr_mode.py`, `docs/evidence-levels.md`): the base revision is
exported with Joern a second time, with the head's `tests/` overlaid so the lambda the test
passes as `getsizeof` exists in the model, `cartographer/plain_class_values.py` is applied
(without it `Cache.__size = _DefaultSize()` holes every read, see
`docs/evidence-cachetools-negative-size.md`), and the whole base export is rendered as
`CachetoolsPRBase`. `differential.py` then runs that model against the head source with the
head tests, restricted (`--focus`) to the changed functions, because with the whole suite
the 600-case cap dropped the one case that matters. The package is put first on the import
path from `src/`: without that the runtime was the copy of cachetools installed in the
interpreter running the tool (0 cases for `Cache.__setitem__`, measured).

### The control: v7.1.5 to v7.1.6

`control-7.1.5-7.1.6.pr.md` is a change that does not alter behaviour: `Cache.__init__` writes
`{}` where it wrote `dict()`, the pair `docs/evidence-cachetools-negative-size.md` identified
as model noise (Core evaluates `dict()` differently from `{}`, so post-heaps differ). The
run reports `Cache.__init__` as `not-compared` ("all 100 divergent case(s) also diverge in
the same-base control (model noise), none was left to compare") and
`suppressed-as-model-noise: 100`; no function is `changed`. Nothing was dropped silently:
the count is in the report, the comment and `pr.json`, and the filter applies only to a
divergence that the control reproduces exactly (same function, inputs, both results). It
would also have hidden a real change that happened to look identical to the noise on the
same inputs; that is the price of the filter, and it is why the count is shown. Wall time
238.87 s, 1.75 GB maximum resident set size.

## What the report does and does not tell a reviewer about the fix

* **It flags the behaviour change.** `Cache.__setitem__` is the first row of the behaviour
  section with the concrete input and both results. This is the cross-revision oracle,
  which the levels (a single-revision comparison) could not do: the head is the fixed
  code, so its model and its runtime agree by construction.
* **The level of `Cache.__setitem__` is still `translated`**, not `oracle-agreed`: the
  head-model oracle compared nothing on it (`callable-source-identity-unresolved`). The
  two results are independent (`docs/evidence-levels.md`).
* **It does not say the change is right.** A behaviour change is not a failure and not a
  defect; the report shows an input and two results. That the new `ValueError` is the
  intended fix is the reviewer's call (the changelog says it is).
* **It does not cover:** other languages (`not-compared`); functions added at head;
  callers of a changed function unless the oracle's cases reach it; inputs the tests and the
  oracle did not generate (`unchanged-on-inputs` states how many were compared, and is
  no proof); `TLRUCache.__setitem__`, whose cases the oracle refused.
* **The head-model levels are unchanged by this work**: on this run the proved helper `ttu`
  came back `translated` ("compared: cached from ..." the oracle's verdict cache) where the
  first example run said `proved`; the oracle cache (`.autoform-work/oracle`) is a
  pre-existing source of that difference and is not touched here.
