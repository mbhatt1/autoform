## autoform: evidence for the functions changed since `0d2a6ea17b36`

Base `0d2a6ea17b36` → head `13bb86a55e36`; module `CachetoolsPR2`; exporter: available.

| level | functions |
|---|---|
| none | 0 |
| hole | 4 |
| translated | 3 |
| oracle-agreed | 0 |
| proved | 0 |
| refuted | 0 |

Levels never round up: a function is listed at the highest level its own artifacts reach (`docs/evidence-levels.md`).

| function | change | level | evidence | artifact |
|---|---|---|---|---|
| `src/cachetools/__init__.py:<module>.Cache.__init__`<br>`src/cachetools/__init__.py`:52 | modified | **translated** | type-checked; not adjudicated by the oracle: blocked (unexercised): unencodable receiver/arguments: callable-source-identity-unresolved | `ast-CachetoolsPR2.json`<br>`Autoform/Generated/CachetoolsPR2.lean` |
| `tests/test_cached.py:<module>.DictWrapperTest.cache`<br>`tests/test_cached.py`:347 | modified | **translated** | type-checked; not adjudicated by the oracle: blocked (unexercised): unencodable receiver/arguments: class-identity-unresolved:TestCase:external-base-uncontracted:unittest.case.TestCase | `ast-CachetoolsPR2.json`<br>`Autoform/Generated/CachetoolsPR2.lean` |
| `tests/test_cachedmethod.py:<module>.DictMethodTest.cache`<br>`tests/test_cachedmethod.py`:637 | modified | **translated** | type-checked; not adjudicated by the oracle: blocked (unexercised): varargs/keyword-only: cannot synthesize a faithful call | `ast-CachetoolsPR2.json`<br>`Autoform/Generated/CachetoolsPR2.lean` |
| `tests/test_threading.py:<module>.ThreadingTest.test_cached_stampede`<br>`tests/test_threading.py`:54 | modified | **hole** | translation holes: class-construction:unresolved-lexical-identity:Thread | `ast-CachetoolsPR2.json` |
| `tests/test_threading.py:<module>.ThreadingTest.test_cachedmethod_stampede`<br>`tests/test_threading.py`:70 | modified | **hole** | translation holes: class-construction:unresolved-lexical-identity:Thread | `ast-CachetoolsPR2.json` |
| `tests/test_threading.py:<module>.ThreadingTest.test_cached_locked`<br>`tests/test_threading.py`:86 | modified | **hole** | translation holes: class-construction:unresolved-lexical-identity:Thread | `ast-CachetoolsPR2.json` |
| `tests/test_threading.py:<module>.ThreadingTest.test_cachedmethod_locked`<br>`tests/test_threading.py`:104 | modified | **hole** | translation holes: class-construction:unresolved-lexical-identity:Thread | `ast-CachetoolsPR2.json` |

### Behaviour changes in this PR

Base-revision model against head-revision runtime on the head tests' inputs (Python only). A behaviour change is reported, not failed. 0 changed, 0 unchanged-on-inputs, 7 not-compared; suppressed-as-model-noise: 100.


| function | behaviour | detail |
|---|---|---|
| `src/cachetools/__init__.py:<module>.Cache.__init__` | not-compared | all 100 divergent case(s) also diverge in the same-base control (model noise), none was left to compare |
| `tests/test_cached.py:<module>.DictWrapperTest.cache` | not-compared | test code: its model is the head's own file |
| `tests/test_cachedmethod.py:<module>.DictMethodTest.cache` | not-compared | test code: its model is the head's own file |
| `tests/test_threading.py:<module>.ThreadingTest.test_cached_stampede` | not-compared | test code: its model is the head's own file |
| `tests/test_threading.py:<module>.ThreadingTest.test_cachedmethod_stampede` | not-compared | test code: its model is the head's own file |
| `tests/test_threading.py:<module>.ThreadingTest.test_cached_locked` | not-compared | test code: its model is the head's own file |
| `tests/test_threading.py:<module>.ThreadingTest.test_cachedmethod_locked` | not-compared | test code: its model is the head's own file |

suppressed-as-model-noise: 100 divergent case(s) also diverge when the base model runs against the base runtime on the same inputs (same-base control), so they are not attributed to the change.

Changed files not analysed (outside `--subdir` or not source code): `.github/ISSUE_TEMPLATE/bug_report.md`, `.readthedocs.yaml`, `CHANGELOG.rst`, `pyproject.toml`, `src/cachetools/keys.pyi`, `tox.ini`

<details><summary>Stages</summary>

| stage | status | seconds | note |
|---|---|---|---|
| export | passed | 36.96 |  |
| render | passed | 0.07 |  |
| build | passed | 2.56 |  |
| oracle | passed | 10.21 |  |
| ledger | passed | 1.68 |  |
| specs | passed | 18.94 |  |
| mutation | skipped |  | --mutants 0 |

</details>

Detection: python-ast for Python files; changed-file (every exported function of a changed file) for other languages. Selection: 40 function(s) in the module, 12 pulled in as callees.
Report: `<workspace>/artifacts/pr/CachetoolsPR2`.
