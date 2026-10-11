## autoform: evidence for the functions changed since `48284d73d0a8`

Base `48284d73d0a8` → head `0d2a6ea17b36`; module `CachetoolsPR`; exporter: available.

| level | functions |
|---|---|
| none | 0 |
| hole | 1 |
| translated | 3 |
| oracle-agreed | 0 |
| proved | 1 |
| refuted | 0 |

Levels never round up: a function is listed at the highest level its own artifacts reach (`docs/evidence-levels.md`).

| function | change | level | evidence | artifact |
|---|---|---|---|---|
| `src/cachetools/__init__.py:<module>.Cache.__setitem__`<br>`src/cachetools/__init__.py`:75 | modified | **translated** | type-checked; not adjudicated by the oracle: blocked (unexercised): unencodable receiver/arguments: callable-source-identity-unresolved | `ast-CachetoolsPR.json`<br>`Autoform/Generated/CachetoolsPR.lean` |
| `src/cachetools/__init__.py:<module>.TLRUCache.__setitem__`<br>`src/cachetools/__init__.py`:630 | modified | **translated** | type-checked; not adjudicated by the oracle: blocked (unexercised): unencodable receiver/arguments: callable-source-identity-unresolved | `ast-CachetoolsPR.json`<br>`Autoform/Generated/CachetoolsPR.lean` |
| `tests/__init__.py:<module>.CacheTestMixin.test_getsizeof_negative`<br>`tests/__init__.py`:287 | added | **hole** | translation holes: class-construction:unresolved-lexical-identity:Cache | `ast-CachetoolsPR.json` |
| `tests/test_tlru.py:<module>.TLRUCacheTest.test_overwrite_existing_with_expired`<br>`tests/test_tlru.py`:147 | added | **translated** | type-checked; not adjudicated by the oracle: blocked (unexercised): unencodable receiver/arguments: class-identity-unresolved:TestCase:external-base-uncontracted:unittest.case.TestCase | `ast-CachetoolsPR.json`<br>`Autoform/Generated/CachetoolsPR.lean` |
| `tests/test_tlru.py:<module>.TLRUCacheTest.test_overwrite_existing_with_expired.ttu`<br>`tests/test_tlru.py`:151 | added | **proved** | proved in the kernel: conform_lru_py__module__TLRUCacheTest_test_overwrite_existing_with_expired_ttu (2 recorded case(s)) Mutation gate skipped: --mutants 0. | `ast-CachetoolsPR.json`<br>`Autoform/Generated/CachetoolsPR.lean`<br>`conformance.json`<br>`Autoform/SpecsGen/CachetoolsPR.lean` `conform_lru_py__module__TLRUCacheTest_test_overwrite_existing_with_expired_ttu`<br>`specs.json` |

Removed at head (nothing to verify): `docs/conf.py:<module>.get_version`

Changed files not analysed (outside `--subdir` or not source code): `.github/workflows/ci.yml`, `.readthedocs.yaml`, `CHANGELOG.rst`, `tox.ini`

<details><summary>Stages</summary>

| stage | status | seconds | note |
|---|---|---|---|
| export | passed | 37.72 |  |
| render | passed | 0.08 |  |
| build | passed | 2.69 |  |
| oracle | passed | 10.14 |  |
| ledger | passed | 1.65 |  |
| specs | passed | 22.69 |  |
| mutation | skipped |  | --mutants 0 |

</details>

Detection: python-ast for Python files; changed-file (every exported function of a changed file) for other languages. Selection: 59 function(s) in the module, 32 pulled in as callees.
Report: `<workspace>/artifacts/pr/CachetoolsPR`.
