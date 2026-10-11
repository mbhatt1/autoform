# Evidence — cachetools 7.1.6: a fixed defect the chain now catches

Roadmap 2.3 asks for a refuted law or divergence that names a fixed bug. This document is
the attempt on cachetools, with the fix commit taken from the changelog. It was first a
negative result (the sections from "Where the chain stood" on are kept as measured then).
**Since 2026-10-10 the cross-revision oracle catches it**: one divergence, on the buggy
call itself. See "The catch" directly below; what changed is listed there.

## The catch (2026-10-10)

Model = the 7.1.6 AST (Joern export + `cartographer/plain_class_values.py`, sha256
`7d8193b5…81b0eb`, 3,248,494 bytes, gitignored), runtime = the 7.1.7 sdist, inputs traced
from the 7.1.7 suite (`tests/test_cache.py`), 100 cases per function, `--no-cache`.
Run products tracked in `artifacts/defect/DefectCachetools/{cross,same}-revision/`.

| run | model | runtime | functions | hole-free | compared functions | agree | divergences | inconclusive |
|---|---|---|---|---|---|---|---|---|
| cross revision | 7.1.6 | 7.1.7 | 499 | 416 | 33 | 563/564 | **1** | 36 |
| same revision (control) | 7.1.6 | 7.1.6 | 499 | 416 | 34 | 560/560 | **0** | 40 |

The one divergence (`conformance.json`, `divergence_detail[0]`):

```
DIVERGENCE cachetools/__init__.py:<module>.Cache.__setitem__(int 4, int 7):
  cpython=unit lean=unit; heap graph=some false [test-suite]
receiver  Cache{getsizeof = test_getsizeof_replace_grow.<lambda>2, maxsize = 10,
                currsize = 7, data = {3: 3, 4: 4}}
7.1.7 runtime post-state:  currsize 10, data {3: 3, 4: 7}
```

It is the replace-grow call itself (call 22 of the suite, `key=4, value=7`). In the
same-revision control the same call AGREES with the 7.1.6 runtime, whose post-state is
`currsize 7, data {4: 7}`: the model of 7.1.6 evicts key 3 exactly as 7.1.6 does, and the
7.1.7 fix keeps it. So the divergence is the fix, not the harness.

What made the call comparable, each a separate, tested change:

1. `cartographer/plain_class_values.py` (docs/evidence-cachetools-negative-size.md): the
   `_Cache__size = _DefaultSize()` class attribute is modelled, so `self.__size[key]`
   evaluates (this corpus's export now goes through the pass, as the 7.1.4 one does).
2. `collections.abc.MutableMapping.popitem` is modelled (`scripts/external_bases.py`
   `METHODS` -> `Autoform/Lang/Core/ExternalMethods.lean`): the eviction loop's
   `self.popitem()` runs CPython 3.11's own `next(iter(self))` / `self[key]` /
   `del self[key]` through `Cache`'s dunders instead of stopping at
   `class-attribute:external-base:…MutableMapping:popitem`.
3. `dict()` allocates the same boxed object as `{}` (not needed by 7.1.6, which writes
   `{}`, but part of the same Core change).

Replay: `tests/test_defect_cachetools.py` checks the tracked row (needs nothing) and the
witness on both corpora; the oracle commands are under "Model" below with the pass added.

## The defect

cachetools 7.1.7 (2026-08-01, PyPI sdist sha256 `a3e2a00b…6cf50`) changelog: *"Improve
`Cache.__setitem__` behavior when replacing an existing cache item with a larger value."*
The 7.1.6 code (sdist sha256 `c7a79e7f…70c47e1`) computes the space reserved for a
replaced key incorrectly when the new value is larger:

```python
if key not in self.__data or self.__size[key] < size:   # 7.1.6
    while self.__currsize + size > maxsize:
        self.popitem()
```

so growing an existing entry reserves its full new size on top of its old one, and the
cache evicts or under-fills. The 7.1.7 fix moves the reservation to `diffsize = size -
self.__size[key]` and loops on it. Observed in CPython (`getsizeof=len`, maxsize 10,
`c["a"]="xxx"; c["b"]="xxxx"; c["b"]="xxxxxxx"`):

| revision | len | currsize | keys |
|---|---|---|---|
| 7.1.6 | 1 | 7 | `['b']` (`a` evicted) |
| 7.1.7 | 2 | 10 | `['a', 'b']` |

The fix is identified by the 7.1.6 → 7.1.7 sdist diff of `src/cachetools/__init__.py` (the
`__setitem__` hunk) and its three regression tests in `tests/__init__.py`. The upstream
commit hash was **not** retrieved: no git clone of the upstream repository was made, so the
evidence for the fix is the released sdist pair, not a commit.

## Where the chain stood before the catch — measured

Corpora (digest-pinned, under `~/.cache/autoform/corpora`, see `reference-corpus-sources`):

* `cachetools-7.1.6-lib-7.1.7-tests/` — `src/cachetools` of 7.1.6, `tests/` of 7.1.7. The
  7.1.6 sources are the PyPI sdist (`cachetools-7.1.6.tar.gz`, sha256 `c7a79e7f…70c47e1`),
  the 7.1.7 tests are from the 7.1.7 sdist (`a3e2a00b…6cf50`). The tests are the 7.1.7
  suite because the bug's regression tests exist only there; the oracle runs *the same
  suite* against the 7.1.6 code. `sha256` list: `cachetools-7.1.6-lib-7.1.7-tests.sha256`.
* `cachetools-7.1.7-sdist-with-tests/` — the 7.1.7 sdist, tests included.

Model: `ast-DefectCachetools.json` (exported from the 7.1.6 tree, **gitignored**, 3.2 MB,
over the 2 MB tracking limit; provenance record gitignored with it). Joern 4.0.606,
exporter `cartographer/export_ast.sc` sha256 `6551e9e9…5426e4`.

```
joern-parse <corpus> --output cpg.bin
joern --script cartographer/export_ast.sc --param cpgPath=cpg.bin --param out=ast.json --param dataModel=lp64
python3 cartographer/plain_class_values.py ast.json <corpus> ast-DefectCachetools.json   # since 2026-10-10
scripts/provenance.py record --artifact ast-DefectCachetools.json --source <corpus> --exporter cartographer/export_ast.sc --command "..."
cartographer/render_lean.py ast-DefectCachetools.json Autoform/Generated/DefectCachetools.lean DefectCachetools --shard-functions 0
lake build Autoform.Generated.DefectCachetools          # ✔ Build completed successfully (57 jobs)
scripts/differential.py ast-DefectCachetools.json <corpus> DefectCachetools 100 --tests <corpus>/tests/test_cache.py --no-cache
```

Results (`artifacts/defect/DefectCachetools/<run>/conformance.log`, `conformance.json`, both tracked):

| run | functions | hole-free | compared | cases agreeing | divergences | inconclusive |
|---|---|---|---|---|---|---|
| same revision (7.1.6 src, 7.1.7 tests) | 499 | 416 | 31 | 435/435 | **0** | 165 |
| cross revision (7.1.7 src, 7.1.7 tests) | 499 | 416 | 31 | 440/440 | **0** | 160 |

The model is the 7.1.6 AST in both rows, so the cross-revision row compares the 7.1.6 model
against the 7.1.7 runtime. Zero divergences in that row is the signal that matters:
the same recorded inputs produce the same outcome in both revisions, because the oracle
never saw the replace-grow input.

**Which `Cache.__setitem__` calls were compared.** The suite makes 2067 `Cache.__setitem__`
calls (counted with `sys.settrace` over `test_cache.py`, 7.1.7 tests); the replace-grow
call is call 22 (`key=4, value=7`). In both runs the compared calls are `(1,1)`, `(4,4)`,
`(4,4)`, all `agree`. The `(4,7)` call is not among the compared cases:

* 91 of the `Cache.__setitem__` cases are inconclusive on `class-attribute:unmodeled-value`.
  The receiver's class attribute `_Cache__size` is a `_DefaultSize` instance; the
  transpiler does not model that value, so every `self.__size[key]` read holes.
* 6 more are inconclusive on `class-attribute:external-base:…MutableMapping:popitem`
  (the external-base contract names `popitem`, but its code is not translated).
* 19 are refused as `local-class-captures` (receivers holding a closure).

So the path that contains the defect (`self.__size[key]`, the `diffsize` reservation) is
exactly the path the model cannot evaluate. This is the cause, not an input-selection
accident: a divergence on this method cannot be produced until `_DefaultSize` is modelled.

**Synthesized specs (roadmap 2.3's second route) were not run** on the 7.1.6 module.
For comparison only: the tracked integration module `Autoform/SpecsGen/Cachetools.lean`
(its `report.json`, 7.1.7 AST, not this defect's run) shows the `Cache.__setitem__` laws
refuted as "interpreter reached an untranslated construct" on 7–8 of 8 cases, the same
hole, so the spec route would not have changed the outcome.

## The witness that does catch it

`tests/fixtures/defect/replace_grow/test_replace_grow.py` is the 7.1.7 regression tests
transcribed with `getsizeof=len` (the builtin cachetools' own manual uses). Replayed by
`tests/test_defect_cachetools.py`:

```
PYTHONPATH=<cachetools-7.1.6-lib-7.1.7-tests> python -m pytest tests/fixtures/defect/replace_grow
  -> 1 failed, 2 passed:  test_getsizeof_replace_grow: AssertionError: 2 != 1
PYTHONPATH=<cachetools-7.1.7-sdist-with-tests> python -m pytest tests/fixtures/defect/replace_grow
  -> 3 passed
```

This is the defect, named and reproduced, at the runtime level. The chain (model + oracle +
kernel) does not reproduce it, for the reason given above.

## What would make the chain catch it

1. Model `_DefaultSize` (the class attribute `_Cache__size`) so that `self.__size[key]`
   and `self.__size[key] = size` translate to a total map operation on the receiver. This
   is a transpiler/semantics change, not an oracle change; it moves 91 cases from
   inconclusive to compared on this method alone.
2. Then rerun the cross-revision oracle with the same command. A divergence at `(4,7)`
   would be the refuted law; the expected result, if the model is right, is agreement on
   the 7.1.6 model against the 7.1.7 runtime, which would be the "same-revision" row
   reversed. Either way the number is measured, not argued.

## Changes made to the chain while doing this (all tested)

* `scripts/native_heap.py`: lambdas are indexed the way the exporter names them
  (`<lambda>N`). Before this, a receiver holding a test's `getsizeof=lambda x: x` was refused
  (`callable-source-identity-unresolved`); the 7.1.7 suite's replace-grow lambdas were all
  refused. Tests: `tests/test_native_heap.py::test_lambda_identities_are_named_the_way_the_exporter_names_them`,
  `::test_two_lambdas_on_one_line_are_refused`. Lambdas inside a loop stay refused.
* `scripts/differential.py`: the `MAX_TOTAL_CASES` cap (600) was a silent random draw over
  every origin. Suite-traced cases are now kept first, and the drop is recorded in
  `conformance.json` `case_cap` and printed. Before this, 4228 cases were dropped with no
  record of which origin lost them.

Measured effect on this module: the first 7.1.7 run had 0 `Cache.__setitem__` cases
compared; after the lambda change 0 compared on the replace-grow call (the blocker is the
class attribute, above), and the cap change decides which suite cases reach the 600 seats.

## Commands to reproduce from a clean clone

Needs the two corpora (digest-verified via the `.sha256` files) and Joern 4.0.606 at
`~/joern`. Without them every oracle number above is a named skip, not a pass.

```
scripts/bootstrap.sh                                  # Lean toolchain, Joern, venv
python -m pytest tests/test_defect_cachetools.py      # replays the witness on both corpora
python -m pytest tests/test_native_heap.py -k "identit or lambda"
```

The oracle commands are listed under *Model* above; the AST is regenerated from the
corpus, its digest is in the provenance record that the regeneration writes, not in git.
