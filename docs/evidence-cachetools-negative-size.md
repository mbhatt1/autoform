# Evidence — cachetools 7.1.4: a fixed defect the chain catches (positive result)

Roadmap 2.3 asks for a divergence that names a fixed bug in a real library.
[`evidence-cachetools.md`](evidence-cachetools.md) is the previous attempt (the 7.1.7
replace-with-larger-value fix) and is a negative result. This document is a different fix in
the same library, and **the chain catches it**: the cross-revision oracle run records one
divergence on `Cache.__setitem__`, the buggy function, whose expected value is the fixed
runtime's `ValueError`.

## The defect

cachetools 7.1.5 (PyPI sdist sha256 `0def7134…b134ab5`) changelog: *"Reject negative cache
item `getsizeof` values."* The fix is two lines in `Cache.__setitem__` (the 7.1.4 → 7.1.5
sdist diff of `src/cachetools/__init__.py`, the first hunk after `__version__`):

```python
        if size > maxsize:
            raise ValueError("value too large")
+       if size < 0:
+           raise ValueError("value size must be non-negative")
```

7.1.4 (sdist sha256 `437f55a4…fc1cd6`) accepts a negative size, so `currsize` can go below
zero and the cache's capacity accounting is wrong. The regression test is
`CacheTestMixin.test_getsizeof_negative` in the 7.1.5 `tests/__init__.py` (it is not in the
7.1.4 suite). The upstream commit hash was **not** retrieved; the evidence for the fix is the
released sdist pair and its changelog, as in the previous document.

## Mechanism: cross-revision oracle

`scripts/differential.py` compares the Lean model of one revision with the real runtime.
On the same revision they agree. Here the model is the AST of the **buggy** revision and
the runtime is the **fixed** revision, with inputs traced from the fixed revision's own
test suite, which contains the regression test:

* `cachetools-7.1.4-lib-7.1.5-tests/` — `src/cachetools` of 7.1.4, `tests/` of 7.1.5 (model
  source, and the same-revision control's runtime). `sha256` list:
  `cachetools-7.1.4-lib-7.1.5-tests.sha256`.
* `cachetools-7.1.5-sdist-with-tests/` — `src/cachetools` and `tests/` of 7.1.5 (the fixed
  runtime). `sha256` list: `cachetools-7.1.5-sdist-with-tests.sha256`.
* both under `~/.cache/autoform/corpora`, built from the two PyPI sdists
  (`cachetools-7.1.4.tar.gz`, `cachetools-7.1.5.tar.gz`, each beside a `.sha256`).

## What had to change in the chain

Before this work the call was not comparable. `Cache.__size = _DefaultSize()` is a class
attribute the exporter records as `opaque / class-attribute:unmodeled-value`, and Core
(`Ctx.classLookupGap`) holes **every** read of that name through an instance, before it looks
in the instance dictionary. The test's cache sets `getsizeof`, so `__init__` stores its own
`self.__size = dict()` and the class attribute is shadowed (Data Model 3.3.2.2), yet the
model still stopped (91 `Cache.__setitem__` cases inconclusive on it in the previous run).

`cartographer/plain_class_values.py` (new, Python) is a pass over the exported AST that turns
such an attribute into a `stored` class attribute holding a fresh instance, allocated in the
module-objects initialiser the way the exporter already allocates `NAME = object()`
sentinels. It does so only when the constructed class is provably plain (top-level, defined
before the owner, no bases, decorators, construction or descriptor hooks, no state); every
other attribute stays opaque and holed. It is a separate pass, not an exporter edit,
deliberately: the exporter's sources are pinned by every provenance record
(`scripts/check_provenance.py`), and an edit to `cartographer/export_ast.sc` or
`cartographer/compiler/SourceCompiler.scala` failed the strict check for every attributed
artifact that records an exporter digest (measured: `check_provenance: 13 violation(s)` with
the edit applied, across six artifacts), including corpora in languages this change does
not touch. With the pass instead, the same command reports 0 violation(s). The pass was validated against the same
edit made inside the exporter: on both 7.1.4 and 7.1.6 the pass output is byte-identical to
the exporter-with-the-edit output (`cmp`), which is the check that the pass says what the
exporter would. The exporter itself is unchanged, so no tracked AST moved.

## Commands

```
joern-parse <cachetools-7.1.4-lib-7.1.5-tests> --output cpg.bin
joern --script cartographer/export_ast.sc --param cpgPath=cpg.bin --param out=raw.json --param dataModel=lp64
python3 cartographer/plain_class_values.py raw.json <cachetools-7.1.4-lib-7.1.5-tests> ast-DefectCachetoolsNeg.json
cartographer/render_lean.py ast-DefectCachetoolsNeg.json Autoform/Generated/DefectCachetoolsNeg.lean DefectCachetoolsNeg --shard-functions 0
lake build Autoform.Generated.DefectCachetoolsNeg          # Build completed successfully (57 jobs)
scripts/differential.py ast-DefectCachetoolsNeg.json <corpus> DefectCachetoolsNeg 100 --tests <corpus>/tests/test_cache.py --no-cache
```

with `<corpus>` = `cachetools-7.1.5-sdist-with-tests` (cross revision) and
`cachetools-7.1.4-lib-7.1.5-tests` (same-revision control). The AST is 3,229,674 bytes,
sha256 `557473f4…0f5e5a`, over the 3 MB tracking limit, so it and its provenance record are
gitignored and regenerated from the pinned corpus; the replay test checks the digest.
Exported 473 functions + 19 module initializers; rendered 493 functions.

## The divergence

`tests/fixtures/defect/getsizeof_negative/recorded-cross-revision.json` (tracked: the divergence rows and counts extracted from the run's gitignored `conformance.json`), model 7.1.4
against the 7.1.5 runtime, `divergence_detail`, the one row on the buggy function:

```
function  cachetools/__init__.py:<module>.Cache.__setitem__
args      (int 1, int 1)
detail    cpython raised ValueError, lean returned unit; heap graph=some false
origin    test-suite
observation.outcome   ["exn", "ValueError"]      <- the FIXED runtime (CPython 3.11.13)
lean_repr Autoform.Core.EResult.val (Autoform.Core.Val.unit)   <- the 7.1.4 model stores the item
receiver  Cache{getsizeof = test_getsizeof_negative.<lambda>2, maxsize = 3, currsize = 0}
```

It is the call `cache[1] = 1` of `test_getsizeof_negative` (`getsizeof=lambda x: -1`). The
log line is `DIVERGENCE cachetools/__init__.py:<module>.Cache.__setitem__(int 1, int 1):
cpython raised ValueError, lean returned unit`.

| run | model | runtime | functions | compared | agree | divergences | `Cache.__setitem__` divergences | inconclusive |
|---|---|---|---|---|---|---|---|---|
| cross revision | 7.1.4 | 7.1.5 | 493 | 548 | 526 | 22 | **1** | 52 |
| same revision (control) | 7.1.4 | 7.1.4 | 493 | 546 | 526 | 20 | **0** | 54 |

The control shows the divergence is the revision difference and not the harness: with the 7.1.4
runtime the same suite's `Cache.__setitem__` cases agree, with the 7.1.5 runtime the
`(1, 1)` case does not.

## The other divergences in these runs are NOT the defect

Both runs also record 20 divergences on `Cache.__init__` (15 or 16) and `RRCache.__init__`
(4 or 5) with `cpython=unit lean=unit; heap graph=some false`: same return value,
different post-state. They are present in the same-revision control, so they are not the
bug. Cause, measured from `conformance.json`: the 7.1.4 source writes `self.__data = dict()`
where 7.1.6 writes `{}`; Core evaluates the call `dict()` to a bare dictionary value
(`Stdlib.lean`, `| "dict", [] => v (.dict [])`) while the literal `{}` allocates a boxed
heap object, so the post-heap graphs differ. This is a model infidelity of `dict()` that
the new modelling exposes (before it, `Cache.__init__` stopped on the class-attribute hole
and was inconclusive). It is **not fixed here**: it is a Core semantics change. The previous
document's 7.1.6 corpus uses `{}`, which is why it had no such rows. These rows are why the
claim is "a divergence names the buggy function", with this caveat attached, not "the model
is exact".

## Tests

`tests/test_defect_cachetools_negative.py`:

* `tests/fixtures/defect/getsizeof_negative` (tracked witness) fails on 7.1.4 and passes on
  7.1.5 (needs the pinned corpora; skipped by name otherwise);
* the tracked evidence holds the one `Cache.__setitem__` divergence with expected
  `["exn", "ValueError"]`, and none in the control (needs nothing);
* unit tests of `plain_class_values` (a plain class is modelled; descriptors, constructors,
  bases, class state and a class defined after its owner are refused);
* a full replay: Joern export, the pass, digest check, render, `lake build`, the oracle,
  asserting the exact divergence line (skipped by name without corpora, Joern or `lake`).

```
python -m pytest tests/test_defect_cachetools_negative.py   # 13 passed in 90.85s
```

## Not done

* The 7.1.7 replace-with-larger-value fix ([`evidence-cachetools.md`](evidence-cachetools.md))
  is still not caught: after this change its call is comparable up to
  `self.popitem()`, whose `collections.abc.MutableMapping` code is not translated
  (`class-attribute:external-base:…MutableMapping:popitem`, 7 `Cache.__setitem__` cases
  inconclusive in the cross-revision run).
* The `dict()` boxing infidelity above.
* The upstream fix commit was not retrieved; the sdist pair and changelog are the reference.
* No synthesized-spec (kernel-refuted law) route was run.
