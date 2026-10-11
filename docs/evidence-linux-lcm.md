# Evidence — Linux `lcm()` overflow (kernel commit 74a5fef7cb08): a fixed bug the chain catches

Roadmap asks for a divergence that names a real, fixed bug in code the project did not
write. This document records one, caught on the **pre-fix** kernel source by comparing the
Lean model of that revision with the **post-fix** native code. The mechanism is the
cross-revision one of `docs/evidence-cachetools.md`; unlike cachetools, the C leg's inputs
come from the oracle's typed boundary pool, so the bug's inputs are reached.

## The defect

`lib/lcm.c`, `lcm(unsigned long a, unsigned long b)`. Commit message of the fix:
*"Ensure that lcm(a,b) returns the mathematically correct result, provided it fits in an
unsigned long. The current version returns garbage if a*b overflows, even if the final
result would fit."* (Rasmus Villemoes, Andrew Morton, 2014-12-10.)

| | commit (full) | the line |
|---|---|---|
| pre-fix | `7b212edf86e28f4d0198f2152b2f0553f51a59a5` | `return (a * b) / gcd(a, b);` |
| fix | `74a5fef7cb0839c6b595f90c7914a62ac9d0bcf9` | `return (a / gcd(a, b)) * b;` |

The commits were read from a blobless clone of `torvalds/linux` (history search:
`git log --grep='fix\|overflow\|wrong\|incorrect' -- lib/math lib/gcd.c lib/lcm.c ...`
listed the candidates; `lib/int_sqrt.c` fbfaf851902c was rejected because its bug needs
`ULONG_MAX < ULLONG_MAX`, unreachable on the LP64 model). `lib/gcd.c` is byte-identical in the
two revisions (Euclid with `while ((r = a % b) != 0)`, no `for (;;)`), so the exporter
translates both files hole-free. The one-line difference is also asserted by
`tests/test_defect_linux_lcm.py`.

## Commands

```
git clone --filter=blob:none --no-checkout --single-branch https://github.com/torvalds/linux.git ~/.cache/autoform/corpora/linux-history
git -C linux-history show 7b212edf86e28f4d0198f2152b2f0553f51a59a5:lib/{gcd,lcm}.c   # -> tests/fixtures/defect/linux_lcm/prefix/lib
git -C linux-history show 74a5fef7cb0839c6b595f90c7914a62ac9d0bcf9:lib/{gcd,lcm}.c   # -> tests/fixtures/defect/linux_lcm/postfix/lib
# two trees: {Kbuild,Kconfig,Makefile,include,tools} of ~/.cache/autoform/corpora/linux-v7.2 + that lib/
scripts/source_context.py <prefix>/lib ctx.json --args-file args
joern-parse <prefix>/lib --output cpg.bin <args>
joern --script cartographer/export_ast.sc --param cpgPath=cpg.bin --param out=ast-LinuxLcmPrefix.json --param dataModel=lp64
scripts/provenance.py record --artifact ast-LinuxLcmPrefix.json --source <prefix>/lib --exporter cartographer/export_ast.sc --command "..."
cartographer/render_lean.py ast-LinuxLcmPrefix.json Autoform/Generated/LinuxLcmPrefix.lean LinuxLcmPrefix --shard-functions 0
lake build Autoform.Generated.LinuxLcmPrefix            # Build completed successfully (57 jobs)
scripts/differential.py ast-LinuxLcmPrefix.json <postfix>/lib LinuxLcmPrefix 100 --no-cache   # cross revision
scripts/differential.py ast-LinuxLcmPrefix.json <prefix>/lib  LinuxLcmPrefix 100 --no-cache   # same revision
```

The model is `ast-LinuxLcmPrefix.json` (4998 bytes, tracked; sha256 `06d9b124…806893`;
provenance `provenance/ast-LinuxLcmPrefix.json.prov.json`, Joern 4.0.606, source identity
`tree-sha256:71767830a9f7…:2files` — the prefix tree is not a git checkout, so the two
commit hashes are pinned in the record's `command` and in the table above). It holds 4
functions, all hole-free (`gcd`, `lcm` and the two module initializers).

## Result (`tests/fixtures/defect/linux_lcm/recorded-cross-revision.json`, tracked; the full conformance.json of each run is a gitignored product)

| run | runtime source | compared | agree | divergences | inconclusive |
|---|---|---|---|---|---|
| same revision | pre-fix | 2 functions | 99/99 | **0** | 101 |
| cross revision | post-fix | 2 functions | 86/99 | **13** | 101 |

The same-revision row shows the model agrees with its own revision's runtime on every
adjudicated case; the divergence is therefore the fix, not a translation error. The 101
inconclusive cases are the same in both runs: 58 in `gcd` and 43 in `lcm` reach
`call:swap` (the kernel `swap()` macro in `gcd`, which the exporter does not model). They
are unadjudicated, not agreeing.

All 13 divergence rows name `lcm`. First row, quoted from `conformance.json`
(`divergence_detail[0]`):

```
DIVERGENCE lcm(int 9223372036854775808, int 2): cc=int 9223372036854775808 lean=int 0 [boundary-typed]
```

`cc` (the expected value) is what the post-fix native code returned; `lean` is the pre-fix
model: `2^63 * 2 = 2^64` wraps to 0. Of the 13 rows, **4 are the bug the fix describes**
(the true lcm fits in 64 bits, so the post-fix value is the mathematically correct one and
the pre-fix result is garbage): `lcm(2^63, 2)`, `lcm(2^40, 2^40)`, `lcm(2^63, 2^16)`,
`lcm(2^62, 2^31)`. The other 9 have a true lcm above `2^64`; both revisions return a
wrapped value there, and they differ because the two formulas wrap differently. Those 9
are real divergences between the revisions but are not the fixed bug, and the fix does not
claim correctness for them.

## Replay

`tests/test_defect_linux_lcm.py` (4 tests): the fixture is the one-line fix; the recorded
rows name `lcm`, expect the post-fix value and (for fitting results) the true lcm; the
native pre/post-fix code differs at `(2^32, 2^32)` (0 vs 2^32); and, behind
`AUTOFORM_TEST_LEAN=1`, the full render, `lake build` and oracle run reproduce the
divergence from the tracked AST. The native and Lean tests skip with a named reason when
`~/.cache/autoform/corpora/linux-v7.2` or `cc` is absent.

## Not done

* The kernel include skeleton comes from v7.2, not from the 2014 revisions' own headers;
  only the two `.c` files are 2014. `swap` is therefore not modelled (the 101 inconclusive).
* `lcm(n, 0)` was fixed separately (69c953c85c6c) and is not covered here.
* The exporter's `for (;;)` hole was not touched.
