# Artifact integrity: checking that the measured program is the intended one

Every claim in this project is a statement about an artifact — `ast-<M>.json`,
`Autoform/Generated/<M>.lean`, `ledger-<M>.json`, `conformance.json`. Kernel-checked proofs
and real oracles say nothing if the artifact under test is not the one named.

Each check below was added in response to a specific incident.

## The underlying rule

> A metric computed from the same artifact it describes will flatter itself.

Stated in `STRATEGY.md` §17 and re-derived in §19, §27, §30, §31, §33 and §34. The only
things that have refuted one of this project's claims are **execution** and **an
independent recomputation**. Care inside a single artifact substitutes for neither.

## `scripts/check_render.py` — is the module a render of the AST?

**Cause.** A mutation-gate mutant reached git and survived four commits.
`_DefaultSize.__getitem__` returned `0` where the cachetools docstring says *"a constant
size 1 for any key"* and `ast-Cachetools.json` says `int 1`:

| commit | value | |
|---|---|---|
| `051f950` | `int 1` | correct |
| `3898d6c` | `int 0` | mutant enters history |
| `7abf59f`, `9d3e6a3`, `d5f2333` | `int 0` | inherited by commits that never touched the file |
| `919ab2f` | `int 1` | self-healed |

Every proof about that module still passed: a mutant is a well-typed program, and nothing
derived from the module could observe the change. Separately, a concurrent pipeline left
the module and the AST 30 functions apart (238 against 208), so measurements described a
build that corresponded to no checked-in AST.

**The check.** `render_lean.py` is deterministic — verified byte-identical across runs — so
`render(AST)` is a total specification of what the module must contain. The check
re-renders and compares, and prints the differing declarations.

```bash
scripts/check_render.py            # every module that has both an AST and a .lean
scripts/check_render.py Cachetools
```

On first run it found three problems: the live mutant, the 238/208 gap, and drift of
`Sample` and `Stress` from their ASTs, predating `moduleInits`.

`ast-*.json` is tracked in git for this reason. It had been ignored while the module
rendered from it was committed; it is the half that makes the other checkable.

## `scripts/check_docs.py` — do the documented figures match the artifacts?

**Cause.** Three documents quoted three different verifiable-core numbers — 45, 45 and 74 —
while the ledger said 69. None were current, and nothing checked.

**Second cause, in the checker itself.** The first version passed 5/5 while the numbers were
wrong, because it compared the docs to a stale ledger. Docs and artifact agreed and neither
was true. Comparing two things that drift together only establishes that they drift
together.

**The check.** Each documented figure is bound to the artifact field it quotes, and
independent artifacts are cross-checked against each other — the ledger's `functions` must
equal the number of functions in the AST it was computed from. It reports:

* a figure that disagrees with its artifact, naming the correct value;
* two artifacts that disagree with each other, naming which is stale;
* a pattern that no longer matches at all — the case where a document is restructured and
  the check silently stops checking;
* an absent input, as a failure rather than a skip. The cross-artifact check went quiet on
  a fresh clone for this reason.

Negative-tested in both directions.

## Concurrency: `build_stable`, `mutation_in_progress`, `measurement_basis`

**Cause.** `scripts/differential.py` wrote its harness to a hardcoded
`/tmp/autoform_diff.lean`. With several processes running it, they overwrote each other
mid-run, so a run could report conformance for another process's program. Every scratch
path now lives under one `mkdtemp`, and the harness copies the compiled `Lang` tree and the
generated `.olean` into a private directory with `LEAN_PATH` pointed at it, so a concurrent
rebuild cannot change the program mid-run.

**Cause.** The mutation gate rewrites `Autoform/Generated/<M>.lean` in place. A conformance
run taken during a mutation reports divergences that are artifacts of the mutant.
`conformance.json` now carries `build_stable` and `mutation_in_progress`, and
`scripts/synth_specs.py` refuses to run (exit 3) against a subject that is git-dirty,
carries a `.mutate-backup` sibling, or contains a `__mutated` marker.

Marker-based detection is not sufficient on its own. A one-line value mutation
(`.int 0` → `.int 1`) carries no marker; the git-dirty check catches that class. All three
conditions are tested rather than only the most obvious one.

**Cause.** The differential harness stopped skipping varargs functions. Conclusive cases
went from 2 to 14 — seven times more of the artifact checked — while the headline rate fell
from 100% to 64%. The rate alone would have read as a regression. `conformance.json` now
records `measurement_basis`, and rates from different bases must not be compared.

## Two failure shapes

A true fact adjacent to the failure is a convincing wrong explanation. Five divergences
were attributed to a real Core gap (`_HashedTuple`), then "corrected" to mutation
contamination on the evidence that the decl was in the mutation list — which establishes
that it *was mutated*, not that it *caused those divergences*. Both accounts were right
about different runs. Two reports of the same count are not reports of the same event. See
§33 and §34.

"The last divergence was the apparatus" is a prior, not a verdict. Applied reflexively it
produced a wrong correction to a right finding.

## Running them

`assure.sh` runs `check_render.py` then `check_docs.py` before building the assurance case.
Both are advisory there (`|| true`) so a stale figure does not block evidence generation. A
red check means every number downstream describes a program nobody wrote.

```bash
scripts/check_render.py && scripts/check_docs.py
```
