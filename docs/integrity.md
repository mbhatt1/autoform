# Artifact integrity: checking that we measured the program we think we measured

Every claim in this project is a statement about an artifact — `ast-<M>.json`,
`Autoform/Generated/<M>.lean`, `ledger-<M>.json`, `conformance.json`. The proofs are
kernel-checked and the oracles are real, but all of that is worthless if the artifact
under test is not the one you believe it is.

This document exists because that failed, repeatedly, and not in ways anyone guessed in
advance. Each check below is named after the incident that motivated it.

## The rule underneath all of it

> A metric computed from the same artifact it describes will flatter itself.

Stated in `STRATEGY.md` §17 and re-derived the hard way in §19, §27, §30, §31, §33 and
§34. The only things that have ever refuted one of this project's claims are **execution**
and **an independent recomputation**. No amount of care inside a single artifact
substitutes for either.

## What is tracked, and why

The AST is the source for a generated module, and `artifact-manifest.json` pins
both input and output hashes. Most rendered modules are untracked build products.
The repository also retains these tracked renders: `CMath`, `Cachetools`,
`LinuxLibSample`, `V8BaseSample`, and `SC`. Check the inventory with
`git ls-files 'Autoform/Generated/*.lean'`; never edit a render by hand.

The move toward AST-first storage was decided on 2026-08-19. The historical
reasoning below explains that policy; the actual tracked exceptions and import
graph still determine what a build and audit check.

**The incident that set the old policy.** A mutation-gate mutant reached git and survived
four commits. `_DefaultSize.__getitem__` returned `0` where the cachetools docstring says
*"a constant size 1 for any key"* and `ast-Cachetools.json` says `int 1`:

| commit | value | |
|---|---|---|
| `051f950` | `int 1` | correct |
| `3898d6c` | `int 0` | mutant enters history |
| `7abf59f`, `9d3e6a3`, `d5f2333` | `int 0` | inherited by commits that never touched the file |
| `919ab2f` | `int 1` | self-healed |

**Every proof about that module still passed, because a mutant is a perfectly well-typed
program.** Separately, a concurrent pipeline left the module and the AST 30 functions
apart (238 against 208). Neither is visible from anything derived from the module; both
are visible to an independent re-render. That argument is still correct and
`check_render.py` still rests on it.

**The incident that reversed it.** A `git add -A` during a merge committed
`Autoform/Generated/Ansible.lean` (21 MB) and `LinuxLib.lean` (6 MB); a 35 MB generated
module went in the same way earlier. Cleaning them up forced the question the first
incident had obscured: *what does tracking the module buy, given the AST is tracked?*

For a fixed renderer and module name, rendering the same AST is deterministic.
Tracking a large render duplicates that derivable content and creates another place
where a mutation can persist unnoticed. Keeping only the AST makes the input diff
the review target. Local renders can still be mutated, so every materialization
must be checked against the reviewed input and renderer.

**Build and replay scope.** The root import graph reaches generated `CMath`,
`Cachetools`, `LinuxLibSample`, `V8BaseSample`, and `V8Base`. CI materializes
`V8Base` from its tracked AST before the root build; the other imported renders
are tracked. A clean clone therefore needs that rendering step before a full
`lake build`. An audit of a root module reaches its imports, not every Lean file
in the directory.

The installed CLI has a separate root, `Autoform.Runtime`. Its only generated
corpus dependency is `Cachetools`, reached through `Autoform.Contracts`. The
historical corpus proofs belong to the repository build and release gate.
`Autoform/SpecsGen/V8Exp.lean` and `V8Exp2.lean` are tracked but outside the root
import graph; a root replay alone provides no replay evidence for those files.

**Input availability.** `ast-V8Base.json` is tracked. The manifest also promises
`Ansible`, `LinuxLib`, and `LinuxCrypto`, whose AST bytes are not tracked. A hash
and an out-of-tree path do not make those inputs available to a clean clone, nor
establish their source revision or extraction history. Missing inputs remain
`UNVERIFIABLE` until the exact bytes can be supplied and checked. Re-exporting a
different source revision with today's exporter produces new evidence, not a
reproduction of the old artifact.

`Autoform/Generated/SC.lean` has neither a tracked AST nor a manifest entry and
is outside both import graphs. `check_render.py` cannot establish its derivation,
and root replay does not check it. That gap must remain explicit.

## `artifact-manifest.json` — the identity of both halves

One entry per module: `ast_sha256`, `ast_bytes`, `render_sha256`, `render_bytes`,
`ast_tracked`, and for the untracked-AST corpora an `ast_hint` path and a `provenance`
note. It is written by `scripts/check_render.py --record`, which should only ever be run
*after* reviewing the change it is about to bless. Re-recording a hash you have not looked
at converts this file from evidence into a rubber stamp.

The recorder currently derives `ast_tracked` from a root-level file's existence,
not Git's index. Check actual tracking with `git ls-files`; do not use that field
alone as evidence that an input will be present in a clean clone.

## `scripts/check_render.py` — three claims that can still be false

Untracking the module did not turn this check into a no-op. It made it check different
things, each independently falsifiable:

1. **AST integrity** — `sha256(ast-<M>.json)` equals the recorded hash. This catches
   changes to the input independently of changes to a materialized module.
2. **Render stability** — `sha256(render(AST))` equals the recorded render hash. This is
   what byte-comparing against the tracked module bought (the pinned identity of the
   artifact every downstream number describes) without the megabytes and without the
   write channel. A renderer change that silently alters output is caught here.
3. **Local materialisation** — if the module exists in the working tree, it must be
   byte-identical to the fresh render. The original mutant check, now over a working tree
   instead of an index.

With `--typecheck` it materialises the render and runs `lake build
Autoform.Generated.<M>`: the claim that the AST renders to a program the Lean kernel
accepts. Weaker than "the committed module is correct", stronger than "the bytes match",
and checked against the toolchain rather than against a hash we wrote ourselves.

```bash
scripts/check_render.py                    # manifest modules and local ast-*.json files
scripts/check_render.py --typecheck V8Base
scripts/check_render.py --record LangGo    # only after reviewing the change
```

Exit codes: `0` all verified, `1` a mismatch, `2` nothing checkable at all, `3` some
verified and some **UNVERIFIABLE**. A missing AST, a missing manifest entry or a failed
render is reported with a reason and a non-zero exit — this check must never pass by
having stopped looking.

**Resolving drift.** Run the checker to obtain the current verdict. Review a fresh
render against the old bytes before recording new pins. Changes to headers and
changes to executable dialects require different evidence; successful elaboration
alone does not establish source equivalence. Regenerate through the renderer,
rebuild affected imports, rerun native comparisons where semantics changed, and
repeat the required proof, mutation and fresh replay checks. A missing corpus or
mismatched render remains a release blocker throughout this process.

**Still in history.** Untracking removes these blobs from the *tip*, not from the object
graph. Historical generated modules remain reachable from old commits and would
need a history rewrite and a force-push to clear — which needs the repository owner's
explicit consent and has not been done.

## `scripts/check_docs.py` — do the documented figures match the artifacts?

**Incident.** Three documents quoted three different verifiable-core numbers — 45, 45 and
74 — while the ledger said 69. None were current. Nothing checked, so nothing complained.

**Second incident, in the checker itself.** The first version passed 5/5 while the numbers
were wrong, because it compared the docs to a *stale* ledger. Docs and artifact agreed
perfectly and neither was true. **Comparing two things that drift together only proves
they drift together.**

**The check.** Each documented figure is bound to the artifact field it quotes, and
independent artifacts are cross-checked against each other — the ledger's `functions` must
equal the number of functions in the AST it was computed from. It reports:

* a figure that disagrees with its artifact, naming the correct value;
* two artifacts that disagree with each other, naming which is stale;
* **a pattern that no longer matches at all** — the failure where a document is
  restructured and the check silently stops checking;
* an absent input, as a failure rather than a skip. The cross-artifact check went quiet on
  a fresh clone for exactly this reason.

Negative-tested in both directions. A checker that has only ever passed has not been
tested.

## Concurrency: `build_stable`, `mutation_in_progress`, `measurement_basis`

**Incident.** `scripts/differential.py` wrote its harness to a hardcoded
`/tmp/autoform_diff.lean`. With several processes running it, they overwrote each other
mid-run — so a run could report conformance **for another process's program**. Every
scratch path now lives under one `mkdtemp`, and the harness copies the compiled `Lang`
tree and the generated `.olean` into a private directory with `LEAN_PATH` pointed at it,
so a concurrent rebuild cannot change the program mid-run.

**Incident.** The mutation gate rewrites `Autoform/Generated/<M>.lean` in place. A
conformance run taken during a mutation reports divergences that are artifacts of the
mutant. `conformance.json` now carries `build_stable` and `mutation_in_progress`, and
`scripts/synth_specs.py` refuses to run (exit 3) against a subject that is git-dirty,
carries a `.mutate-backup` sibling, or contains a `__mutated` marker.

**Marker-based detection is not sufficient on its own.** A one-line value mutation
(`.int 0` → `.int 1`) carries no marker. The git-dirty check is what catches that class,
which is why all three conditions are tested rather than the most obvious one.

**Incident.** The differential harness stopped skipping varargs functions. Conclusive
cases went from 2 to 14 — seven times more of the artifact actually checked — while the
headline rate fell from 100% to 64%. Quoting the rate alone would have read as a
regression when it was a large improvement. `conformance.json` now records
`measurement_basis`, and rates from different bases must not be compared.

## The tracked ASTs predate the character-literal fix

`check_render` asks whether a committed module is the render of its committed AST.
Nothing asks whether the committed **AST** is what today's exporter would produce —
and there is a case in the tree where it is not.

`cartographer/export_ast.sc` used to parse `'0'` as the integer `0` rather than the
codepoint `48` (docs/languages.md item 8, found by the differential oracle against the
JVM). Every `ast-*.json` in this repository was exported before that fix, so any of
them containing a digit character literal encodes the old, wrong value. The renders,
recorded hashes and generated specs are all consistent *with those ASTs*, so every
gate stays green: the artifacts agree with each other, and the thing they agree on is
stale. That is the failure mode this file exists for, one level up from where the
checks currently look.

Re-exporting is not a local change. The large corpora's ASTs are deliberately not in
git (their sources and CPGs are not either), so a re-export has to be done from the
original corpora and landed together with fresh renders, re-recorded manifest hashes
and regenerated specs — and any spec whose truth depended on the old literal value
will legitimately change. Until then, treat a tracked AST as evidence about the
exporter that produced it, not about the exporter in the tree.

The guard for exactly this existed and was switched off. `scripts/provenance.py
record` writes `exporter_sha256` (the hash of the `.sc` that produced an AST) next to
`joern_version`, and its docstring calls that the field that "earns its keep without
any CPG at all" — but nothing invoked it, so `provenance/` held one
`unattributed.json` and every AST in the tree was unattributed. The field that would
have flagged this exporter change as a reason to re-export was never written.

`autoform.sh` stage 3 now records it, so ASTs produced from here on are attributed.
That does **not** retroactively attribute the ones already committed: they remain
unattributed, which is now itself the signal that they predate the fix.

`scripts/check_provenance.py` **is now a required CI gate**, which it could not be while
it exited 1. Three artifacts were violating it: `ast-Cachetools.json` and
`ast-V8Numbers.json` had been regenerated since their baseline entries were written, so
their digests no longer matched and the entries had stopped applying; `ast-V8Base.json`
was in neither the baseline nor `provenance/`, which was an omission rather than a signal.

One of the three was closed with evidence rather than with a digest bump.
`ast-Cachetools.json`'s source tree was previously "not identified anywhere in the
repository"; it is now identified as **cachetools v7.1.7** — the only release predating the
2026-08-22 regeneration — because a fresh export of that tag reproduces its exact 209-entry
`(name, file)` set across all five modules. It still DIFFERS in the bodies, for two
separable reasons worth keeping apart: today's exporter emits six per-function keys the
artifact has no trace of (`paramTypes`, `paramIntegerTypes`, `pythonSignature`,
`returnType`, `returnIntegerType`, `sourceName`), and after discounting those, 105 of 209
entries still differ. So the artifact predates exporter work considerably larger than the
character-literal fix, and re-exporting would produce new evidence rather than reproduce
the old artifact.

The other two are recorded honestly as the weakest class of entry in the file: they name
the commit that produced or changed the artifact and nothing about the tree it came from.
A V8-sized C++ corpus cannot be identified by matching a fresh export the way cachetools
was. **The gate passing does not mean the ASTs are attributed** — it reports 0 of 14
attributed, with all 14 named. What it now prevents is a *new* unattributed artifact, and
a regenerated one silently keeping an entry that no longer describes it.

## Two failure shapes worth naming

**A true fact adjacent to the failure is the most convincing wrong explanation
available.** Five divergences were attributed to a real Core gap (`_HashedTuple`), then
"corrected" to mutation contamination on the evidence that the decl was in the mutation
list — which proves it *was mutated*, not that it *caused those divergences*. Both
accounts were right about different runs. Two reports of the same *count* are not reports
of the same *event*. See §33 and §34.

**"The last divergence was the apparatus" is a prior, not a verdict.** Applied reflexively
it produced a wrong correction to a right finding.

## Running them

Repository CI runs these integrity checks as required gates. The package's release
workflow requires that repository CI before publication. `assure.sh` delegates to
`scripts/assure.py`, which builds evidence for the selected source and module; it
does not run the repository-wide historical render or documentation checks. A
successful scoped run therefore does not establish release readiness.

```bash
scripts/check_render.py && scripts/check_docs.py && scripts/check_provenance.py
```
