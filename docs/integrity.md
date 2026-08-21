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

## What is tracked, and why (policy decided 2026-08-19)

> **The AST is the tracked source of truth. `Autoform/Generated/<M>.lean` is a build
> product and is not tracked.** The one exception is `Cachetools.lean`; see below.

This reverses the earlier policy, and the reversal is the point of the section.

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

`render_lean.py` is a deterministic function of the JSON alone — verified byte-identical
across runs. So a tracked module carries **no information the tracked AST does not already
determine**. What it carries instead is a write channel, and the mutant used it: the
mutant reached git *because* the module was tracked. A 21 MB machine-generated file has no
reviewable diff, so a one-token change inside it passes every human gate. Untracking the
module does not remove a defence; it removes the hole the defence was patching. A mutant
now has to enter through `ast-<M>.json`, where it is a small, reviewable JSON diff.

**The cost, stated honestly.** A clean clone can no longer `lake build
Autoform.Generated.<M>` without running the renderer first (`autoform.sh` and
`scripts/check_render.py --typecheck` both do). `Autoform.lean` imports no generated
module, so the root build is unaffected. For the four large corpora — Ansible, LinuxLib,
LinuxCrypto, V8Base — the AST is itself 15–55 MB, *larger* than the module it renders to,
so tracking the AST by bytes would trade one blob for a bigger one. Those four are tracked
by **sha256 + provenance** in `artifact-manifest.json` and are otherwise reproducible only
by re-exporting from the corpus CPG. That is a real reduction in what a clean clone can
check on its own, and it is recorded here rather than papered over.

**The exception.** `Autoform/Generated/Cachetools.lean` stays tracked. Two conditions make
tracking a render worth its drift risk, and only Cachetools meets both: hand-written
theorems refer to it by name (all 108 of them), and at 300 KB its diff is still something
a person can read. `check_render.py` diffs it against a fresh render on every run — the
original check, kept exactly where it has teeth.

`Autoform/Generated/SC.lean` is a second, less comfortable exception: there is no
`ast-SC.json` anywhere in the repo, so the AST-only policy has nothing to regenerate it
from and untracking it would delete it rather than move it upstream. It stays tracked, and
`check_render.py` can say nothing about it at all. That is a gap, named here so it is not
mistaken for coverage.

## `artifact-manifest.json` — the identity of both halves

One entry per module: `ast_sha256`, `ast_bytes`, `render_sha256`, `render_bytes`,
`ast_tracked`, and for the untracked-AST corpora an `ast_hint` path and a `provenance`
note. It is written by `scripts/check_render.py --record`, which should only ever be run
*after* reviewing the change it is about to bless. Re-recording a hash you have not looked
at converts this file from evidence into a rubber stamp.

## `scripts/check_render.py` — three claims that can still be false

Untracking the module did not turn this check into a no-op. It made it check different
things, each independently falsifiable:

1. **AST integrity** — `sha256(ast-<M>.json)` equals the recorded hash. Under the new
   policy the AST is the only place a mutant can enter.
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
scripts/check_render.py                    # every module in the manifest
scripts/check_render.py --typecheck V8Base
scripts/check_render.py --record LangGo    # only after reviewing the change
```

Exit codes: `0` all verified, `1` a mismatch, `2` nothing checkable at all, `3` some
verified and some **UNVERIFIABLE**. A missing AST, a missing manifest entry or a failed
render is reported with a reason and a non-zero exit — this check must never pass by
having stopped looking.

**Open finding, recorded rather than laundered.** On the first run under the new policy,
`Cachetools` came back MISMATCH: the tracked module was rendered by an older
`render_lean.py` (no `set_option maxRecDepth`, pre-indent-cap layout) and is ~1148 lines
different from a fresh render, though whitespace-insensitively the terms agree. It was not
re-rendered here, because the theorems that depend on it were being edited
concurrently. `check_render.py` therefore exits 1 today, on purpose. The fix is to
re-render Cachetools and re-run its proofs; suppressing the verdict until then would be
the exact failure mode this document exists to prevent.

**Still in history.** Untracking removes these blobs from the *tip*, not from the object
graph. The 35 MB module and today's 27 MB are still reachable from old commits and would
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

`assure.sh` runs `check_render.py` then `check_docs.py` before building the assurance
case. Both are advisory there (`|| true`) so a stale figure does not block evidence
generation — but a red check means every number downstream describes a program nobody
wrote, and should be treated that way.

```bash
scripts/check_render.py && scripts/check_docs.py
```
