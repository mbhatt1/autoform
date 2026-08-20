# FVSpec evaluation harness (`scripts/fvspec.py`)

STRATEGY.md §11 adopts [FVSpec](https://github.com/GaloisInc/fvspec) for two purposes: it
is the evaluation set for our Specifier, and its 9,415 LLM-transpiled Lean specs were never
mutation-validated, so running our anti-vacuity gate across them is a contribution back.
This script is the second half.

## Where the data lives

The plan's pointer is incomplete:

| Artifact | Location | Contents |
|---|---|---|
| `github.com/GaloisInc/fvspec` | git clone (~32 MB) | generation pipeline, leaderboard, baselines — **no formalizations** |
| `GaloisInc/fvspec-pbt` (HF) | dataset | *upstream* Python PBT corpus (21,746 PBTs) |
| **`GaloisInc/fvspec-fv`** (HF) | `train.jsonl`, ~235 MB | **the benchmark: 9,415 Lean formalizations** |

So the clone is only a locator; the specs come from `fvspec-fv`. The script tries
`--path`, then the git clone, then the HF download, and aborts with copy-pasteable
recovery instructions if all fail. It never fabricates rows.

Each row carries `spec` (theorems with `sorry`), `impl` (computable defs), `pbt_code`
(reference Python), and `pbt_repo` — normalized into `Problem` by `read_problems`.

## The gate

Source-level analogue of `Autoform/Harness/Audit.lean`, which cannot run here because
elaborating 9,415 Lean projects is a different order of cost. A tiny Lean surface reader
splits each theorem into binders / hypotheses / conclusion, then:

| Check | Fires when |
|---|---|
| `dependency_vacuity` | statement mentions no name defined in `Impl.lean` — the `#audit_depends` condition, statically |
| `opaque_subject` | the symbols under test are `axiom`s declared in the spec itself, or `sorry`-bodied impl stubs |
| `trivial_conclusion` | conclusion is syntactically `True` |
| `reflexive_conclusion` | conclusion is `t = t` / `t ↔ t` / `t ≤ t` — provable by `rfl`, constrains nothing |
| `unsatisfiable_hypotheses` | premises are syntactically contradictory (`False`, `p` and `¬p`, `x ≠ x`, `n < 0 : Nat`, empty literal ranges) |
| `empty_quantification` | a binder ranges over `Empty` / `PEmpty` / `Fin 0` / `False`, or membership in `[]` |
| `no_sorry_obligation` | the theorem carries no `sorry` — nothing for a model to discharge |

**Honesty contract.** A surviving spec is `clean_static`, never "passed": it means only
that the checks that ran did not fire. Unparseable specs are `not_analyzed` and are
counted separately, never folded into the clean bucket. The report lists `not_checked`
explicitly — elaboration, Plausible refutation, the mutation gate, and semantic (rather
than syntactic) hypothesis satisfiability all require Lean.

## Usage

```sh
scripts/fvspec.py                                  # fetch, full run
scripts/fvspec.py --path train.jsonl --limit 500   # offline, partial
scripts/fvspec.py --canonical-only                 # 2,772 canonical formalizations
scripts/fvspec.py --per-theorem --out report.json  # full per-theorem detail
```

Full run: ~34 s, 13 MB JSON. Downloads and reports go to `--cache` (a temp dir), never
into the project tree.

## Measured result (full 9,415-row run)

| | |
|---|---|
| problems read / analyzed | 9,415 / 9,352 (63 had no recognizable theorem) |
| theorems analyzed | 73,046 across 251 repos, 78,751 `sorry` placeholders |
| **problems flagged** | **3,833 (41.0%)** |
| theorems flagged | 10,699 (14.6%) |
| canonical problems flagged | 1,047 of 2,772 (37.8%) |

By check (problems / theorems): dependency-vacuity 2,485 / 7,388 · opaque-subject
1,359 / 3,959 · reflexive-conclusion 920 / 1,221 · no-sorry 328 / 1,028 ·
trivial-`True` 256 / 444 · unsatisfiable hypotheses 9 / 13 · empty quantification 2 / 2.

Verified examples from the dataset (raw text, not paraphrase):

```lean
theorem fuzz_event_code_terminates : True := sorry
theorem test_dawg_deterministic (data : Array (String × Char)) :
  build_compression_dawg data = build_compression_dawg data := by sorry
```

The second is the dominant failure mode: a Python determinism PBT (`f(x) == f(x)`)
transliterated into Lean, where purity makes it `rfl` and so contentless.

The dataset ships its own `actually_invokes_given` flag; our dependency check disagrees
with it on 3,321 of 9,352 problems (2,112 where the dataset claims the impl is invoked
but no theorem mentions an impl name, 1,209 the other way). Both signals are heuristic —
the disagreement is reported rather than adjudicated.

These are *screening* results. A flag means "cannot constrain the implementation as
written" on syntactic grounds; converting flags into refutations is the Plausible /
mutation gate's job.
