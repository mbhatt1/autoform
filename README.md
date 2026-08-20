# autoform

Turn an arbitrary codebase into autoformalized Lean 4 by mapping it onto a formal
interpreter written in Lean. See `STRATEGY.md` for the design and the build/buy audit.

**The central bet:** don't formalize the program, formalize the *language* — then the
program becomes data, and every property is a theorem about `eval` applied to it.

**Why it generalizes:** Joern's code property graph is already a universal AST. C, C++,
Java, JavaScript, Python, Kotlin and binaries all normalize to one node vocabulary, so
*one* semantics and *one* exporter cover all of them. No per-language transpiler.

## Use

```sh
./autoform.sh <source-dir> [ModuleName]
```

```
source ──Joern──▶ CPG ──▶ neutral JSON AST ──▶ Lean Core program ──▶ trust ledger
                   │                                   │
                   └─▶ formalization graph             └─▶ differential vs real runtime
```

## Verified end to end

| Corpus | Language | Functions | Verifiable core | Conformance vs real runtime |
|---|---|---|---|---|
| `cachetools` (real repo) | Python | 233 | 12 (5%) | no module-level int fns to compare |
| stress corpus | Python | 6 | 5 (83%) | **25/25 (100%)** vs CPython |
| sample | Python | 5 | 2 (40%) | **10/10 (100%)** vs CPython |
| ctest | C | 7 | 6 (85%) | **25/25 (100%)** vs `cc` |

All generated Lean type-checks. The "verifiable core" is the set of **hole-free**
functions — the only ones that can be verified unconditionally.

The `cachetools` figure was originally reported as 130 (30%). It was wrong: 120 of those
were Joern-synthesised `<metaClassAdapter>` wrappers duplicating real methods. The
exporter now drops them. **5% is the honest number**, and the gap is objects — see
`STRATEGY.md` §13.

## The oracle has teeth

The differential harness is not decoration. On first run it found a real bug:

```
DIVERGENCE fmod(6, -9): cpython=-3 lean=6
DIVERGENCE gcdish(16, -20): cpython=-4 lean=4
```

Python floors integer division and modulo; C and Java truncate toward zero. The
semantics had silently assumed one convention. The fix was not to patch an operator but
to make the semantics **dialect-parameterized** (`Core.Dialect`), with the transpiler
recording the source language. Deliberately mislabelling C as Python now reproduces 7
divergences, so the harness demonstrably discriminates.

This is the failure mode `STRATEGY.md` §5 warns about — a proof about a semantics that
doesn't match the runtime is theater — caught automatically rather than by inspection.

## Layout

| Path | Layer | Role |
|---|---|---|
| `Autoform/Lang/Core/Syntax.lean` | 3 | Universal deep embedding: objects, heap, exceptions, containers, iteration. `Expr.hole`/`Stmt.hole` are the effect boundary. |
| `Autoform/Lang/Core/Semantics.lean` | 2 | Fuel-indexed total interpreter with an explicit heap, method dispatch, exceptions. Dialect-parameterized. No `sorry`, no `partial`. |
| `Autoform/Ledger.lean` | 6 | Coverage, holes-by-cause, verifiable core; JSON evidence for the assurance case. |
| `Autoform/Tactics/Portfolio.lean` | 5 | Tiered proof portfolio; records open obligations instead of admitting them. |
| `scripts/audit_all.py` | 6 | Axiom sweep over every declaration + source sweep for escape hatches. |
| `scripts/mutate.py` | 4 | Source-level mutation gate — the *sufficient* anti-vacuity test. |
| `scripts/sacm.py` | 6 | SACM assurance case + in-toto attestation. |
| `scripts/fvspec.py` | 4 | Vacuity screen over the FVSpec benchmark. |
| `Autoform/Harness/Audit.lean` | 6 | `#audit_axioms`, `#audit_depends`, `#audit_ledger` — Lean metaprogramming. |
| `Autoform/Harness/Conformance.lean` | 4 | Specimen-derived generators; the refutation gate. |
| `Autoform/Lang/Imp/*` | — | Minimal worked example with a proved `evalStmt_sound`. |
| `cartographer/formalization_graph.sc` | 1 | Joern query: call graph, effects, formalizability score. |
| `cartographer/export_ast.sc` | 3 | CPG → neutral AST. Deterministic; no LLM on this path. |
| `cartographer/render_lean.py` | 3 | Neutral AST → Lean. Infers dialect from file extension. |
| `scripts/differential.py` | 2 | Conformance oracle vs CPython / `cc`. |
| `Demo.lean` | — | Refutation gate, axiom audit, vacuity detection, ledger. |

## Design commitments

- **Nothing is silently dropped.** Untranslated constructs become holes tagged with the
  CPG node label that produced them, and the ledger counts them by cause.
- **Ignorance ≠ behaviour.** `outOfFuel` (didn't run long enough), `hole` (didn't
  translate), and a real value are three distinct outcomes.
- **The gate never manufactures its own evidence.** It uses `Testable.check`, never the
  `plausible` tactic, which closes goals with `sorry` — the exact thing the audit exists
  to catch.
- **Total semantics.** Structurally recursive on fuel; no `partial`, no `sorry`.

## Findings the tooling produced (not designed in)

- **Dialect arithmetic.** The differential harness caught Python's floored `%` against
  Lean's `Int`, which had silently mistranslated every C and Java program. Fix: the Core
  language is now parameterized by dialect.
- **Vacuity the dependency check cannot see.** The mutation gate scored `evalStmt_sound`
  at 25% (WEAK) — all six survivors were `evalBExpr` mutations, because `BigStep`'s side
  conditions are stated in terms of `evalBExpr` itself, so a mutation changes both sides
  of the equation. Adding independent characterization lemmas took it to **100%, HAS
  TEETH**.
- **41% of the FVSpec benchmark is vacuous under static screening.** 3,833 of 9,352
  analyzed problems. The dominant pattern: Python determinism tests (`f(x) == f(x)`)
  transliterated into Lean, where purity makes them `rfl`. Spec *translation* is not spec
  *preservation*.

## Not yet built

Neural/SMT prover tiers, spec synthesis, boxed mutable containers (`Stmt.setIndex` is
still an honest hole), `lean4checker` in the loop (the `.olean` files have never been
independently re-verified).

## Dependencies

Lean 4.30.0-rc1 · [Specimen](https://github.com/strata-org/specimen) ·
[Plausible](https://github.com/leanprover-community/plausible) ·
[Joern](https://github.com/joernio/joern) 4.0.606 · Python 3 · a C compiler (for C conformance)
