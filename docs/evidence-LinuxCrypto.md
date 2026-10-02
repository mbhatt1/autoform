# Evidence for LinuxCrypto (linux/crypto, C, 1,955 functions)

> **DATED SNAPSHOT, produced 2026-08-19. Not current. Status re-checked 2026-10-02 (tree `9639df0`).**
>
> * **Internal consistency, verified:** every figure in the tables below was compared with the
>   tracked `evidence-LinuxCrypto.json` and `core-oracle-LinuxCrypto.json` and agrees, with one
>   exception, corrected in place (the hole-occurrence count is 5,886 in the ledger transcription,
>   not 5,884).
> * **Not re-derivable from a clone:** `ast-LinuxCrypto.json` is in no clone. `scripts/check_render.py`
>   reports `LinuxCrypto` as `NOT-TRACKED` by reviewed policy (never counted as verified); the
>   manifest pins an AST of 18.9 MB (`sha256 98d3a13e5175...`), while this document says the AST it
>   measured was 14.8 MB, so the pinned file is not the measured one. `core-oracle-LinuxCrypto.json`
>   records an author-local AST path. The 9-minute run time, the 3-second ledger and the
>   recomputation of "154 empty bodies" cannot be re-checked here.
> * **Produced by an older pipeline:** before typed integer operators, the C address model,
>   statement-hole contracts and several exporter changes (STRATEGY.md §59-66). The hole counts, the
>   verifiable core and the survivor counts would all move; none has been re-measured.
> * **Superseded statements** are marked "(as of 2026-08-19)" below.
>
> The original staleness notice (STRATEGY.md §40) said the module had since been re-rendered and
> that the counts describe the previous render; that remains true and is why these are labelled a
> dated measurement.


First ledger, assurance case and execution-oracle run for one of the five large corpora.
Before this, all 108 theorems and every conformance number in the repo were about one
238-function Python library. `ledger-*.json` and `sacm-*.json` are gitignored, so the
numbers are transcribed into the committed `evidence-LinuxCrypto.json`;
`core-oracle-LinuxCrypto.json` is committed in full.

> **Correction (see STRATEGY.md §40).** The "108 theorems" figure above was a `grep` count. No `Autoform/SpecsGen/*.lean` module was in the build, and `SpecsGen/Cachetools.lean` -- the 79 of those 108 that were about `cachetools` -- does not elaborate: its whole-table `tryFinally`-free premise became false when the exporter learned to translate `try/finally`. Run `scripts/check_specs.py` for the current, elaboration-based count.


Reproduce:

```sh
sed 's/@MODULE@/LinuxCrypto/g' scripts/ledger.lean.tmpl > /tmp/L.lean
lake env lean /tmp/L.lean                             # 3 s; writes ledger-LinuxCrypto.json (`--run` also prints it but exits 1: no `main`)
cp /tmp/final-LinuxCrypto.json ast-LinuxCrypto.json   # 14.8 MB, not committed
python3 scripts/core_oracle.py ast-LinuxCrypto.json LinuxCrypto --no-tests -n 12 \
        --out core-oracle-LinuxCrypto.json            # 9 min, 3,816 cases
python3 scripts/sacm.py --module LinuxCrypto --root <dir holding the three artifacts>
```

## The claim, and what execution did to it

| figure | value | how it was obtained |
|---|--:|---|
| functions translated | 1,955 | ledger |
| hole-free (static upper bound) | 692 (35%) | ledger |
| **verifiable core** (hole-free AND call-closed) | **318** (16%) | ledger |
| dynamic-hole risk | 18,541 constructs | ledger |
| core functions actually executed | 318 / 318 (100%) | oracle, 3,816 synthetic cases |
| **never holed when run** | **182** (57% of the claim) | oracle |
| holed on some input | 136 | oracle |
| holed on a *real* recorded input | 0 — **there are no real inputs** | oracle |
| **survivors with a semantically empty body** | **154 of 182** | recomputed from the AST |
| **survivors that do anything at all** | **28** (1.4% of the module) | recomputed from the AST |

Static overstatement of runtime hole-freedom: **1.75x** (318 → 182), or **11.4x**
(318 → 28) once empty bodies are excluded. The Python (cachetools) figure is 2.47x
(74 → 30; the cachetools figures are from the module as it was on 2026-08-19, whose core is 98 today, `docs/scale.md`). C's ratio looks better only because C's static core is already small; it is
not better, it is emptier.

The 154 empty bodies are a transpiler artifact: Joern materialises `EXPORT_SYMBOL`,
`DEFINE_MUTEX`, `MODULE_ALIAS_CRYPTO`, `DECLARE_WORK` and per-file `<global>` nodes as
functions with no body. All 154 land in the survivor set (0 of the 136 refuted functions
has an empty body), and they are counted inside the 1,955 / 692 / 318 figures too. An
empty body cannot hole; it also cannot be evidence.

## Why the refutations happen

Top runtime hole labels over the claimed core: `unop:-` (298), `op:indirection:pointer`
(96), `control:FOR` (84), `field:sk:non-object` (84), `call:crypto_skcipher_reqtfm` (72),
`call:ahash_request_ctx` (60), `op:alloc:array-decl` (48).

Two of these deserve separate treatment.

* **29 of the 136** refutations hole only on `field:X:non-object` / `setField:X:non-object`
  — a synthetic integer was passed where the C code expects a pointer to a struct. The
  apparatus chose that shape, so this is weaker evidence (§27). The other **107** hole on
  constructs no choice of argument avoids.
* **`call:` labels refute call closure itself.** `crypto_skcipher_reqtfm`,
  `ahash_request_ctx` and `kpp_tfm_ctx` fail to resolve at runtime *inside functions the
  ledger declared call-closed*. Call closure was correction number two to "hole-free";
  it is now measured as overstated in its own right.

## Assurance case

Top claim `G1` is **UNDEVELOPED**. Nothing was tuned to make a goal green.

| goal | status | why |
|---|---|---|
| G2 semantics + transpiler agree with the real runtime | UNDEVELOPED | `conformance.json` absent — no differential run had been made for a C corpus (as of 2026-08-19; the C leg of `differential.py` has since been run on a SQLite sample, `docs/scale.md`, never on LinuxCrypto) |
| G3 every function translated without holes | UNSUPPORTED | 1,263 / 1,955 functions carry ≥1 hole; 5,886 occurrences (ledger transcription; 5,884 in an earlier draft of this table) over 370 distinct labels |
| G3.1 the 318-function core is statically hole-free and call-closed | SUPPORTED (STATIC), COUNTERED | evidence E6, countered by D3.1 |
| G3.2 the core is hole-free at RUNTIME | **DEFEATED** | execution: 182 / 318 |
| G4 specifications are non-vacuous | UNDEVELOPED | no mutation run for this module |
| G5 theorems kernel-checked, no unsound axiom | UNDEVELOPED | there are no theorems about LinuxCrypto |

`sacm.py` reads the fixed filename `core-oracle.json` and checks its `module` tag. Run
from the repo root it therefore reports G3.2 UNSUPPORTED at 0% coverage, because the
tracked `core-oracle.json` is tagged `Cachetools`. That provenance check is correct — the
per-module filename is the gap — so the case above was produced with `--root` pointing at
a directory holding this module's three artifacts.

## Harness bug fixed (loudly)

`scripts/core_oracle.py`'s Lean harness called
`applyFunc ctx fuel h fn self args` after `applyFunc` gained a trailing keyword-argument
parameter. The scratch module did not elaborate, so **Lean answered nothing for every
case** and the run would have reported 318/318 INCONCLUSIVE and zero refutations on a
corpus where 136 functions demonstrably hole. Fixed by passing `[]`, and by adding a
smoke gate that aborts with Lean's diagnostics if the first case produces no answer.

At the time, `scripts/differential.py` emitted the same stale call and was owned by another
agent, so it was not touched. That is fixed: it now passes `[]` for the keyword list
(`differential.py`, the generated harness line `applyFunc octx {fuel} h fn c.slf c.args []`), and
conformance runs work (`docs/conformance.md`).
