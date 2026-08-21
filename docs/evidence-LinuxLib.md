# Evidence for `LinuxLib` (Linux `lib/`, C, 3368 functions)

> **Staleness notice added during the merge (STRATEGY.md §40).** The figures in this
> document were produced against the `Autoform/Generated/<M>.lean` that was committed at
> the time. That module has since been re-rendered: every large corpus's committed render
> was behind its neutral AST, and all five were regenerated and re-pinned in
> `artifact-manifest.json`. The counts below therefore describe the *previous* render.
> `core_oracle.py`'s own body-staleness gate is what makes this visible rather than
> silent; re-running it against the current module is the way to refresh these numbers,
> and until that is done they should be read as a dated measurement, not as today's.


First coverage/hole accounting for one of the five large corpora. Produced 2026-08-20
from `ast-LinuxLib.json` (= `/tmp/final-LinuxLib.json`, 3368 functions) and
`Autoform/Generated/LinuxLib.lean`, both current at the time of the run (the oracle's
§19 freshness gate confirmed every one of the 3368 AST functions is present in the
`.olean` Lean actually loaded).

`ledger-LinuxLib.json` and `sacm-LinuxLib.json` are gitignored (`ledger-*.json`,
`sacm-*.json`), so their numbers are preserved here and in the committed
`evidence-LinuxLib.json`. `core-oracle-LinuxLib.json` is committed in full.

## 1. Trust ledger (`ledger-LinuxLib.json`, regenerable in 5 s)

| quantity | value |
|---|---|
| functions translated | 3368 |
| AST nodes | 106399 |
| holes | 10105 (9% of nodes) |
| hole-free (static upper bound) | 1168 / 3368 (34%) |
| verifiable core (hole-free AND call-closed) | 843 / 3368 (25%) |
| dynamic-hole risk | 25412 constructs may hole at runtime |

Top hole causes: `op:addressOf:local:unknown-type` 2782, `op:addressOf:field:unknown-type`
709, `stmt:UNKNOWN:static` 574, `control:FOR` 492, `control:GOTO` 402,
`assign:lhs:indirection` 350, `op:indirection:pointer` 322, `op:and` 296,
`op:arrayInitializer` 289 — 409 distinct labels in all. C's holes are dominated by
address-of / pointer indirection, i.e. by the memory model, not by exotic syntax.

**Cost note.** The ledger is quadratic (`Ctx.resolve` is O(n)) but on 3368 C functions it
ran in **5 seconds** wall clock, not the 363 s seen on Django's 10k. No sampling or
truncation was needed.

## 2. Assurance case (`sacm-LinuxLib.json`)

Top goal **G1 = UNDEVELOPED**. Nothing was tuned to make a goal green.

| goal | status | why |
|---|---|---|
| G2 agreement with the real runtime | UNDEVELOPED | `conformance.json` absent — no differential run exists for this module, and none can be produced the usual way: the corpus is kernel C with no in-process oracle. |
| G3 every function translated hole-free | UNSUPPORTED | 2200/3368 functions carry ≥1 hole; 10106 hole occurrences over 409 causes. |
| G3.1 the 843-function core is statically hole-free and call-closed | SUPPORTED | ledger evidence (STATIC — an upper bound by construction). |
| G3.2 the core is hole-free **at runtime** | **DEFEATED** | settled by execution, not estimated: 466 of 843 never holed; **377 did**. |
| D3.1 refutation of G3.1 by execution | DEFEATED (i.e. the refutation stands) | counters G3.1. |
| G4 specifications non-vacuous | UNDEVELOPED | `mutation.json` absent — no source-level mutation gate for this module. |
| G5 theorems kernel-checked, no unsound axiom | UNDEVELOPED | no theorems about LinuxLib exist at all, so there is nothing to audit. |

Artifacts missing for this module: audit, axioms, conformance, contracts, graph, mutation.

## 3. Execution oracle (`core-oracle-LinuxLib.json`) — the number that matters

843 claimed-core functions × 8 synthetic inputs = **6744 cases, 6744 answered, 0 unanswered**.

| outcome | count |
|---|---|
| claimed verifiable core (static) | 843 / 3368 |
| exercised (produced a value, exception or hole) | 843 / 843 (100%) |
| exercised with **real** (test-suite) inputs | **0** |
| NEVER HOLED | **466** |
| HOLED on some input | **377** (0 on a real input — there were none) |
| INCONCLUSIVE | 0 |

**Static-over-runtime overstatement for C: 843 / 466 = 1.81×** (cachetools/Python: 2.5×).

Honest banding of that ratio. Of the 377 refuted functions, 104 hole *only* on
`field:…:non-object` / `setField:…:non-object` — labels a synthetic `int` argument where
real code passes a struct pointer can manufacture, which is exactly the §27 apparatus
risk. Excluding all 104 as possibly-apparatus gives a floor of 273 refutations and a
survivor ceiling of 570, i.e. the overstatement is **between 1.48× and 1.81×**. The
remaining 273 include 175 that hole only on `op:addressOf…` / `op:indirection…` — the C
memory model reaching a hole at runtime inside functions the AST called hole-free — which
no choice of argument shape avoids.

Runtime hole labels (events): `op:addressOf:local:scalar` 752, `op:indirection:pointer`
568, `op:arrayInitializer` 120, `binop:+` 80, `call:va_start` 56, `field:parent:non-object`
52 … 2980 hole events total across 11 label families.

**Denominator disclosure.** Every input was synthetic. Linux `lib/` has no test suite this
harness can trace (the tracer records Python call arguments), so
`core_functions_with_real_inputs = 0`. The 466 survivors are "never holed on 8 synthetic
inputs each", not "never hole". They are an *upper* bound on runtime hole-freedom just as
the static 843 was, only a tighter one.

## 4. Apparatus bug found and fixed — the run before this one was silently empty

`scripts/core_oracle.py`'s Lean harness called

```
applyFunc octx 5000 h fn c.slf c.args
```

but `applyFunc` has gained a sixth parameter, the keyword-argument list
`List (String × Val)`, since the harness was written. Every generated case therefore
**failed to elaborate**; the driver saw only "no answer", bisected down to singletons, and
would have reported all 843 core functions as INCONCLUSIVE — a well-formed artifact full
of zeros, reading as ignorance rather than as breakage. Fixed by passing `[]` (the oracle
calls positionally), plus a loud canary: if the very first batch answers nothing, the run
now aborts with the scratch path instead of writing an artifact.

Any core-oracle run made against this harness before 2026-08-20 00:00 is invalid and
should be re-run.
