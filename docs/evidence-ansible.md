# Evidence for `Ansible` (Python, 5,546 functions)

The first of the five large corpora to get all three evidence artifacts: a trust ledger, an
assurance case, and an **execution** oracle over the claimed verifiable core. Until this
run, all 108 theorems and every coverage claim in the repository were about `cachetools`
(238 functions); 12,700 of the 12,946 translated functions had no coverage claim and no
hole accounting at all.

Everything below is a measured number from this run. Where a number could not be measured,
that is said rather than estimated.

| | |
|---|---|
| Source tree | `ansible/lib/ansible` @ 2.22.0.dev0 |
| Neutral AST | `ast-Ansible.json` (52 MB, = `/tmp/final-Ansible.json`) |
| Generated module | `Autoform/Generated/Ansible.lean` (21 MB, builds in 79 s) |
| Dialect | Python |

## 1. Trust ledger (`ledger-Ansible.json`)

```
functions translated : 5546
AST nodes            : 345010
holes                : 8060  (2% of nodes)
hole-free (upper bd) : 3304 / 5546 functions  (59%)
VERIFIABLE CORE      : 2096 / 5546 functions  (37%) — hole-free AND call-closed
dynamic-hole risk    : 59507 constructs may hole at runtime (input-dependent)
```

Top hole causes: `import:module-value` 1416, `import:unresolved` 1309, `import:operand`
1199, `lit:unquoted` 974, `op:formatString` 781, `op:slice` 325, `expr:BLOCK-impure` 293.
Imports dominate: 3,924 of 8,060 holes (49%) are one of the three import labels, so the
single highest-value transpiler fix for this corpus is import resolution, not control flow.

**Cost.** 33.7 s wall clock for the whole ledger, not the multi-minute quadratic feared
from Django's 10k-function run (363 s). `Ctx.resolve` is still O(n) per lookup; at 5,546
functions that constant has not yet bitten.

## 2. Assurance case (`sacm-Ansible.json`)

Top claim **G1: UNDEVELOPED**. Sub-goals:

| Goal | Status | Why |
|---|---|---|
| G2 semantics agrees with the runtime | UNDEVELOPED | `conformance.json` absent — no differential run has ever been made for this module. Faithfulness is untested here, not merely unproved. |
| G3 every function translated without holes | UNSUPPORTED | 2,242 / 5,546 functions carry at least one hole; 8,060 occurrences over 38 distinct causes. |
| G3.1 the 2,096-function core is hole-free and call-closed *in the AST* | SUPPORTED (static) | from the ledger — but see the defeater below |
| G3.2 the core is hole-free at **runtime** | **DEFEATED** | settled by execution: 511 of 2,096 never holed; 1,585 did |
| D3.1 defeater | asserted | static hole-freedom overstates runtime hole-freedom by **4.1x** on this corpus |
| G4 specifications are non-vacuous | UNDEVELOPED | `mutation.json` absent — no mutation gate has been run for Ansible |
| G5 theorems kernel-checked, no unsound axiom | UNDEVELOPED | no theorems exist about Ansible, and no per-module axiom dump was captured. The verification half of the pipeline does not exist for this corpus. |

Nothing was tuned to turn a goal green. Three goals are UNDEVELOPED because the evidence
genuinely does not exist for this module, and the runtime goal is DEFEATED by this
project's own oracle.

Two reporting warts observed, not fixed (they change no status): `sacm.py` reads the core
oracle from the fixed filename `core-oracle.json` rather than `core-oracle-<Module>.json`,
so this case was generated with `--root` pointed at a directory where the Ansible oracle
output carries that name; and a `core-oracle.json` belonging to a *different* module is
still hashed into `subject` and listed in `artifactsPresent` even though the module-tag
check correctly refuses to use it as evidence.

## 3. Execution oracle (`core-oracle-Ansible.json`) — the number that matters

`scripts/core_oracle.py` runs the claimed core instead of describing it.

```
ledger's static claim   : 2096 / 5546 functions (37%) hole-free AND call-closed
executed                : 8786 cases over 2096 claimed-core functions (4 synthetic
                          inputs each + 402 argument tuples traced from test/units)
exercised at all        : 2096 / 2096 (100%) — every claimed-core function ran
  … with real inputs    : 139
NEVER HOLED (executed)  : 511 / 2096  (24% of the claim survives)
HOLED on some input     : 1585        (87 of them on a *real*, test-suite input)
INCONCLUSIVE            : 0
answered                : 8786 / 8786 cases — no case went unanswered
```

**Static hole-freedom overstates runtime hole-freedom by 4.1x on Ansible**, against 2.5x
measured on cachetools. Restricted to functions that received arguments recorded from
Ansible's own unit tests, the picture is worse, not better: 87 of the 139 core functions
reached by real inputs (63%) holed on one.

Runtime hole labels are a different population from the static ones — none of the top
static causes (imports) appears here, because a function containing an import hole is
excluded from the core in the first place:

| runtime label | count |
|---|---|
| `call:isinstance` | 563 |
| `setIndex:immutable-containers` | 310 |
| `binop:%` | 192 |
| `index:unsupported` | 182 |
| `mcall:get_bin_path:non-object` | 154 |
| `forIn:non-iterable` | 148 |
| `call:dict:keyword-to-builtin` | 126 |
| `mcall:deprecate:non-object` | 115 |

`call:isinstance` alone accounts for 563 holing cases: an untranslated builtin, not a
control-flow gap. `*:non-object` labels are the synthetic-receiver caveat — a field holding
an `int` where real code holds an object — which is why the real-input number (87 / 139) is
reported separately and is the one to quote.

### Caveat on the denominator

The 4 synthetic inputs per function are diverse but arbitrary; a function that survives
them is *not verified*, only unrefuted on four inputs. Only 139 of 2,096 core functions
(6.6%) were reached by real arguments, because `differential.py`'s encoder rejected 7,901
traced calls whose arguments are Ansible objects it cannot encode. That skip count is the
honest denominator: refutation here is a lower bound on the true refutation rate.

## Reproducing

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build Autoform.Generated.Ansible Autoform.Ledger

sed 's/@MODULE@/Ansible/g' scripts/ledger.lean.tmpl > /tmp/L.lean
lake env lean /tmp/L.lean                       # NOT --run: the template has no `main`

# the oracle needs Ansible importable (its test suite is the input source) and a
# python that can parse PEP 695 syntax (3.12+); 3.11 and 3.9 both fail on lib/ansible
PYTHONPATH=<ansible>/lib python3.13 scripts/core_oracle.py \
    ast-Ansible.json Ansible <ansible>/lib/ansible \
    --tests <ansible>/test/units -n 4 --out core-oracle-Ansible.json \
    --scratch <a private scratch dir>

python3 scripts/sacm.py --module Ansible --root <dir with ast/ledger/core-oracle.json>
```

Two traps, both of which produce *silence* rather than an error:

* Without `PYTHONPATH=<ansible>/lib` the traced pytest run exits with rc 4 (collection
  error) and the oracle reports `inputs recorded from the test suite: 0` while still
  producing a full synthetic-only result. The first run of this measurement lost all real
  inputs that way.
* `--scratch` defaults to `/tmp`, and concurrent oracle runs then share
  `/tmp/core_oracle_scratch.lean` and overwrite each other's batches. Always pass a
  private directory.

`ledger-*.json` and `sacm-*.json` are gitignored and `core-oracle-Ansible.json` is 2.0 MB,
so the numbers above are also committed in machine-readable form, with the sha256 of each
artifact this run produced, as `evidence-Ansible.summary.json`.
