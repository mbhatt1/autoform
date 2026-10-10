# Evidence levels

What `autoform pr` says about each function a change touched, in the order the chain
establishes it. Each level names the artifact that proves it; a reviewer who wants to
see the evidence opens that file. Nothing here quotes a figure: every number comes
from the command in the section that mentions it.

```
autoform pr <repo> --base <sha> [--head <sha>] --sarif pr.sarif --markdown pr.md
```

A function is reported at the **highest level its own artifacts reach**, never above.
When a stage did not run (no Lean on the path, the oracle refused, the proof stage was
skipped because another function diverged), the functions it would have served stay at
the level below and the reason names the stage. The report never infers a level from a
neighbour, a previous run, or the rest of the corpus.

## The levels

| level | what it claims | what it does not claim | artifact |
|---|---|---|---|
| `none` | nothing. The frontend exported no function by this name, or there was no exporter output at all (no Joern and no `--ast`). | that the function is wrong, or untranslatable in principle | `pr.json` `functions[].reason`; `export.log` when the exporter ran |
| `hole` | the translation contains at least one hole; its labels are listed. The function is in the model, but a construct in it is not modelled. | anything about the function's behaviour, including on the paths that are modelled | `ast-<M>.json` (the `hole` / `holeS` nodes in the function's body); `ledger-<M>.json` `holesByLabel` |
| `translated` | hole-free, rendered to Lean and **type-checked**. The model of this function is a total Lean definition. | that the model matches the runtime: the oracle built no comparable case (the reason is `coverage.by_status` for the function, for example `blocked (value model): float`) | `Autoform/Generated/<M>.lean` (`f_<name>`); `build.log`; `conformance.json` `coverage.by_status` |
| `oracle-agreed` | every recorded runtime case of the function agreed with the model: the same inputs, the same outcome (value or exception) in CPython (or the language's runtime) and in the Lean interpreter. | anything about inputs that were not recorded; that any theorem holds | `conformance.json` `runtime_cases` (the cases, `comparison: agree`) and `measurement_basis` |
| `proved` | a theorem stating that the model reproduces the recorded cases is proved in the Lean kernel, with no `sorry`, `native_decide` or new axiom. | that the function is correct for all inputs: the theorem is about the recorded cases (`domain` in `specs.json`), proved at the stated fuel | `Autoform/SpecsGen/<M>.lean` (the named theorem); `specs.json` `specs[]` with `proved: true` and `build_clean: true` |
| `refuted` | a witness: the model and the runtime **disagree** on a recorded input, or a candidate theorem about the function has a counterexample. | which side is right. A divergence is a defect in the translation, the semantics or the code; the witness is the fact | `conformance.json` `divergence_detail[]` (inputs, both outcomes); `specs.json` `specs[]` with `status: refuted` and its `reason` |

Two things sit beside the levels without changing them:

* **Mutation gate.** With `--mutants N`, `scripts/mutate.py` injects faults into the
  rendered definitions of the proved functions and rebuilds the theorems. `killed` means
  the theorem failed on the mutant (it has teeth); `survived` means it did not notice.
  A proved function whose theorems let a mutant survive stays `proved` -- the proof is
  real -- and the report says how many survived (`mutation.json` `theorems[].survivors`).
* **Removed functions** are listed, not levelled: there is nothing at head to verify.

## What "changed" means

`git diff --name-status BASE [HEAD]` names the files; `HEAD` is the working tree when
omitted, untracked files included. For a Python file the functions are compared with
the standard-library `ast` module at both commits: a `def` (method or nested function)
whose syntax tree differs, or exists only at head, is changed; whitespace and comments
are not a change. This is also where the line numbers in the SARIF come from, because
the exporter's AST carries none. For any other language, every function the exporter
exported from a changed file is reported (`detection: changed-file`), which rounds a
one-line edit up to the whole file -- in the set of functions examined, never in a
level.

The chain runs on the changed functions, their enclosing scopes and nested functions,
and the callees that resolve inside the exported AST (`pr.json` `selection.closure`),
so a call from a changed function has a definition to run. A changed function that
calls something outside that set reaches at most `translated`, and the oracle's
reason says why.

## Reading the outputs

`pr.json` is the record: per function, `level`, `reason`, `artifacts[]` (each with
its `path` inside the report directory or the Lean project, and the theorem or
divergence index where one applies), `holes[]`, `oracle` (agree / diverge /
inconclusive counts), `theorems[]`, `mutation`. `stages` has each stage's status,
seconds, log file and, when it did not pass, the reason. `exporter` says whether the
AST came from Joern or from `--ast FILE`, with its digest.

`pr.sarif` is SARIF 2.1.0 with one result per changed function: rule
`autoform/<level>`, level `error` for `refuted`, `warning` for `hole` and `none`,
`note` for the rest, the reason as the message, and the function's file and line as
the location. The script validates it against the shape GitHub code scanning
ingests before writing it (`validate_sarif` in `scripts/pr_mode.py`); the committed
fixture output was also checked against the OASIS SARIF 2.1.0 JSON schema.

`pr.md` is the review comment: the level counts, one row per function with its reason
and artifacts, the removed and unanalysed items by name, and the stage table.

## Seeing it on the fixture

The repository's own fixture is two commits of `numbers.py` (`scripts/pr_fixture.py`
builds them from `examples/source/python/numbers.py` and
`tests/fixtures/pr/head/numbers.py`). `.github/workflows/pr.yml` runs it on every pull
request and checks that each function lands at the level its artifacts reach:

```sh
python3 scripts/pr_fixture.py /tmp/pr-fixture
python3 scripts/pr_mode.py /tmp/pr-fixture --base base --head head \
    --module PullRequestFixture --mutants 4 --out /tmp/pr-out \
    --sarif /tmp/pr-out/pr.sarif --markdown /tmp/pr-out/pr.md
python3 -c 'import json; r = json.load(open("/tmp/pr-out/pr.json")); \
    print({f["name"]: f["level"] for f in r["functions"]}); print(r["summary"])'
```

The last command prints the levels; the workflow fails if they are not the fixture's
(`quotient`, `clamp`, `label` proved; `first` translated, because indexing an integer
is a runtime hole the oracle cannot adjudicate; `raw` a hole, `lit:bytes`). `add` and
`fraction` are unchanged between the commits and are not reported at all.

## What none of this says

The chain is the one `docs/trust-model.md` describes, cut down to a few functions.
`proved` is a kernel-checked statement about recorded inputs under the interpreter's
semantics; it is not a correctness proof of the function, and no level here is. A
clean report on a pull request means the changed functions reached the levels listed,
with the artifacts to show it -- and that the unchanged ones were not looked at.
