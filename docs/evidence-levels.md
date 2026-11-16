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
exported from a changed file is a candidate (`detection: changed-file`). The behaviour
stage exports the base tree whenever there are such candidates (also when no runtime
can compare their language), and each candidate is compared with it: a function
whose exported AST is identical at base and head is dropped as unchanged -- unless that
AST contains a hole, which carries none of the source it stands for, so the function
stays `modified` (`change_detail: identical to the base export except inside its
holes`) -- one absent at
base is `added`, a base function absent at head is listed as `removed`, a signature
change of a single `file + class + method` is paired as `modified` (`change_detail:
signature changed`), and lambdas are matched by body, not by their index
(`pr.json` `change_identity`). Without a base export (`--no-behaviour`, or a failed
export) every exported function of the file is reported,
which rounds a one-line edit up to the whole file -- in the set of functions examined,
never in a level -- and `change_identity.reason` says why. Either way these functions
carry no line number: the exporter records no position for an exported function.

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

## A real run

[`examples/pr-cachetools-7.1.5/`](examples/pr-cachetools-7.1.5/README.md) is the output of `pr` on a real
cachetools change (v7.1.4 to v7.1.5), with a plain reading of each level and of what the
report does and does not say about the fix.

## What none of this says

The chain is the one `docs/trust-model.md` describes, cut down to a few functions.
`proved` is a kernel-checked statement about recorded inputs under the interpreter's
semantics; it is not a correctness proof of the function, and no level here is. A
clean report on a pull request means the changed functions reached the levels listed,
with the artifacts to show it -- and that the unchanged ones were not looked at.

## Behaviour: did the change alter what the function does

The levels above compare one revision's model with that revision's runtime, so they cannot
see that a change altered behaviour. `pr` therefore adds a second, separate result per
changed function, `behaviour`, which is never a level and, unless `--fail-on` is given, never
a failure (a pull request may change behaviour on purpose; the exit code is unchanged).
`--fail-on behaviour-changed` exits `1` when a changed function's behaviour `changed`, and
either `--fail-on` value exits `3` when no changed non-test function was compared at all
(the gate, below):

* the model is the AST of the **base** revision (a second Joern export of the base checkout,
  with the head's `tests/` overlaid so the inputs a test builds exist in the model, and
  `cartographer/plain_class_values.py` applied as in
  `docs/evidence-cachetools-negative-size.md`), rendered as its own module `<Module>Base`;
* the runtime is the **head** source, with inputs from the head's tests and the oracle's
  random cases (`--behaviour-cases`, default 100).

For Java (and Kotlin, where a Kotlin compiler is present) the same design runs on the JVM
oracle (`java_backend` in `scripts/differential.py`): the base model against the head
source, compiled with `javac` against the head tree's own source roots, on the oracle's
seeded random inputs, which are identical at both revisions. There is no test overlay and
`plain_class_values.py` is not applied (both are Python-specific). Only static methods with
a primitive/String signature are called; an instance method or a non-primitive signature
is `not-compared` with the oracle's own reason (e.g. `instance method: needs a receiver`).
Kotlin never compiles test source sets; it compiles the candidate files with the other
main sources, then the candidate files alone, then each one alone, recording every attempt
and its first errors in `kotlin_compile_attempts`. A Kotlin lambda is `not-compared`
(`lambda: not callable by name`), not a static candidate.
For C (`.c` files, where `cc` is present) the design runs on the native C oracle
(`native_c` via `c_runtime` in `scripts/differential.py`): the base model against the head
tree's translation units, compiled with `cc` and called in the sandboxed worker, on the
oracle's seeded typed-boundary inputs (all-zero first, then each fixed-width type's
extremes and powers of two, then seeded small integers), identical at both revisions. No
test overlay. Only functions with a scalar fixed-width integer signature defined in a
`.c` unit are called; a pointer or aggregate signature is `not-compared` with the
oracle's reason. A case the model leaves as a hole -- undefined behaviour such as signed
overflow -- is inconclusive, never a divergence. A `.h` function is not C here (the
extension is shared with C++); outside a C++ corpus it is `not-compared` with the reason.
Go (`go_backend`: package-level functions with scalar parameters, on fixed per-type pools)
and JavaScript/TypeScript (`node_backend`: module-scope functions and static methods, on a
fixed numeric pool and the body's own string literals) run the same way: base model
against the head source, on inputs built from the base export alone. A method that needs
a receiver, or a function returning an object, is `not-compared` with the backend's reason.
A revision is a `git archive`, which carries no installed packages, so the working tree's
`node_modules` directories are linked into it at the same paths (`pr.json` `dependencies`
names each; `AUTOFORM_NODE_MODULES` names one more to link). With none installed, an
import of a package that tsc would not emit (every binding it introduces is used only as a
type: its name no longer occurs in Node's type-stripped text) is dropped from the oracle's
copy, as the compiled program drops it, unless the `tsconfig.json` keeps such imports
(`verbatimModuleSyntax`, `preserveValueImports`, `importsNotUsedAsValues`,
`emitDecoratorMetadata`, or an `extends` that cannot be read); an extensionless relative
import is spelled with the file it resolves to. A module that still imports a missing
package is `not-compared` with `module load failed: package(s) not installed: <names>`
and the fix (`npm ci`).
For C++ (the `cpp` row: `.cc`, `.cpp`, `.cxx`, `.hh`, `.hpp`, `.hxx`, and `.h` in a C++
corpus), where `c++` is present, the base model runs against the head source through the
native oracle (`scripts/native_c.py`) on the same seeded random and width-boundary inputs:
each free or static member function with a fixed-width integer signature is called
through a C ABI thunk compiled in its own translation unit (a header, in a C++ corpus, is
one), named by its qualified name and, when its declared types are builtins, cast to its
exact function type so one overload is selected. A non-static member function, a private
member and an ambiguous overload are `not-compared` with the reason, without taking the
rest of the file down. A `.h` is C++ only in a C++ corpus (no `.c` file, and a C++ source
or header, or a `.h` with a C++-only declaration); in a C project nothing changes.
A language is compared when the oracle has a cross-revision backend for it
(`CROSS_REVISION_INPUTS` in `scripts/runtime_backends.py`, which also says what the inputs
are) and its toolchain is on PATH; any other language is `not-compared` with the reason.
A function's language is taken from its file extension; one run compares one language (the
one with the most changed functions), and the others are `not-compared` with that reason.
`behaviour.languages` in `pr.json` lists the languages of the functions actually compared.

| `behaviour` | meaning | not meant |
|---|---|---|
| `changed` | on at least one input the base model and the head runtime disagree; up to 3 counter-inputs are listed (call, receiver, what the base model returns, what the head runtime returns) | that the change is wrong |
| `unchanged-on-inputs` | N compared cases all agreed; N is stated | equivalence on other inputs |
| `not-compared` | no case was compared; the reason is stated (added at head, test code, all cases inconclusive, no Joern, a language with no cross-revision backend or toolchain here, a method or C function the backend cannot call, a stage failed) | that the behaviour is unchanged |

A function whose cases were all inconclusive is `not-compared`, never `unchanged-on-inputs`.
A divergence that also appears in a same-base control run (the base model against the
base runtime on the same inputs) is a model infidelity, not a revision difference; it is
removed from `changed` and counted, in the report and the comment, as
`suppressed-as-model-noise: n`. The control is only run when the cross-revision run has
divergences. `pr.json` has `functions[].behaviour` and a top-level `behaviour` block
(model, runtime, control, suppression count, stages); SARIF has rule
`autoform/behaviour-changed` (level `warning`, message with the input and both results);
the comment leads with a "PR verdict" section (one row per changed function: `changed`,
`unchanged-on-inputs`, `not-compared`), and the evidence level follows under "Head model
conformance": it is about the head revision's own model, so a function whose behaviour
changed can still be `proved` there. SARIF messages also lead with the PR verdict.

Inputs reach the change, or the verdict says they did not. The behaviour runs pass
`--literal-inputs` to the oracle: a string-typed or unannotated parameter also draws
strings built from the literals of the function, its file and the head revision of the
function (each literal, `a<sep>b`, a prefix, a suffix, pairs joined), Java/Kotlin `String`
parameters and Node string pools take the same strings, and integer and C parameters the
neighbours of the integer literals; every draw is seeded from the export, so the run and
its same-base control get identical inputs. For Python the cross-revision run also records
which changed lines and which outcomes of a changed `if`/`while` condition the COMPARED
cases executed (`change_coverage` in `conformance.json`). An `unchanged-on-inputs` whose
inputs never ran a changed statement or only ever took one side of a changed condition says
so in its reason ("branch coverage: the inputs did not reach the change") and does not
count as evidence for `--fail-on`: when every compared function is such, the gate is
inconclusive (exit 3). Outcome coverage, not condition coverage: an `a or b` changed to
`a and b` is checked through the outcomes of its `if`, not each operand. Other languages
report `change_coverage` as not measured. `gate.exit_code` is always the exit code. A
function identical to the base export except inside its holes is listed but is a gate
subject only when no other function is. Covered: Python functions, static
primitive/String Java and Kotlin methods, scalar Go package functions, JavaScript/
TypeScript module-scope functions and static methods, and scalar fixed-width C functions
of `.c` files, that exist at base and were modified. Not covered: other languages,
methods that need a receiver the backend cannot build and C functions with pointer or
aggregate signatures (`not-compared`), functions
added at head, callers of a changed function unless the oracle happened to exercise them
through it, and anything the model cannot represent (inconclusive cases).
`--no-behaviour` skips it. The worked example is `docs/examples/pr-cachetools-7.1.5/`.
