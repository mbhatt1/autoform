# autoformalize: code → English → Lean statements → checks → proofs

`autoform autoformalize` (also `python -m autoform.nl`) reads a repository, writes English
specifications of its functions, turns each English property into a Lean statement, checks
it on concrete inputs against both a Lean model and the real code, tries to prove the
statements that survive, and reports what it found. Code lives in `src/autoform/nl/`;
the stage contracts are in `src/autoform/nl/schema.py`.

## Pipeline

```
                ┌─ model (default) ── AI-written Lean def per function, validated ─┐
 source ────────┤                     against real runs + a second translation     ├─► translation.json
                └─ translate (--deep) ─ Joern → Core, run by `runFunc`  ───────────┘
                                                                                        │
   describe ─► english.json      English properties from docs, tests, implementation (untrusted)
   formalize ─► statements.json  Lean statements over the translation's `call_template` (must elaborate)
   check ─────► checks.json      bounded `decide +kernel` over a finite domain + real CPython runs
   prove ─────► proofs.json      prover agent; every proof re-checked by the kernel
   refine ────► refine.json      (--deep-too) L1: model proved equal to the deep translation
   report ────► report.json, report.md
```

With a judge (`--judge`, on by default from the CLI) two stages join the pipeline:

```
   describe ─► select ─────► selection.json     rank + budget the English properties (judge)
   formalize … check ─► adjudicate ─► adjudication.json   classify counterexamples, repair (judge)
   … prove (original + repaired statements, highest utility first) ─► report
```

Each stage reads and writes JSON in one run directory (default `artifacts/nl/<Module>`).
`run.json` records each stage's input hash, output hash, status, time and spend; a rerun
skips any stage whose inputs and outputs are unchanged, and a failed stage does not stop
the rest: later stages run on whatever exists, and the report is always written.

## The model stage

`src/autoform/nl/model.py` (`python -m autoform.nl.model <src> --out DIR [--tests DIR]`):

1. **Discovery** with Python's `ast`: every top-level function, method, property getter
   and constructor, named `path/mod.py:<module>.Class.meth` like the deep translation. A
   static screen skips generators, closures, classmethods, property setters, decorated
   functions and anything that touches I/O, time, randomness, subprocesses, the network,
   files or module-level state, transitively through repository callees, through the
   constructor that builds a method's receiver (a `timer=time.monotonic` default excludes
   every method of that class), and through repository classes a function instantiates
   whose methods have such effects. Classes with a builtin base (`dict`, `list`, ...) and
   exception classes are skipped. Every reason is kept in `translation.notes` and counted in
   `model.meta.json` (`skip_reasons`).
2. **Translation A.** The model states in English what the function computes, then writes
   a plain Lean `def`: `Int` for Python int, `Bool`, `String`, `Option`, `List`, tuples,
   `Val` for genuinely mixed values, `Fl` (IEEE bits) only for floats; raising is
   `Except String τ` with the exact exception class name; `//` and `%` are `Int.fdiv` and
   `Int.fmod`. Callees are translated first and offered to the caller.
3. **Dispatcher.** Generated, not written by the model: `call : String → List Val → EResult`
   decodes arguments (a wrong shape is `.hole "nl:arg-type"`), runs the def and encodes the
   result (`.error e` becomes `.exn (.str e)`). Everything is structurally recursive, so the
   kernel evaluates `call` (`decide +kernel`); a few points per function are checked so.
4. **Differential validation.** Inputs are the argument tuples observed while the repo's
   own tests run under a tracer, plus typed boundary values. The real function runs in
   CPython (subprocess, per-call timeout), the model in one batched `#eval`, and outcomes are
   compared exactly. Counterexamples go back to the model for up to `--repairs` rounds.
5. **Translation B.** An independent translation from the code alone runs on the same
   inputs; `second_translation` records whether it agrees with A.

Tests may live outside the source tree: `--tests DIR` (repeatable, also on `autoform
autoformalize`) adds test directories; they are traced for inputs and their lines are
shown to the model and to describe. `AUTOFORM_PYTHON` selects the interpreter that runs the
code under test (tracer, differential runner, check-stage runtime), e.g. a newer Python
than the one running autoform.

### Methods and objects

- **Structures.** Each repository class with an attempted method gets a generated Lean
  `structure S_<Class>` with one field `f_<attr>` per instance attribute (all attributes
  along the repository MRO; private names mangled as CPython does, e.g. `_Cache__data`).
  The attribute set and the field types come from the receiver states the tracer records
  (before every traced method call and after every traced `__init__`): the most common
  attribute set wins, and each type is the join of the observed values' types
  (`Int`, `Dict Val Val`, `Option Int`, ...; mixed → `Val`). The structures are validated in
  Lean: they must elaborate (else fields fall back to `Val`), and observed states must
  round-trip through the generated `dObj_S`/`eObj_S` (`structures.*.roundtrip_ok` in
  `model.meta.json`). Without observations, the attributes assigned in the class's code
  are used, typed `Val`.
- **Methods** are plain Lean functions whose first parameter is `self : S_<Class>`. A method
  that can change its receiver declares `"mutates": true` and returns
  `τ × S_<Class>` (or `Except String (τ × S_<Class>)`): the Python result and the receiver
  after the call (state threading); others return just `τ`. A constructor (`__init__`)
  takes the arguments after `self` and returns `S_<Class>`. Exceptions are `Except String`.
- **Inheritance.** Fields and method lookup follow the repository MRO. Bases outside the
  repository (e.g. `collections.abc.MutableMapping`) contribute nothing: a receiver call
  to a method only such a base defines (`self.popitem()` in `Cache.__setitem__`) is
  *unmodelled*: the model returns `.error "nl:unmodelled"` on that path, the dispatcher turns
  it into `.hole "nl:unmodelled"`, and those inputs are excluded from the comparison
  (counted in the notes). Methods the class itself overrides (`get`, `pop`, ...) are modelled.
- **Dispatcher.** `call "<method>" (self :: args)` returns the Python result; the second
  entry `call "<method>#post" (self :: args)` returns `.tuple [result, receiver after the
  call]`. A constructor's entry returns the new object.
- **Statements about methods** range over real receivers. The formalize stage adds
  `(Autoform.NLModel.<M>.dObj_S_<Class> self).isSome` to the precondition. Without it,
  `self` would range over every `Val`: for `.unit` the dispatcher returns a hole and the
  statement is false for a reason that says nothing about the code. Class invariants that
  the decoder does not enforce (e.g. a size field that matches the stored data) still
  have to be stated in `pre`.
- **Differential testing.** A method's inputs start with a receiver state; CPython rebuilds
  the receiver without running `__init__` (`__new__`, then each recorded attribute is set;
  container attributes get their recorded exact type back, e.g. `OrderedDict`), runs the
  method, and reports the result AND the receiver afterwards. Both are compared with the
  model's `#post` entry. Traced receivers whose attributes do not fit the structure, and
  outcomes whose object has attributes outside it, are skipped and counted. Boundary
  inputs pair recorded receivers with typed argument values. A trailing argument that is
  the parameter's own unencodable default (a sentinel `object()`, a function alias such as
  `cache_setitem=Cache.__setitem__`) is dropped from traced calls, so the call replays with
  its default.

### Data encoding (`pyvalues.py`, the prelude of every model module)

| Python | Lean model type | `Val` |
|---|---|---|
| int / bool / str / None | `Int` / `Bool` / `String` / `Unit`, `Option τ` | `.int` / `.bool` / `.str` / `.unit` |
| float | `Fl` (IEEE bits) | `.float` |
| fixed tuple | `τ × σ` (≤ 4) | `.tuple [..]` |
| variable tuple | `Tuple τ` (= `List τ`) | `.tuple [..]` |
| list | `List τ` | `.list [..]` |
| dict | `Dict κ ν` (= `List (κ × ν)`, insertion order) | `.dict [(k, v), ..]` in insertion order |
| set / frozenset | `PySet τ` / `FrozenSet τ` (= `List τ`) | `.bobj "set" (.list elems)` |
| bytes | `Bytes` (= `List Nat`) | `.bobj "bytes" (.list [.int b, ..])` |
| object of a modelled class | `S_<Class>` | `.bobj "obj:<module>.<Class>" (.dict [(.str attr, v), ..])` |

Sets are encoded with their elements sorted by canonical string and deduplicated, on both
sides (the Lean encoder normalizes whatever list the model keeps), so equal sets have equal
encodings; mixed-type elements that are equal in Python (`1`, `True`, `1.0`) are refused by
the tracer. Object attributes are sorted by name. The check stage encodes real CPython
outcomes the same way, so its runtime comparison covers every type in the table.
Statements can use the helpers `vField o "attr"`, `vGet d k`, `vHas d k`, `vLen v`, `vKeys d`
and `vElems v` (opened by `schema.lean_opens`), and `Val` binders, whose check-stage domain
is the function's validated sample inputs (`FunctionInfo.samples`); a statement with
`"entry": "post"` is about the receiver after the call.

The module is `Autoform/NLModel/<M>.lean` (a build product, not tracked), built with
`lake build Autoform.NLModel.<M>`. Later stages import the module that the translation's
`call_template` names (`schema.lean_imports`).

## Trust levels

Every function gets a level, and every statement inherits one:

| level | meaning |
|---|---|
| **L1** | The model is proved, by the kernel, equal to the deep translation for the statement's argument shape (`theorem l1_<f> : ∀ a b, Model.call "f" [.int a, .int b] = <deep call> …`). Proofs about the model therefore hold for the deep translation. Fidelity rests on the deep translator and the Core interpreter, both differentially tested separately. |
| **L0** | The proof is about an AI-written model. That model agreed with the real code on every one of N tested inputs and with an independent second translation. This is evidence of fidelity, not proof. |
| deep | The statement is about the deep translation itself (`--deep`). |
| none | No validated model. Results say nothing reliable about the code. |

Only the kernel sets PROVED, BOUNDED_HOLDS or REFUTED_MODEL. The English and the Lean
statements are untrusted: a statement may not mean what its English says.

## Findings

- **Potential bugs** come first. These are statements refuted on a validated model (or on the
  deep translation) whose English came from docs or tests. The code contradicts what its
  documentation says. With a judge, the rule is stricter: the judge must also read the
  counterexample as REAL_BUG with a confident intent (cross-validation, below); REAL_BUG
  without that support is listed as a *suspected bug*.
- **Model defects** are statements with status REFUTED_RUNTIME only. The statement holds on
  the model but fails on a real run, so the model and the code disagree. They are listed
  separately and are not bug reports.
- Refutations whose English was read off the implementation, and refutations on a model that
  did not validate, are listed last.

## Selection, budget, adjudication and repair (`judge.py`, `repair.py`)

The judge is the harness's typed-decision judge (`autoform.harness.judge`, see
[`harness.md`](harness.md)): a state, a question and typed options go in, one score per
option comes out. `--judge semif` uses SemIf/OpenJev (Qwen3.5-4B on MLX from
`~/semif/.venv`; weights load once per run), `heuristic` uses the deterministic priors each
decision computes anyway (offline, reproducible), `replay:PATH` re-reads the scores of a
previous `decisions.jsonl`, `auto` (the default) takes SemIf when it is installed, and
`none` turns both stages off.

**Trust: the judge never sets a status.** It chooses what to formalize first, how to read a
counterexample and which repair to try. PROVED, BOUNDED_HOLDS and REFUTED_* still come only
from Lean (elaboration, `decide +kernel`, kernel-checked proofs) and real executions. A
repaired property is a new, separately checked statement; the refuted original stays
refuted.

### Selection (`select`)

Per function the judge sees the *interface* only (name, signature, docstring, tests,
callers), never the body: shown `return True`, a judge rates "always returns True" as the
intended contract. It makes three kinds of decision:

| decision | over | options |
|---|---|---|
| `PROPERTY_JUDGMENT` | each English property | USEFUL_PROPERTY, SECURITY_RELEVANT, TRIVIAL, UNSUPPORTED_BY_EVIDENCE, TOO_STRONG, TOO_WEAK, LIKELY_VACUOUS |
| `PROPERTY_SELECTION` | the function's properties, listwise | which is most worth proving |
| `INTENT_SELECTION` | each group of mutually incompatible properties | which reading is intended |

Two properties are incompatible when they state different outcomes for the same call on
the same condition or domain ("If b is 0, f(a, b) raises …" / "… returns 0"; "For all
integers a and b, add(a, b) returns a + b" / "… a − b"). "Returns an integer" is compatible
with any specific value. The utility is

    U = .30·Useful + .25·Security + .20·Selection + .20·Evidence + .10·Nontrivial
        − .10·Unsupported − .05·TooStrong − .10·(implementation-only evidence)
        + .10 if the chosen intent of its rival group, − .15 if a losing reading

where Evidence weighs tests .5, docstring .4, callers .3, comments .2, name .15 (capped at
1), and Security is at least .5 when the property, name or docstring mentions an
authorization, validation or integrity term.

### Budget (`--budget-usd`, `--max-properties-per-function`)

The budget covers the whole run, including the earlier cost of stages resumed from a
previous run. When proving is on, selection holds back a proving reserve,
`AUTOFORM_PROVE_SHARE` (default 0.4) of what is left after `describe`. Formalize and
repairs may not spend it, so the prove stage always gets money. Each property is estimated at
its formalize cost (`AUTOFORM_EST_FORMALIZE_USD`, default $0.08, measured on cachetools).
Proofs are paid for from the reserve and anything formalize left unspent. Each agent call
reserves its own cap before it starts: the smaller of `AUTOFORM_PROVE_CALL_CAP_USD`
(default $1.50) and what is left. That cap is passed to `claude --max-budget-usd`, so no call
can spend more than it reserved. A call starts only if at least `AUTOFORM_EST_PROVE_USD`
(default $0.60) is left.
Priority is utility × 0.85^rank, where rank is the property's place inside
its function, so the best property of each function comes before the third-best of
another. Properties are admitted in priority order until the next estimate would exceed
the budget less the reserve; that one and every later one are skipped
("budget: estimated $X would exceed $B"). A property past the per-function cap is skipped
with that reason. Then the money is actually spent in the same order:

- `formalize` runs the admitted properties in waves of three and stops once its measured
  spend reaches the remaining budget less the reserve; the rest are recorded in `budget.json`;
- `adjudicate` formalizes a repair only if one more formalization fits;
- `prove` receives the statements (original and repaired) in utility order, and the prover
  stops starting agent calls when the budget is gone. Those statements are SKIPPED with
  `budget exhausted` in the reason, and counted as "not attempted (budget)", not as failed
  proofs. Proving cannot overshoot, because every call is capped by its reservation.
  Formalize checks its spend between waves of three calls, so it can overshoot by at
  most one wave (about $0.25).

The report's **Spent vs budget** section lists the budget, the spend per stage, the
planned spend and every skip with its stage and reason; each function lists its skipped
properties.

### Counterexample adjudication (`adjudicate`)

For each REFUTED_MODEL / REFUTED_RUNTIME statement, deterministic gates run first:

| fact | allowed classes |
|---|---|
| REFUTED_RUNTIME only (holds on the model, fails on the code) | INCOMPLETE_MODEL (forced) |
| the model's outcome at the witness is a hole or out of fuel | INCOMPLETE_MODEL (forced) |
| the real code satisfies the statement on every checked input | INCOMPLETE_MODEL (forced) |
| otherwise | REAL_BUG, BAD_SPEC |
| … and the witness lies outside the inputs the docstring or tests use (or none is known) | + MISSING_PRECONDITION |
| … and the real code was not run | + ABSTRACTION_ARTIFACT |
| the property lost its INTENT_SELECTION | − REAL_BUG |

The tested domain is read from the literal arguments of calls in the tests and doctest
examples (per parameter: its types, the numeric range, and for strings the values
themselves); the documented domain from phrases like
"b must be nonzero". The judge (`COUNTEREXAMPLE_CLASSIFICATION`) then chooses among the
allowed classes, shown the function source, the English, the Lean pre/postcondition, the
counterexample, the model's and the real code's outcomes.

- **REAL_BUG** becomes a *finding* only if cross-validated: the property has evidence other
  than "implementation", and its intent is confident (it is the chosen reading of its rival
  group with probability ≥ 0.8, or it has no rival and was not judged
  UNSUPPORTED_BY_EVIDENCE or TOO_STRONG). Otherwise it is a *suspected bug* for review. A
  REAL_BUG is never repaired.
- **INCOMPLETE_MODEL** gets a `MODEL_DEFECT_CLASSIFICATION` (hole ⇒ UNMODELED_CONSTRUCT or
  FRONTEND_MISTRANSLATION; out of fuel ⇒ FUEL_BOUND; otherwise SEMANTICS_MISMATCH or
  FRONTEND_MISTRANSLATION) and a report entry naming the model (the AI-written def, or the
  deep translation). Repairing models is the model stage's job.
- **BAD_SPEC / MISSING_PRECONDITION** are repaired.

### Repair

Candidates are restatements of the English, generated deterministically:

- a precondition from the code's own guards (`if C: raise` ⇒ `not C`; `assert C` ⇒ `C`;
  `if C: return …` ⇒ `C` or `not C`), from the docstring ("b must be nonzero" ⇒ `b != 0`),
  or from the tested domain (`x >= 0`, `x > 0`, `lo <= x <= hi` from the tested values);
- a weakening: one direction of "exactly when" / "if and only if", or allowing the exception
  the model raised at the witness;
- REJECT (the property does not describe intended behavior).

A precondition that mentions a witness value found nowhere in the code, docstring, tests
or English is never offered, and neither is one the witness satisfies (it would not
exclude the counterexample). With several preconditions, `PRECONDITION_SELECTION` picks
one; `REPAIR_SELECTION` then weighs it against the weakenings and REJECT. The chosen
restatement (`p2` → `p2_r1`) goes through formalize → check again, and later prove. A repair
refuted again is adjudicated again, for at most `--repair-rounds` rounds (default 2); a
refutation after the last round is classified but not repaired (`repair_limit`). Every
repaired property and statement keeps a `parent` link, and the report shows the lineage.
Each classification and repair choice carries its margin (top-1 minus top-2 probability);
a repair chosen with a margin below 0.02 is marked "a tie: review" (SemIf's bf16 logits do
tie, and the tie then falls to the first option).

### Decision log and JEVBench

Every judge decision (task, state, options, scores, choice, backend; forced ones included)
goes to `decisions-select.jsonl` / `decisions-adjudicate.jsonl`. At the end of the run they
are joined with the verifier outcomes into `decisions.jsonl`, and `jevbench.jsonl` labels
each unforced decision where verification settles it: the harness rules
(`harness/bench.py`: an established statement ⇒ USEFUL/SECURITY acceptable; the class
whose repair was then established ⇒ right, refuted again ⇒ wrong; …), plus:

| task | rule added for this flow |
|---|---|
| `PROPERTY_JUDGMENT` | skipped for budget/cap or never formalized ⇒ unlabeled; UNCHECKABLE ⇒ unlabeled (a precondition no domain point meets may be vacuous, or the finite domain may miss the one input it is about); refutation attributed to the model ⇒ unlabeled |
| `COUNTEREXAMPLE_CLASSIFICATION`, `REPAIR_SELECTION`, `PRECONDITION_SELECTION` | repaired statement REFUTED_RUNTIME (a model defect) ⇒ unlabeled; repair did not elaborate ⇒ unlabeled; repair skipped for budget ⇒ unlabeled |

`python -m autoform.harness.bench fit-temperature <run>/jevbench.jsonl --out t.json` fits
per-task temperatures from these rows, as for the harness.

## The L1 step (`refine.py`, `--deep-too`)

L1 is attempted for each function that has both a VALIDATED model and a hole-free,
call-closed deep translation. A statement is made for each argument shape: the model's
signature, plus every binder shape a statement about the function uses. The right-hand
side is the deep translation's `call_template`, which is the initialized-heap entry
`Autoform.NL.<M>.call` when the function reads module state.

Before any agent call, a bounded `decide +kernel` check runs over the check stage's domain,
and a model that disagrees with the deep translation there is skipped. A statement that
passes goes to the same prover as the prove stage. If every shape is proved, the function
reaches level L1. Otherwise it stays at L0, and the reason is recorded.

## Prerequisites

- Lean 4 via elan (`lake` on PATH or in `~/.elan/bin`), and this checkout built with
  `lake build` (the model modules import `Autoform.NL.Basis`).
- The `claude` CLI. All model calls go through `claude -p`. `AUTOFORM_CLAUDE_AUTH=login`
  (the default) uses the logged-in account and ignores `ANTHROPIC_API_KEY`.
  `AUTOFORM_CLAUDE_AUTH=api-key` bills the key instead, for machines with no login such as CI.
- The Python the analysed code needs (`AUTOFORM_PYTHON`, default `python3`), with the
  code's own dependencies importable. The model stage runs the real functions.

**The analysed code is executed.** The model, fuzz and check stages import the repository and
call its functions and its tests in CPython with your user's permissions. The prover agents
work inside the Lean checkout. Run untrusted repositories in a disposable environment
with no credentials, as described in [SECURITY.md](../SECURITY.md). `--no-runtime` skips
real executions in the check stage, but the model stage still runs the code to validate models.
- Optional: SemIf (`--judge semif`, see `judge.py`). `--judge auto` falls back to the
  heuristic judge when SemIf is not installed.

Before any stage runs, the CLI checks the Lean project, `lake`, the `claude` CLI and the
numeric options, and exits with status 2 on a problem. `--skip-preflight` turns this off.

## Commands

```sh
autoform autoformalize ./src MyLib                  # model path (Python)
autoform autoformalize https://github.com/o/r.git   # a remote repository (--ref, --subdir)
autoform autoformalize ./src MyLib --deep           # the deep Joern translation instead
autoform autoformalize ./src MyLib --deep-too       # both, and attempt L1
    [--functions f g] [--no-second] [--repairs N] [--no-prove] [--no-runtime]
    [--budget-usd X] [--domain-size N] [--parallel N] [--out DIR] [--no-resume]
    [--judge auto|semif|heuristic|replay:PATH|none] [--max-properties-per-function N]
    [--repair-rounds N] [--tests DIR ...] [--skip-preflight]
```

Exit status: 2 if the preflight failed or no translation was produced, 1 if there are
potential bugs, else 0.

## Costs

Every language-model call goes through headless Claude Code (`llm.py`). Calls that use no
tools are cached on disk by prompt, so rerunning one costs nothing.
The prove and L1 stages call an agent per statement. `--budget-usd` caps the total spend
of those two stages (with a judge, also of formalize and repairs, allocated by utility).
Accepted proofs are cached and re-checked by the kernel, not trusted. The per-stage spend is listed in `run.json` and in the report.

## Limits

- The model path reads Python only. Other languages need `--deep`.
- Bounded checks cover a finite domain of Int/Nat/Bool/String arguments, and `Val` binders
  over the recorded sample inputs only (24 per function, spread across distinct receivers).
  A method's receivers come from the tests' calls on exactly its class plus generated
  states. If the tests only exercise subclasses, those are mostly empty objects, and a
  precondition such as "the key is in the cache" is then met by no point. Such statements
  are reported UNCHECKABLE (vacuous), never as holding. On cachetools, about 20% of the
  statements end up here.
- Methods are modelled for receivers of exactly their class; an inherited method is not
  re-modelled per subclass (a subclass method that calls it gets its source as context).
  Instances that hold other objects (linked nodes, locks, callables) have no encoding and
  their methods are UNTESTABLE or skipped. After an exception, the receiver's state is
  not compared.
- L0 is empirical. Only L1 connects a proof to the deep translation, and even that is only
  as faithful as the translator and the interpreter (see [`trust-model.md`](trust-model.md)).
- An L1 result covers only the argument shapes proved. A statement at any other shape
  stays at L0.
