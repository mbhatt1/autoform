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

Each stage reads and writes JSON in one run directory (default `artifacts/nl/<Module>`).
`run.json` records each stage's input hash, output hash, status, time and spend; a rerun
skips any stage whose inputs and outputs are unchanged, and a failed stage does not stop
the rest: later stages run on whatever exists, and the report is always written.

## The model stage

`src/autoform/nl/model.py` (`python -m autoform.nl.model <src> --out DIR [--tests DIR]`):

1. **Discovery** with Python's `ast`: every top-level function and method, named
   `path/mod.py:<module>.Class.meth` like the deep translation. A static screen skips
   methods (receiver state), generators, closures, decorated functions and anything that
   touches I/O, time, randomness, subprocesses, the network, files or module-level state
   (transitively through repository callees); the reason is kept in `translation.notes`.
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
  documentation says.
- **Model defects** are statements with status REFUTED_RUNTIME only. The statement holds on
  the model but fails on a real run, so the model and the code disagree. They are listed
  separately and are not bug reports.
- Refutations whose English was read off the implementation, and refutations on a model that
  did not validate, are listed last.

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

## Commands

```sh
autoform autoformalize ./src MyLib                  # model path (Python)
autoform autoformalize https://github.com/o/r.git   # a remote repository (--ref, --subdir)
autoform autoformalize ./src MyLib --deep           # the deep Joern translation instead
autoform autoformalize ./src MyLib --deep-too       # both, and attempt L1
    [--functions f g] [--no-second] [--repairs N] [--no-prove] [--no-runtime]
    [--budget-usd X] [--domain-size N] [--parallel N] [--out DIR] [--no-resume]
```

Exit status: 2 if no translation was produced, 1 if there are potential bugs, else 0.

## Costs

Every language-model call goes through headless Claude Code (`llm.py`). Calls that use no
tools are cached on disk by prompt, so rerunning one costs nothing.
The prove and L1 stages call an agent per statement. `--budget-usd` caps the total spend
of those two stages, and accepted proofs are cached and re-checked by the kernel, not
trusted. The per-stage spend is listed in `run.json` and in the report.

## Limits

- The model path reads Python only. Other languages need `--deep`.
- Bounded checks cover a finite domain of Int/Nat/Bool/String arguments. Other types are
  UNCHECKABLE.
- L0 is empirical. Only L1 connects a proof to the deep translation, and even that is only
  as faithful as the translator and the interpreter (see [`trust-model.md`](trust-model.md)).
- An L1 result covers only the argument shapes proved. A statement at any other shape
  stays at L0.
