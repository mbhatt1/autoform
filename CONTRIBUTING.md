# Contributing

This project's output is an argument about trustworthiness rather than a program, and its
working rules follow from that. Most of the rules below exist because breaking them once
produced a confident, specific, wrong result. Read them before opening a change.

Orientation: [`docs/architecture.md`](docs/architecture.md) for the shape of the system,
[`docs/trust-model.md`](docs/trust-model.md) for what is claimed,
[`docs/core-language.md`](docs/core-language.md) for the Core language and the hole
taxonomy. `STRATEGY.md` is the design record and carries the reasoning.

---

## The rules

### 1. A hole beats a wrong translation.

When a construct cannot be translated faithfully, emit `Expr.hole` / `Stmt.hole` with a
label precise enough to identify the shape that defeated it (`op:starredUnpack`,
`control:TRY-finally-escaping`, `str:pointer-compare-not-modelled`). Do not guess a
plausible answer.

A hole is counted by the ledger, declared as an assumption in the assurance case, and
blocks proof at exactly the right point. A wrong translation is invisible until an oracle
happens to look. That has happened four times in this project: floored `%` mapped to
truncating division, `<operator>.and`/`.or` mapped to logical `&&`/`||` when they are
bitwise, C `char*` given Python string semantics, and Python private name mangling omitted
so a field read returned `unit`.

Corollaries:

* **Ambiguity resolves to a hole, not to a guess.** `Ctx.resolve`'s suffix matching accepts
  a *unique* match and holes on an ambiguous one.
* **A label is part of the interface.** It appears in `ledger-*.json`, becomes a SACM
  assumption node, and is how a reader decides whether a gap is work or a boundary. Make it
  specific; extend the taxonomy in `docs/core-language.md` when you add one.
* **Making a hole disappear is not automatically progress.** If it disappears because the
  construct is now translated *incorrectly*, the artefact is worse and the numbers are
  better. Several coverage figures in this project's history moved *down* when the
  translation got more honest.

### 2. Never close a goal with `sorry`. Record an open obligation instead.

`sorry` is banned outside `Demo.lean`, which contains one deliberately so the audit can be
seen catching it. `scripts/audit_all.py` sweeps for both the axiom (`sorryAx`) and the
token, and CI fails on either.

Instead, state the obligation as data. `Autoform/Tactics/Portfolio.lean` records an
`Obligation` when the ladder is exhausted; `Autoform/SpecsGen/Basis.lean` emits a
`Prop`-valued `def` plus a record. A `def` of a `Prop` asserts nothing; `sorry` produces a
theorem that looks proved from the outside.

The same applies to tactics that admit goals. The refutation gate uses `Testable.check`,
never the `plausible` tactic, because the latter closes goals with `sorry`.

A rung of the proof portfolio counts as success only if it closes the goal **and** the
resulting term passes `hasSorry`/`hasExprMVar` screening. Output from an external solver or
a model is untrusted text: it must re-elaborate and pass the same screen. An SMT `unsat` is
recorded as *evidence on an open obligation*; it can never close a goal, because no Lean
proof is reconstructed from it.

### 3. No `partial`, `unsafe`, `native_decide`, `@[implemented_by]` or `@[extern]` in the Core.

The Core semantics is total by construction: structurally recursive on fuel. CI audits for
every one of these escape hatches (`scripts/audit_all.py`, source sweep), so the claim in
the README is checked rather than asserted.

If a change needs one of them, the change is wrong. Common shapes:

* Wanting `partial` because the recursion is not obviously structural — thread the fuel
  explicitly. This is why the heap is threaded through `evalExpr`/`execStmt` by hand
  instead of living in a monad: the visible structure is the point, and the ergonomic cost
  is the price.
* Wanting `native_decide` to discharge a computation — it makes the Lean compiler part of
  the trusted base and shows up as `ofReduceBool` in the axiom sweep. `bv_decide` is fine:
  its SAT certificate is replayed *in the kernel*, so it adds no trusted code.
* Wanting `Float` — it is an opaque `@[extern]` type the kernel cannot reduce, so anything
  touching it becomes unprovable. `Autoform/Lang/Core/Float.lean` exists because of this.

Two known and accepted exceptions, both outside the Core and both recorded rather than
hidden: `Autoform/Harness/Audit.lean` uses `partial def transitiveDeps` (the audit tool's
own walker), and `Demo.lean` is deliberately unclean. Do not add a third silently.

### 4. An oracle must never report a disagreement it caused itself.

This discipline is what makes conformance numbers worth reading. It has three parts:

* **Establish you are reading the current artefact before reporting anything.** A stale
  `.olean` once answered with the previous semantics and produced ten fictitious
  divergences. The oracles now `lake build` first. That check belongs *in the oracle*, not
  in its caller.
* **Verify your own setup.** The differential harness computes receiver addresses Lean-side,
  checks that the globals frame has not been clobbered and that each receiver's class still
  matches, and returns `harness:*` INCONCLUSIVE rather than a comparison when it cannot.
  These guards are fault-injection tested: introduce the off-by-one that would alias the
  globals frame and the harness reports the alias rather than a false agreement.
* **Refuse rather than approximate.** Representability of encoded values is checked
  recursively and *fatally*. Dropping an unencodable nested field and continuing is how an
  apparatus artefact becomes a reported divergence. The stricter the refusal, the more the
  remaining agreements mean.

Stated explicitly: **never fix the measurement to match a broken artefact.** Teaching the
value encoder to expose unmangled field aliases would have made the numbers agree while
leaving the transpiler wrong.

Related: outcomes are three-valued, never two — agree / diverge / INCONCLUSIVE. A case that
was not compared must never be reported as passing. Ignorance is not verification.

### 5. A metric computed from the artefact it describes will flatter itself.

Every number needs a check that does not share the artefact's assumptions:

| Number | Independent check |
|---|---|
| semantics fidelity | the real runtime (`scripts/differential.py`) |
| specification adequacy | mutation (`scripts/mutate.py`) |
| coverage / verifiable core | execution (`scripts/core_oracle.py`) |
| proof validity | an independent kernel replay (`leanchecker --fresh`) |

If you add a metric, say what could disagree with it, and build that first. If nothing
could, the metric is an upper bound and must be labelled as one — this is why the ledger
reports hole-free, call-closed and dynamic-hole risk as three separate figures rather than
one headline. Dependency vacuity (`#audit_depends`) is necessary but not sufficient, and
the mutation gate exists because that gap is real.

### 6. Say "we never checked" and "we checked and it failed" differently.

`UNDEVELOPED` ≠ `UNSUPPORTED` ≠ `DEFEATED`. Missing evidence is emitted as an undeveloped
goal, never omitted. A claim quantified over a population may not be `SUPPORTED` on
evidence touching part of it — narrow the claim (preferred) or accept the coverage cap;
weakening the status of an over-broad claim leaves a false claim on the page. Evidence that
cannot be attributed to its subject (untagged, off-subject, repo-wide) cannot fully support
a claim about that subject.

### 7. Do not embed volatile numbers in prose.

Coverage, hole counts and claim statuses change with almost every commit. In documentation
and comments, prefer naming the command that regenerates a figure. If a snapshot is needed,
label it with the date and `git rev-parse --short HEAD`. Documentation that silently goes
stale is worse than documentation that says "run this to find out".

---

## Practical workflow

```sh
lake build                                 # must be clean
python3 scripts/audit_all.py --strict      # axioms, escape hatches, kernel replay
lake env lean Demo.lean 2>&1 | grep -E "TRUSTED-CODE LEAK|VACUOUS"   # both must appear
```

If you touched the exporter, the printer, or the semantics, also re-run the end-to-end
pipeline on at least one corpus and diff the ledger:

```sh
./assure.sh <src-dir> <ModuleName>
```

A moved number is a result. Report it — including which direction it moved and why — rather
than quietly regenerating the artefacts.

### Where things live

* `Autoform/Generated/*.lean` is transpiler output. **Never hand-edit it.** It is a pure
  function of `ast-<Module>.json`; fix `cartographer/export_ast.sc` or
  `cartographer/render_lean.py` instead. The printer must stay deterministic: no
  timestamps, no dict-iteration-order dependence, byte-identical output for identical
  input.
* Specifications about generated code belong in `Autoform/Specs/`, stated **by import** so
  that mutating the generated module mutates the subject of the theorems. Copying a deep
  term into the spec file breaks the mutation gate silently.
* Hand-written vocabulary that generated specs are written in belongs in
  `Autoform/SpecsGen/Basis.lean` — small enough to read, because generated Lean is only as
  trustworthy as the vocabulary it is generated in.
* Orchestration, HTTP, sandboxing and anything driving an external runtime stays in Python.
  Anything that touches a Lean term should be written in Lean, where `Lean.Environment` and
  proof terms are ordinary data.
* `lakefile.toml` and the dependency set are deliberately minimal. Adding a dependency is a
  design decision, not a convenience.

### Commit and review expectations

* Explain **why**, not what. This repository's history is part of its evidence: several
  findings in `STRATEGY.md` are legible only because the reasoning was recorded at the time.
* A change that moves a number must say which oracle confirmed the movement.
* A finding that cannot be fixed is still worth landing — as a labelled hole, a stated
  obligation, or a paragraph in the design record. Suppressed findings are worse than red
  builds, which is why `assure.sh` records failures in steps 2–4 and continues.
