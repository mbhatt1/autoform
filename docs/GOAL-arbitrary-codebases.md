# Goal: arbitrary codebases

**Status: a goal statement, not a status report.** Nothing in this document is a claim
about what the tree does today; `README.md`'s hole table, `docs/scale.md` and the
ledgers are. This is the bar the project is aiming at, written so that an agent (or a
person) can be pointed at it and know when they are done — every milestone names the
artifact that proves it and the gate that fails if it regresses. It was written on
2026-09-21, after the cachetools v7.1.7 re-land (189/209 hole-free, 97 in the
verifiable core once the ledger's call analysis was made exhaustive, 219 agree / 0
diverge vs CPython), which is the point of departure.

It is written in the imperative because it is meant to be pasted into a goal-directed
session verbatim. The rules at the end are the ones `CONTRIBUTING.md`, `STRATEGY.md`
and the integrity scripts already enforce; they are repeated here so the goal cannot be
met by bending them.

---

Make autoform translate, execute and prove specifications about **arbitrary Python
repositories**, then extend the same bar to JavaScript/TypeScript and Java, without ever
hiding a gap. Work in milestones; do not start milestone N+1 until N's exit criteria are
green in the tree (`lake build`, `pytest`, `scripts/audit_all.py --strict`,
`check_docs.py`, `check_render.py`, `check_specs_fresh.py`, `check_provenance.py`) and
committed. Use agents in isolated worktrees for independent milestones; merge one at a
time; build after each merge.

## The bar

On each of the eight scale corpora in `docs/scale.md` (cachetools, sqlparse, requests,
flask, jinja, click, rich, django):

* ≥ 85 % of functions hole-free;
* ≥ 60 % in the verifiable core (hole-free AND call-closed, with standard-library calls
  closed by **contracts**, not by pretending to translate them);
* 0 divergences against CPython on ≥ 500 compared calls per corpus
  (`scripts/differential.py`, `measurement_basis` recorded);
* the generated spec module (`scripts/synth_specs.py`) proving every conformance
  observation with 0 open obligations and an empty `--exclude-subjects` list;
* all of it re-landed through `scripts/reland_corpus.sh` with provenance recorded
  (`provenance/ast-<M>.json.prov.json`).

Every figure quoted in `README.md` or `docs/` must come from a ledger, conformance or
specs artifact that `scripts/check_docs.py` pins. A number that cannot be reproduced by
a named command is not a result.

## Milestone 1 — the Python object protocol

The biggest fidelity gap. Dunder dispatch in Core: `in`, `[]`, `[]=`, `del []`,
`==`/`!=`, the `<` family, `len()`, iteration, `bool()`, `hash()`, `str()`/`repr()` on a
user instance call `__contains__`/`__getitem__`/`__setitem__`/`__delitem__`/`__eq__`/
`__lt__`/`__len__`/`__iter__`/`__bool__`/`__hash__`/`__str__` through
`Ctx.resolveMethod`, falling back to today's behaviour when the class defines none.

*Exit:* `Cache.get`/`pop`/`setdefault` leave INCONCLUSIVE and AGREE vs CPython; one
`#guard` per protocol in `Semantics.lean`; `FuelMono.lean` and `ExcSafe.lean` extended
with no `sorry`; `in:non-container` and `index:non-container` are 0 on cachetools.

## Milestone 2 — calling conventions, completed

1. **Value-callees.** `Expr.callValue e args kws`: calling a closure, function value or
   bound method held in a variable, a dict, or returned by a branch.
   `call:computed-callee` → 0 on cachetools.
2. **A receiver followed by nothing but collectors** (`def f(self, *args, **kwargs)`).
   `call:python-receiver-signature` → 0.
3. **Decorators applied at definition time** when the decorator is in-corpus
   (`functools.wraps` as a contract, Milestone 3).

*Exit:* `examples/python_control/receivers.py` translates fully except the shapes
`tests/test_python_receivers.py` names as deliberate refusals; every refusal is a
theorem or a test, not prose.

## Milestone 3 — standard-library contracts

Mine the top-100 external callees across the eight scale corpora
(`scripts/lang_matrix.py` plus a new `scripts/external_callees.py`). Give each either a
`Stdlib.lean` model — pure, total, with a `_excSafe` lemma and a CPython differential
row — or a `Contracts.lean` boundary assumption with a satisfiability witness.

*Exit:* call-closure on each corpus counts contracted calls as closed; the ledger
reports `closedByContract` separately from `closedByTranslation`
(`docs/ledger-schema.md` updated); `README.md` says which is which.

## Milestone 4 — control constructs and exception values

Generators and `yield` (suspended frames as heap objects); `with` (context managers via
`__enter__`/`__exit__`); comprehensions and generator expressions (`expr:genExp` → 0);
`async`/`await` as an explicit, counted hole. Exception payloads: `Val.exc name args`,
so `except E as e: e.args` translates; `ExcSafe` restated over the new representation,
the TRY dispatch unchanged.

## Milestone 5 — kernel-scale proofs

Replace `Ctx.resolve`'s linear suffix scan with an index built once per `Program`
(keyed by reversed dotted name) whose lookup the kernel reduces without
`String.endsWith`; prove `resolveIndex_agrees_with_resolve`. Make every `String`
operation on the interpreter's hot path structurally recursive — no well-founded
recursion, which the kernel cannot unfold.

*Exit:* the three constructors excluded from `Autoform/SpecsGen/Cachetools.lean`
(`FIFOCache.__init__`, `LRUCache.__init__`, `RRCache.__init__`) prove by computation;
Django's ledger runs under 60 s; the `--exclude-subjects` list for cachetools is empty.

## Milestone 6 — deeper specifications

Discharge `Refine.lean` obligations (3), the loop-invariant rule, and (4), the
heap-representation predicate. Restate `FuelMono`'s transport so `tryFinally` bodies
transport under a reachability side condition (retire `C_not_tfFree`).

*Exit:* one eviction loop in cachetools (`_Link.unlink` or `LRUCache.popitem`) has a
proved functional specification against a `HeapRep`; the mutation gate on the spec
module is re-measured and the `README.md` figure replaced with that command's output.

## Milestone 7 — the scale re-land

Re-land sqlparse, requests, flask, jinja, click, rich and django with
`scripts/reland_corpus.sh` (provenance, conformance, specs, ledger for each); close the
top-5 hole labels per corpus; regenerate the eight-row table in `docs/scale.md` from the
ledgers only.

*Exit:* the bar holds on every row, or the row states the exact label and count that
misses it.

## Milestone 8 — other languages, same discipline

Per-language dialects: `.javascript` exists — route `.typescript` to it and fix the
`.tsx`/`.jsx` Python-dialect bug (`docs/languages.md` §2); split `.java` and `.go` from
`.cLike` with 64-bit `long`/`int` and IEEE doubles. A differential oracle per runtime
(Node, `java`, `go run`) wired into `scripts/differential.py` with a
`measurement_basis` string. The `ledger-LangJS/LangTS/LangJava.json` top labels
(`op:alloc`, `control:THROW`, `op:cast`, `op:instanceOf`, `op:await`,
`op:postIncrement`) closed or counted.

*Exit:* the support matrix in `docs/languages.md` has no ⚠️ or ❌ cell in a row that
claims a number, and every language with "yes" under *Translates* has "yes" under
*Differential oracle*.

## Rules that do not bend

* No `sorry`, no `native_decide`, no new axioms — `scripts/audit_all.py --strict` is
  the judge.
* A hole is never replaced by a guess. When a construct cannot be modelled faithfully
  it stays a named `Stmt.hole`/`Expr.hole` and its count goes in the table.
* Never re-record a manifest or spec digest without regenerating what it pins.
* Never quote a number the docs cannot trace to an artifact.
* When a theorem becomes false in the good direction (a hole closes), replace it with
  the positive statement and say so in a `RELAND`/`CHANGED` note.
* Silence is not success: every skipped subject, excluded theorem, inconclusive
  comparison and unattributed artifact is listed by name in a report the gates read.
* Prefer a smaller true claim to a larger unverified one.
* Commit after each green milestone.
