#!/usr/bin/env python3
"""Layer 4 — automatic specification synthesis (STRATEGY.md §4).

Every specification about translated code in this repository is hand-written today, which
does not scale past a demo. This script generates them, working *down* §4's list of
sources by descending trustworthiness rather than jumping to invention:

  1. **Existing artifacts** — docstrings carried through the AST, `assert`/`raise` guards,
     doctests, and above all the repository's own test suite, whose executions are
     recorded by `scripts/differential.py`'s trace hook. §15 measured that a repo's own
     property-based tests are the highest-yield source; here the suite plays that role,
     and the outcome CPython produced for each recorded call is a fact this system did
     not manufacture.
  2. **Structural / safety specs, free for all code** — for a function in the call-closed
     core, "on this domain the interpreter returns a value, never `.hole` and never
     `.outOfFuel`" is a real, provable, non-trivial property: `Refine.lean`'s `Outcome`
     has no constructor for either.
  3. **Algebraic laws mined from behaviour** — constancy, projection, identity,
     idempotence, involutivity, commutativity, range bounds, heap purity. Mined from
     observed executions, then *pruned by a refutation pass* over a fuzzed domain before
     anything is emitted.
  4. **Cross-implementation equivalence** — the conformance family: the Lean interpreter
     reproduces what CPython did, stated as a kernel-checked theorem rather than a test
     report.

## The non-negotiable part

§15 measured that **41% of FVSpec's 9,415 LLM-transpiled specs are vacuous** under static
screening, dominated by determinism properties (`f(x) == f(x)`) that become `rfl` in a
pure setting. This generator is built so that it can be measured the same way and report
the number honestly:

* every candidate is **refuted before it is emitted** — mined laws are evaluated over a
  fuzzed domain in the Lean semantics, and a single counterexample drops the candidate;
* every survivor passes a **vacuity screen** with the same check names §15 used
  (`reflexive_conclusion`, `trivial_conclusion`, `empty_quantification`,
  `dependency_vacuity`, `opaque_subject`), and the flagged fraction is reported as *this
  generator's own vacuity rate*;
* a `Deterministic` family is mined deliberately and then rejected in full, so the number
  §15 found dominant is measured here rather than assumed absent;
* nothing is admitted. Statements that cannot be proved are emitted as `Prop`-valued
  `def`s plus `OpenObligation` records. There is no `sorry` anywhere — `scripts/audit_all.py`
  audits for it.

Both anti-vacuity gates run on the output: the emitted module ends with `#audit_depends`
for every theorem (so a statement that never mentions the generated implementation fails
the *build*), and the module is a valid target for
`scripts/mutate.py Autoform/Generated/<M>.lean Autoform.Generated.<M>
 --spec-file Autoform/SpecsGen/<M>.lean --spec-module Autoform.SpecsGen.<M>`.

Usage:
    synth_specs.py <ast.json> <source-dir> <Module> [--tests DIR] [--cases N]
                   [--no-mine] [--json PATH]
"""
from __future__ import annotations

import argparse
import json
import os
import random
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(REPO, "cartographer"))

import differential as D                                  # noqa: E402  (trace + encoder)
import mutate as M                                        # noqa: E402  (decl parser)
from render_lean import ident as lean_ident               # noqa: E402  (name mangling)

random.seed(20260819)

FUEL = 400             # fuel budget the emitted theorems are stated at
INIT_FUEL = 5000       # fuel for `initGlobals`, matching scripts/differential.py
MAX_DOMAIN = 8         # cases per mined law: the kernel has to evaluate every one
MIN_LAW_DOMAIN = 3     # below this a "law" is an anecdote, not a law
OUTDIR = os.path.join(REPO, "Autoform", "SpecsGen")
SCRATCH = os.environ.get("AUTOFORM_SCRATCH", "/tmp")
GLOBALS = ("[]", "0")   # filled in by `globals_literal` once the module is known
ENV = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])


# ---------------------------------------------------------------------------
# 0. Lean plumbing
# ---------------------------------------------------------------------------

def lean_run(src: str, tag: str, timeout: int = 900):
    """Elaborate a Lean source string; return (rc, stdout, stderr)."""
    path = os.path.join(SCRATCH, "autoform_synth_%s.lean" % tag)
    with open(path, "w", encoding="utf-8") as f:
        f.write(src)
    r = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True,
                       env=ENV, cwd=REPO)
    return r.returncode, r.stdout, r.stderr, path


def core_names(module: str):
    """The call-closed core, straight from `Program.callClosed` — the Lean definition is
    the authority on which functions are analysable, so it is asked rather than
    re-implemented here."""
    src = ("import Autoform.Ledger\nimport Autoform.Generated.%s\n"
           "open Autoform.Core in\n#eval do\n"
           "  let p : Program := Autoform.Generated.program\n"
           "  IO.println (String.intercalate \"\\n\" "
           "(p.callClosed.map (fun f : Func => f.name)))\n" % module)
    rc, out, err, _ = lean_run(src, "core")
    if rc != 0:
        print("could not query the call-closed core:\n%s" % (err or out)[:400])
        return None
    return [l for l in out.splitlines() if l.strip()]


def globals_literal(module: str):
    """The module-initialiser heap, as a Lean *source* literal.

    Module-level bindings (`Stmt.setGlobal`, `Expr.closure`) only exist after the
    initialisers have run, so every case has to run against that frame — the same frame
    `scripts/differential.py` builds. Writing `initGlobals P 5000 moduleInits` into the
    generated module would be simpler, but the kernel has no sharing: every `by rfl` proof
    would re-run every initialiser once per case. Evaluating it once here and emitting the
    resulting heap as a literal keeps the proofs affordable, and the literal is Lean's own
    `Repr` output for the value, not a reconstruction of it."""
    src = ("import Autoform.Generated.%s\n"
           "open Autoform.Core Autoform.Generated\n"
           "#eval do\n"
           "  let gp := initGlobals program %d Autoform.Generated.moduleInits\n"
           "  IO.println (\"@@\" ++ ((repr gp.1).pretty (width := 100000000)))\n"
           "  IO.println (\"##\" ++ toString gp.2)\n" % (module, INIT_FUEL))
    rc, out, err, _ = lean_run(src, "globals")
    heap = gref = None
    for line in out.splitlines():
        if line.startswith("@@"):
            heap = line[2:]
        elif line.startswith("##"):
            gref = line[2:]
    if heap is None:
        print("   could not materialise the globals frame; falling back to an empty "
              "heap (functions that read module-level names will hole and be dropped)")
        return "[]", "0"
    return heap, gref


# ---------------------------------------------------------------------------
# 1. Source artifacts (§4 source 1)
# ---------------------------------------------------------------------------

def strip_doc(body):
    """A leading docstring is an `exprS` of a string literal; peel it off.

    It is peeled rather than ignored because the *shape* underneath is what decides
    whether a universally quantified specification can be generated and proved."""
    doc = None
    while body.get("k") == "seq" and body["a"].get("k") == "exprS" \
            and body["a"]["e"].get("k") == "str":
        doc = body["a"]["e"]["v"]
        body = body["b"]
    return doc, body


DOCTEST = re.compile(r'^\s*>>> ', re.M)


def mine_artifacts(funcs, src_root):
    """Count what §4 source 1 actually offers on this corpus, without guessing.

    Docstrings and guards come from the AST (so they are exactly what was translated);
    doctests and property-based tests are counted from the source tree, because a PBT is
    evidence about the *repository*, not about any one translated function."""
    art = {"docstrings": 0, "doctests": 0, "asserts": 0, "raises": 0,
           "pbt_files": 0, "pbt_properties": 0, "test_files": 0}
    for f in funcs:
        doc, _ = strip_doc(f["body"])
        if doc:
            art["docstrings"] += 1
            if DOCTEST.search(doc):
                art["doctests"] += 1
        blob = json.dumps(f["body"])
        art["raises"] += blob.count('"k": "raise"') + blob.count('"k":"raise"')
    for root, _dirs, files in os.walk(src_root):
        if ".git" in root:
            continue
        for fn in files:
            if not fn.endswith(".py"):
                continue
            p = os.path.join(root, fn)
            try:
                txt = open(p, encoding="utf-8", errors="replace").read()
            except OSError:
                continue
            if os.path.basename(p).startswith("test") or "/tests" in p:
                art["test_files"] += 1
            art["asserts"] += len(re.findall(r'^\s*assert\b', txt, re.M))
            if "hypothesis" in txt:
                art["pbt_files"] += 1
                art["pbt_properties"] += len(re.findall(r'^\s*@given\b', txt, re.M))
            art["doctests"] += 0
    return art


# ---------------------------------------------------------------------------
# 2. Observations (§4 source 1 + 4): the repository's own test suite
# ---------------------------------------------------------------------------

def observe(ast_path, src_root, tests_override, per_fn):
    """Drive the repo's suite under `differential.py`'s trace hook.

    Reused wholesale rather than rebuilt: the encoder there already refuses every value
    it cannot represent faithfully, which is precisely the property a specification
    generator needs from its input."""
    funcs = json.load(open(ast_path))
    holefree = [f for f in funcs if not D.has_hole(f["body"])]
    wanted = set(f["name"] for f in holefree if D.classify(f))
    rels = sorted(set(f.get("file", "") for f in funcs))
    root = D.resolve_src_root(src_root, rels)
    tests = [tests_override] if tests_override else D.find_tests(root)
    index = D.build_lineno_index(root, rels)
    stats = {"skip_varargs": 0, "skip_unencodable_args": 0, "skip_unencodable_ret": 0,
             "test_runs": []}
    recs = D.trace_tests(root, tests, index, wanted, per_fn, stats) if tests else []
    return funcs, recs, stats, root, tests


# ---------------------------------------------------------------------------
# 3. Fuzzing: candidate domains
# ---------------------------------------------------------------------------

INT_PERTURB = [0, 1, -1, 2, 7, -7, 1000000]


def perturb(v, rng):
    """One structural mutation of an encoded value. Used to build the refutation domain:
    a law that only ever saw the test suite's arguments has not been tested."""
    t = v[0]
    if t == "int":
        return ("int", rng.choice(INT_PERTURB))
    if t == "bool":
        return ("bool", not v[1])
    if t == "str":
        return ("str", rng.choice(["", "x", v[1] + "!"]))
    if t in ("list", "tuple"):
        if v[1] and rng.random() < 0.5:
            i = rng.randrange(len(v[1]))
            return (t, [perturb(x, rng) if j == i else x for j, x in enumerate(v[1])])
        return (t, [])
    if t == "dict":
        return (t, []) if rng.random() < 0.5 else v
    if t == "unit":
        return ("int", 0)
    return v


def fuzz_cases(rec, rng, n):
    """Fuzz a recorded call: perturb arguments, and perturb the receiver's fields.

    The receiver matters more than the arguments here — most of the call-closed core of a
    cache library is accessors, and a law about an accessor is only tested by varying the
    object it reads."""
    out = []
    for _ in range(n):
        args = [perturb(a, rng) if rng.random() < 0.7 else a for a in rec["args"]]
        heap = [list(o) for o in rec["heap"]]
        for o in heap:
            o[1] = [(k, perturb(x, rng) if rng.random() < 0.4 else x) for k, x in o[1]]
        out.append({"heap": [(c, fs) for c, fs in heap], "self": rec["self"],
                    "args": args})
    return out


# ---------------------------------------------------------------------------
# 4. Lean rendering of cases
# ---------------------------------------------------------------------------

def val_lit(v):
    return D.lean_val(v)


def heap_lit(heap):
    """Heap literal, written with named fields.

    `differential.py`'s `lean_heap` uses the anonymous constructor, which no longer
    accepts `Obj` now that it carries a third (defaulted) `captured` field — named fields
    are the form that survives a structure gaining one."""
    return "[%s]" % ", ".join(
        "{ cls := %s, fields := [%s] }"
        % (json.dumps(cls), ", ".join("(%s, %s)" % (json.dumps(k), val_lit(v))
                                      for k, v in fields))
        for cls, fields in heap)


def case_lit(c):
    slf = "none" if c["self"] is None else "(some (%s))" % val_lit(c["self"])
    return ("{ heap := h0 ++ %s, self := %s, args := [%s] }"
            % (heap_lit(c["heap"]), slf,
               ", ".join(val_lit(a) for a in c["args"])))


def eresult_lit(outcome):
    """The outcome CPython produced, as a Core `EResult`.

    Only `val` and `exn` occur: `hole` and `outOfFuel` are statements about *our*
    ignorance and the real runtime never makes them."""
    kind, payload = outcome
    if kind == "val":
        return "EResult.val (%s)" % val_lit(payload)
    return "EResult.exn (Val.str %s)" % json.dumps(payload)


def obs_lit(rec):
    return "{ case := %s, expected := %s }" % (case_lit(rec), eresult_lit(rec["outcome"]))


# ---------------------------------------------------------------------------
# 5. Candidate generation
# ---------------------------------------------------------------------------

class Cand:
    """One candidate specification, before anything is known about whether it is true."""

    def __init__(self, cid, family, source, subject, fdef, law, dom, kind="law",
                 dom_kind="case", note="", extra=None):
        self.id, self.family, self.source = cid, family, source
        self.subject, self.fdef = subject, fdef
        self.law = law                 # Lean text: partially applied law
        self.dom = dom                 # list of Lean case/obs literals
        self.kind = kind               # "law" | "universal"
        self.dom_kind = dom_kind       # "case" | "obs"
        self.note = note
        self.extra = extra or {}
        self.status = "candidate"
        self.reason = ""
        self.proved = False
        self.checked = None            # refutation verdict

    def as_json(self):
        return {"id": self.id, "family": self.family, "source": self.source,
                "subject": self.subject, "kind": self.kind, "domain": len(self.dom),
                "status": self.status, "reason": self.reason, "proved": self.proved,
                "checked": self.checked, "note": self.note}


def writes_heap(body):
    blob = json.dumps(body)
    return any(k in blob for k in ('"setField"', '"setIndex"', '"alloc"'))


def can_hole_or_loop(body):
    """Does this function have any construct that could hole at runtime or fail to
    terminate? Mirrors `Ledger.lean`'s `Analysis.eRisk`: `field`, `index`, `mcall`,
    `call`, `inOp`, arithmetic, and every looping form."""
    blob = json.dumps(body)
    return any('"%s"' % k in blob for k in
               ("field", "index", "mcall", "call", "alloc", "inOp", "binop",
                "loop", "forIn", "setIndex"))


def gen_candidates(core, byname, recs, rng):
    """Mine candidates for every call-closed function the suite actually exercised."""
    cands = []
    by_fn = {}
    for r in recs:
        by_fn.setdefault(r["name"], []).append(r)

    for name in core:
        f = byname.get(name)
        if f is None:
            continue
        fdef = lean_ident(name)
        obs = by_fn.get(name, [])
        sid = re.sub(r'[^A-Za-z0-9]', '_', name)[-70:].strip("_")
        doc, core_body = strip_doc(f["body"])

        # ---- §4 source 4: cross-implementation equivalence, one theorem per function.
        if obs:
            seen, uniq = set(), []
            for r in obs:
                k = json.dumps([r["heap"], r["self"], r["args"]], sort_keys=True)
                if k in seen:
                    continue
                seen.add(k)
                uniq.append(r)
            cands.append(Cand("conform_" + sid, "conform", "cross-runtime (§4.4)", name,
                              fdef, "lawConform C FUEL %s" % fdef,
                              [obs_lit(r) for r in uniq[:MAX_DOMAIN]], dom_kind="obs",
                              note="expected outcomes recorded from CPython by "
                                   "scripts/differential.py"))

        # ---- the fuzz domain every behavioural law is refuted against
        base = []
        for r in obs[:4]:
            base.append({"heap": r["heap"], "self": r["self"], "args": r["args"]})
            base.extend(fuzz_cases(r, rng, 3))
        seen, dom = set(), []
        for c in base:
            k = json.dumps(c, sort_keys=True)
            if k in seen:
                continue
            seen.add(k)
            dom.append(c)
        dom = dom[:MAX_DOMAIN]
        if not dom:
            continue
        lits = [case_lit(c) for c in dom]
        triv_hole = not can_hole_or_loop(core_body)
        triv_heap = not writes_heap(core_body)

        def add(fam, source, law, note="", trivial=False, extra=None, tag=""):
            c = Cand("%s%s_%s" % (fam, tag, sid), fam, source, name, fdef, law, lits,
                     note=note, extra=extra)
            if trivial:
                c.extra["structurally_trivial"] = True
            cands.append(c)

        # ---- §4 source 2: structural / safety, free for all code
        add("runs", "structural (§4.2)", "lawRuns C FUEL %s" % fdef,
            note="no .hole and no .outOfFuel within the stated fuel budget",
            trivial=triv_hole)
        add("returns", "structural (§4.2)", "lawReturns C FUEL %s" % fdef,
            note="returns a value; does not even raise", trivial=triv_hole)

        # ---- §4 source 3: algebraic laws mined from behaviour
        add("heappure", "algebraic (§4.3)", "lawHeapPreserved C FUEL %s" % fdef,
            note="the call leaves the heap structurally unchanged", trivial=triv_heap)
        add("nonneg", "algebraic (§4.3)", "lawNonneg C FUEL %s" % fdef,
            note="integer result is non-negative")
        if any(len(c["args"]) >= 1 for c in dom):
            add("identity", "algebraic (§4.3)", "lawIdentity C FUEL %s" % fdef,
                note="returns its first argument unchanged")
            add("idempotent", "algebraic (§4.3)", "lawIdempotent C FUEL %s" % fdef,
                note="f (f x) = f x")
            add("involutive", "algebraic (§4.3)", "lawInvolutive C FUEL %s" % fdef,
                note="f (f x) = x")
        if any(len(c["args"]) >= 2 for c in dom):
            add("commutes", "algebraic (§4.3)", "lawCommutes C FUEL %s" % fdef,
                note="symmetric in its first two arguments")

        # constants and projections are mined from what was observed, then refuted
        vals = [r["outcome"] for r in obs if r["outcome"][0] == "val"]
        if vals and all(json.dumps(v) == json.dumps(vals[0]) for v in vals):
            add("const", "algebraic (§4.3)",
                "lawConst C FUEL %s (%s)" % (fdef, val_lit(vals[0][1])),
                note="constant output")
        exns = [r["outcome"] for r in obs if r["outcome"][0] == "exn"]
        if exns and not vals and all(e[1] == exns[0][1] for e in exns):
            add("raises", "artifact (§4.1)",
                "lawRaises C FUEL %s (Val.str %s)" % (fdef, json.dumps(exns[0][1])),
                note="always raises %s — the postcondition of a guard the suite "
                     "exercised" % exns[0][1])
        flds = set()
        for r in obs:
            if r["self"] and r["self"][0] == "ref":
                idx = r["self"][1]
                if idx < len(r["heap"]):
                    flds.update(k for k, _ in r["heap"][idx][1])
        for fld in sorted(flds)[:6]:
            add("projects", "algebraic (§4.3)",
                "lawProjects C FUEL %s %s" % (fdef, json.dumps(fld)),
                note="the accessor reads field %s" % fld,
                tag="_" + re.sub(r'[^A-Za-z0-9]', '_', fld))

        # ---- deliberately mined, and never emitted: the §15 pattern
        cands.append(Cand("determ_" + sid, "determinism", "algebraic (§4.3)", name, fdef,
                          "", lits, kind="determinism",
                          note="f(x) = f(x): the property §15 found dominates FVSpec's "
                               "vacuous 41%"))

        # ---- universally quantified families, with generated proofs
        if core_body.get("k") == "ret" and core_body["e"].get("k") in (
                "int", "str", "bool"):
            e = core_body["e"]
            lit = {"int": "Val.int (%s)" % e.get("v"), "bool": "Val.bool %s" %
                   ("true" if e.get("v") else "false"),
                   "str": "Val.str %s" % json.dumps(str(e.get("v")))}[e["k"]]
            cands.append(Cand("uconst_" + sid, "u_const", "structural (§4.2)", name, fdef,
                              "", [], kind="universal",
                              note="constant on every input, at every fuel budget ≥ 8",
                              extra={"shape": "const", "lit": lit}))
        if core_body.get("k") == "ret" and core_body["e"].get("k") == "field" \
                and core_body["e"]["a"].get("k") == "name" \
                and core_body["e"]["a"].get("v") == "self" and not f["params"]:
            cands.append(Cand("uproj_" + sid, "u_projection", "algebraic (§4.3)", name,
                              fdef, "", [], kind="universal",
                              note="accessor: returns receiver field %s on every heap"
                                   % core_body["e"]["f"],
                              extra={"shape": "projection",
                                     "field": core_body["e"]["f"],
                                     "documented": doc is not None}))
    # Lean names must be unique; a collision would silently drop a candidate.
    seen = {}
    for c in cands:
        if c.id in seen:
            seen[c.id] += 1
            c.id = "%s_%d" % (c.id, seen[c.id])
        else:
            seen[c.id] = 0
    return cands


# ---------------------------------------------------------------------------
# 6. Refutation
# ---------------------------------------------------------------------------

HEADER = """import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.%s

/-! Generated by `scripts/synth_specs.py`. Do not edit by hand. -/
namespace Autoform.SpecsGen.%s

open Autoform.Core Autoform.Refine Autoform.SpecsGen

-- The proofs below are by computation on concrete inputs: the kernel walks the
-- interpreter, and deeply nested calls need more than the default budgets.
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

abbrev P : Program := Autoform.Generated.program

/-- The module-initialiser heap, evaluated once by `initGlobals P %d moduleInits` and
frozen into this literal so that the kernel does not re-run the initialisers for every
case of every proof. -/
def h0 : Heap := %s

/-- Address of the globals frame. -/
def gref : Ref := %s
def base : Nat := h0.length
def C : Ctx := { dialect := P.dialect, table := P.table, globals := gref }
def FUEL : Nat := %d
open Autoform.Generated
"""


def domain_defs(c):
    ty = "Obs" if c.dom_kind == "obs" else "Case"
    body = ",\n   ".join(c.dom)
    return "def dom_%s : List %s :=\n  [%s]\n" % (c.id, ty, body)


def refute(cands, module, chunk=120):
    """Evaluate every candidate over its domain, in the Lean semantics, before anything
    is emitted. A single counterexample drops the candidate.

    The check is `#eval`, not a proof: refutation is cheap and must not be allowed to
    fail merely because the kernel is slow. What survives is *then* asked to be proved."""
    live = [c for c in cands if c.kind == "law"]
    for i in range(0, len(live), chunk):
        part = live[i:i + chunk]
        src = [HEADER % (module, module, INIT_FUEL, GLOBALS[0], GLOBALS[1], FUEL)]
        for c in part:
            src.append(domain_defs(c))
            src.append('#eval IO.println ("@@%s@@" ++ toString '
                       '((dom_%s).all (%s)) ++ " " ++ toString (dom_%s).length ++ " " '
                       '++ toString ((dom_%s).countP (fun x => %s)))\n'
                       % (c.id, c.id, c.law, c.id, c.id,
                          "isHole (runCase C FUEL %s x.case).2" % c.fdef
                          if c.dom_kind == "obs" else
                          "isHole (runCase C FUEL %s x).2" % c.fdef))
        src.append("end Autoform.SpecsGen.%s\n" % module)
        # A concurrently rebuilt `.olean` makes `lake env lean` fail for reasons that
        # have nothing to do with the candidates; retry once before recording a chunk as
        # unevaluated, since "not checked" silently shrinks the population.
        got = {}
        for attempt in range(2):
            rc, out, err, path = lean_run("\n".join(src), "refute%d" % i)
            for line in out.splitlines():
                m = re.match(r'@@([A-Za-z0-9_]+)@@(true|false) (\d+) (\d+)', line)
                if m:
                    got[m.group(1)] = (m.group(2) == "true", int(m.group(3)),
                                       int(m.group(4)))
            if got:
                break
            subprocess.run(["lake", "build", "Autoform.Generated.%s" % module,
                            "Autoform.SpecsGen.Basis"], capture_output=True, env=ENV,
                           cwd=REPO)
        for c in part:
            if c.id not in got:
                c.status, c.reason = "not_checked", "lean could not evaluate the domain"
                c.checked = {"error": (err or out)[-300:]}
                continue
            holds, n, holes = got[c.id]
            c.checked = {"holds": holds, "domain": n, "holes": holes}
            if holes:
                c.status = "refuted"
                c.reason = ("interpreter reached an untranslated construct on %d/%d "
                            "cases — the law is inconclusive, not true" % (holes, n))
            elif not holds:
                c.status, c.reason = "refuted", "counterexample in the fuzzed domain"
        if rc != 0 and not got:
            print("  refutation chunk %d: lean failed (%s)" % (i, path))
    return cands


# ---------------------------------------------------------------------------
# 7. The vacuity screen — the same check names §15 applied to FVSpec
# ---------------------------------------------------------------------------

def screen(cands):
    for c in cands:
        if c.status not in ("candidate",):
            continue
        if c.kind == "determinism":
            c.status = "vacuous"
            c.reason = ("reflexive_conclusion: f(x) = f(x) is closed by `rfl` in a pure "
                        "setting — see SpecsGen.Basis.deterministic_vacuous")
            continue
        if c.kind == "universal":
            continue                                   # screened by construction below
        if not c.dom:
            c.status, c.reason = "vacuous", "empty_quantification: no domain"
            continue
        if c.extra.get("structurally_trivial"):
            c.status = "vacuous"
            c.reason = ("trivial_conclusion: the AST contains no construct that could "
                        "falsify this, so the statement is true by shape, not by "
                        "behaviour")
            continue
        if c.fdef not in c.law:
            c.status = "vacuous"
            c.reason = "dependency_vacuity: statement never mentions the implementation"
            continue
        if c.dom_kind == "case" and len(c.dom) < MIN_LAW_DOMAIN:
            c.status = "vacuous"
            c.reason = ("empty_quantification: %d-case domain is an anecdote, not a "
                        "quantifier" % len(c.dom))
            continue
    return cands


# ---------------------------------------------------------------------------
# 8. Emission
# ---------------------------------------------------------------------------

PROOF_CONST = """theorem %(id)s :
    Refines P %(name)s 8 (fun _ => True) (fun _ => .ret (%(lit)s)) := by
  intro args _
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ %(fdef)s rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set, %(fdef)s, ctxOf, P]
"""

PROOF_PROJ = """theorem %(id)s :
    MRefines P %(name)s 4
      (fun _ self _ => ∃ r, self = .ref r)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r %(field)s)
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨r, rfl⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ %(fdef)s rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h %(fdef)s %(field)s rfl rfl r args
"""

PROOF_PROJ_DOC = """theorem %(id)s :
    MRefines P %(name)s 5
      (fun _ self _ => ∃ r, self = .ref r)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r %(field)s)
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨r, rfl⟩
  refine forall_ge_of_forall_add (N := 5) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ %(fdef)s rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_doc_ret_field_self (ctxOf P) k h %(fdef)s %(field)s _ rfl rfl r args
"""

DOC = '''
/-!
# Synthesized specifications — `%(module)s`

**Generated by `scripts/synth_specs.py`. Do not edit by hand.**

Every statement below is about `Autoform/Generated/%(module)s.lean` *by import*, so a
mutation of the generated module is a mutation of the subject of these theorems
(`scripts/mutate.py --spec-file`). The `#audit_depends` block at the end fails the build
for any theorem that does not mention the implementation it claims to constrain.

What each family claims, in the order of `STRATEGY.md` §4:

* `conform_*` (§4.4, cross-implementation) — the interpreter reproduces, case by case,
  the outcome **CPython** produced when the repository's own test suite called this
  function. The right-hand sides were recorded by `scripts/differential.py`'s trace hook;
  they are not this system's own output, which is what keeps the family from being an
  elaborate `rfl`.
* `runs_*` / `returns_*` (§4.2, structural) — on this domain the interpreter neither
  reaches an untranslated construct nor exhausts its fuel. `EResult` distinguishes
  `.hole` and `.outOfFuel` from behaviour, so this is a real property, and it is stated
  only for functions whose AST *could* violate it.
* `heappure_*`, `const_*`, `projects_*`, `identity_*`, `idempotent_*`, `involutive_*`,
  `commutes_*`, `nonneg_*` (§4.3, algebraic) — laws mined from observed executions and
  **refuted against a fuzzed domain before emission**. Survivors only.
* `uconst_*`, `uproj_*` — universally quantified refinements, proved for every input and
  every fuel budget above a stated bound.

Domains are finite and explicit, and the theorems about them are proved by computation.
That is deliberate: a kernel-checked test is a test whose axiom basis is auditable and
whose subject a mutation gate can attack. Where the honest generalization (over *all*
fuel budgets, or all inputs) could not be proved, it is recorded in `obligations` below
as a `Prop`-valued `def` — a statement, not an admission. There is no `sorry` in this
file.

Counts for this run are in `Autoform/SpecsGen/report.json`.
-/
'''


def emit(cands, module, obligations_extra):
    survivors = [c for c in cands if c.status in ("candidate", "proved")]
    out = [HEADER % (module, module, INIT_FUEL, GLOBALS[0], GLOBALS[1], FUEL)]
    out.insert(1, DOC % {"module": module})
    obs = []
    thms = []
    for c in survivors:
        if c.kind == "law":
            out.append(domain_defs(c))
            out.append("theorem %s : ((dom_%s).all (%s)) = true := by rfl\n"
                       % (c.id, c.id, c.law))
            thms.append((c.id, c.fdef))
            # the honest generalization: fuel-independence, stated and not proved
            out.append("/-- Open: the same statement at **every** fuel budget ≥ `FUEL`. "
                       "Proved only at `FUEL`. -/\ndef ob_%s : Prop :=\n"
                       "  ∀ fuel, FUEL ≤ fuel → ((dom_%s).all (%s)) = true\n"
                       % (c.id, c.id, c.law.replace("C FUEL", "C fuel")))
            obs.append((("ob_" + c.id), c.source, c.subject,
                        "proved at FUEL only; fuel-independence unproved"))
        elif c.kind == "universal":
            d = {"id": c.id, "name": json.dumps(c.subject), "fdef": c.fdef,
                 "lit": c.extra.get("lit", ""),
                 "field": json.dumps(c.extra.get("field", ""))}
            if c.extra["shape"] == "const":
                out.append(PROOF_CONST % d)
            elif c.extra.get("documented"):
                out.append(PROOF_PROJ_DOC % d)
            else:
                out.append(PROOF_PROJ % d)
            thms.append((c.id, c.fdef))
    for name, source, subject, reason in obligations_extra:
        obs.append((name, source, subject, reason))
    out.append("/-- Everything this module states but does not prove. A `Prop`-valued "
               "`def` asserts nothing, so nothing here is admitted. -/\n"
               "def obligations : List OpenObligation :=\n  [%s]\n"
               % ",\n   ".join('{ name := %s, source := %s, subject := %s, reason := %s }'
                               % (json.dumps(n), json.dumps(s), json.dumps(sub),
                                  json.dumps(r)) for n, s, sub, r in obs))
    out.append("#eval IO.println (renderObligations %s obligations)\n"
               % json.dumps(module))
    out.append("/-! ## Anti-vacuity gate\n\n`#audit_depends` fails the build if a "
               "theorem's proof term never mentions the generated definition it claims "
               "to be about — the necessary half of the gate. The sufficient half is "
               "`scripts/mutate.py`, run against this file. -/\n")
    for tid, fdef in thms:
        out.append("#audit_depends %s on %s" % (tid, fdef))
    out.append("\nend Autoform.SpecsGen.%s\n" % module)
    return "\n".join(out), thms, obs


def compile_repair(cands, module, path, rounds=6):
    """Emit, compile, and demote whatever will not prove to an open obligation.

    A generator that cannot prove a statement has exactly two honest options: state it
    without proof, or drop it. `sorry` is neither."""
    demoted = []
    for _ in range(rounds):
        src, thms, _obs = emit(cands, module, demoted)
        with open(path, "w", encoding="utf-8") as f:
            f.write(src)
        r = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True,
                           env=ENV, cwd=REPO)
        if r.returncode == 0:
            for c in cands:
                if c.status == "candidate":
                    c.status, c.proved = "proved", True
            return True, demoted, r.stdout
        lines = src.splitlines(keepends=True)
        decls = M.parse_decls(lines)
        bad = set()
        for m in re.finditer(r'^%s:(\d+):\d+: error' % re.escape(path),
                             r.stdout + r.stderr, re.M):
            ln = int(m.group(1))
            for d in decls:
                if d.start <= ln <= d.end and d.kind in ("theorem", "lemma"):
                    bad.add(d.name)
        if not bad:
            print("  build failed with no attributable theorem:\n%s"
                  % (r.stdout + r.stderr)[:600])
            return False, demoted, r.stdout + r.stderr
        for c in cands:
            if c.id in bad and c.status == "candidate":
                c.status = "unproved"
                c.reason = "no proof found by the generated portfolio"
                demoted.append(("stmt_" + c.id, c.source, c.subject,
                                "statement survived refutation; the generated proof "
                                "portfolio could not close it"))
        print("  demoted to open obligations: %s" % ", ".join(sorted(bad)))
    return False, demoted, "gave up after %d repair rounds" % rounds


# ---------------------------------------------------------------------------
# 9. main
# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description="Layer 4: automatic specification synthesis")
    ap.add_argument("ast")
    ap.add_argument("src_root")
    ap.add_argument("module")
    ap.add_argument("--tests", default=None)
    ap.add_argument("--cases", type=int, default=10,
                    help="traced calls to keep per function")
    ap.add_argument("--refute-cache", default=None,
                    help="cache the refutation verdicts here, keyed by candidate id. "
                         "Refuting 500 candidates means elaborating half a megabyte of "
                         "Lean; when only the emission changed, replay instead")
    ap.add_argument("--obs-cache", default=None,
                    help="cache the traced calls here; the repository's suite takes "
                         "minutes to run under `sys.settrace` and the recording is "
                         "deterministic, so re-running it on every iteration is waste")
    ap.add_argument("--json", dest="json_path",
                    default=os.path.join(OUTDIR, "report.json"))
    args = ap.parse_args()

    os.makedirs(OUTDIR, exist_ok=True)
    rng = random.Random(20260819)

    print("== 0. the analysable core")
    b = subprocess.run(["lake", "build", "Autoform.Generated.%s" % args.module,
                        "Autoform.SpecsGen.Basis"],
                       capture_output=True, text=True, env=ENV, cwd=REPO)
    if b.returncode != 0:
        # README: "a stale `.olean` made the oracle lie ... an oracle reading a stale
        # cache is worse than no oracle". The same applies here, and worse: a red
        # baseline makes *every* generated proof fail, and the repair loop would then
        # demote every real theorem to an open obligation and overwrite a good module
        # with a wrong one. Refuse instead, and leave the previous output alone.
        print("REFUSING TO RUN: the baseline does not build, so no proof attempt below "
              "would mean anything, and the previous output would be overwritten with "
              "an artefact of the broken build:\n%s"
              % (b.stderr or b.stdout)[-600:])
        return 2
    global GLOBALS
    GLOBALS = globals_literal(args.module)
    core = core_names(args.module)
    if core is None:
        return 2
    funcs = json.load(open(args.ast))
    byname = {f["name"]: f for f in funcs}
    print("   %d functions translated, %d call-closed" % (len(funcs), len(core)))

    print("== 1. existing artifacts (§4 source 1)")
    art = mine_artifacts(funcs, args.src_root)
    print("   docstrings %d, doctests %d, `raise` guards %d, asserts %d, "
          "hypothesis PBT files %d (%d @given properties)"
          % (art["docstrings"], art["doctests"], art["raises"], art["asserts"],
             art["pbt_files"], art["pbt_properties"]))

    print("== 2. observations from the repository's own test suite")
    if args.obs_cache and os.path.exists(args.obs_cache):
        blob = json.load(open(args.obs_cache))
        funcs, recs, stats, tests = (json.load(open(args.ast)), blob["recs"],
                                     blob["stats"], blob["tests"])
        print("   (replayed from %s)" % args.obs_cache)
    else:
        funcs, recs, stats, root, tests = observe(args.ast, args.src_root, args.tests,
                                                  args.cases)
        if args.obs_cache:
            json.dump({"recs": recs, "stats": stats, "tests": tests},
                      open(args.obs_cache, "w"))
    incore = [r for r in recs if r["name"] in set(core)]
    print("   %d calls recorded over %d functions; %d of them in the call-closed core"
          % (len(recs), len(set(r["name"] for r in recs)), len(incore)))

    print("== 3. candidate generation")
    cands = gen_candidates(core, byname, incore, rng)
    print("   %d candidates" % len(cands))

    print("== 4. refutation (fuzz every candidate before emitting anything)")
    cache = {}
    if args.refute_cache and os.path.exists(args.refute_cache):
        cache = json.load(open(args.refute_cache))
    hit = [c for c in cands if c.id in cache]
    for c in hit:
        v = cache[c.id]
        c.status, c.reason, c.checked = v["status"], v["reason"], v["checked"]
    miss = [c for c in cands if c.id not in cache]
    if hit:
        print("   (%d verdicts replayed from %s, %d to check)"
              % (len(hit), args.refute_cache, len(miss)))
    refute(miss, args.module)
    if args.refute_cache:
        for c in cands:
            if c.kind == "law" and c.checked is not None:
                cache[c.id] = {"status": c.status, "reason": c.reason,
                               "checked": c.checked}
        json.dump(cache, open(args.refute_cache, "w"))
    refuted = [c for c in cands if c.status == "refuted"]
    nochk = [c for c in cands if c.status == "not_checked"]
    print("   %d refuted, %d not checkable, %d survive"
          % (len(refuted), len(nochk),
             len([c for c in cands if c.status == "candidate"])))

    print("== 5. vacuity screen (the checks §15 ran over FVSpec, run over ourselves)")
    screen(cands)
    vac = [c for c in cands if c.status == "vacuous"]
    kinds = {}
    for c in vac:
        kinds[c.reason.split(":")[0]] = kinds.get(c.reason.split(":")[0], 0) + 1
    for k, v in sorted(kinds.items(), key=lambda kv: -kv[1]):
        print("   %-24s %d" % (k, v))
    survivors = [c for c in cands if c.status == "candidate"]
    print("   %d flagged vacuous, %d emitted" % (len(vac), len(survivors)))

    print("== 6. emission + proof")
    path = os.path.join(OUTDIR, "%s.lean" % args.module)
    ok, demoted, log = compile_repair(cands, args.module, path)
    proved = [c for c in cands if c.proved]
    unproved = [c for c in cands if c.status == "unproved"]
    print("   %s: %d theorems proved, %d statements left open"
          % ("clean" if ok else "BUILD FAILED", len(proved), len(unproved)))

    considered = [c for c in cands if c.status != "not_checked"]
    vac_rate = (100.0 * len(vac) / len(considered)) if considered else 0.0
    report = {
        "module": args.module,
        "corpus": os.path.abspath(args.src_root),
        "functions": len(funcs),
        "call_closed": len(core),
        "artifacts": art,
        "observations": {"calls": len(recs), "in_core": len(incore),
                         "tests": tests, "skipped": {k: v for k, v in stats.items()
                                                     if k != "test_runs"}},
        "candidates": len(cands),
        "refuted": len(refuted),
        "not_checked": len(nochk),
        "vacuous": len(vac),
        "vacuity_checks": kinds,
        "vacuity_rate_pct": round(vac_rate, 1),
        "emitted": len(survivors),
        "proved": len(proved),
        "open_obligations": len(unproved) + len(proved),
        "build_clean": ok,
        "by_family": {},
        "specs": [c.as_json() for c in cands],
        "not_checked_gates": [
            "scripts/mutate.py — run separately; a surviving mutant means the spec is "
            "vacuous in the sufficient sense",
            "scripts/audit_all.py — axiom basis of the emitted theorems"],
    }
    for c in cands:
        b = report["by_family"].setdefault(c.family, {"candidates": 0, "refuted": 0,
                                                      "vacuous": 0, "proved": 0})
        b["candidates"] += 1
        b["refuted"] += c.status == "refuted"
        b["vacuous"] += c.status == "vacuous"
        b["proved"] += c.proved
    json.dump(report, open(args.json_path, "w"), indent=1)

    print("\n== summary")
    print("   candidates generated : %d" % len(cands))
    print("   refuted by fuzzing   : %d" % len(refuted))
    print("   flagged vacuous      : %d  (%.1f%% of %d screened — FVSpec's rate was "
          "41.0%%)" % (len(vac), vac_rate, len(considered)))
    print("   emitted + proved     : %d" % len(proved))
    print("   open obligations     : %d" % report["open_obligations"])
    print("   report               : %s" % args.json_path)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
