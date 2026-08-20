#!/usr/bin/env python3
"""sacm.py — emit a SACM-shaped assurance case for one autoformalized module.

STRATEGY.md §10: the composition calculus for heterogeneous verification evidence is
the *assurance case* field, not something to reinvent. The model here is a small profile
of **SACM** (OMG Structured Assurance Case Metamodel v2.1), which unifies GSN and CAE and
already models our three concerns: arguments (claims + inferential links), artifacts
(evidence), and terminology. The proof-integration pattern — mechanized proof results as
first-class SACM artifacts referenced by structured claims — is Isabelle/SACM's
(arXiv:2009.12154). The transport envelope is in-toto/SLSA style.

Ours is only the domain-specific part: the evidence types (conformance rate, hole count /
verifiable core, mutation score, axiom basis) and the rules for combining them into a
claim. See `docs/ledger-schema.md`.

Two design commitments, both about *not lying*:

  1. **Every hole becomes a named Assumption node.** An untranslated construct is not an
     absence, it is an assumption the argument rests on. It must appear in the argument
     structure, not vanish from it.
  2. **Missing evidence is UNDEVELOPED, never omitted.** A claim with no supporting
     artifact is an undeveloped goal (GSN's diamond), which is a visible hole in the
     argument. Silently dropping it would manufacture confidence.

Usage:
    scripts/sacm.py --module Cachetools [--out sacm-Cachetools.json] [--root .]
                    [--markdown sacm-Cachetools.md] [--quiet]

Reads whichever of these exist, degrading gracefully:
    ast-<Module>.json         neutral AST      -> coverage, holes, assumptions
    formalization-graph.json  Joern cartography-> population, purity, effects
    conformance.json          differential run -> translation faithfulness
    mutation.json             mutation gate    -> specification adequacy
    axioms.json               #audit_axioms    -> proof validity
"""
from __future__ import annotations

import argparse
import collections
import datetime
import hashlib
import json
import os
import sys

TOOL = "autoform/sacm.py"
TOOL_VERSION = "0.1"
PREDICATE_TYPE = "https://autoform.dev/attestations/sacm-assurance-case/v0.1"
SACM_PROFILE = "OMG SACM 2.1 (profile: autoform-evidence-v0.1)"

# ---------------------------------------------------------------------------
# Status lattice. Ordered worst -> best; a claim never outranks its weakest
# supporting sub-claim (see docs/ledger-schema.md, "combination rules").
# ---------------------------------------------------------------------------
UNDEVELOPED = "UNDEVELOPED"   # no evidence cited at all — GSN undeveloped goal
DEFEATED = "DEFEATED"         # evidence exists and *contradicts* the claim
UNSUPPORTED = "UNSUPPORTED"   # evidence exists but does not reach the threshold
WEAK = "WEAK"                 # threshold met, but a defeater is unaddressed
SUPPORTED = "SUPPORTED"       # threshold met, no unaddressed defeater

ORDER = {UNDEVELOPED: 0, DEFEATED: 0, UNSUPPORTED: 1, WEAK: 2, SUPPORTED: 3}
GLYPH = {UNDEVELOPED: "◇", DEFEATED: "✗", UNSUPPORTED: "✗", WEAK: "~", SUPPORTED: "✔"}

# ---------------------------------------------------------------------------
# Evidence kinds (R8/R9). SACM keeps *what kind of thing was done* separate from
# *how strong the result was*: a claim discharged by kernel-checked proof and one
# discharged by 104 passing test cases are not the same assertion even when both
# reach threshold. The trust ledger already draws this line — it prints
# `NOT PROVED : transpiler faithfulness` — so the assurance case must draw it too
# rather than blurring test evidence into a green tick that reads as proof.
# ---------------------------------------------------------------------------
PROOF = "PROOF"       # kernel-checked; holds for all inputs
TEST = "TEST"         # sampled execution against an independent oracle
STATIC = "STATIC"     # computed from the artifact itself; an upper bound (§17)

# A claim quantified over a population may only be SUPPORTED when the evidence
# actually touches all of that population. Below that, either narrow the claim
# (preferred) or cap the status.
COVERAGE_FULL = 1.0
COVERAGE_WEAK = 0.80   # ≥ this, a population claim may reach WEAK; below, UNSUPPORTED


def coverage_cap(status, covered, population):
    """R8: bound a population-quantified claim by the fraction of its subject the
    evidence exercised. Returns (status, coverage-fraction or None).

    This is the defect this function exists to prevent: `divergences == 0` over 104
    cases touching 92 of 238 functions said nothing whatsoever about the other 146,
    yet flipped the claim to SUPPORTED. Support is now bounded by coverage.
    """
    if not population:
        return status, None
    frac = (covered or 0) / population
    if frac >= COVERAGE_FULL:
        cap = SUPPORTED
    elif frac >= COVERAGE_WEAK:
        cap = WEAK
    else:
        cap = UNSUPPORTED
    return (status if ORDER[status] <= ORDER[cap] else cap), frac


def weakest(statuses):
    """Conjunctive combination: an argument is as strong as its weakest leg.

    UNDEVELOPED and DEFEATED both sit at rank 0 but are not the same thing, so tie-break
    toward DEFEATED — a refuted leg is worse news than an unexamined one.
    """
    statuses = list(statuses)
    if not statuses:
        return UNDEVELOPED
    lo = min(ORDER[s] for s in statuses)
    if lo == 0:
        return DEFEATED if DEFEATED in statuses else UNDEVELOPED
    return next(s for s in statuses if ORDER[s] == lo)


# ---------------------------------------------------------------------------
# Case builder — a thin SACM ArgumentPackage / ArtifactPackage emitter.
# ---------------------------------------------------------------------------
class Case:
    def __init__(self, module):
        self.module = module
        self.claims = []
        self.reasoning = []
        self.evidence = []
        self.assumptions = []
        self.links = []
        self.terminology = []
        self._ids = set()

    def _new(self, ident):
        if ident in self._ids:
            n = 2
            while f"{ident}.{n}" in self._ids:
                n += 1
            ident = f"{ident}.{n}"
        self._ids.add(ident)
        return ident

    def claim(self, ident, description, status=UNDEVELOPED, expression=None,
              assumed=False, notes=None, evidence_kind=None, scope=None):
        node = {
            "id": self._new(ident),
            "sacmClass": "Claim",
            "description": description,
            "status": status,
            "assumed": assumed,
            "toBeSupported": status in (UNDEVELOPED, UNSUPPORTED, DEFEATED),
        }
        if expression:
            # Isabelle/SACM: SACM claims admit structured expressions, so a formal
            # statement embeds directly rather than living only in prose.
            node["structuredExpression"] = expression
        if evidence_kind:
            # R9: what discharged this claim — PROOF | TEST | STATIC. A claim
            # discharged by TEST is never a proved claim, however green it is.
            node["evidenceKind"] = evidence_kind
            node["proved"] = evidence_kind == PROOF
        if scope:
            # R8: the subject this claim is quantified over, stated on the node.
            node["scope"] = scope
        if notes:
            node["notes"] = notes
        self.claims.append(node)
        return node["id"]

    def reason(self, ident, description, strategy=None):
        node = {"id": self._new(ident), "sacmClass": "ArgumentReasoning",
                "description": description}
        if strategy:
            node["strategy"] = strategy
        self.reasoning.append(node)
        return node["id"]

    def evid(self, ident, description, artifact=None, value=None, status=None,
             metric=None, evidence_kind=None, scope=None):
        node = {"id": self._new(ident), "sacmClass": "ArtifactReference",
                "description": description, "artifact": artifact}
        if evidence_kind:
            node["evidenceKind"] = evidence_kind
        if scope:
            node["scope"] = scope
        if value is not None:
            node["value"] = value
        if metric:
            node["metric"] = metric
        if status:
            node["evaluation"] = status
        self.evidence.append(node)
        return node["id"]

    def assume(self, ident, description, count=None, sites=None):
        node = {"id": self._new(ident), "sacmClass": "Claim", "assumed": True,
                "description": description, "status": "ASSUMED"}
        if count is not None:
            node["occurrences"] = count
        if sites:
            node["exampleSites"] = sites
        self.assumptions.append(node)
        return node["id"]

    def link(self, source, target, kind):
        # kind: SUPPORTS | COUNTERS (AssertedInference / AssertedEvidence /
        # AssertedContext / AssertedChallenge in full SACM)
        self.links.append({"sacmClass": "AssertedRelationship", "type": kind,
                           "source": source, "target": target})

    def term(self, name, definition):
        self.terminology.append({"sacmClass": "TerminologyElement", "name": name,
                                 "definition": definition})


# ---------------------------------------------------------------------------
# Artifact loading
# ---------------------------------------------------------------------------
def load_json(path):
    try:
        with open(path) as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return None


def sha256(path):
    try:
        with open(path, "rb") as fh:
            return hashlib.sha256(fh.read()).hexdigest()
    except OSError:
        return None


def walk_holes(node, out, path="body"):
    """Collect holes by label. `hole` is an Expr hole, `holeS` a Stmt hole; both carry
    the CPG node label that produced them, which is what makes them nameable."""
    if isinstance(node, dict):
        if node.get("k") in ("hole", "holeS"):
            out.append((node.get("label", "<unlabelled>"), node["k"]))
        for k, v in node.items():
            walk_holes(v, out, f"{path}.{k}")
    elif isinstance(node, list):
        for i, v in enumerate(node):
            walk_holes(v, out, f"{path}[{i}]")


def analyse_ast(ast):
    """-> (total functions, hole-free functions, Counter(label -> count), label -> fns)"""
    total = len(ast)
    holefree = 0
    labels = collections.Counter()
    sites = collections.defaultdict(list)
    kinds = {}
    for fn in ast:
        found = []
        walk_holes(fn.get("body"), found)
        if not found:
            holefree += 1
        for label, kind in found:
            labels[label] += 1
            kinds[label] = kind
            if len(sites[label]) < 5 and fn.get("name") not in sites[label]:
                sites[label].append(fn.get("name"))
    return total, holefree, labels, sites, kinds


# ---------------------------------------------------------------------------
# The argument
# ---------------------------------------------------------------------------
def build_case(module, root):
    paths = {
        "ast": os.path.join(root, f"ast-{module}.json"),
        "graph": os.path.join(root, "formalization-graph.json"),
        "conformance": os.path.join(root, "conformance.json"),
        "mutation": os.path.join(root, "mutation.json"),
        # The Lean-side trust ledger: call closure and dynamic-hole risk, which the
        # AST alone cannot report (STRATEGY.md §17).
        "ledger": os.path.join(root, f"ledger-{module}.json"),
        "axioms": os.path.join(root, "axioms.json"),
        # Contract-relative theorems: which results are conditional, on what, and
        # whether the conditions are known to be satisfiable (scripts/emit_contracts.py).
        "contracts": os.path.join(root, f"contracts-{module}.json"),
        # Fallback: the repo-wide audit sweep, if the per-module axiom dump is absent.
        "audit": os.path.join(root, "audit.json"),
    }
    art = {k: load_json(p) for k, p in paths.items()}
    present = {k: p for k, p in paths.items() if art[k] is not None}

    c = Case(module)
    c.term("hole", "A construct the transpiler could not translate. Tagged with the CPG "
                   "node label that produced it. Holes are the effect boundary: "
                   "ignorance, distinct from both a value and from non-termination.")
    c.term("verifiable core", "The hole-free functions of a module — the only ones whose "
                              "behaviour the semantics determines unconditionally.")
    c.term("conformance rate", "Fraction of differential test cases on which the Lean "
                               "Core interpreter and the real runtime agree.")
    c.term("tested, not proved", "A claim discharged by sampled execution against an "
                                 "independent oracle. It is real evidence — it is how "
                                 "floored modulo, short-circuit evaluation and name "
                                 "mangling were caught — but it quantifies over the "
                                 "sample, not over all inputs. The trust ledger prints "
                                 "this as `NOT PROVED : transpiler faithfulness`.")
    c.term("coverage of a claim", "The fraction of the subject a claim is quantified over "
                                  "that its evidence actually touched. A claim's status "
                                  "is bounded by it (rule R8): 104 agreeing cases over 92 "
                                  "of 238 functions say nothing about the other 146.")
    c.term("axiom basis", "The axioms the kernel-checked proofs actually depend on; "
                          "`sorryAx` in the basis defeats proof validity outright.")

    # ---- Top claim ---------------------------------------------------------
    top = c.claim(
        "G1", f"Module {module} behaves as specified.",
        expression=f"∀ f ∈ {module}, ∀ σ, evalStmt f σ ≈ spec_f σ")

    strat = c.reason(
        "S1",
        "Argue over the four independent ways the pipeline can be wrong: the semantics "
        "may not match the runtime (faithfulness); the translation may be incomplete "
        "(coverage); the specification may be vacuous (adequacy); the proof may rest on "
        "an unsound basis (validity). All four must hold.",
        strategy="argument by decomposition over failure modes (STRATEGY.md §5)")
    c.link(strat, top, "SUPPORTS")

    sub_status = {}

    # ---- G2 faithfulness ---------------------------------------------------
    # R1 + R8 + R9. Three separate questions, previously collapsed into one tick:
    #   (a) did the compared cases agree?            -> case-level result
    #   (b) how much of the subject was compared?    -> coverage (R8)
    #   (c) what kind of evidence is that?           -> TEST, not PROOF (R9)
    # The old rule answered only (a) and emitted SUPPORTED for a claim quantified
    # over "the translated functions" on evidence touching 39% of them, which also
    # contradicted the trust ledger's `NOT PROVED : transpiler faithfulness`.
    g2 = "G2"
    conf = art["conformance"]
    faith_children = []
    if conf is None:
        st = UNDEVELOPED
        notes = "conformance.json absent — no differential run for this module."
        cid = c.claim(g2, "The Lean Core semantics + transpiler agree with the real "
                          "runtime on the translated functions.", st, notes=notes)
    else:
        total = conf.get("total", 0) or 0
        agree = conf.get("agree", 0) or 0
        div = conf.get("divergences", 0) or 0
        rate = (agree / total) if total else 0.0
        tag = conf.get("module")
        covered = conf.get("functions_covered")
        population = conf.get("functions_total") or 0
        notes = []
        # (a) case-level result on the cases that were actually compared.
        if total == 0:
            case_st = UNSUPPORTED
            notes.append("zero comparable cases: a vacuous oracle is not evidence, it is "
                         "an untested claim wearing a green tick.")
        elif div > 0:
            case_st = DEFEATED
            notes.append(f"{div} divergence(s) — the semantics is refuted on this corpus.")
        elif rate >= 1.0:
            case_st = SUPPORTED
        else:
            case_st = UNSUPPORTED
        # Provenance (unchanged rule): unattributable evidence cannot support a claim
        # about this subject.
        if tag is None:
            if ORDER[case_st] >= ORDER[WEAK]:
                case_st = WEAK
            notes.append("conformance.json carries no module tag; provenance unconfirmed.")
        elif tag != module:
            case_st = UNDEVELOPED
            notes.append(f"conformance.json is tagged module={tag!r}, not {module!r}.")

        e = c.evid("E1", f"Differential conformance vs {conf.get('runtime', '?')}: "
                         f"{agree}/{total} agree, {div} divergence(s), over "
                         f"{covered if covered is not None else '?'}/"
                         f"{population or '?'} functions.",
                   artifact="conformance.json", value=conf, metric="conformance-rate",
                   evidence_kind=TEST,
                   scope={"functionsExercised": covered, "functionsTotal": population})

        off_subject = tag is not None and tag != module
        # (b) narrow the claim to what the evidence covers. Narrowing keeps the claim
        # *true*; weakening the status of an over-broad claim leaves a false claim on
        # the page with a hedge attached.
        n_cov = 0 if off_subject else (covered if covered is not None else 0)
        population = 0 if off_subject else population
        remainder = max((population or 0) - n_cov, 0)
        exercised = None if off_subject else c.claim(
            "G2.1",
            f"On the {n_cov} function(s) the differential harness actually exercised, "
            f"the Lean Core semantics + transpiler agree with the real runtime "
            f"({agree}/{total} cases, {div} divergence(s)).",
            case_st, evidence_kind=TEST,
            scope={"functionsExercised": n_cov, "functionsTotal": population,
                   "quantifiedOver": "exercised subset"},
            notes="TESTED, NOT PROVED: this is sampled execution against CPython, not a "
                  "theorem. It is the same fact the trust ledger reports as "
                  "`NOT PROVED : transpiler faithfulness — see conformance.json`. "
                  "The sample is what caught floored modulo, short-circuit evaluation, "
                  "-INT_MIN and private name mangling (STRATEGY.md §19, §26).")
        faith_children.append(case_st)

        if exercised is not None:
            c.link(e, exercised,
                   "SUPPORTS" if case_st in (SUPPORTED, WEAK) else "COUNTERS")
        if remainder > 0:
            rest_st = UNDEVELOPED
            c.claim("G2.2",
                    f"On the remaining {remainder} translated function(s), never reached "
                    f"by any differential case, the semantics agrees with the runtime.",
                    rest_st, evidence_kind=None,
                    scope={"functionsExercised": 0, "functionsTotal": remainder},
                    notes="No evidence of any kind. Untouched by the oracle is not the "
                          "same as correct; the structural ceilings on oracle reach "
                          "(skip_unencodable_args, skip_varargs, skip_self_not_object — "
                          "STRATEGY.md §27) bound this independently of translation "
                          "coverage.")
            faith_children.append(rest_st)

        # (c) the population-level claim is the conjunction of the two, and separately
        # capped by coverage so the number is on the node even when a leg is missing.
        pop_st, frac = coverage_cap(weakest(faith_children), n_cov, population)
        st = pop_st
        if frac is not None:
            notes.append(f"coverage {n_cov}/{population} = {frac:.1%} of the quantified "
                         f"subject; R8 caps a population claim at its coverage.")
        cid = c.claim(g2, "The Lean Core semantics + transpiler agree with the real "
                          "runtime on the translated functions.", st,
                      evidence_kind=TEST,
                      scope={"functionsExercised": n_cov, "functionsTotal": population,
                             "coverage": frac},
                      notes=" ".join(notes) or None)
        if exercised is None:
            c.link(e, cid, "COUNTERS")
        for child in ("G2.1", "G2.2"):
            if any(n["id"] == child for n in c.claims):
                c.link(child, cid, "SUPPORTS")
        if total == 0:
            d = c.claim("D1", "Differential coverage is empty for this module, so "
                              "faithfulness is untested rather than confirmed "
                              "(STRATEGY.md §13 Tier 2.3).", UNSUPPORTED)
            c.link(d, cid, "COUNTERS")
        elif frac is not None and frac < COVERAGE_FULL:
            # A defeater with teeth: it is not decorative, it is what holds G2 down.
            d = c.claim("D2",
                        f"Coverage defeater: {population - n_cov} of {population} "
                        f"functions are unexercised, so no differential result can speak "
                        f"for them. Undefeated.", UNSUPPORTED)
            c.link(d, cid, "COUNTERS")
    sub_status[g2] = st
    c.link(cid, strat, "SUPPORTS")
    faithful_id = cid

    # ---- G3 coverage -------------------------------------------------------
    ast = art["ast"]
    if ast is None:
        st = UNDEVELOPED
        cov = c.claim("G3", f"Every function of {module} is translated without holes.",
                      st, notes=f"ast-{module}.json absent.")
        fn_total = holefree = 0
        labels, sites, kinds = collections.Counter(), {}, {}
    else:
        fn_total, holefree, labels, sites, kinds = analyse_ast(ast)
        nholes = sum(labels.values())
        frac = holefree / fn_total if fn_total else 0.0
        st = SUPPORTED if nholes == 0 else UNSUPPORTED
        cov = c.claim(
            "G3", f"Every function of {module} is translated without holes.", st,
            expression="∀ f ∈ module, holeFree f",
            notes=None if nholes == 0 else
            f"{fn_total - holefree}/{fn_total} functions contain at least one hole; "
            f"{nholes} hole occurrences across {len(labels)} distinct causes. Only the "
            f"{holefree}-function verifiable core is unconditionally analysable.")
        c.evid("E2", f"Verifiable core: {holefree}/{fn_total} functions hole-free "
                     f"({frac:.1%}); {nholes} hole occurrences.",
               artifact=f"ast-{module}.json",
               value={"functions": fn_total, "holeFree": holefree,
                      "holeOccurrences": nholes, "distinctCauses": len(labels)},
               metric="verifiable-core-fraction", status=st)
        c.link("E2", cov, "SUPPORTS" if st == SUPPORTED else "COUNTERS")

        # The key move: each hole label becomes an explicit named Assumption.
        for label, n in labels.most_common():
            aid = c.assume(
                "A." + label.replace(" ", "-"),
                f"Assumed: no behaviour of {module} depends on `{label}` "
                f"({'statement' if kinds.get(label) == 'holeS' else 'expression'} "
                f"position). The transpiler could not translate it; the semantics "
                f"returns a hole rather than a value.",
                count=n, sites=sites.get(label))
            c.link(aid, cov, "SUPPORTS")
            c.link(aid, top, "SUPPORTS")

        # ---- Contract-relative theorems ------------------------------------
        # A theorem proved under a contract is a *conditional* claim, and the condition
        # belongs to that theorem, not to the module: discharging `op:starredUnpack` for
        # one function says nothing about the other 32 occurrences. So each `relativeTo`
        # entry becomes an Assumption attached to the theorem's own claim, and is NOT
        # linked to the top goal the way a module-wide hole assumption is.
        #
        # Two rules, both from theorems in `Autoform/Contracts.lean` rather than taste:
        #
        #   `refinesUnder_of_unsatisfiable` — an unsatisfiable contract environment
        #   proves EVERY spec. So `satisfiable: false` is a disqualification, not a
        #   caveat: the claim is recorded DEFEATED and linked COUNTERS, because it
        #   carries no information at all.
        #
        #   `methodkey_not_refinable_under_top` — `topContract` ("the hole may do
        #   anything") is satisfiable and still proves nothing. So `satisfiable: true`
        #   is necessary and NOT sufficient, and this consumer must not treat it as a
        #   green light on its own.
        con = art.get("contracts")
        if isinstance(con, dict) and con.get("module") == module:
            ths = con.get("theorems") or []
            # The parent cannot outrank its children. A first cut had this SUPPORTED
            # whenever any contract-relative theorem existed, so a DEFEATED child sat
            # under a green parent — the same shape as a metric computed from the
            # artifact it describes. Status is the weakest of the children.
            nsat = sum(1 for t in ths if not t.get("satisfiable"))
            cong = c.claim(
                "G.CONTRACT",
                f"Every contract-relative result about {module} is recorded as "
                f"conditional, with its assumptions attached to the theorem that "
                f"carries them ({len(ths)} such theorems"
                + (f"; {nsat} with NO satisfiability proof and therefore vacuous)."
                   if nsat else ")."),
                status=(UNDEVELOPED if not ths
                        else DEFEATED if nsat else SUPPORTED),
                evidence_kind=PROOF, scope=module)
            c.link(cong, top, "SUPPORTS")
            c.reason("R.CONTRACT",
                     "A contract-relative theorem and an unconditional one are "
                     "different claims. Satisfiability of the contract environment is "
                     "necessary for the former to say anything "
                     "(`refinesUnder_of_unsatisfiable`) and is not sufficient "
                     "(`methodkey_not_refinable_under_top`).",
                     strategy="argument-over-assumptions")
            for t in ths:
                name = t.get("theorem", "?")
                rel = t.get("relativeTo") or []
                sat = bool(t.get("satisfiable"))
                proof = t.get("satisfiabilityProof")
                short = name.rsplit(".", 1)[-1]
                tid = c.claim(
                    "G.CONTRACT." + short,
                    f"`{name}` holds relative to {len(rel)} contract(s). "
                    + (f"Satisfiability proved by `{proof}`."
                       if sat else
                       "NO satisfiability proof: by `refinesUnder_of_unsatisfiable` an "
                       "unsatisfiable environment proves every spec, so this theorem "
                       "carries no information."),
                    status=SUPPORTED if sat else DEFEATED,
                    evidence_kind=PROOF, scope=name)
                c.link(tid, cong, "SUPPORTS" if sat else "COUNTERS")
                for a in rel:
                    lbl = a.get("label", "?")
                    aid2 = c.assume(
                        f"A.{short}.{lbl}".replace(" ", "-"),
                        f"Assumed of `{name}` only: the hole `{lbl}` satisfies "
                        f"\"{a.get('statement', '')}\" at fuel >= "
                        f"{a.get('fuelBound', '?')}. This is an assumption of THIS "
                        f"theorem, not of {module}: the same label occurs elsewhere "
                        f"and is not discharged there.",
                        count=1)
                    # Attached to the theorem's goal, never to the module's top goal.
                    c.link(aid2, tid, "SUPPORTS")
        # ---- The restricted core -------------------------------------------
        # §17: static hole-freedom is an UPPER BOUND, not a guarantee — the
        # interpreter introduces holes at runtime that the AST cannot show. So the
        # honest restricted claim is the call-closed core from the Lean ledger, and
        # even that is a *static* claim; runtime hole-freedom is a separate goal.
        led = art["ledger"]
        led_ok = isinstance(led, dict) and (led.get("module") == module)
        closed = led.get("verifiableCore") if led_ok else None
        risk = led.get("dynamicHoleRisk") if led_ok else None
        if led_ok:
            led_fns = led.get("functions") or fn_total
            c.evid("E6", f"Trust ledger: {closed}/{led_fns} functions hole-free AND "
                         f"call-closed; dynamic-hole risk {risk} constructs may hole at "
                         f"runtime.",
                   artifact=f"ledger-{module}.json",
                   value={"verifiableCore": closed, "functions": led_fns,
                          "holeFree": led.get("holeFree"),
                          "dynamicHoleRisk": risk},
                   metric="call-closed-core", evidence_kind=STATIC,
                   status=None)

        core_n = closed if closed is not None else holefree
        core_st = SUPPORTED if core_n else UNSUPPORTED
        core_notes = None
        if closed is None:
            # Without call closure, "hole-free" counts functions whose behaviour is
            # entirely unknown (a call to an untranslated function is indistinguishable
            # in the AST from a call to a translated one — §17). Cap accordingly.
            core_st = weakest([core_st, WEAK])
            core_notes = (f"ledger-{module}.json absent or off-subject: call closure "
                          f"unverified, so {holefree} is the static upper bound, not the "
                          f"verifiable core (STRATEGY.md §17).")
        core = c.claim(
            "G3.1",
            f"The {core_n}-function core of {module} is hole-free and call-closed in the "
            f"AST — i.e. statically free of untranslated constructs.",
            core_st, evidence_kind=STATIC,
            scope={"functions": core_n, "functionsTotal": fn_total,
                   "quantifiedOver": "call-closed core"},
            notes=core_notes)
        c.link(core, cov, "SUPPORTS")
        if led_ok:
            c.link("E6", core, "SUPPORTS")

        # G3.2 — the claim people actually read G3.1 as making. Static analysis cannot
        # discharge it; only execution can, and execution has covered 39% of the module.
        exec_cov = (art["conformance"] or {}).get("functions_covered") \
            if isinstance(art["conformance"], dict) else None
        if risk == 0:
            dyn_st, dyn_frac = SUPPORTED, None
            dyn_note = "no construct in the module can hole at runtime."
        else:
            dyn_st, dyn_frac = coverage_cap(WEAK, exec_cov or 0, fn_total)
            dyn_note = (f"{risk if risk is not None else 'an unreported number of'} "
                        f"constructs are input-dependent and may hole at runtime; only "
                        f"execution can settle this, and the differential harness has "
                        f"reached {exec_cov if exec_cov is not None else 0}/{fn_total} "
                        f"functions. Static hole-freedom is an upper bound "
                        f"(STRATEGY.md §17, §19).")
        dyn = c.claim(
            "G3.2",
            f"The core of {module} is hole-free at RUNTIME: no execution of it reaches a "
            f"hole on any input.",
            dyn_st, evidence_kind=TEST if risk != 0 else STATIC,
            scope={"functionsExercised": exec_cov or 0, "functionsTotal": fn_total,
                   "coverage": dyn_frac},
            notes=dyn_note)
        c.link(dyn, cov, "SUPPORTS")
        if dyn_st != SUPPORTED:
            d3 = c.claim("D3", "Upper-bound defeater: `Func.total` is computed from the "
                               "same AST it describes, so it cannot see holes the "
                               "interpreter introduces. Undefeated except where "
                               "execution has looked.", UNSUPPORTED)
            c.link(d3, core, "COUNTERS")
    sub_status["G3"] = st
    c.link(cov, strat, "SUPPORTS")

    # ---- G4 specification adequacy ----------------------------------------
    mut = art["mutation"]
    if mut is None:
        st = UNDEVELOPED
        spec = c.claim("G4", "The specifications are non-vacuous: they constrain "
                             "behaviour strongly enough that perturbing the program "
                             "breaks them.", st,
                       notes="mutation.json absent — source-level mutation gate unbuilt "
                             "(STRATEGY.md §13 Tier 3). Dependency-vacuity alone is "
                             "necessary but not sufficient.")
    else:
        # scripts/mutate.py writes {"theorems": {name: {killed, survived, ...}}, ...};
        # a plain list of per-mutant rows is also accepted.
        mut_mod = (mut or {}).get("module") or ""
        # Provenance, same rule already applied to conformance.json: evidence that cannot
        # be attributed to this subject cannot support a claim about this subject. The
        # mutation gate currently runs over the Imp reference semantics, not over
        # translated modules, so its score is real but off-subject.
        mut_attributable = module.lower() in mut_mod.lower() if mut_mod else False
        if mut and not mut_attributable:
            killed, tot = 0, 0
            st = UNDEVELOPED
            spec = c.claim("G4", "The specifications are non-vacuous.", st,
                           notes=(f"mutation.json covers module '{mut_mod}', not "
                                  f"'{module}'. The score is real but OFF-SUBJECT: the "
                                  "mutation gate runs over the Imp reference semantics, "
                                  "not over translated modules. Borrowing it would repeat "
                                  "the provenance defect already flagged on "
                                  "conformance.json."))
            c.evid("E3", f"Mutation evidence exists but is scoped to '{mut_mod}'; "
                         f"no mutation evidence for '{module}'.",
                   artifact="mutation.json", value={"module": mut_mod},
                   metric="mutation-score", status=UNDEVELOPED)
            c.link("E3", spec, "COUNTERS")
        else:
            if isinstance(mut, dict) and isinstance(mut.get("theorems"), dict):
                thm = mut["theorems"].values()
                killed = sum(r.get("killed", 0) for r in thm)
                tot = killed + sum(r.get("survived", 0) for r in thm)
            else:
                rows = mut if isinstance(mut, list) else (mut.get("mutants") or [])
                killed = sum(1 for r in rows if r.get("killed"))
                tot = len(rows)
            score = killed / tot if tot else 0.0
            st = SUPPORTED if tot and score >= 1.0 else (UNSUPPORTED if tot else UNDEVELOPED)
            spec = c.claim("G4", "The specifications are non-vacuous.", st,
                           notes=None if st == SUPPORTED else
                           f"{tot - killed} mutant(s) survived: those theorems do not "
                           f"constrain the behaviour they appear to.")
            c.evid("E3", f"Mutation score: {killed}/{tot} mutants killed ({score:.1%}).",
                   artifact="mutation.json",
                   value={"killed": killed, "total": tot}, metric="mutation-score",
                   evidence_kind=TEST, status=st)
            c.link("E3", spec, "SUPPORTS" if st == SUPPORTED else "COUNTERS")
    sub_status["G4"] = st
    c.link(spec, strat, "SUPPORTS")

    # ---- G5 proof validity -------------------------------------------------
    ax = art["axioms"]
    ax_file = "axioms.json"
    if ax is None and isinstance(art["audit"], dict) and art["audit"].get("axiom_sweep"):
        # Normalise the repo-wide audit sweep into the same shape.
        sweep = art["audit"]["axiom_sweep"]
        ax = {"axioms": sorted((sweep.get("axiom_histogram") or {})
                               or sweep.get("declared_axioms") or []),
              "theorems": sweep.get("declarations") or 0,
              "leaks": sweep.get("leaks") or [],
              "source": "audit.json:axiom_sweep (repo-wide, not module-scoped)"}
        ax_file = "audit.json"
    if ax is None:
        st = UNDEVELOPED
        pv = c.claim("G5", "All theorems about this module are kernel-checked and depend "
                           "on no unsound axiom (in particular no `sorryAx`).", st,
                     notes="axioms.json absent — `#audit_axioms` output not captured for "
                           "this module. No theorems are recorded either "
                           "(STRATEGY.md §13 Tier 3: the verification half does not exist).")
    else:
        used = ax.get("axioms", ax if isinstance(ax, list) else [])
        thms = ax.get("theorems", 0)
        # `declarations` is a count in audit.json but a list in other producers; accept both.
        n_thms = len(thms) if hasattr(thms, "__len__") else int(thms or 0)
        bad = [a for a in used if "sorry" in str(a).lower()]
        bad += [l for l in (ax.get("leaks") or []) if l not in bad]
        if bad:
            st = DEFEATED
        elif n_thms:
            st = SUPPORTED
        else:
            st = UNSUPPORTED
        # R4 + R8: the sweep in audit.json is REPO-wide, not module-scoped. Same
        # standard already applied to conformance.json (untagged) and mutation.json
        # (off-subject): evidence that cannot be attributed to this subject cannot
        # fully support a claim about this subject. Here the evidence is not
        # off-subject — the module is interpreted by the very environment that was
        # swept — so it is not UNDEVELOPED; but it is not module-scoped either, and
        # no module-specific theorem set exists, so it is capped at WEAK and the
        # part that *is* earned is asserted as a narrowed sibling.
        repo_scoped = ax_file != "axioms.json"
        g5_notes = [f"sorryAx present: {bad}"] if bad else \
            ([] if n_thms else ["no theorems recorded — nothing to validate."])
        if repo_scoped and not bad:
            if ORDER[st] >= ORDER[WEAK]:
                st = WEAK
            g5_notes.append(
                f"the {n_thms} declaration(s) swept are repo-wide (audit.json), not "
                f"theorems about {module}: no module-scoped `#audit_axioms` dump exists, "
                f"so nothing here is attributable to this module in particular. "
                f"Capped at WEAK by the same provenance rule applied to conformance.json "
                f"and mutation.json.")
        pv = c.claim("G5", "All theorems about this module are kernel-checked and depend "
                           "on no unsound axiom.", st,
                     evidence_kind=PROOF,
                     scope={"scopedTo": "repository" if repo_scoped else module,
                            "declarations": n_thms},
                     notes=" ".join(g5_notes) or None)
        c.evid("E4", f"Axiom basis: {', '.join(map(str, used)) or 'none'} "
                     f"over {n_thms} theorem/declaration(s)"
                     + (f"; source: {ax['source']}" if ax.get("source") else "") + ".",
               artifact=ax_file, value={"axioms": used, "theorems": n_thms},
               metric="axiom-basis", evidence_kind=PROOF,
               scope={"scopedTo": "repository" if repo_scoped else module}, status=st)
        c.link("E4", pv, "SUPPORTS" if st in (SUPPORTED, WEAK) else "COUNTERS")
        if repo_scoped:
            # The narrowed claim that the sweep does earn, stated as true rather than
            # hedged: it is about the repository, and it is about the repository that
            # this module's semantics lives in.
            repo_st = DEFEATED if bad else (SUPPORTED if n_thms else UNSUPPORTED)
            chk = (art["audit"] or {}).get("lean4checker") \
                if isinstance(art["audit"], dict) else None
            g51 = c.claim(
                "G5.1",
                f"The Autoform repository's {n_thms} kernel-checked declaration(s) — "
                f"which include the Core semantics this module is interpreted by — rest "
                f"only on {', '.join(map(str, used)) or 'no'} axiom(s), with no leak.",
                repo_st, evidence_kind=PROOF,
                scope={"scopedTo": "repository", "declarations": n_thms},
                notes=(f"lean4checker: {chk.get('status')} ({chk.get('mode')})"
                       if isinstance(chk, dict) else None))
            c.link(g51, pv, "SUPPORTS")
            c.claim("C2", "Context: audit.json's axiom sweep is repo-wide. It bounds the "
                          "axiom basis of everything in the repository, including this "
                          "module's semantics, but it is not evidence about theorems "
                          "specific to this module — there are none.",
                    assumed=True, status="ASSUMED")
    sub_status["G5"] = st
    c.link(pv, strat, "SUPPORTS")

    # ---- Roll up -----------------------------------------------------------
    top_status = weakest(sub_status.values())
    # Holes are an independent blocker on the *top* claim: an argument resting on
    # assumptions cannot assert unconditional behaviour, whatever the sub-claims say.
    blockers = []
    if sum(labels.values()) if labels else 0:
        blockers.append(f"{sum(labels.values())} unresolved holes carried as assumptions")
        top_status = weakest([top_status, UNSUPPORTED])
    if sub_status.get("G2") != SUPPORTED:
        blockers.append("translation faithfulness not established over the whole module "
                        "(see G2 coverage)")
    # R9: even a fully-covering differential run is TEST evidence. G1 asserts behaviour
    # for all inputs; sampled execution cannot discharge that, so the top claim carries
    # the distinction the trust ledger prints as `NOT PROVED : transpiler faithfulness`.
    g2_node = next((n for n in c.claims if n["id"] == "G2"), None)
    if g2_node is not None and g2_node.get("evidenceKind") == TEST:
        blockers.append("transpiler faithfulness is TESTED, not PROVED "
                        "(agrees with the trust ledger's NOT PROVED line)")
        top_status = weakest([top_status, WEAK])
    for node in c.claims:
        if node["id"] == top:
            node["status"] = top_status
            node["toBeSupported"] = top_status != SUPPORTED
            node["assertable"] = top_status == SUPPORTED
            node["blockers"] = blockers
            break

    # ---- Population context from the formalization graph -------------------
    graph = art["graph"]
    if graph is not None:
        rows = [r for r in graph if isinstance(r, dict)]
        pure = sum(1 for r in rows if r.get("pure"))
        eff = collections.Counter(e for r in rows for e in (r.get("effects") or []))
        c.evid("E5", f"Cartography: {len(rows)} functions, {pure} flagged pure; "
                     f"effects {dict(eff.most_common(5))}.",
               artifact="formalization-graph.json",
               value={"functions": len(rows), "pure": pure,
                      "effects": dict(eff.most_common())},
               metric="population-context")
        c.link("E5", strat, "SUPPORTS")
        c.claim("C1", "Context: the formalization graph is not module-scoped; it "
                      "describes the whole parsed corpus.", assumed=True, status="ASSUMED")

    meta = {
        "module": module,
        "artifactsPresent": sorted(present),
        "artifactsMissing": sorted(set(paths) - set(present)),
        "counts": {"functions": fn_total, "holeFree": holefree,
                   "holeOccurrences": sum(labels.values()) if labels else 0,
                   "distinctHoleCauses": len(labels)},
        "subClaimStatus": sub_status,
        "topStatus": top_status,
    }
    return c, meta, paths, present


# ---------------------------------------------------------------------------
# Serialization
# ---------------------------------------------------------------------------
def to_sacm(c, meta):
    return {
        "sacmVersion": SACM_PROFILE,
        "id": f"AssuranceCase:{c.module}",
        "generatedBy": {"tool": TOOL, "version": TOOL_VERSION},
        "generatedAt": datetime.datetime.now(datetime.timezone.utc)
                       .replace(microsecond=0).isoformat(),
        "summary": meta,
        "argumentPackage": {
            "claims": c.claims,
            "argumentReasoning": c.reasoning,
            "assumptions": c.assumptions,
            "assertedRelationships": c.links,
        },
        "artifactPackage": {"artifactReferences": c.evidence},
        "terminologyPackage": {"terms": c.terminology},
    }


def to_intoto(case, module, paths, present):
    """in-toto/SLSA-style envelope: subject (what is being talked about, with digests)
    + predicate (what is being said about it). STRATEGY.md §10: transport stays in-toto,
    the payload is SACM."""
    subject = []
    for key in sorted(present):
        p = paths[key]
        d = sha256(p)
        if d:
            subject.append({"name": os.path.basename(p), "digest": {"sha256": d}})
    return {
        "_type": "https://in-toto.io/Statement/v1",
        "subject": subject or [{"name": f"module:{module}", "digest": {}}],
        "predicateType": PREDICATE_TYPE,
        "predicate": case,
    }


def render_markdown(c, meta):
    L = []
    st = meta["topStatus"]
    L.append(f"# Assurance case — {c.module}\n")
    L.append(f"*{SACM_PROFILE}; envelope in-toto Statement v1. "
             f"Generated by `{TOOL}`.*\n")
    L.append(f"**Top claim: {GLYPH[st]} {st}** — "
             f"`G1: module {c.module} behaves as specified.`\n")
    top = next(n for n in c.claims if n["id"] == "G1")
    if top.get("blockers"):
        L.append("Not assertable because:\n")
        for b in top["blockers"]:
            L.append(f"- {b}")
        L.append("")

    byid = {n["id"]: n for n in c.claims}
    ev_for = collections.defaultdict(list)
    for e in c.evidence:
        ev_for[e["id"]] = e
    tgt = collections.defaultdict(list)
    for l in c.links:
        tgt[l["target"]].append(l)

    L.append("## Argument tree\n")
    L.append("```")
    L.append(f"{GLYPH[st]} G1  module {c.module} behaves as specified   [{st}]")
    L.append("└── S1  argue over the four failure modes")
    order = ["G2", "G2.1", "G2.2", "G3", "G3.1", "G3.2", "G4", "G5", "G5.1"]
    for cid in order:
        n = byid.get(cid)
        if not n:
            continue
        s = n["status"]
        indent = "    │   └── " if "." in cid else "    ├── "
        kind = n.get("evidenceKind")
        cov = (n.get("scope") or {}).get("coverage")
        tail = f"  [{s}"
        if kind:
            tail += f"; {kind}"
        if cov is not None:
            tail += f"; coverage {cov:.1%}"
        tail += "]"
        L.append(f"{indent}{GLYPH.get(s, '?')} {cid}  {n['description']}{tail}")
        for e in c.evidence:
            if any(l["source"] == e["id"] and l["target"] == cid for l in c.links):
                mark = "evidence" if any(
                    l["source"] == e["id"] and l["target"] == cid
                    and l["type"] == "SUPPORTS" for l in c.links) else "counter-evidence"
                L.append(f"    │       ({mark}) {e['id']}: {e['description']}")
        for n2 in c.claims:
            if n2["id"].startswith("D") and any(
                    l["source"] == n2["id"] and l["target"] == cid for l in c.links):
                L.append(f"    │       (defeater) {n2['id']}: {n2['description']}")
        if n.get("notes"):
            L.append(f"    │       (note) {n['notes']}")
    L.append("```\n")

    if c.assumptions:
        L.append(f"## Assumptions carried ({len(c.assumptions)})\n")
        L.append("Every untranslated construct is an explicit assumption of the "
                 "argument, not an omission from it.\n")
        L.append("| Assumption | Occurrences | Example sites |")
        L.append("|---|---|---|")
        for a in sorted(c.assumptions, key=lambda x: -(x.get("occurrences") or 0)):
            sites = ", ".join((a.get("exampleSites") or [])[:2]) or "—"
            L.append(f"| `{a['id']}` | {a.get('occurrences', '—')} | {sites} |")
        L.append("")

    und = [n["id"] for n in c.claims
           if n["status"] == UNDEVELOPED and n["id"] != "G1"]
    bad = [n["id"] for n in c.claims
           if n["status"] in (UNSUPPORTED, DEFEATED) and n["id"] != "G1"]
    L.append("## Trust boundary\n")
    L.append(f"- Verifiable core: **{meta['counts']['holeFree']}/"
             f"{meta['counts']['functions']}** functions hole-free.")
    L.append(f"- Assumptions carried: **{meta['counts']['holeOccurrences']}** hole "
             f"occurrences over **{meta['counts']['distinctHoleCauses']}** distinct causes.")
    L.append(f"- Undeveloped goals: **{', '.join(und) or 'none'}**.")
    L.append(f"- Unsupported/defeated: **{', '.join(bad) or 'none'}**.")
    L.append(f"- Artifacts missing: **{', '.join(meta['artifactsMissing']) or 'none'}**.")
    g2n = byid.get("G2")
    if g2n is not None:
        cov = (g2n.get("scope") or {}).get("coverage")
        L.append(f"- Faithfulness: **TESTED, NOT PROVED**"
                 + (f", over {cov:.1%} of the module's functions" if cov else "")
                 + ". This is the same statement as the trust ledger's "
                   "`NOT PROVED : transpiler faithfulness — see conformance.json`; the "
                   "two artifacts agree.")
    L.append("")
    return "\n".join(L)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--module", required=True)
    ap.add_argument("--out", default=None, help="default sacm-<Module>.json")
    ap.add_argument("--markdown", default=None, help="also write a markdown summary")
    ap.add_argument("--root", default=".", help="directory holding the evidence artifacts")
    ap.add_argument("--quiet", action="store_true")
    a = ap.parse_args(argv)

    c, meta, paths, present = build_case(a.module, a.root)
    case = to_sacm(c, meta)
    stmt = to_intoto(case, a.module, paths, present)

    out = a.out or os.path.join(a.root, f"sacm-{a.module}.json")
    with open(out, "w") as fh:
        json.dump(stmt, fh, indent=2)
        fh.write("\n")

    md = render_markdown(c, meta)
    if a.markdown:
        with open(a.markdown, "w") as fh:
            fh.write(md)
    if not a.quiet:
        print(md)
        print(f"wrote {out}" + (f" and {a.markdown}" if a.markdown else ""))
    # Exit non-zero when the top claim is not assertable: usable as a CI gate.
    return 0 if meta["topStatus"] == SUPPORTED else 1


if __name__ == "__main__":
    sys.exit(main())
