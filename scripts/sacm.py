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
              assumed=False, notes=None):
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
             metric=None):
        node = {"id": self._new(ident), "sacmClass": "ArtifactReference",
                "description": description, "artifact": artifact}
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
        "axioms": os.path.join(root, "axioms.json"),
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
    g2 = "G2"
    conf = art["conformance"]
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
        notes = []
        if total == 0:
            st = UNSUPPORTED
            notes.append("zero comparable cases: the harness only compares module-level "
                         "int→int functions, and this module yielded none. A vacuous "
                         "oracle is not evidence.")
        elif div > 0:
            st = DEFEATED
            notes.append(f"{div} divergence(s) — the semantics is refuted on this corpus.")
        elif rate >= 1.0:
            st = SUPPORTED
        else:
            st = UNSUPPORTED
        if tag is None:
            # Honest provenance: the harness does not stamp the module it ran against,
            # so this artifact cannot be attributed. Never silently assume it is ours.
            if ORDER[st] >= ORDER[WEAK]:
                st = WEAK
            notes.append("conformance.json carries no module tag; provenance unconfirmed "
                         "(it may be from another module's run).")
        elif tag != module:
            st = UNDEVELOPED
            notes.append(f"conformance.json is tagged module={tag!r}, not {module!r}.")
        cid = c.claim(g2, "The Lean Core semantics + transpiler agree with the real "
                          "runtime on the translated functions.", st,
                      notes=" ".join(notes) or None)
        e = c.evid("E1", f"Differential conformance vs {conf.get('runtime', '?')}: "
                         f"{agree}/{total} agree, {div} divergence(s).",
                   artifact="conformance.json", value=conf, metric="conformance-rate")
        c.link(e, cid, "SUPPORTS" if st in (SUPPORTED, WEAK) else "COUNTERS")
        if total == 0:
            d = c.claim("D1", "Differential coverage is empty for this module, so "
                              "faithfulness is untested rather than confirmed "
                              "(STRATEGY.md §13 Tier 2.3).", UNSUPPORTED)
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
        # Sub-claim on the restricted core, which *can* be supported.
        core_st = SUPPORTED if holefree > 0 else UNSUPPORTED
        core = c.claim("G3.1", f"The {holefree}-function verifiable core of {module} is "
                               "hole-free and therefore analysable unconditionally.",
                       core_st)
        c.link(core, cov, "SUPPORTS")
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
                   status=st)
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
        pv = c.claim("G5", "All theorems about this module are kernel-checked and depend "
                           "on no unsound axiom.", st,
                     notes=f"sorryAx present: {bad}" if bad else
                     (None if n_thms else "no theorems recorded — nothing to validate."))
        c.evid("E4", f"Axiom basis: {', '.join(map(str, used)) or 'none'} "
                     f"over {n_thms} theorem/declaration(s)"
                     + (f"; source: {ax['source']}" if ax.get("source") else "") + ".",
               artifact=ax_file, value={"axioms": used, "theorems": n_thms},
               metric="axiom-basis", status=st)
        c.link("E4", pv, "SUPPORTS" if st == SUPPORTED else "COUNTERS")
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
        blockers.append("translation faithfulness not established")
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
    order = ["G2", "G3", "G3.1", "G4", "G5"]
    for cid in order:
        n = byid.get(cid)
        if not n:
            continue
        s = n["status"]
        indent = "    │   └── " if cid == "G3.1" else "    ├── "
        L.append(f"{indent}{GLYPH.get(s, '?')} {cid}  {n['description']}  [{s}]")
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
