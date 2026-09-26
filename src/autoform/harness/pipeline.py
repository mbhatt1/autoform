"""The formalization harness, end to end, for one translated module.

    ingest → CPIR → evidence → generators → critic → judge (typed judgment, listwise
    selection, routing) → verifier (Lean kernel / structural) → judge (counterexample
    classification) → repairs → judge (repair ranking) → reverify … → ledger, report

Invariant: generators and the judge decide *what to try* and *how to read a witness*;
statuses come only from the verifier.
"""
from __future__ import annotations

import json
import subprocess
import time
from dataclasses import dataclass, field
from pathlib import Path

from . import cegis, claims as C, cpir, critic, evidence, ledger, verifier
from .environment import Environment
from .generator import generators
from .judge import CLAIM_JUDGMENTS, DecisionLog, Judge, make_scorer

INTENT_THRESHOLD = 0.8


@dataclass
class Options:
    root: Path
    module: str
    ast: Path | None = None
    source: Path | None = None
    out: Path | None = None
    judge: str = 'semif'
    generators: str = 'template'
    environment: Path | None = None
    functions: list = field(default_factory=list)
    top_k: int = 8
    max_refinements: int = cegis.MAX_REFINEMENTS
    fuel: int = 1000
    timeout: int = 900
    deep_proofs: bool = False
    build: bool = False
    cache: Path | None = None
    temperature: Path | None = None
    native: bool = True


def _git_revision(path: Path | None):
    if not path:
        return None
    try:
        out = subprocess.run(['git', '-C', str(path), 'rev-parse', 'HEAD'], capture_output=True, text=True,
                             timeout=10)
        dirty = subprocess.run(['git', '-C', str(path), 'status', '--porcelain', '--', '.'],
                               capture_output=True, text=True, timeout=30).stdout.strip()
        return dict(revision=out.stdout.strip(), dirty=bool(dirty)) if out.returncode == 0 else None
    except (OSError, subprocess.TimeoutExpired):
        return None


def _find_ast(root: Path, module: str) -> Path:
    for p in (root / 'artifacts/pipeline' / module / f'ast-{module}.json', root / f'ast-{module}.json'):
        if p.is_file():
            return p
    raise FileNotFoundError(f'no ast-{module}.json under {root} or {root}/artifacts/pipeline/{module}; '
                            'translate the source first (autoform source)')


def _state(ctx, implementation=True) -> dict:
    """The judge's view of a function: compact, deterministic, no hidden identifiers.

    Intent questions (which claim is meant?) get the *interface* view — name, signature,
    documentation, tests, callers — and not the body: a judge shown `return True` rates
    "always returns true" as the intended contract. Counterexample questions (is the code
    or the claim wrong?) need the implementation and get it."""
    signature = (f"{ctx['source_name'] or ctx['name']}(" + ', '.join(p['name'] for p in ctx['params'])
                 + f") -> {ctx['return_sort']}")
    view = dict(function=signature, file=ctx['file'], documentation=ctx['doc'][:400],
                callers=ctx['callers'][:8], callees=ctx['callees'][:8],
                externals=[f"{e['name']} ({e['semantics']})" for e in ctx['externals']],
                evidence=[f"{e['type']} @ {e.get('location')}: {e.get('text', '')}"[:160] for e in ctx['evidence'][:10]
                          if implementation or e['type'] != 'guard'])
    if implementation:
        view['implementation'] = ctx['body'][:2000]
    return view


def _judgment_prior(claim, ctx) -> dict:
    p = {k: 0.1 for k in CLAIM_JUDGMENTS}
    ev = C.evidence_score(claim)
    if C.mentions_result(claim['property']):
        p['USEFUL_PROPERTY'] += 0.25
    if ev > 0.3:
        p['USEFUL_PROPERTY'] += 0.2
    if claim['category'] == 'security' and ctx['security_relevant']:
        p['SECURITY_RELEVANT'] += 0.45
    if C.complexity(claim) <= 1:
        p['TRIVIAL'] += 0.25
    if claim.get('dominated_by'):
        p['TOO_WEAK'] += 0.25
    if C.independent_sources(claim) == 0 and claim['provenance'].get('generator') == 'template':
        p['UNSUPPORTED_BY_EVIDENCE'] += 0.2
    if any(f['severity'] == 'warn' for f in claim.get('critic', [])):
        p['LIKELY_VACUOUS'] += 0.2
    return p


def utility(claim, judgment, select_p, coverage) -> float:
    """Utility = α·Evidence + β·SecurityImpact + γ·Coverage + δ·Nontriviality + ε·Selection
               − ζ·AssumptionCost − η·SolverCost."""
    j = judgment or {}
    nontrivial = 1 - j.get('TRIVIAL', 0) - j.get('LIKELY_VACUOUS', 0)
    return round(0.20 * C.evidence_score(claim) + 0.25 * j.get('SECURITY_RELEVANT', 0)
                 + 0.30 * j.get('USEFUL_PROPERTY', 0) + 0.05 * coverage.get('confidence', 0)
                 + 0.10 * nontrivial + 0.25 * select_p
                 - 0.10 * j.get('UNSUPPORTED_BY_EVIDENCE', 0) - 0.08 * len(claim['assumptions'])
                 - 0.05 * bool(claim.get('dominated_by')) - 0.01 * C.complexity(claim), 4)


class Harness:
    def __init__(self, opts: Options):
        self.o = opts
        self.root = Path(opts.root).resolve()
        self.ast_path = Path(opts.ast) if opts.ast else _find_ast(self.root, opts.module)
        self.out = Path(opts.out or self.root / 'artifacts/harness' / opts.module)
        self.out.mkdir(parents=True, exist_ok=True)
        self.program = cpir.build(self.ast_path, opts.module, str(opts.source) if opts.source else None)
        self.env = Environment.load(self.root, opts.environment)
        self.log = DecisionLog(self.out / 'decisions.jsonl')
        temperature = json.loads(Path(opts.temperature).read_text()) if opts.temperature else None
        self.judge = Judge(make_scorer(opts.judge), self.log, temperature)
        self.gens, self.notes = generators(opts.generators)
        self.ledger = ledger.AssumptionLedger()
        self.cache = ledger.ProofCache(opts.cache)
        self.claims = {}         # id -> claim record (validated claim + result + metadata)
        self.rejected = []
        self.review = []
        self.contexts = {}
        with open(self.ast_path) as stream:
            self.bodies = {f['name']: f.get('body') for f in json.load(stream) if isinstance(f, dict)}

    # ---------------------------------------------------------------------------
    def targets(self):
        fns = [f for f in self.program.functions if not f.synthetic]
        if self.o.functions:
            wanted = set(self.o.functions)
            fns = [f for f in fns if f.name in wanted or f.source_name in wanted or f.id in wanted]
        return fns

    def run(self) -> dict:
        started = time.time()
        status = verifier.build_status(self.root, self.o.module, build=self.o.build)
        if not status['ok']:
            raise RuntimeError(status['reason'])
        self.model_sha = status['model_sha256']
        selected = []
        for fn in self.targets():
            selected += self.propose(fn)
        self.verify(selected)
        self.refine([c for c in selected if self.claims[c]['result']['status'] == 'REFUTED'])
        return self.finish(time.time() - started)

    # --- stages 5–8: evidence, generation, critic, judgment, selection, routing --------
    def propose(self, fn) -> list:
        ctx = evidence.context(self.program, self.env, fn, self.o.source)
        self.contexts[fn.id] = ctx
        raw = []
        for g in self.gens:
            raw += g.generate(self.program, fn, ctx)
        for g in self.gens:
            for r in getattr(g, 'rejections', []):
                self.rejected.append(dict(stage='generator', function=fn.name, reason=r['reason']))
        accepted, rejected = critic.screen(raw, self.program)
        self.rejected += [dict(r, function=fn.name) for r in rejected]
        if not accepted:
            return []
        state = _state(ctx, implementation=False)
        texts = [C.render_claim(c, self.program) + (f"\n({c['description']})" if c.get('description') else '')
                 for c in accepted]
        decisions = self.judge.judge_claims(state, texts, [_judgment_prior(c, ctx) for c in accepted],
                                            [dict(claim=c['id'], function=fn.name) for c in accepted])
        judgments = {c['id']: d['probabilities'] for c, d in zip(accepted, decisions)}
        select = self.judge.select(state, [dict(id=c['id'], text=t) for c, t in zip(accepted, texts)],
                                   {c['id']: 0.2 + 0.5 * judgments[c['id']].get('USEFUL_PROPERTY', 0)
                                    + 0.5 * judgments[c['id']].get('SECURITY_RELEVANT', 0) for c in accepted},
                                   dict(function=fn.name))
        # Formalization policy: among mutually exclusive readings, the judge picks the intended one.
        for gi, group in enumerate(critic.rival_groups(accepted, self.program)):
            d = self.judge.intent(state, [dict(id=c['id'], text=t) for c, t in zip(accepted, texts) if c in group],
                                  {c['id']: select.get(c['id'], 0.1) + 0.1 for c in group},
                                  dict(function=fn.name, group=[c['id'] for c in group]))
            winner = next(c for c in group if c['id'] == d['chosen'])
            lits = [v for vals in fn.literals.values() for v in vals]
            for c in group:
                c['intent'] = dict(group=f'{fn.id}/R{gi}', chosen=c['id'] == d['chosen'],
                                   contradicts_intent=c is not winner and critic.rivals(c, winner, lits),
                                   probability=round(d['probabilities'].get(c['id'], 0), 4),
                                   rivals=[x['id'] for x in group if x is not c], decision=d['decision_id'])
        for c in accepted:
            c['judgment'] = dict(probabilities=judgments[c['id']],
                                 label=max(judgments[c['id']], key=judgments[c['id']].get),
                                 selection_probability=round(select.get(c['id'], 0), 4))
            c['utility'] = utility(c, judgments[c['id']], select.get(c['id'], 0), ctx['coverage'])
        ranked = sorted(accepted, key=lambda c: -c['utility'])
        # Prefer claims the judge does not call trivial or vacuous; fill up to top-k by utility.
        weak = lambda c: c['judgment']['label'] in ('TRIVIAL', 'LIKELY_VACUOUS')  # noqa: E731
        intended = [c for c in ranked if (c.get('intent') or {}).get('chosen')]
        chosen = (intended + [c for c in ranked if not weak(c) and c not in intended]
                  + [c for c in ranked if weak(c) and c not in intended])[:max(self.o.top_k, len(intended))]
        for c in ranked:
            if c not in chosen:
                self.register(c, fn, dict(status='NOT_SELECTED',
                                          reason=f"utility {c['utility']} below the top-{self.o.top_k} "
                                                 f"(judged {c['judgment']['label']})"),
                              selected=False)
        for c in chosen:
            self.route(c, fn, state)
        return [c['id'] for c in chosen]

    def route(self, claim, fn, state):
        feasible = verifier.feasible_backends(claim)
        if not feasible:
            self.register(claim, fn, dict(status='UNSUPPORTED',
                                          reason='no available backend expresses: ' +
                                          ', '.join(sorted(C.operators(claim['property'])))))
            return
        d = self.judge.route(state, feasible, {b['id']: 1.0 for b in feasible}, dict(claim=claim['id']))
        claim['backend'] = d['chosen']
        self.register(claim, fn, dict(status='PENDING'))

    def register(self, claim, fn, result, selected=True):
        assumptions = self.env.assumptions_for(self.program, fn, claim)
        claim['assumption_ids'] = [a['id'] for a in assumptions]
        self.claims[claim['id']] = dict(claim=claim, function=fn.id, result=result, selected=selected,
                                        assumptions=assumptions, depth=claim.get('depth', 0))
        if selected:
            self.ledger.record(claim['id'], assumptions)

    # --- stage 9: verification -----------------------------------------------------
    def verify(self, ids):
        lean_batch, structural = [], verifier.StructuralBackend(self.bodies)
        for cid in ids:
            rec = self.claims[cid]
            if rec['result']['status'] != 'PENDING':
                continue
            claim, fn = rec['claim'], self.program.by_id[rec['function']]
            unsupported = self.env.unsupported_reach(self.program, fn)
            if claim['backend'] == 'cpir-structural':
                rec['result'] = structural.verify(claim, fn)
            else:
                key = ledger.ProofCache.key(claim, self.program, fn, self.model_sha, self.env.hash,
                                            'lean-kernel', self.o.fuel)
                cached = self.cache.get(key)
                if cached:
                    rec['result'] = cached
                else:
                    rec['cache_key'] = key
                    lean_batch.append((claim, fn))
            if unsupported:
                rec['unsupported_externals'] = unsupported
        if lean_batch:
            backend = verifier.LeanBackend(self.root, self.o.module, self.out / 'lean', timeout=self.o.timeout,
                                           fuel=self.o.fuel, deep=self.o.deep_proofs)
            results = backend.verify(lean_batch, self.program)
            for claim, _ in lean_batch:
                rec = self.claims[claim['id']]
                rec['result'] = results[claim['id']]
                self.cache.put(rec.pop('cache_key'), rec['result'])
        for cid in ids:
            rec = self.claims[cid]
            r = rec['result']
            kind = r.get('witness', {}).get('outcome_kind')
            if r.get('status') == 'REFUTED' and kind == 'undefined_behavior':
                r['undefined_behavior'] = r['witness']['model_outcome']
            if r.get('status') == 'REFUTED' and kind in ('hole', 'out_of_fuel'):
                r['status'] = 'MODEL_INCOMPLETE'
                r['reason'] = 'the witness drives evaluation into an unmodeled construct or fuel exhaustion'

    # --- stage 10: counterexample-guided refinement ------------------------------------
    def refine(self, refuted):
        frontier = list(refuted)
        for round_no in range(1, self.o.max_refinements + 1):
            fresh = []
            for cid in frontier:
                fresh += self.adjudicate(cid, round_no)
            if not fresh:
                break
            self.verify(fresh)
            frontier = [c for c in fresh if self.claims[c]['result']['status'] == 'REFUTED']

    def adjudicate(self, cid, round_no) -> list:
        rec = self.claims[cid]
        claim, fn, r = rec['claim'], self.program.by_id[rec['function']], rec['result']
        ctx = self.contexts[fn.id]
        witness = r.get('witness', {})
        native = verifier.native_replay(self.o.source, fn, list(witness.get('inputs', {}).values())) \
            if self.o.native else dict(status='not_run', reason='disabled')
        match = verifier.native_agrees(native, witness.get('model_outcome', ''))
        allowed = cegis.allowed_classes(r, fn, match, claim)
        if (claim.get('intent') or {}).get('contradicts_intent') and len(allowed) > 1:
            # A reading that contradicts the one the judge chose as intended cannot be a finding.
            allowed = [a for a in allowed if a != 'REAL_BUG'] or allowed
        state = dict(_state(ctx), claim=C.render_claim(claim, self.program),
                     claim_meaning=claim.get('description', ''),
                     violation=cegis.explain(claim, witness, self.program),
                     counterexample=dict(inputs=witness.get('inputs'), model_outcome=witness.get('model_outcome'),
                                         native_outcome=native.get('result'), native_agrees=match))
        d = self.judge.classify_counterexample(state, allowed,
                                               cegis.classification_prior(claim, r, ctx, match),
                                               dict(claim=cid, round=round_no))
        rec['counterexample'] = dict(claim=cid, inputs=witness.get('inputs'), model_outcome=witness.get('model_outcome'),
                                     outcome_kind=witness.get('outcome_kind'), native=native, native_agrees=match,
                                     classification=d['chosen'], classification_probabilities=d['probabilities'],
                                     allowed_classifications=allowed, decision=d['decision_id'])
        if d['chosen'] == 'REAL_BUG':
            # Cross-validation (design §31): a defect claim needs the intent to be supported by
            # something other than a template — independent evidence, or a confident intent pick.
            intent = claim.get('intent') or {}
            confident = {r['claim']['id'] for r in self.claims.values()
                         if r['function'] == fn.id and (r['claim'].get('intent') or {}).get('chosen')
                         and r['claim']['intent'].get('probability', 0) >= INTENT_THRESHOLD}
            supported = (C.independent_sources(claim) >= 1 or cid in confident
                         or bool(confident & set(claim.get('dominated_by', []))))   # implied by the intent
            rec['disposition'] = 'finding' if supported else 'suspected_bug'
            if not supported:
                self.review.append(dict(kind='conflicting evidence', claim=cid,
                                        detail='counterexample judged a real bug, but the claimed intent has no '
                                               'independent support: ' + C.render_claim(claim, self.program)))
            return []
        if d['chosen'] == 'MODEL_INCOMPLETE':
            r['status'] = 'MODEL_INCOMPLETE'
            rec['disposition'] = 'model_gap'
            self.review.append(dict(kind='missing environment model', claim=cid,
                                    detail='the counterexample is attributed to the model, not the code'))
            return []
        if rec['depth'] >= self.o.max_refinements:
            rec['disposition'] = 'refinement_limit'
            return []
        options = cegis.repairs(claim, r, fn, ctx)
        prior = {o['id']: cegis.repair_prior(o, claim, d['chosen']) for o in options}
        pick = self.judge.rank_repairs(state, options, prior, dict(claim=cid, classification=d['chosen']))
        chosen = next(o for o in options if o['id'] == pick['chosen'])
        rec['repair'] = dict(chosen=chosen['id'], text=chosen['text'], decision=pick['decision_id'],
                             options=[o['id'] for o in options])
        if chosen['claim'] is None:
            rec['disposition'] = 'rejected_by_repair'
            return []
        if chosen['new_assumptions']:
            verdict = self.judge.assumption(state, chosen['claim']['assumptions'][-1],
                                            {'ACCEPTABLE': 0.2, 'UNACCEPTABLE': 0.3, 'NEEDS_HUMAN_REVIEW': 0.5},
                                            dict(claim=cid))
            if verdict['chosen'] != 'ACCEPTABLE':
                self.review.append(dict(kind='high-impact assumption', claim=cid,
                                        detail=chosen['claim']['assumptions'][-1], judgment=verdict['chosen']))
            if verdict['chosen'] == 'UNACCEPTABLE':
                rec['disposition'] = 'repair_refused'
                return []
        accepted, rejected = critic.screen([chosen['claim']], self.program)
        if not accepted:
            rec['disposition'] = 'repair_rejected_by_critic'
            rec['repair']['critic'] = rejected[0]['reason'] if rejected else 'duplicate'
            return []
        new = accepted[0]
        if new['id'] in self.claims:
            rec['disposition'] = 'repair_duplicates_existing'
            return []
        new['depth'] = rec['depth'] + 1
        new['judgment'] = dict(label='REPAIR', probabilities={}, selection_probability=0)
        new['utility'] = claim.get('utility', 0)
        rec['disposition'] = 'repaired'
        rec['repaired_by'] = new['id']
        self.route(new, fn, _state(ctx))
        return [new['id']] if self.claims[new['id']]['result']['status'] == 'PENDING' else []

    # --- ledger, certificates, confidence, report ------------------------------------
    def finish(self, seconds) -> dict:
        self.cache.save()
        records = []
        for cid, rec in self.claims.items():
            claim, fn, r = rec['claim'], self.program.by_id[rec['function']], rec['result']
            if r.get('status') in ('PROVED', 'BOUNDED_PROVED') and claim['assumptions']:
                r['status_before_assumptions'] = r['status']
                r['status'] = 'ASSUMPTION_DEPENDENT'
            if r.get('status') in ('PROVED', 'BOUNDED_PROVED') and rec.get('unsupported_externals'):
                r['note'] = 'reaches unsupported externals: ' + ', '.join(rec['unsupported_externals'])
            coverage = self.contexts[fn.id]['coverage']
            match = (rec.get('counterexample') or {}).get('native_agrees')
            rec['confidence'] = ledger.confidence(claim, r, (claim.get('judgment') or {}).get('probabilities'),
                                                  coverage, match)
            rec['certificate'] = ledger.certificate(claim, r, fn, self.program, self.model_sha, self.env.hash,
                                                    rec['assumptions'])
            if (rec['selected'] and claim['category'] == 'security'
                    and r.get('status') in ('UNKNOWN', 'TIMEOUT', 'UNSUPPORTED')):
                self.review.append(dict(kind='unprovable but important property', claim=cid,
                                        detail=C.render_claim(claim, self.program)))
            probs = sorted(((claim.get('judgment') or {}).get('probabilities') or {}).values(), reverse=True)
            if (rec['selected'] and len(probs) > 1 and self.judge.backend == 'semif'
                    and probs[0] - probs[1] < 0.05):
                self.review.append(dict(kind='ambiguous intent', claim=cid,
                                        detail='the judge cannot separate its top two readings of '
                                               + C.render_claim(claim, self.program)))
            records.append(self.record(cid, rec, fn))
        for fn in self.targets():
            gaps = self.env.unsupported_reach(self.program, fn)
            if gaps:
                self.review.append(dict(kind='missing environment model', function=fn.name,
                                        detail='unsupported externals: ' + ', '.join(gaps)))
        self.annotate_decisions()
        from . import report
        data = report.build(self, records, seconds)
        report.write(self.out, data, self)
        return data

    def record(self, cid, rec, fn) -> dict:
        claim, r = rec['claim'], rec['result']
        return dict(id=cid, function=fn.name, function_id=fn.id, file=fn.file,
                    text=C.render_claim(claim, self.program), description=claim.get('description', ''),
                    category=claim['category'], subtype=claim['subtype'], selected=rec['selected'],
                    status=r.get('status'), reason=r.get('reason'), backend=r.get('backend', claim.get('backend')),
                    claim=claim, result={k: v for k, v in r.items() if k not in ('log_tail',)},
                    assumptions=rec['assumptions'], counterexample=rec.get('counterexample'),
                    repair=rec.get('repair'), disposition=rec.get('disposition'), parent=claim.get('parent'),
                    repaired_by=rec.get('repaired_by'), depth=rec['depth'], confidence=rec['confidence'],
                    intent=claim.get('intent'),
                    certificate=rec['certificate'], utility=claim.get('utility'),
                    judgment=claim.get('judgment'), evidence=claim['evidence'], provenance=claim['provenance'],
                    coverage=self.contexts[fn.id]['coverage'])

    def annotate_decisions(self):
        """Attach downstream verification outcomes to each decision (training signal)."""
        entries = []
        for e in self.log.entries:
            ctx = e.get('context') or {}
            rec = self.claims.get(ctx.get('claim')) if isinstance(ctx, dict) else None
            if rec:
                repaired = self.claims.get(rec.get('repaired_by') or '', {})
                e['outcome'] = dict(status=rec['result'].get('status'), disposition=rec.get('disposition'),
                                    repair_status=(repaired.get('result') or {}).get('status'),
                                    classification=(rec.get('counterexample') or {}).get('classification'),
                                    native_agrees=(rec.get('counterexample') or {}).get('native_agrees'))
            entries.append(e)
        self.log.path.write_text(''.join(json.dumps(e, default=str) + '\n' for e in entries))
