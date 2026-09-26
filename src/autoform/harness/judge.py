"""The judgment layer: typed decisions between generation and verification.

    Generator → Judge → Verifier
    "what might be true?" → "which hypothesis is best supported / most useful?" → "is it true under M?"

The judge is a Jev-style decision model: a state, a criterion and a list of typed
options go in; one probability per option comes out (SemIf reads option logits
directly, no generated text). Its decisions choose *what to try* and *how to read a
counterexample*. They never set a proof status: every verdict comes from the Lean
kernel or the deterministic structural checker.

Deterministic facts constrain the judge rather than the other way around. If the
witness evaluates to a hole, the counterexample is INCOMPLETE_MODEL and no model
is consulted; if only one backend can express a claim, routing is forced.

Vocabulary: COUNTEREXAMPLE_CLASSES are the judge's *readings* of a witness. They are
not statuses. The verifier status MODEL_INCOMPLETE (verifier.STATUSES) is set by
deterministic code: a hole/out-of-fuel witness, or a counterexample the gates and the
judge attribute to the model (class INCOMPLETE_MODEL). MODEL_DEFECTS then says *what
kind* of model defect it is; PROOF_VALUES says what an established proof is worth.
Neither changes a status.

Backends
  semif      SemIf/OpenJev typed-logit scoring (MLX on Apple silicon, Torch elsewhere)
  heuristic  the deterministic priors each task computes anyway; reproducible, offline
  replay:F   decisions read back from a previous run's decisions.jsonl (tests, audits)
"""
from __future__ import annotations

import atexit
import hashlib
import json
import math
import os
import subprocess
import sys
import threading
from pathlib import Path

MAX_OPTIONS = 16   # SemIf's letter-slot limit
SEMIF_MODEL = 'Qwen/Qwen3.5-4B'
SEMIF_REVISION = '851bf6e806efd8d0a36b00ddf55e13ccb7b8cd0a'

CLAIM_JUDGMENTS = {
    'USEFUL_PROPERTY': 'A useful, non-trivial statement of the intended behavior, worth proving.',
    'SECURITY_RELEVANT': 'States a security requirement (authorization, validation, integrity) of this code.',
    'TRIVIAL': 'True of almost any implementation; proving it says little about this function.',
    'UNSUPPORTED_BY_EVIDENCE': 'Nothing in the code, names, docs or tests suggests this is intended.',
    'TOO_STRONG': 'Probably stricter than intended; likely false for legitimate behavior.',
    'TOO_WEAK': 'Probably true but misses the essential part of the intended behavior.',
    'LIKELY_VACUOUS': 'Its conditions are rarely or never met, so it constrains nothing.',
}
COUNTEREXAMPLE_CLASSES = {
    'REAL_BUG': 'The implementation violates what it is meant to do; the witness is a genuine defect.',
    'BAD_SPEC': 'The code behaves as intended; the claimed property is wrong (too strong or misstated).',
    'MISSING_PRECONDITION': 'The witness uses an input that callers are not meant to supply.',
    'INCOMPLETE_MODEL': 'The formal model does not capture the relevant behavior (unmodeled construct, '
                        'fuel bound, or a semantics gap).',
    'ENVIRONMENT_MISMATCH': 'The violation depends on external/environment behavior that differs from what '
                            'the claim takes for granted, not on this code.',
    'ABSTRACTION_ARTIFACT': 'The witness is an artifact of the chosen bounds, domain or encoding, not '
                            'reachable behavior.',
}
MODEL_DEFECTS = {
    'UNMODELED_CONSTRUCT': 'The interpreter has no semantics for a construct the code uses (a named hole).',
    'FUEL_BOUND': 'Evaluation ran out of fuel: a bound of the check, not necessarily a defect of the code.',
    'SEMANTICS_MISMATCH': 'The model evaluates the construct differently from the real runtime.',
    'EXTERNAL_UNMODELED': 'The behavior depends on a callee the program does not define and the environment '
                          'does not summarize.',
    'FRONTEND_MISTRANSLATION': 'The front end translated the source into Core incorrectly or incompletely.',
    'EVALUATOR_KERNEL_DISAGREEMENT': 'Compiled evaluation and kernel evaluation of the same model disagree.',
}
PROOF_VALUES = {
    'HIGH_VALUE': 'Establishes an essential, non-obvious part of the intended contract (e.g. a security '
                  'requirement).',
    'ROUTINE': 'Correct and useful, but a standard property one would expect to hold.',
    'TRIVIAL_IN_HINDSIGHT': 'Holds for almost any implementation with this interface; the proof says little.',
    'WEAKER_THAN_INTENDED': 'Holds, but only because it states less than the intended contract (weakened, '
                            'bounded, or assumption-dependent).',
}
ASSUMPTION_VERDICTS = {
    'ACCEPTABLE': 'A reasonable, standard assumption for this code and its callers.',
    'UNACCEPTABLE': 'Hides a real defect or excludes inputs that callers legitimately supply.',
    'NEEDS_HUMAN_REVIEW': 'Plausible but consequential; a person should confirm it.',
}


def _sha(value) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, default=str).encode()).hexdigest()


def softmax(values, temperature=1.0):
    m = max(v / temperature for v in values)
    w = [math.exp(v / temperature - m) for v in values]
    s = sum(w)
    return [x / s for x in w]


class DecisionLog:
    """Every decision is recorded with its inputs, scores and (later) its downstream outcome."""

    def __init__(self, path: Path | None):
        self.path = Path(path) if path else None
        self.entries = []
        if self.path:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            self.path.write_text('')

    def add(self, entry):
        self.entries.append(entry)
        if self.path:
            with self.path.open('a') as stream:
                stream.write(json.dumps(entry, default=str) + '\n')
        return entry


# --- scoring backends -----------------------------------------------------------

class HeuristicScorer:
    name = 'heuristic'
    metadata = {'backend': 'heuristic', 'note': 'deterministic priors; not a learned model'}

    def score(self, rows, shared=False):
        out = []
        for row in rows:
            prior = row.get('prior') or {}
            logits = [math.log(max(prior.get(o['id'], 1e-3), 1e-6)) for o in row['options']]
            out.append(dict(id=row['id'], option_ids=[o['id'] for o in row['options']],
                            option_logits=logits, probabilities=softmax(logits)))
        return out


class ReplayScorer:
    name = 'replay'

    def __init__(self, path):
        self.metadata = {'backend': 'replay', 'source': str(path)}
        self.table = {}
        for line in Path(path).read_text().splitlines():
            if line.strip():
                entry = json.loads(line)
                if not entry.get('option_logits'):
                    continue   # forced decisions carry no scores
                # decisions.jsonl names the option list `options`; a bare score file `option_ids`.
                entry['option_ids'] = entry.get('option_ids') or entry.get('options')
                self.table[entry['key']] = entry
        self.fallback = HeuristicScorer()

    def score(self, rows, shared=False):
        out = []
        for row in rows:
            hit = self.table.get(row_key(row))
            if hit and hit['option_ids'] == [o['id'] for o in row['options']]:
                out.append(dict(id=row['id'], option_ids=hit['option_ids'], option_logits=hit['option_logits'],
                                probabilities=softmax(hit['option_logits'])))
            else:
                out.extend(self.fallback.score([row]))
                out[-1]['replay_miss'] = True
        return out


class SemIfScorer:
    """Long-lived SemIf worker process; weights load once per harness run."""
    name = 'semif'

    def __init__(self, python=None, model=None, revision=None, bits=None, backend='auto', timeout=900):
        python = python or os.environ.get('AUTOFORM_SEMIF_PYTHON',
                                          str(Path.home() / 'semif/.venv/bin/python'))
        if not Path(python).exists():
            raise RuntimeError(f'SemIf interpreter not found at {python}; install SemIf '
                               '(https://github.com/TheoLeeCJ/SemIf-OpenJev) or set AUTOFORM_SEMIF_PYTHON')
        model = model or os.environ.get('AUTOFORM_SEMIF_MODEL', SEMIF_MODEL)
        revision = revision or os.environ.get('AUTOFORM_SEMIF_REVISION', SEMIF_REVISION)
        bits = bits or (int(os.environ['AUTOFORM_SEMIF_BITS']) if os.environ.get('AUTOFORM_SEMIF_BITS') else None)
        command = [python, str(Path(__file__).with_name('semif_worker.py')), '--model', model,
                   '--revision', revision, '--backend', backend]
        if bits:
            command += ['--bits', str(bits)]
        self.timeout = timeout
        self.process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE, text=True, bufsize=1)
        self._stderr = []
        threading.Thread(target=self._drain, daemon=True).start()
        ready = self._read()
        if not ready.get('ready'):
            self.close()
            raise RuntimeError('SemIf worker failed to load: ' + str(ready.get('error') or self._tail()))
        self.metadata = dict(ready['model'], backend='semif', worker=command[1:])
        atexit.register(self.close)

    def _drain(self):
        for line in self.process.stderr:
            self._stderr.append(line)
            del self._stderr[:-50]

    def _tail(self):
        return ''.join(self._stderr[-10:])

    def _read(self):
        result = {}

        def target():
            result['line'] = self.process.stdout.readline()
        t = threading.Thread(target=target, daemon=True)
        t.start()
        t.join(self.timeout)
        line = result.get('line')
        if not line:
            raise RuntimeError('SemIf worker stopped responding: ' + self._tail())
        return json.loads(line)

    def score(self, rows, shared=False):
        payload = [{k: r[k] for k in ('id', 'state', 'question', 'options')} for r in rows]
        self.process.stdin.write(json.dumps({'rows': payload, 'shared': shared}) + '\n')
        self.process.stdin.flush()
        reply = self._read()
        if 'error' in reply:
            raise RuntimeError('SemIf scoring failed: ' + reply['error'])
        return reply['results']

    def close(self):
        if self.process and self.process.poll() is None:
            self.process.stdin.close()
            try:
                self.process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                self.process.kill()


def row_key(row) -> str:
    return _sha({k: row[k] for k in ('state', 'question', 'options')})


def make_scorer(spec: str):
    if spec == 'heuristic':
        return HeuristicScorer()
    if spec.startswith('replay:'):
        return ReplayScorer(spec.split(':', 1)[1])
    if spec == 'semif':
        return SemIfScorer()
    raise ValueError(f'unknown judge {spec!r} (semif | heuristic | replay:PATH)')


# --- the judge --------------------------------------------------------------------

class Judge:
    def __init__(self, scorer, log: DecisionLog, temperature: dict | None = None):
        self.scorer = scorer
        self.log = log
        self.temperature = temperature or {}
        self.counter = 0

    @property
    def backend(self):
        return self.scorer.name

    def _decide(self, task, rows, shared=False, forced=None):
        """Score rows; return decisions (argmax + calibrated-by-temperature probabilities)."""
        if forced is not None:
            return [self.log.add(dict(decision_id=self._next(task), task=task, key=row_key(r), forced=True,
                                      options=[o['id'] for o in r['options']], chosen=forced,
                                      probabilities={forced: 1.0}, backend='forced', context=r.get('context')))
                    for r in rows]
        results = []
        for start in range(0, len(rows), 32):
            results += self.scorer.score(rows[start:start + 32], shared=shared)
        t = self.temperature.get(task, 1.0)
        out = []
        for row, res in zip(rows, results):
            probs = softmax(res['option_logits'], t)
            ids = res['option_ids']
            chosen = ids[max(range(len(ids)), key=probs.__getitem__)]
            out.append(self.log.add(dict(
                decision_id=self._next(task), task=task, key=row_key(row), state_sha256=_sha(row['state']),
                state=row['state'], question=row['question'], options=ids,
                option_descriptions=[o['description'] for o in row['options']], option_logits=res['option_logits'],
                probabilities=dict(zip(ids, probs)), chosen=chosen, backend=self.scorer.name,
                temperature=t, prompt_sha256=res.get('prompt_sha256'), replay_miss=res.get('replay_miss', False),
                probability_status='uncalibrated option score' if t == 1.0 else 'temperature-scaled option score',
                context=row.get('context'))))
        return out

    def _next(self, task):
        self.counter += 1
        return f'D_{self.counter:05d}_{task}'

    # 1. per-candidate typed judgment ------------------------------------------------
    def judge_claims(self, state, rendered: list, priors: list, contexts: list):
        rows = [dict(id=f'claim-{i}', state=state,
                     question=('Candidate specification for this function:\n' + text +
                               '\nWhich judgment best describes this candidate?'),
                     options=[dict(id=k, description=v) for k, v in CLAIM_JUDGMENTS.items()],
                     prior=prior, context=ctx)
                for i, (text, prior, ctx) in enumerate(zip(rendered, priors, contexts))]
        return self._decide('PROPERTY_JUDGMENT', rows, shared=True)

    # 2. listwise selection ------------------------------------------------------------
    def select(self, state, candidates: list, priors: dict, context):
        """Listwise: which candidate is the best-supported, most useful claim to prove?
        Candidates beyond 16 are scored in chunks and renormalized over all options."""
        decisions = []
        for start in range(0, len(candidates), MAX_OPTIONS):
            chunk = candidates[start:start + MAX_OPTIONS]
            if len(chunk) < 2:
                decisions.append(dict(chosen=chunk[0]['id'], probabilities={chunk[0]['id']: 1.0}))
                continue
            row = dict(id=f'select-{start}', state=state,
                       question='Which candidate is the most useful, evidence-supported statement of what '
                                'this function is meant to do, and therefore most worth proving?',
                       options=[dict(id=c['id'], description=c['text']) for c in chunk],
                       prior={c['id']: priors.get(c['id'], 0.1) for c in chunk}, context=context)
            decisions += self._decide('PROPERTY_SELECTION', [row])
        merged = {}
        for d in decisions:
            merged.update(d['probabilities'])
        total = sum(merged.values()) or 1.0
        return {k: v / total for k, v in merged.items()}

    # 2b. intent: one reading among mutually exclusive candidates ---------------------
    def intent(self, state, rivals: list, priors: dict, context):
        """The formalization policy: which of these incompatible readings is intended?"""
        row = dict(id='intent', state=state,
                   question='These candidate specifications are mutually exclusive: no implementation can satisfy '
                            'all of them, so at most one describes the intended behavior. Based on the name, '
                            'signature, documentation, tests and callers, which one is intended?',
                   options=[dict(id=c['id'], description=c['text']) for c in rivals[:MAX_OPTIONS]],
                   prior={c['id']: priors.get(c['id'], 0.1) for c in rivals[:MAX_OPTIONS]}, context=context)
        return self._decide('INTENT_SELECTION', [row])[0]

    # 3. counterexample adjudication ----------------------------------------------
    def classify_counterexample(self, state, allowed: list, prior: dict, context):
        if len(allowed) == 1:
            return self._decide('COUNTEREXAMPLE_CLASSIFICATION',
                                [dict(id='ce', state=state, question='', options=[dict(id=allowed[0],
                                      description=COUNTEREXAMPLE_CLASSES[allowed[0]])], context=context)],
                                forced=allowed[0])[0]
        row = dict(id='ce', state=state,
                   question='The verifier found this counterexample to the claim. What does it most likely '
                            'mean?',
                   options=[dict(id=k, description=COUNTEREXAMPLE_CLASSES[k]) for k in allowed],
                   prior=prior, context=context)
        return self._decide('COUNTEREXAMPLE_CLASSIFICATION', [row])[0]

    # 3b. which precondition (listwise, precondition candidates only) -----------------
    def select_precondition(self, state, candidates: list, prior: dict, context):
        """MISSING_PRECONDITION with several candidate preconditions: pick the one callers are
        meant to respect. REPAIR_SELECTION then weighs only the winner against other repair kinds."""
        if len(candidates) == 1:
            return self._decide('PRECONDITION_SELECTION', [dict(id='precondition', state=state, question='',
                                options=[dict(id=candidates[0]['id'], description=candidates[0]['text'])],
                                context=context)], forced=candidates[0]['id'])[0]
        row = dict(id='precondition', state=state,
                   question='The counterexample uses an input callers are not meant to supply. Which '
                            'precondition states the input contract callers are actually expected to respect '
                            '(not merely one that excludes the witness)?',
                   options=[dict(id=c['id'], description=c['text']) for c in candidates[:MAX_OPTIONS]],
                   prior=prior, context=context)
        return self._decide('PRECONDITION_SELECTION', [row])[0]

    # 3c. model-defect diagnosis ---------------------------------------------------
    def classify_model_defect(self, state, allowed: list, prior: dict, context):
        if len(allowed) == 1:
            return self._decide('MODEL_DEFECT_CLASSIFICATION',
                                [dict(id='defect', state=state, question='', options=[dict(
                                    id=allowed[0], description=MODEL_DEFECTS[allowed[0]])], context=context)],
                                forced=allowed[0])[0]
        row = dict(id='defect', state=state,
                   question='Verification attributes this result to the formal model, not to the code. '
                            'What kind of model defect is it?',
                   options=[dict(id=k, description=MODEL_DEFECTS[k]) for k in allowed],
                   prior=prior, context=context)
        return self._decide('MODEL_DEFECT_CLASSIFICATION', [row])[0]

    # 4. repair ranking ------------------------------------------------------------
    def rank_repairs(self, state, repairs: list, prior: dict, context):
        if len(repairs) == 1:
            return self._decide('REPAIR_SELECTION', [dict(id='repair', state=state, question='',
                                options=[dict(id=repairs[0]['id'], description=repairs[0]['text'])],
                                context=context)], forced=repairs[0]['id'])[0]
        row = dict(id='repair', state=state,
                   question='Which repair of the refuted claim is the minimal, evidence-consistent '
                            'interpretation of the intended behavior (not merely one that becomes provable)?',
                   options=[dict(id=r['id'], description=r['text']) for r in repairs[:MAX_OPTIONS]],
                   prior=prior, context=context)
        return self._decide('REPAIR_SELECTION', [row])[0]

    # 5. backend routing ------------------------------------------------------------
    def route(self, state, feasible: list, prior: dict, context):
        if len(feasible) == 1:
            return self._decide('BACKEND_SELECTION', [dict(id='route', state=state, question='',
                                options=[dict(id=feasible[0]['id'], description=feasible[0]['text'])],
                                context=context)], forced=feasible[0]['id'])[0]
        row = dict(id='route', state=state,
                   question='Which verification backend should check this claim first?',
                   options=[dict(id=b['id'], description=b['text']) for b in feasible],
                   prior=prior, context=context)
        return self._decide('BACKEND_SELECTION', [row])[0]

    # 6. assumption acceptability ----------------------------------------------------
    def assumption(self, state, text, prior, context):
        row = dict(id='assumption', state=state,
                   question='A repair proposes to add this assumption: ' + text + '\nIs it acceptable?',
                   options=[dict(id=k, description=v) for k, v in ASSUMPTION_VERDICTS.items()],
                   prior=prior, context=context)
        return self._decide('ASSUMPTION_ACCEPTABILITY', [row])[0]

    # 7. proof value (interface view; never a status) -----------------------------------
    def proof_value(self, state, rendered: list, priors: list, contexts: list):
        rows = [dict(id=f'value-{i}', state=state,
                     question=('The verifier established this claim about the function:\n' + text +
                               '\nJudged against what the function is meant to do, what is this proof worth?'),
                     options=[dict(id=k, description=v) for k, v in PROOF_VALUES.items()],
                     prior=prior, context=ctx)
                for i, (text, prior, ctx) in enumerate(zip(rendered, priors, contexts))]
        return self._decide('PROOF_VALUE_JUDGMENT', rows, shared=True) if rows else []
