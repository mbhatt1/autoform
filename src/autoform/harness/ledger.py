"""Assumption ledger, proof certificates, proof cache and the confidence triple.

Three scores are kept separate and never merged (design §54):
  intent_confidence  — is this the claim the authors meant?     (judge + evidence)
  model_confidence   — does the model capture the code?          (coverage + native agreement)
  proof_confidence   — how strong is the verdict under the model? (kernel status)
"""
from __future__ import annotations

import json
import shutil
from pathlib import Path

from .cpir import sha256

KERNEL_STATUSES = {'PROVED', 'BOUNDED_PROVED', 'REFUTED', 'ASSUMPTION_DEPENDENT'}
PROOF_CONFIDENCE = {'PROVED': 1.0, 'REFUTED': 1.0, 'ASSUMPTION_DEPENDENT': 0.8, 'BOUNDED_PROVED': 0.5,
                    'MODEL_INCOMPLETE': 0.0, 'UNKNOWN': 0.0, 'TIMEOUT': 0.0, 'UNSUPPORTED': 0.0,
                    'INCONSISTENT_MODEL': 0.0}


class AssumptionLedger:
    """Global graph: assumption → claims that depend on it (and the reverse)."""

    def __init__(self):
        self.assumptions = {}
        self.dependents = {}

    def record(self, claim_id, assumptions):
        for a in assumptions:
            self.assumptions.setdefault(a['id'], {k: v for k, v in a.items()})
            self.dependents.setdefault(a['id'], [])
            if claim_id not in self.dependents[a['id']]:
                self.dependents[a['id']].append(claim_id)

    def invalidated_by(self, assumption_ids) -> list:
        return sorted({c for a in assumption_ids for c in self.dependents.get(a, [])})

    def to_json(self):
        return dict(assumptions=[dict(a, dependents=sorted(self.dependents.get(a['id'], [])),
                                      text_sha256=sha256(a['text']))
                                 for a in sorted(self.assumptions.values(), key=lambda a: a['id'])])


class ProofCache:
    """key = (claim, semantics of the call closure, model, environment, backend, fuel)."""

    def __init__(self, directory: Path | None):
        self.dir = Path(directory) if directory else None
        self.index = {}
        self.hits = 0
        if self.dir:
            (self.dir / 'artifacts').mkdir(parents=True, exist_ok=True)
            path = self.dir / 'index.json'
            if path.is_file():
                try:
                    self.index = json.loads(path.read_text())
                except ValueError:
                    self.index = {}

    @staticmethod
    def key(claim, program, fn, model_sha, env_hash, backend_version, fuel) -> str:
        closure = [program.by_id[f].semantics_hash for f in program.closure(fn.id)]
        return sha256(dict(claim=claim['id'], closure=closure, model=model_sha, env=env_hash,
                           backend=backend_version, fuel=fuel, pre=claim['preconditions'],
                           prop=claim['property']))

    def get(self, key):
        hit = self.index.get(key)
        if hit and all(Path(p).is_file() for p in hit.get('artifacts', [])):
            self.hits += 1
            return dict(hit['result'], cache='hit')
        return None

    def put(self, key, result):
        if not self.dir or result.get('status') not in KERNEL_STATUSES:
            return
        kept = []
        for field in ('lean_file', 'witness_file'):
            src = result.get(field)
            if src and Path(src).is_file():
                dst = self.dir / 'artifacts' / (sha256(Path(src).read_bytes())[7:] + '.lean')
                if not dst.exists():
                    shutil.copyfile(src, dst)
                result = dict(result, **{field: str(dst)})
                kept.append(str(dst))
        self.index[key] = dict(result=result, artifacts=kept)

    def save(self):
        if self.dir:
            (self.dir / 'index.json').write_text(json.dumps(self.index, indent=1, sort_keys=True))


def certificate(claim, result, fn, program, model_sha, env_hash, assumptions) -> dict | None:
    status = result.get('status')
    if status not in KERNEL_STATUSES:
        return None
    lean = result.get('backend') == 'lean-kernel'
    artifact = result.get('witness_file') if status == 'REFUTED' else result.get('lean_file')
    return dict(claim_id=claim['id'], status=status,
                semantics_hash=fn.semantics_hash, model_sha256=model_sha, environment_hash=env_hash,
                assumptions=[a['id'] for a in assumptions],
                backend=dict(name=result.get('backend'), version=result.get('backend_version')),
                solver_result=('kernel-checked counterexample' if status == 'REFUTED' else
                               'kernel-checked proof' if lean else 'structural re-check'),
                certificate=dict(format='lean4-theorem' if lean else 'cpir-structural-query',
                                 artifact=artifact,
                                 artifact_sha256=result.get('witness_file_sha256' if status == 'REFUTED'
                                                            else 'lean_file_sha256'),
                                 theorems=result.get('theorems', []),
                                 axioms=['propext', 'Classical.choice', 'Quot.sound'] if lean else []),
                scope=dict(functions=[program.by_id[f].name for f in program.closure(fn.id)],
                           quantification='universal' if status in ('PROVED', 'ASSUMPTION_DEPENDENT')
                           and result.get('universal_proof', True) else
                           f"finite domain of {result.get('domain_size')} points" if status == 'BOUNDED_PROVED'
                           else 'single witness' if status == 'REFUTED' else 'n/a'),
                soundness='Proof(c) ⇒ Semantics_M(P) ⊨ c for M = the Core interpreter at this build; '
                          'not a statement about real execution unless M refines it.')


def confidence(claim, result, judgments, coverage, native_match) -> dict:
    j = judgments or {}
    intent_judge = j.get('USEFUL_PROPERTY', 0) + j.get('SECURITY_RELEVANT', 0)
    from .claims import evidence_score
    intent = round(0.5 * intent_judge + 0.5 * evidence_score(claim), 3) if j else evidence_score(claim)
    native = 1.0 if native_match is True else 0.6 if native_match is False else 0.9
    model = round(coverage.get('confidence', 0) * native, 3)
    return dict(intent_confidence=intent, model_confidence=model,
                proof_confidence=PROOF_CONFIDENCE.get(result.get('status'), 0.0))
