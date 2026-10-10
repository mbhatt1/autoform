"""Formalization-JEVBench: judge decisions labeled by what verification later showed.

    judge decision → verification outcome → training signal

Labels are derived from the verifier, so they are only as strong as the downstream
evidence. Where the outcome cannot separate the options (a REAL_BUG verdict needs the
authors' intent), the row is exported unlabeled rather than guessed.

Tasks: PROPERTY_JUDGMENT, PROPERTY_SELECTION, INTENT_SELECTION, PRECONDITION_SELECTION,
COUNTEREXAMPLE_CLASSIFICATION, MODEL_DEFECT_CLASSIFICATION, REPAIR_SELECTION,
BACKEND_SELECTION, ASSUMPTION_ACCEPTABILITY, PROOF_VALUE_JUDGMENT.

Label kinds: `single` (this option is right), `acceptable` (any of these), `negative`
(this option was wrong), `unlabeled` (with the reason no verifier outcome settles it),
`forced` (a deterministic gate left one option; not exported).
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

HELD = {'PROVED', 'BOUNDED_PROVED', 'ASSUMPTION_DEPENDENT'}


TASKS = ('PROPERTY_JUDGMENT', 'PROPERTY_SELECTION', 'INTENT_SELECTION', 'PRECONDITION_SELECTION',
         'COUNTEREXAMPLE_CLASSIFICATION', 'MODEL_DEFECT_CLASSIFICATION', 'REPAIR_SELECTION',
         'BACKEND_SELECTION', 'ASSUMPTION_ACCEPTABILITY', 'PROOF_VALUE_JUDGMENT')


def label(entry) -> dict:
    task, out = entry['task'], entry.get('outcome') or {}
    status, chosen = out.get('status'), entry.get('chosen')
    if entry.get('forced'):
        return dict(kind='forced')
    if task == 'PROPERTY_JUDGMENT':
        if status in HELD:
            return dict(kind='acceptable', labels=['USEFUL_PROPERTY', 'SECURITY_RELEVANT'])
        if status == 'REFUTED':
            cls = out.get('classification')
            if cls in ('BAD_SPEC', 'MISSING_PRECONDITION'):
                return dict(kind='acceptable', labels=['TOO_STRONG'])
            if cls == 'REAL_BUG':
                return dict(kind='acceptable', labels=['SECURITY_RELEVANT', 'USEFUL_PROPERTY'])
            return dict(kind='acceptable', labels=['TOO_STRONG', 'UNSUPPORTED_BY_EVIDENCE'])
        return dict(kind='unlabeled', reason=f'outcome {status}')
    if task == 'COUNTEREXAMPLE_CLASSIFICATION':
        if out.get('repair_status') in HELD:
            return dict(kind='single', label=chosen, reason='the repair implied by this class was then established')
        if out.get('repair_status') == 'REFUTED':
            return dict(kind='negative', label=chosen, reason='the implied repair was refuted again')
        return dict(kind='unlabeled', reason='intent-dependent; needs a human label')
    if task == 'PRECONDITION_SELECTION':
        if out.get('repair_chosen') != chosen:
            return dict(kind='unlabeled', reason=f"REPAIR_SELECTION chose {out.get('repair_chosen')}; "
                                                 'this precondition was never verified')
        if out.get('repair_status') in HELD:
            return dict(kind='single', label=chosen, reason='the claim under this precondition was established')
        if out.get('repair_status') == 'REFUTED':
            return dict(kind='negative', label=chosen, reason='refuted again under this precondition')
        return dict(kind='unlabeled', reason=out.get('disposition') or 'the repaired claim was not verified')
    if task == 'REPAIR_SELECTION':
        if out.get('repair_status') in HELD:
            return dict(kind='single', label=chosen)
        if out.get('repair_status'):
            return dict(kind='negative', label=chosen)
        return dict(kind='unlabeled', reason=out.get('disposition') or 'no repair verified')
    if task == 'BACKEND_SELECTION':
        if status in HELD | {'REFUTED'}:
            return dict(kind='single', label=chosen)
        return dict(kind='unlabeled', reason=f'outcome {status}')
    if task == 'ASSUMPTION_ACCEPTABILITY':
        repaired = out.get('repair_status')
        if repaired == 'REFUTED':
            # The claim still fails with the assumption: accepting it bought nothing.
            return dict(kind='negative', label='ACCEPTABLE',
                        reason='the claim repaired by this assumption was refuted again')
        if repaired in HELD and out.get('assumption_free_sibling'):
            return dict(kind='single', label='UNACCEPTABLE',
                        reason=f"unnecessary: {out['assumption_free_sibling']} establishes the claim without it")
        return dict(kind='unlabeled', reason='acceptability of an assumption the verifier did not refute or '
                                             'make redundant is a judgment about callers; needs a human label')
    if task == 'MODEL_DEFECT_CLASSIFICATION':
        return dict(kind='unlabeled', reason='only a fix to the interpreter or the front end (or a person) '
                                             'separates the admissible defect classes; this run cannot')
    if task == 'PROOF_VALUE_JUDGMENT':
        return dict(kind='unlabeled', reason='the kernel settles truth, not value; value is intent-dependent')
    if task in ('PROPERTY_SELECTION', 'INTENT_SELECTION'):
        return dict(kind='unlabeled', reason='which claim is intended is not settled by verification')
    return dict(kind='unlabeled', reason='no verifier-derived label for this task')


def export(decisions: Path, destination: Path) -> int:
    rows = []
    if not Path(decisions).is_file():
        return 0
    for line in Path(decisions).read_text().splitlines():
        if not line.strip():
            continue
        e = json.loads(line)
        lab = label(e)
        if lab['kind'] == 'forced':
            continue
        rows.append(dict(id=e['decision_id'], task=e['task'], state=e.get('state'), question=e.get('question'),
                         options=[dict(id=i, description=d) for i, d in
                                  zip(e.get('options', []), e.get('option_descriptions', []))],
                         model_choice=e.get('chosen'), option_logits=e.get('option_logits'),
                         backend=e.get('backend'), label=lab, outcome=e.get('outcome')))
    Path(destination).write_text(''.join(json.dumps(r, default=str) + '\n' for r in rows))
    return len(rows)


def _nll(rows, t):
    total = 0.0
    for r in rows:
        logits = [x / t for x in r['option_logits']]
        m = max(logits)
        z = math.log(sum(math.exp(x - m) for x in logits)) + m
        ids = [o['id'] for o in r['options']]
        wanted = r['label'].get('labels') or [r['label']['label']]
        idx = [ids.index(w) for w in wanted if w in ids]
        if not idx:
            continue
        p = sum(math.exp(logits[i] - z) for i in idx)
        total -= math.log(max(p, 1e-12))
    return total


def fit_temperatures(paths) -> dict:
    """Per-task temperature minimizing NLL on verifier-labeled rows (calibration only;
    the argmax, and therefore every decision, is unchanged)."""
    by_task = {}
    for path in paths:
        for line in Path(path).read_text().splitlines():
            r = json.loads(line)
            if r['label']['kind'] in ('single', 'acceptable') and r.get('option_logits') and r['backend'] == 'semif':
                by_task.setdefault(r['task'], []).append(r)
    grid = [0.25 * i for i in range(1, 41)]
    return {task: dict(temperature=min(grid, key=lambda t: _nll(rows, t)), rows=len(rows))
            for task, rows in by_task.items() if len(rows) >= 5}


def main(argv=None):
    ap = argparse.ArgumentParser(description='Formalization-JEVBench utilities')
    sub = ap.add_subparsers(dest='cmd', required=True)
    fit = sub.add_parser('fit-temperature', help='fit per-task judge temperatures from jevbench.jsonl files')
    fit.add_argument('files', nargs='+', type=Path)
    fit.add_argument('--out', type=Path, required=True)
    args = ap.parse_args(argv)
    fitted = fit_temperatures(args.files)
    args.out.write_text(json.dumps({k: v['temperature'] for k, v in fitted.items()}, indent=1))
    print(json.dumps(fitted, indent=1))
    return 0
