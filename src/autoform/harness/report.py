"""Reports: repository summary, per-claim cards, certificates, formalization diff."""
from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

from .verifier import BACKENDS, STATUSES

ORDER = {s: i for i, s in enumerate(('REFUTED', 'PROVED', 'BOUNDED_PROVED', 'ASSUMPTION_DEPENDENT',
                                     'MODEL_INCOMPLETE', 'INCONSISTENT_MODEL', 'UNKNOWN', 'TIMEOUT',
                                     'UNSUPPORTED', 'NOT_SELECTED'))}
HELD = {'PROVED', 'BOUNDED_PROVED', 'ASSUMPTION_DEPENDENT'}


def build(h, records, seconds) -> dict:
    selected = [r for r in records if r['selected']]
    counts = Counter(r['status'] for r in selected)
    fns = h.targets()
    blocks = sum(len(f.blocks) for f in fns)
    modeled = sum(len(f.blocks) - len(f.holes) for f in fns)
    security = {}
    for r in selected:
        if r['category'] == 'security':
            s = security.setdefault(r['subtype'], dict(held=0, total=0))
            s['total'] += 1
            s['held'] += r['status'] in HELD
    externals = sorted({n for f in fns for n in h.env.unsupported_reach(h.program, f)})
    assumptions = h.ledger.to_json()['assumptions']
    critical = [a for a in assumptions if a['kind'] in ('external', 'claim', 'input_domain')]
    findings = [r for r in records if r.get('disposition') == 'finding']
    defects = [r for r in selected if r.get('model_defect')]
    values = Counter(r['proof_value']['label'] for r in selected if r.get('proof_value'))
    suspected = [r for r in records if r.get('disposition') == 'suspected_bug']
    return dict(
        schema_version=1, module=h.o.module, generated_in_seconds=round(seconds, 1),
        repository=dict(source=str(h.o.source) if h.o.source else None,
                        git=_git(h), ast=str(h.ast_path), ast_hash=h.program.ast_hash, model_sha256=h.model_sha),
        judge=dict(backend=h.judge.backend, metadata=getattr(h.judge.scorer, 'metadata', {}),
                   decisions=len(h.log.entries), temperature=h.judge.temperature or None,
                   role='ranks and classifies; never sets a proof status'),
        generators=[g.name for g in h.gens], notes=h.notes,
        environment=dict(hash=h.env.hash, model=h.env.model),
        backends={k: dict(available=v.get('available', True), reason=v.get('reason')) for k, v in BACKENDS.items()},
        semantic_coverage=round(modeled / blocks, 4) if blocks else 1.0,
        claims_generated=len(records) + len([x for x in h.rejected if x.get('stage') != 'generator']),
        claims_rejected_before_verification=len(h.rejected), claims_selected=len(selected),
        results={s: counts.get(s, 0) for s in STATUSES if counts.get(s, 0)},
        security=security, findings=[dict(id=r['id'], function=r['function'], text=r['text'],
                                          witness=(r.get('counterexample') or {}).get('inputs'),
                                          native_agrees=(r.get('counterexample') or {}).get('native_agrees'))
                                     for r in findings],
        suspected_bugs=[dict(id=r['id'], function=r['function'], text=r['text'],
                             witness=(r.get('counterexample') or {}).get('inputs')) for r in suspected],
        model_defects=[dict(id=r['id'], function=r['function'], status=r['status'],
                            classification=r['model_defect']['classification'],
                            forced=r['model_defect']['forced'], hole_label=r['model_defect'].get('hole_label'),
                            allowed=r['model_defect']['allowed']) for r in defects],
        proof_values=dict(values),
        unmodeled_externals=externals, critical_assumptions=critical, cache_hits=h.cache.hits,
        human_review=h.review,
        functions=[dict(id=f.id, name=f.name, coverage=h.contexts.get(f.id, {}).get('coverage'),
                        claims=[r['id'] for r in records if r['function_id'] == f.id]) for f in fns],
        claims=sorted(records, key=lambda r: (not r['selected'], ORDER.get(r['status'], 99), r['function'])),
        rejected=[dict(stage=x.get('stage'), function=x.get('function'), reason=x.get('reason'),
                       claim=(x.get('claim') or {}).get('id')) for x in h.rejected],
        soundness='A status is a statement about the Core interpreter model M at this build, '
                  'not about real execution. Judge probabilities are rankings, not confidence in truth.')


def _git(h):
    from .pipeline import _git_revision
    return _git_revision(h.o.source)


def card(r) -> list:
    c = r['confidence']
    lines = [f"### {r['id']} · {r['status']}", '', f"**{r['text']}**", '']
    if r.get('description'):
        lines += [r['description'], '']
    lines += [f"- Scope: `{r['function']}` ({r['file']})",
              f"- Category: {r['category']} / {r['subtype']} · backend: {r.get('backend')}",
              f"- Confidence — intent {c['intent_confidence']} · model {c['model_confidence']} · "
              f"proof {c['proof_confidence']}"]
    if r.get('proof_value'):
        v = r['proof_value']
        lines.append(f"- Proof value (judge; not a status): {v['label']} "
                     f"(p={v['probabilities'].get(v['label'], 0):.2f})")
    if r.get('reason'):
        lines.append(f"- Reason: {r['reason']}")
    if r.get('judgment') and r['judgment'].get('label'):
        lines.append(f"- Judge: {r['judgment']['label']} (selection p={r['judgment'].get('selection_probability')})")
    ev = ', '.join(f"{e['type']}" + (f" @ {e['location']}" if e.get('location') else '') for e in r['evidence'][:6])
    lines.append(f"- Evidence: {ev or 'none'}")
    lines.append('- Assumptions: ' + '; '.join(a['id'] for a in r['assumptions']))
    ce = r.get('counterexample')
    if ce:
        lines.append(f"- Counterexample: inputs {ce['inputs']} → model `{ce['model_outcome']}`; native "
                     f"{'agrees' if ce['native_agrees'] else 'disagrees' if ce['native_agrees'] is False else 'not compared'}; "
                     f"judged **{ce['classification']}**")
    elif (r['result'].get('witness') or {}).get('inputs') is not None:
        w = r['result']['witness']
        lines.append(f"- Counterexample: inputs {w['inputs']} → model `{w.get('model_outcome')}`")
    if r.get('model_defect'):
        m = r['model_defect']
        lines.append(f"- Model defect: **{m['classification']}**"
                     + (f" (hole `{m['hole_label']}`)" if m.get('hole_label') else '')
                     + (' — forced by verifier facts' if m['forced'] else f" — judged among {', '.join(m['allowed'])}"))
    if r.get('repair'):
        pre = r['repair'].get('precondition')
        if pre:
            lines.append(f"- Precondition chosen: {pre['chosen']} (of {', '.join(pre['options'])})")
        lines.append(f"- Repair: {r['repair']['text']} → {r.get('repaired_by') or r.get('disposition')}")
    if r.get('parent'):
        lines.append(f"- Refines: {r['parent']}")
    cert = r.get('certificate')
    if cert:
        lines.append(f"- Certificate: {cert['certificate']['format']} `{', '.join(cert['certificate']['theorems'])}` "
                     f"in `{Path(cert['certificate']['artifact'] or '').name}` ({cert['scope']['quantification']})")
    return lines + ['']


def markdown(d) -> str:
    L = [f"# Formalization report — {d['module']}", '',
         f"Judge: **{d['judge']['backend']}** ({d['judge']['decisions']} decisions) · generators: "
         f"{', '.join(d['generators'])} · {d['generated_in_seconds']}s", '',
         f"> {d['soundness']}", '', '```',
         f"Semantic coverage:        {d['semantic_coverage'] * 100:.1f}%",
         f"Claims generated:         {d['claims_generated']}",
         f"Rejected before proving:  {d['claims_rejected_before_verification']}",
         f"Selected for proof:       {d['claims_selected']}", '', 'Results:']
    L += [f"  {n:>4} {s}" for s, n in sorted(d['results'].items(), key=lambda kv: ORDER.get(kv[0], 99))]
    if d['security']:
        L += ['', 'Security properties:']
        L += [f"  {'✓' if v['held'] == v['total'] else '✗'} {k}: {v['held']}/{v['total']}" for k, v in d['security'].items()]
    L += ['', f"Findings (REAL_BUG, intent supported): {len(d['findings'])}",
          f"Suspected bugs (needs review): {len(d['suspected_bugs'])}",
          f"Model defects:            {len(d['model_defects'])}",
          f"Unmodeled externals:      {len(d['unmodeled_externals'])}",
          f"Critical assumptions:     {len(d['critical_assumptions'])}",
          f"Proof cache hits:         {d['cache_hits']}"]
    if d['proof_values']:
        L.append('Proof value (judge):      ' + ', '.join(f'{k} {v}' for k, v in sorted(d['proof_values'].items())))
    L += ['```', '']
    if d['findings']:
        L += ['## Findings', '']
        L += [f"- **{f['function']}** — `{f['text']}` fails at {f['witness']}"
              + (' (reproduced natively)' if f['native_agrees'] else '') for f in d['findings']]
        L.append('')
    if d['human_review']:
        L += ['## Needs human review', '']
        L += [f"- {x['kind']}: {x.get('claim') or x.get('function')} — {x['detail']}" for x in d['human_review']]
        L.append('')
    L += ['## Claims', '']
    for r in d['claims']:
        if r['selected']:
            L += card(r)
    skipped = [r for r in d['claims'] if not r['selected']]
    if skipped:
        L += ['## Not selected', ''] + [f"- {r['id']} `{r['text']}` — {r['reason']}" for r in skipped] + ['']
    return '\n'.join(L)


def write(out: Path, d, h):
    out = Path(out)
    (out / 'report.json').write_text(json.dumps(d, indent=1, default=str))
    (out / 'report.md').write_text(markdown(d))
    (out / 'cpir.json').write_text(json.dumps(h.program.to_json(), indent=1, default=str))
    (out / 'entities.json').write_text(json.dumps(h.program.entity_table(), indent=1))
    (out / 'ledger.json').write_text(json.dumps(h.ledger.to_json(), indent=1))
    (out / 'certificates.json').write_text(json.dumps([r['certificate'] for r in d['claims'] if r['certificate']],
                                                      indent=1))
    from . import bench
    bench.export(out / 'decisions.jsonl', out / 'jevbench.jsonl')


# --- formalization diff (CI) ----------------------------------------------------------

def diff(old: dict, new: dict) -> dict:
    o = {r['id']: r for r in old['claims'] if r['selected']}
    n = {r['id']: r for r in new['claims'] if r['selected']}
    oa = {a['id']: a['text_sha256'] for a in old.get('critical_assumptions', [])}
    na = {a['id']: a['text_sha256'] for a in new.get('critical_assumptions', [])}
    changes = dict(new=[], removed=[], preserved=[], lost=[], gained=[], changed=[],
                   assumptions_changed=sorted({k for k in set(oa) | set(na) if oa.get(k) != na.get(k)}))
    for cid in sorted(set(o) | set(n)):
        a, b = o.get(cid), n.get(cid)
        if a is None:
            changes['new'].append(b)
        elif b is None:
            changes['removed'].append(a)
        elif a['status'] == b['status']:
            if a['status'] in HELD:
                changes['preserved'].append((a, b))
        elif a['status'] in HELD and b['status'] not in HELD:
            changes['lost'].append((a, b))
        elif b['status'] in HELD and a['status'] not in HELD:
            changes['gained'].append((a, b))
        else:
            changes['changed'].append((a, b))
    return changes


def diff_markdown(c) -> str:
    L = ['# Formalization diff', '', '```',
         f"+ {len(c['new'])} new claims", f"✓ {len(c['preserved'])} proofs preserved",
         f"✗ {len(c['lost'])} previously established claims lost",
         f"↑ {len(c['gained'])} claims newly established",
         f"? {len(c['assumptions_changed'])} assumptions changed", '```', '']
    for a, b in c['lost']:
        L += ['```diff', f"CLAIM {a['id']}  {a['text']}", f"- {a['status']}", f"+ {b['status']}", '```']
        w = (b.get('counterexample') or {}).get('inputs') or (b['result'].get('witness') or {}).get('inputs')
        if w is not None:
            L += [f"Witness: {w}"]
        if b.get('reason'):
            L += [f"Reason: {b['reason']}"]
        L.append('')
    if c['assumptions_changed']:
        L += ['Changed assumptions (dependent proofs must be re-established): '
              + ', '.join(c['assumptions_changed']), '']
    return '\n'.join(L)
