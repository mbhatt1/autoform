"""Prove stage: universal proofs of bounded-checked statements, re-checked by the kernel.

Only statements that elaborate and whose check status is BOUNDED_HOLDS go to the prover
agent (`autoform.harness.prover`); everything else is SKIPPED with the reason. The theorem
the kernel checks is `theorem <id> : <lean_prop>` under a prefix that imports the
translated module(s) and the `af_eval` tactic header, so a proof is about the translated
program — the agent's answer is never trusted.
"""
from __future__ import annotations

import os
import re
from dataclasses import asdict
from pathlib import Path

from .schema import FILES, ProofResult, dump

OK_STATUS = 'BOUNDED_HOLDS'
DEFAULT_CACHE = Path(os.environ.get('AUTOFORM_PROOF_CACHE', Path.home() / '.cache/autoform/proofs'))


def _d(x) -> dict:
    return asdict(x) if hasattr(x, '__dataclass_fields__') else dict(x)


def theorem_name(statement_id: str) -> str:
    """A Lean identifier for the statement id (ids may contain '.', ':', '<', '/')."""
    name = re.sub(r'[^A-Za-z0-9_]', '_', statement_id).strip('_') or 'stmt'
    return name if name[0].isalpha() else 'stmt_' + name


def header(translation: dict) -> str:
    """compiler.header for the translation's module, plus any further modules it names."""
    from autoform.harness import compiler
    module = translation['module']
    extra = [m for m in translation.get('modules', []) or [] if m != module]
    text = compiler.header(module)
    if extra:
        text = ''.join(f'import Autoform.Generated.{m}\n' for m in extra) + text
    return text


def blueprint(stmt: dict, fn: dict | None, check: dict | None, translation: dict) -> str:
    lines = [f"English property (model-generated, untrusted): {stmt.get('english', '')}"]
    if stmt.get('pre') not in (None, '', 'true'):
        lines.append(f"Precondition (Bool): {stmt['pre']}")
    if stmt.get('post'):
        lines.append(f"Postcondition over the result r : EResult (Bool): {stmt['post']}")
    lines.append(f"The call is `{translation.get('call_template', '')}` on the translated program "
                 f"{translation.get('program_const', '')}; `af_eval` symbolically evaluates it.")
    if fn:
        if fn.get('doc'):
            lines.append('Docstring: ' + fn['doc'][:800])
        if fn.get('source'):
            lines.append(f"Source of {fn.get('source_name', '')} ({fn.get('file', '')}):\n" + fn['source'][:2000])
    if check:
        ev = f"Check evidence: status {check.get('status')}"
        if check.get('domain_size'):
            ev += f", holds on {check['domain_size']} domain points"
        if check.get('kernel_bounded_proof'):
            ev += ' (kernel-checked bounded proof)'
        if check.get('runtime_agrees') is not None:
            ev += f", real-runtime agreement: {check['runtime_agrees']}"
        lines.append(ev + '.')
        if check.get('detail'):
            lines.append('Check detail: ' + str(check['detail'])[:600])
    lines.append('Typical proof: `intro ...` then `af_eval` then `simp`/`omega`/`split`/`decide`.')
    return '\n'.join(lines)


def eligibility(stmt: dict, check: dict | None) -> str | None:
    """None if the statement should be proved; otherwise the reason it is skipped."""
    if not stmt.get('elaborates'):
        return 'statement does not elaborate'
    if check is None:
        return 'no check result'
    if check.get('status') != OK_STATUS:
        why = check.get('status', '?')
        if check.get('counterexample'):
            why += f" (counterexample {check['counterexample'].get('inputs')})"
        return f'check status {why}'
    return None


def prove(translation: dict, statements: list, checks: list, out_dir, *, parallel: int = 2,
          budget_usd: float | None = None, agent=None, lean_root=None, attempts: int = 2,
          cache_dir=DEFAULT_CACHE) -> list:
    from autoform.harness import prover
    translation = _d(translation)
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    root = Path(lean_root or translation['lean_root']).resolve()
    fns = {f['name']: f for f in map(_d, translation.get('functions', []))}
    by_id = {c['statement']: c for c in map(_d, checks)}
    prefix = header(translation)
    results, jobs, owners = {}, [], {}
    stmts = [_d(s) for s in statements]
    for s in stmts:
        why = eligibility(s, by_id.get(s['id']))
        if why:
            results[s['id']] = ProofResult(s['id'], 'SKIPPED', reason=why)
            continue
        name = theorem_name(s['id'])
        while name in owners:
            name += '_'
        owners[name] = s['id']
        jobs.append(prover.Job(name=name, prefix=prefix, statement=f"theorem {name} : {s['lean_prop']}",
                               blueprint=blueprint(s, fns.get(s['function']), by_id.get(s['id']), translation)))
    if jobs:
        done = prover.prove_many(jobs, root, out / 'prover', parallel=parallel, budget_usd=budget_usd,
                                 agent=agent, attempts=attempts, cache_dir=cache_dir)
        for res in done:
            sid = owners[res.name]
            notes = []
            if res.cached:
                notes.append('cached proof re-checked by the kernel')
            if res.restored:
                notes.append(f'agent modified tracked files (restored): {res.restored}')
            if res.status == 'PROVED':
                results[sid] = ProofResult(sid, 'PROVED', proof=((res.helpers.strip() + '\n\n') if res.helpers.strip()
                                                                  else '') + res.proof,
                                           certificate=res.certificate, axioms=res.axioms, seconds=res.seconds,
                                           cost_usd=res.cost_usd, reason='; '.join(notes))
            else:
                reason = ('budget exhausted: ' if res.status == 'BUDGET' else
                          'agent timed out: ' if res.status == 'TIMEOUT' else '') + (res.reason or res.status)
                results[sid] = ProofResult(sid, 'FAILED', seconds=res.seconds, cost_usd=res.cost_usd,
                                           reason='; '.join([reason[:2000]] + notes))
    ordered = [results[s['id']] for s in stmts]
    dump(ordered, out / FILES['proofs'])
    return ordered
