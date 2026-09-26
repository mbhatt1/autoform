"""The natural-language autoformalizer end to end.

    translate → describe → formalize → check → prove → report

Every stage reads and writes JSON in one run directory (schema.FILES). `run.json` records,
per stage, the hash of its inputs, its status, wall time and model spend. With `resume`, a
stage whose output exists and whose recorded input hash matches is not rerun. A failing
stage is recorded and later stages run on whatever exists (a stage whose inputs are
missing is `blocked`); the report is always written.

    autoform autoformalize <git-url|dir> [Module] [--functions f g] [--no-prove]
                           [--no-runtime] [--budget-usd X] [--out DIR]
    python -m autoform.nl ...
"""
from __future__ import annotations

import argparse
import hashlib
import importlib
import json
import os
import re
import sys
import threading
import time
import traceback
from contextlib import contextmanager
from pathlib import Path

from .schema import FILES, dump

STAGES = ('translate', 'describe', 'formalize', 'check', 'prove')
NEEDS = {'describe': ('translation',), 'formalize': ('translation', 'english'),
         'check': ('translation', 'statements'), 'prove': ('translation', 'statements', 'checks')}
OUTPUT = {'translate': 'translation', 'describe': 'english', 'formalize': 'statements', 'check': 'checks',
          'prove': 'proofs'}
SKIP_DIRS = {'.git', '.hg', '.svn', '__pycache__', '.lake', 'node_modules', '.venv', 'venv', '.tox', 'build', 'dist'}


def _impl(stage: str):
    """The stage function, imported lazily (tests replace this)."""
    return getattr(importlib.import_module(f'autoform.nl.{stage}'), stage)


def is_url(source: str) -> bool:
    return bool(re.match(r'^(https?|ssh|git)://|^git@[^:]+:', str(source)))


def default_module(source: str) -> str:
    base = re.sub(r'\.git$', '', str(source).rstrip('/').split('/')[-1].split(':')[-1]) or 'Source'
    words = [w for w in re.split(r'[^A-Za-z0-9]+', base) if w]
    name = ''.join(w[:1].upper() + w[1:] for w in words) or 'Source'
    return 'Nl' + name


def default_lean_root() -> Path:
    here = Path(__file__).resolve().parents[3]
    for cand in (Path.cwd(), here):
        if (cand / 'lakefile.toml').is_file() or (cand / 'lakefile.lean').is_file():
            return cand
    return here


def source_fingerprint(source: str) -> str:
    """Cheap digest of a source tree (paths, sizes, mtimes); the URL itself for remotes."""
    if is_url(source) or not Path(source).exists():
        return str(source)
    h = hashlib.sha256()
    root = Path(source).resolve()
    for dirpath, dirs, files in os.walk(root):
        dirs[:] = sorted(d for d in dirs if d not in SKIP_DIRS)
        for name in sorted(files):
            f = Path(dirpath) / name
            try:
                st = f.stat()
            except OSError:
                continue
            h.update(f'{f.relative_to(root)}\0{st.st_size}\0{st.st_mtime_ns}\n'.encode())
    return f'{root}:{h.hexdigest()}'


def _hash(*parts) -> str:
    h = hashlib.sha256()
    for p in parts:
        h.update(p if isinstance(p, bytes) else json.dumps(p, sort_keys=True, default=str).encode())
        h.update(b'\0')
    return h.hexdigest()


def _file_bytes(out: Path, key: str) -> bytes:
    f = out / FILES[key]
    return f.read_bytes() if f.is_file() else b''


def _load(out: Path, key: str):
    f = out / FILES[key]
    return json.loads(f.read_text()) if f.is_file() else None


@contextmanager
def metered():
    """Sum the cost of every llm.ask call made while active (best effort: stages that
    call the backend through `llm.ask`/`llm.ask_json`)."""
    from . import llm
    orig, box, lock = llm.ask, [0.0], threading.Lock()

    def ask(*a, **k):
        text, cost = orig(*a, **k)
        with lock:
            box[0] += float(cost or 0)
        return text, cost

    llm.ask = ask
    try:
        yield box
    finally:
        llm.ask = orig


def run(source, *, module=None, out=None, lean_root=None, functions=None, prove=True, runtime=True,
        budget_usd=None, resume=True, ref=None, subdir=None, domain_size=64, parallel=None) -> dict:
    source = str(source)
    if not is_url(source) and Path(source).exists():
        source = str(Path(source).resolve())
    module = module or default_module(source)
    lean_root = Path(lean_root).resolve() if lean_root else default_lean_root()
    out = Path(out) if out else Path.cwd() / 'artifacts/nl' / module
    out.mkdir(parents=True, exist_ok=True)
    functions = list(functions or [])
    runf = out / 'run.json'
    previous = {}
    if resume and runf.is_file():
        try:
            previous = json.loads(runf.read_text()).get('stages', {})
        except ValueError:
            previous = {}
    info = {'source': source, 'module': module, 'lean_root': str(lean_root), 'out': str(out),
            'functions': functions, 'prove': prove, 'runtime': runtime, 'budget_usd': budget_usd,
            'started': time.strftime('%Y-%m-%dT%H:%M:%S'), 'stages': {}}
    spent = 0.0

    def save():
        info['cost_usd'] = round(spent, 4)
        runf.write_text(json.dumps(info, indent=1, default=str))

    for stage in STAGES:
        key = OUTPUT[stage]
        rec = info['stages'][stage] = {'status': 'pending', 'output': FILES[key]}
        if stage == 'prove' and not prove:
            rec['status'] = 'disabled'
            save()
            continue
        missing = [k for k in NEEDS.get(stage, ()) if not (out / FILES[k]).is_file()]
        if missing:
            rec.update(status='blocked', error='missing ' + ', '.join(FILES[k] for k in missing))
            save()
            continue
        if stage == 'translate':
            inputs = _hash(source_fingerprint(source), module, str(lean_root), ref, subdir)
        else:
            extra = {'describe': [functions], 'check': [runtime, domain_size], 'prove': [budget_usd]}.get(stage, [])
            inputs = _hash(*[_file_bytes(out, k) for k in NEEDS[stage]], *extra)
        rec['input_hash'] = inputs
        prev = previous.get(stage, {})
        if resume and prev.get('status') in ('ok', 'resumed') and prev.get('input_hash') == inputs \
                and (out / FILES[key]).is_file():
            rec.update(status='resumed', seconds=0.0, cost_usd=0.0)
            save()
            continue
        stale = out / FILES[key]
        if stale.is_file():   # its inputs changed (or no resume): never let later stages read it
            stale.replace(stale.with_name(stale.name + '.stale'))
        started, box = time.time(), [0.0]
        try:
            with metered() as box:
                fn = _impl(stage)
                kw = {}
                if stage == 'translate':
                    result = fn(source, module, str(lean_root), out, ref=ref, subdir=subdir)
                else:
                    translation = _load(out, 'translation')
                    if stage == 'describe':
                        if functions:
                            kw['functions'] = functions
                        result = fn(translation, out, **kw)
                    elif stage == 'formalize':
                        result = fn(translation, _load(out, 'english'), out, **kw)
                    elif stage == 'check':
                        result = fn(translation, _load(out, 'statements'), out, domain_size=domain_size,
                                    runtime=runtime)
                    else:
                        remaining = None if budget_usd is None else max(0.0, budget_usd - spent)
                        if parallel:
                            kw['parallel'] = parallel
                        result = fn(translation, _load(out, 'statements'), _load(out, 'checks'), out,
                                    budget_usd=remaining, **kw)
            cost = box[0]
            if stage == 'prove':
                cost += sum(float((r.get('cost_usd') if isinstance(r, dict) else getattr(r, 'cost_usd', 0)) or 0)
                            for r in result or [])
            if not (out / FILES[key]).is_file():
                dump(result, out / FILES[key])
            rec.update(status='ok', count=len(result) if isinstance(result, list) else None)
        except Exception as exc:  # graceful degradation: record, keep going
            # A partial output the stage chose to write is kept, and later stages use it.
            cost = box[0]
            rec.update(status='failed', error=f'{type(exc).__name__}: {exc}',
                       traceback=traceback.format_exc()[-4000:], partial_output=(out / FILES[key]).is_file())
        rec.update(seconds=round(time.time() - started, 2), cost_usd=round(cost, 4))
        spent += cost
        save()

    from .report import report
    started = time.time()
    try:
        rep = report(out, proofs=[] if not prove else None, run_info=info, functions=functions)
        info['stages']['report'] = {'status': 'ok', 'seconds': round(time.time() - started, 2),
                                    'output': FILES['report']}
    except Exception as exc:
        rep = {}
        info['stages']['report'] = {'status': 'failed', 'error': f'{type(exc).__name__}: {exc}',
                                    'traceback': traceback.format_exc()[-4000:]}
    info['finished'] = time.strftime('%Y-%m-%dT%H:%M:%S')
    save()
    if rep:   # rewrite with the final run info (report stage timing included)
        rep['run'] = info
        (out / FILES['report']).write_text(json.dumps(rep, indent=1, ensure_ascii=False, default=str))
    return {'out': str(out), 'run': info, 'totals': rep.get('totals', {}),
            'report': str(out / FILES['report']), 'report_md': str(out / 'report.md'),
            'potential_bugs': len((rep.get('findings') or {}).get('potential_bugs', []))}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog='autoform autoformalize',
                                 description='Code -> Lean model -> English -> Lean statements -> bounded kernel + '
                                             'real-runtime check -> kernel-checked proofs -> report.')
    ap.add_argument('source', help='git URL or local directory')
    ap.add_argument('module', nargs='?', help='Lean module suffix (Autoform.Generated.<Module>)')
    ap.add_argument('--functions', nargs='+', default=[], help='only these functions (source or qualified names)')
    ap.add_argument('--no-prove', action='store_true', help='stop after checking')
    ap.add_argument('--no-runtime', action='store_true', help='do not execute the source code')
    ap.add_argument('--budget-usd', type=float, help='total model spend cap (enforced for proving)')
    ap.add_argument('--out', type=Path, help='run directory (default: ./artifacts/nl/<Module>)')
    ap.add_argument('--lean-root', type=Path, help='Lean project root (default: this checkout)')
    ap.add_argument('--ref', help='git ref to check out')
    ap.add_argument('--subdir', help='directory inside the source to analyze')
    ap.add_argument('--no-resume', action='store_true', help='rerun every stage')
    a = ap.parse_args(argv)
    res = run(a.source, module=a.module, out=a.out, lean_root=a.lean_root, functions=a.functions,
              prove=not a.no_prove, runtime=not a.no_runtime, budget_usd=a.budget_usd, resume=not a.no_resume,
              ref=a.ref, subdir=a.subdir)
    for name, st in res['run']['stages'].items():
        print(f"{name:10s} {st.get('status'):9s} {st.get('seconds', '')!s:>8}s  ${st.get('cost_usd', 0)}"
              + (f"  {st['error'].splitlines()[0][:140]}" if st.get('error') else ''))
    t = res['totals']
    if t:
        print(f"\nstatements {t['statements']} (elaborated {t['statements_elaborated']}); bounded "
              f"{t['bounded_holds']}; refuted model/runtime {t['refuted_by_model']}/{t['refuted_by_runtime']}; "
              f"proved {t['proved']}; potential bugs {t['potential_bugs']}")
    print(f"Report: {res['report_md']}")
    if res['run']['stages']['translate']['status'] in ('failed', 'blocked'):
        return 2
    return 1 if res['potential_bugs'] else 0


if __name__ == '__main__':
    sys.exit(main())
