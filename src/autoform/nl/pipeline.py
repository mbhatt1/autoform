"""The natural-language autoformalizer end to end.

    model (default) ──┐
    translate (--deep)┴─► describe → formalize → check → prove [→ refine (--deep-too)] → report
    with a judge (--judge, the CLI default):
                        describe → select → formalize → check → adjudicate → prove …

`model` (autoform.nl.model) has a language model write a plain Lean def per function and
validates it against the real code and an independent second translation (level L0).
`translate` is the deep Joern → Core translation (`runFunc`). `--deep-too` runs both: the
English, statements, checks and proofs are about the models, and `refine` then tries to
prove each validated model equal to its hole-free deep translation (level L1). If the model
stage fails under `--deep-too`, the later stages fall back to the deep translation.

Every stage reads and writes JSON in one run directory (schema.FILES). `run.json` records,
per stage, the hash of its inputs, its status, wall time and model spend. With `resume`, a
stage whose outputs exist and whose recorded input hash matches is not rerun. A failing
stage is recorded and later stages run on whatever exists (a stage whose inputs are
missing is `blocked`); the report is always written.

    autoform autoformalize <url|dir> [Module] [--deep | --deep-too] [--no-second]
                           [--functions f g] [--no-prove] [--no-runtime] [--budget-usd X]
                           [--judge auto|semif|heuristic|replay:PATH|none]
                           [--max-properties-per-function N] [--repair-rounds N] [--out DIR]

`select` (autoform.nl.judge) ranks the English properties with the typed-decision judge and
allocates `--budget-usd` across functions; `formalize` and `prove` then spend in that order
and stop when the budget is gone. `adjudicate` (autoform.nl.repair) classifies each refuted
statement (deterministic gates first), turns cross-validated REAL_BUG readings into
findings, and repairs BAD_SPEC / MISSING_PRECONDITION properties through formalize → check
again. The judge never sets a status.
    python -m autoform.nl ...
"""
from __future__ import annotations

import argparse
import hashlib
import importlib
import json
import os
import re
import shutil
import sys
import threading
import time
import traceback
from contextlib import contextmanager
from pathlib import Path

from .schema import FILES, dump

MODEL_STAGES = ('model', 'describe', 'formalize', 'check', 'prove')
DEEP_STAGES = ('translate', 'describe', 'formalize', 'check', 'prove')
DEEP_TOO_STAGES = ('model', 'translate', 'describe', 'formalize', 'check', 'prove', 'refine')
STAGES = MODEL_STAGES
MODES = {'model': MODEL_STAGES, 'deep': DEEP_STAGES, 'deep_too': DEEP_TOO_STAGES}
NEEDS = {'describe': ('translation',), 'formalize': ('translation', 'english'),
         'select': ('translation', 'english'), 'adjudicate': ('translation', 'statements', 'checks'),
         'check': ('translation', 'statements'), 'prove': ('translation', 'statements', 'checks'),
         'refine': ('translation', 'models', 'deep_translation')}
OUTPUT = {'model': 'translation', 'translate': 'translation', 'describe': 'english', 'formalize': 'statements',
          'check': 'checks', 'prove': 'proofs', 'refine': 'refine', 'select': 'selection',
          'adjudicate': 'adjudication'}
STAGE_MODULE = {'select': 'judge', 'adjudicate': 'repair'}
SKIP_DIRS = {'.git', '.hg', '.svn', '__pycache__', '.lake', 'node_modules', '.venv', 'venv', '.tox', 'build', 'dist'}


def _impl(stage: str):
    """The stage function, imported lazily (tests replace this)."""
    return getattr(importlib.import_module(f'autoform.nl.{STAGE_MODULE.get(stage, stage)}'), stage)


def with_judge(stages: tuple) -> tuple:
    """Insert `select` after describe and `adjudicate` after check."""
    out = []
    for s in stages:
        out.append(s)
        if s == 'describe':
            out.append('select')
        elif s == 'check':
            out.append('adjudicate')
    return tuple(out)


def outputs(stage: str, mode: str) -> tuple:
    """schema.FILES keys a stage writes in this mode (all must exist for a resume)."""
    if stage == 'model':
        return ('translation', 'models')
    if stage == 'translate' and mode == 'deep_too':
        return ('deep_translation',)
    return (OUTPUT[stage],)


def is_url(source: str) -> bool:
    return bool(re.match(r'^(https?|ssh|git|file)://|^git@[^:]+:', str(source)))


def default_module(source: str) -> str:
    base = re.sub(r'\.git$', '', str(source).rstrip('/').split('/')[-1].split(':')[-1]) or 'Source'
    words = [w for w in re.split(r'[^A-Za-z0-9]+', base) if w]
    name = ''.join(w[:1].upper() + w[1:] for w in words) or 'Source'
    return 'NL' + name   # NL*-named modules are per-run and not tracked (see the ignore file)


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


def local_source(source: str, out: Path, module: str, ref=None, subdir=None) -> str:
    """A local directory for the model stage (which reads Python files directly): the
    directory itself, its `subdir`, or a checkout of a remote repository under `out`."""
    if not is_url(source) and not ref:
        root = Path(source).resolve() / (subdir or '.')
        return str(root.resolve())
    from autoform.repository import resolve_source
    path, _ = resolve_source(source, out, module, ref=ref, subdir=subdir)
    return str(path)


def _hash(*parts) -> str:
    h = hashlib.sha256()
    for p in parts:
        h.update(p if isinstance(p, bytes) else json.dumps(p, sort_keys=True, default=str).encode())
        h.update(b'\0')
    return h.hexdigest()


def _file_bytes(out: Path, key: str) -> bytes:
    f = out / FILES[key]
    return f.read_bytes() if f.is_file() else b''


def _above_reserve(remaining, selection):
    """What formalize and repairs may spend: the remaining budget less selection's proving reserve."""
    if remaining is None:
        return None
    return max(0.0, remaining - ((selection or {}).get('prove_reserve_usd') or 0.0))


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


def _result_cost(result) -> float:
    return sum(float((r.get('cost_usd') if isinstance(r, dict) else getattr(r, 'cost_usd', 0)) or 0)
               for r in result or [])


def run(source, *, module=None, out=None, lean_root=None, functions=None, prove=True, runtime=True,
        budget_usd=None, resume=True, ref=None, subdir=None, domain_size=64, parallel=None,
        deep=False, deep_too=False, second=True, repairs=3, judge=None, max_properties_per_function=None,
        repair_rounds=2, tests=()) -> dict:
    """`judge=None` runs without the judge stages (select, adjudicate); the CLI default is 'auto'."""
    source = str(source)
    if not is_url(source) and Path(source).exists():
        source = str(Path(source).resolve())
    mode = 'deep_too' if deep_too else 'deep' if deep else 'model'
    stages = MODES[mode]
    judge = None if judge in (None, 'none') else judge
    if judge:
        stages = with_judge(stages)
    module = module or default_module(source)
    lean_root = Path(lean_root).resolve() if lean_root else default_lean_root()
    out = Path(out) if out else Path.cwd() / 'artifacts/nl' / module
    out.mkdir(parents=True, exist_ok=True)
    functions = list(functions or [])
    tests = [str(Path(t).resolve()) for t in tests or ()]   # extra test directories (--tests)
    runf = out / 'run.json'
    previous = {}
    if resume and runf.is_file():
        try:
            previous = json.loads(runf.read_text()).get('stages', {})
        except ValueError:
            previous = {}
    info = {'source': source, 'module': module, 'mode': mode, 'lean_root': str(lean_root), 'out': str(out),
            'functions': functions, 'prove': prove, 'runtime': runtime, 'budget_usd': budget_usd,
            'second': second, 'judge': judge, 'max_properties_per_function': max_properties_per_function,
            'tests': tests, 'started': time.strftime('%Y-%m-%dT%H:%M:%S'), 'stages': {}}
    spent = 0.0

    def save():
        info['cost_usd'] = round(spent, 4)
        runf.write_text(json.dumps(info, indent=1, default=str))

    for stage in stages:
        keys = outputs(stage, mode)
        rec = info['stages'][stage] = {'status': 'pending', 'output': ', '.join(FILES[k] for k in keys)}
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
        elif stage == 'model':
            inputs = _hash('model', source_fingerprint(source), module, str(lean_root), ref, subdir, functions,
                           second, repairs, *([tests] if tests else []))
        else:
            extra = {'describe': [functions] + ([tests] if tests else []), 'check': [runtime, domain_size],
                     'prove': [budget_usd],
                     'refine': [_file_bytes(out, 'statements'), budget_usd, domain_size],
                     'select': [judge, budget_usd, max_properties_per_function, prove],
                     'adjudicate': [judge, _file_bytes(out, 'english'), _file_bytes(out, 'selection'), runtime,
                                    domain_size, budget_usd, repair_rounds]}.get(stage, [])
            if judge and stage == 'formalize':
                extra = [_file_bytes(out, 'selection'), budget_usd]
            if judge and stage == 'prove':
                extra = extra + [_file_bytes(out, 'adjudication'), _file_bytes(out, 'selection')]
            inputs = _hash(*[_file_bytes(out, k) for k in NEEDS[stage]], *extra)
        rec['input_hash'] = inputs
        prev = previous.get(stage, {})
        # Resume only when the inputs match AND the outputs are the bytes this stage wrote
        # (translation.json is written by `model` or by `translate`, depending on the mode).
        if resume and prev.get('status') in ('ok', 'resumed') and prev.get('input_hash') == inputs \
                and all((out / FILES[k]).is_file() for k in keys) \
                and prev.get('output_hash') == _hash(*[_file_bytes(out, k) for k in keys]):
            rec.update(status='resumed', seconds=0.0, cost_usd=0.0, output_hash=prev['output_hash'],
                       earlier_cost_usd=round((prev.get('cost_usd') or 0) + (prev.get('earlier_cost_usd') or 0), 4))
            spent += rec['earlier_cost_usd']   # the budget covers the whole run, resumed stages included
            save()
            continue
        for k in keys:   # its inputs changed (or no resume): never let later stages read it
            stale = out / FILES[k]
            if stale.is_file():
                stale.replace(stale.with_name(stale.name + '.stale'))
        key = keys[0]
        started, box = time.time(), [0.0]
        remaining = None if budget_usd is None else max(0.0, budget_usd - spent)
        try:
            with metered() as box:
                fn = _impl(stage)
                kw = {}
                if stage == 'translate':
                    if mode == 'deep_too':   # the model owns translation.json; the deep one lives beside it
                        sub = out / 'deep'
                        sub.mkdir(exist_ok=True)
                        (sub / FILES['translation']).unlink(missing_ok=True)
                        result = fn(source, module, str(lean_root), sub, ref=ref, subdir=subdir)
                        if (sub / FILES['translation']).is_file():
                            shutil.copyfile(sub / FILES['translation'], out / FILES[key])
                    else:
                        result = fn(source, module, str(lean_root), out, ref=ref, subdir=subdir)
                elif stage == 'model':
                    root = local_source(source, out, module, ref, subdir)
                    if functions:
                        kw['functions'] = functions
                    if parallel:
                        kw['parallel'] = parallel
                    if tests:
                        kw['tests'] = tests
                    if budget_usd is not None:   # the model stage starts no new function past it
                        kw['budget_usd'] = budget_usd
                    result = fn(root, out, str(lean_root), module=module, repairs=repairs, second=second, **kw)
                else:
                    translation = _load(out, 'translation')
                    if stage == 'describe':
                        if functions:
                            kw['functions'] = functions
                        if tests:
                            kw['tests'] = tests
                        result = fn(translation, out, **kw)
                    elif stage == 'formalize':
                        selection = _load(out, 'selection') if judge else None
                        if selection:
                            from .judge import formalize_within_budget
                            result = formalize_within_budget(fn, translation, _load(out, 'english'), out, selection,
                                                             _above_reserve(remaining, selection), **kw)
                        else:
                            result = fn(translation, _load(out, 'english'), out, **kw)
                    elif stage == 'select':
                        result = fn(translation, _load(out, 'english'), out, judge=judge, budget_usd=remaining,
                                    max_properties_per_function=max_properties_per_function, prove=prove)
                    elif stage == 'adjudicate':
                        result = fn(translation, _load(out, 'statements'), _load(out, 'checks'), out, judge=judge,
                                    english=_load(out, 'english'), selection=_load(out, 'selection'),
                                    models=_load(out, 'models'), formalize_fn=_impl('formalize'),
                                    check_fn=_impl('check'), rounds=repair_rounds,
                                    budget_usd=_above_reserve(remaining, _load(out, 'selection')),
                                    domain_size=domain_size, runtime=runtime)
                    elif stage == 'check':
                        result = fn(translation, _load(out, 'statements'), out, domain_size=domain_size,
                                    runtime=runtime)
                    else:
                        if parallel:
                            kw['parallel'] = parallel
                        if stage == 'prove':
                            statements, checks = _load(out, 'statements'), _load(out, 'checks')
                            adjudication = _load(out, 'adjudication') if judge else None
                            if adjudication:   # repaired statements are proved too
                                statements = statements + adjudication.get('statements', [])
                                checks = checks + adjudication.get('checks', [])
                            if judge:          # highest utility first: the budget runs out on the rest
                                from .judge import order_by_utility
                                statements = order_by_utility(statements, out)
                            result = fn(translation, statements, checks, out, budget_usd=remaining, **kw)
                        else:
                            result = fn(translation, _load(out, 'models'), _load(out, 'deep_translation'), out,
                                        statements=_load(out, 'statements'), budget_usd=remaining,
                                        domain_size=domain_size, **kw)
            cost = box[0]
            if stage in ('prove', 'refine'):
                cost += _result_cost(result)
            if not (out / FILES[key]).is_file():
                dump(result, out / FILES[key])
            rec.update(status='ok', count=len(result) if isinstance(result, list) else None,
                       output_hash=_hash(*[_file_bytes(out, k) for k in keys]))
        except Exception as exc:  # graceful degradation: record, keep going
            # A partial output the stage chose to write is kept, and later stages use it.
            cost = box[0]
            rec.update(status='failed', error=f'{type(exc).__name__}: {exc}',
                       traceback=traceback.format_exc()[-4000:], partial_output=(out / FILES[key]).is_file())
        rec.update(seconds=round(time.time() - started, 2), cost_usd=round(cost, 4))
        spent += cost
        if stage == 'translate' and mode == 'deep_too' and not (out / FILES['translation']).is_file() \
                and (out / FILES['deep_translation']).is_file():
            # The model stage produced nothing: the statements are about the deep translation instead.
            shutil.copyfile(out / FILES['deep_translation'], out / FILES['translation'])
            info['fallback'] = 'model stage failed; later stages use the deep translation'
            rec['note'] = info['fallback']
        save()

    if judge:
        try:
            from .judge import finalize_decisions
            info['decisions'] = finalize_decisions(out)
        except Exception as exc:  # the decision log is diagnostics; never block the report
            info['decisions'] = {'error': f'{type(exc).__name__}: {exc}'}
    from .report import report
    started = time.time()
    has_models = 'model' in stages and not info.get('fallback')
    try:
        rep = report(out, proofs=[] if not prove else None, run_info=info, functions=functions,
                     models=None if has_models else [], refine=None if mode == 'deep_too' else [],
                     deep_translation=None if mode == 'deep_too' else {},
                     selection=None if judge else {}, adjudication=None if judge else {})
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
    ap.add_argument('module', nargs='?', help='Lean module suffix (Autoform.NLModel.<Module> / Generated.<Module>)')
    how = ap.add_mutually_exclusive_group()
    how.add_argument('--deep', action='store_true',
                     help='use the deep Joern -> Core translation instead of AI-written models')
    how.add_argument('--deep-too', action='store_true',
                     help='run both; try to prove each validated model equal to its deep translation (L1)')
    ap.add_argument('--no-second', action='store_true',
                    help='skip the independent second translation when validating models')
    ap.add_argument('--repairs', type=int, default=3, help='model repair rounds per function (default 3)')
    ap.add_argument('--parallel', type=int, help='concurrent model/prover jobs')
    ap.add_argument('--functions', nargs='+', default=[], help='only these functions (source or qualified names)')
    ap.add_argument('--no-prove', action='store_true', help='stop after checking')
    ap.add_argument('--no-runtime', action='store_true', help='do not execute the source code')
    ap.add_argument('--budget-usd', type=float,
                    help='total model spend cap; with a judge it is allocated across functions by utility and '
                         'enforced for formalize, repairs and proving (otherwise for proving only)')
    ap.add_argument('--judge', default='auto',
                    help='typed-decision judge for selection and counterexample adjudication: auto (SemIf if '
                         'installed, else heuristic), semif, heuristic, replay:PATH, or none')
    ap.add_argument('--max-properties-per-function', type=int,
                    help='formalize at most N properties per function (highest utility first)')
    ap.add_argument('--repair-rounds', type=int, default=2, help='repair rounds per refuted property (default 2)')
    ap.add_argument('--domain-size', type=int, default=64, help='points per bounded check (default 64)')
    ap.add_argument('--out', type=Path, help='run directory (default: ./artifacts/nl/<Module>)')
    ap.add_argument('--lean-root', type=Path, help='Lean project root (default: this checkout)')
    ap.add_argument('--ref', help='git ref to check out')
    ap.add_argument('--subdir', help='directory inside the source to analyze')
    ap.add_argument('--no-resume', action='store_true', help='rerun every stage')
    ap.add_argument('--tests', action='append', default=[], metavar='DIR',
                    help='a test directory outside the source tree (repeatable); its tests are traced '
                         'for model inputs and shown to describe')
    a = ap.parse_args(argv)
    res = run(a.source, module=a.module, out=a.out, lean_root=a.lean_root, functions=a.functions,
              prove=not a.no_prove, runtime=not a.no_runtime, budget_usd=a.budget_usd, resume=not a.no_resume,
              ref=a.ref, subdir=a.subdir, domain_size=a.domain_size, parallel=a.parallel, deep=a.deep,
              deep_too=a.deep_too, second=not a.no_second, repairs=a.repairs, judge=a.judge,
              max_properties_per_function=a.max_properties_per_function, repair_rounds=a.repair_rounds,
              tests=a.tests)
    for name, st in res['run']['stages'].items():
        print(f"{name:10s} {st.get('status'):9s} {st.get('seconds', '')!s:>8}s  ${st.get('cost_usd', 0)}"
              + (f"  {st['error'].splitlines()[0][:140]}" if st.get('error') else ''))
    t = res['totals']
    if t:
        print(f"\nstatements {t['statements']} (elaborated {t['statements_elaborated']}); bounded "
              f"{t['bounded_holds']}; refuted model/runtime {t['refuted_by_model']}/{t['refuted_by_runtime']}; "
              f"proved {t['proved']}; potential bugs {t['potential_bugs']}; model defects {t['model_defects']}")
        lv = t.get('by_level') or {}
        if lv:
            print('by level: ' + '; '.join(f"{k}: {v['functions']} functions, {v['proved']} proved"
                                           for k, v in lv.items()))
    dec = res['run'].get('decisions') or {}
    if dec.get('decisions') is not None:
        print(f"judge decisions {dec['decisions']} (forced {dec['forced']}); JEVBench rows {dec['jevbench_rows']} "
              f"{dec.get('labels')}")
    print(f"Report: {res['report_md']}")
    if not (Path(res['out']) / FILES['translation']).is_file():
        return 2
    return 1 if res['potential_bugs'] else 0


if __name__ == '__main__':
    sys.exit(main())
