#!/usr/bin/env python3
"""regression.py -- what could be proven about a codebase at one commit that cannot at another?

A pipeline run (`autoform.sh`, `autoform source`) leaves a report directory with:

    ast-<Module>.json      every translated function, holes inline (`hole` / `holeS`)
    conformance.json       runtime observations: per function, per case, agree/diverge
    specs.json             one record per synthesized theorem: proved, refuted, open
    pipeline.json          which stage the run reached and its status
    repository.json        the commit that was analyzed (when the source was a Git ref)

`profile()` reduces one such directory to the facts a proof-based comparison can stand
on: which functions translate without holes, which theorems hold in the kernel, which
recorded runtime cases agree with the model, and what each case's outcome was.

`compare()` diffs two profiles. It never guesses why something changed; it reports:

    regressions        a fact that held at BASE and does not hold at HEAD
    improvements       the reverse
    behavior_changes   the same function on the same recorded inputs has a different
                       outcome at HEAD -- the semantic difference between the commits,
                       proven in the kernel on both sides when `proven_both` is true
    added / removed    functions present at one commit only (never a regression by
                       themselves; a removed function's lost theorems are listed)

Exit status of `compare`: 0 nothing regressed and no behavior changed; 1 at least one
regression or behavior change; 2 a report is missing or unreadable. A change in a
recorded outcome is reported under its own heading rather than folded into
"regressions", because the tool cannot tell an intended change from a bug -- only that
the two commits provably compute different things on the same inputs.
"""
from __future__ import annotations

import argparse
import datetime
import json
import os
from pathlib import Path
import sys

SCHEMA_VERSION = 1


class ReportError(ValueError):
    """A report directory does not hold what a comparison needs."""


def _load(path):
    try:
        with open(path, encoding='utf-8') as stream:
            return json.load(stream)
    except FileNotFoundError:
        return None
    except (OSError, ValueError) as exc:
        raise ReportError(f'{path}: unreadable: {exc}') from exc


def _walk(value):
    pending = [value]
    while pending:
        current = pending.pop()
        if isinstance(current, dict):
            yield current
            pending.extend(current.values())
        elif isinstance(current, list):
            pending.extend(current)


def function_holes(function):
    """Every hole label in a translated function, sorted, duplicates kept."""
    labels = []
    for node in _walk(function.get('body')):
        if node.get('k') in ('hole', 'holeS'):
            labels.append(str(node.get('label', '')))
    return sorted(labels)


def _case_key(case):
    return json.dumps([case.get('name'), case.get('self'), case.get('args')],
                      sort_keys=True, separators=(',', ':'))


def profile(report_dir, module=None):
    """The provable facts recorded by one pipeline run."""
    report_dir = Path(report_dir)
    if not report_dir.is_dir():
        raise ReportError(f'{report_dir}: not a report directory')
    pipeline = _load(report_dir / 'pipeline.json') or {}
    module = module or pipeline.get('module')
    if module is None:
        candidates = sorted(report_dir.glob('ast-*.json'))
        if len(candidates) == 1:
            module = candidates[0].name[len('ast-'):-len('.json')]
    if module is None:
        raise ReportError(f'{report_dir}: no pipeline.json or ast-<Module>.json to name the module')
    ast = _load(report_dir / f'ast-{module}.json')
    if ast is None:
        raise ReportError(f'{report_dir}: no ast-{module}.json; the run did not reach translation')
    if isinstance(ast, dict):
        ast = ast.get('functions', [])
    conformance = _load(report_dir / 'conformance.json') or {}
    specs = _load(report_dir / 'specs.json') or {}
    repository = _load(report_dir / 'repository.json') or {}

    functions = {}
    for function in ast:
        name = function.get('name')
        if not isinstance(name, str):
            continue
        functions[name] = {'file': function.get('file'), 'holes': function_holes(function),
                           'conformance': None, 'cases': {'agree': 0, 'diverge': 0, 'other': 0}}
    for name, status in (conformance.get('coverage') or {}).get('by_status', {}).items():
        if name in functions:
            functions[name]['conformance'] = status
    cases = {}
    for case in conformance.get('runtime_cases') or []:
        name = case.get('name')
        comparison = case.get('comparison')
        if name in functions:
            bucket = ('agree' if comparison == 'agree' else
                      'diverge' if comparison == 'diverge' else 'other')
            functions[name]['cases'][bucket] += 1
        cases[_case_key(case)] = {'name': name, 'outcome': case.get('outcome'),
                                  'comparison': comparison, 'origin': case.get('origin')}

    theorems = {}
    for record in specs.get('specs') or []:
        identifier = record.get('id')
        if not isinstance(identifier, str):
            continue
        theorems[identifier] = {'family': record.get('family'), 'subject': record.get('subject'),
                                'status': record.get('status'), 'proved': bool(record.get('proved')),
                                'domain': record.get('domain')}

    return {
        'schema_version': SCHEMA_VERSION,
        'module': module,
        'report_dir': str(report_dir),
        'commit': repository.get('commit'),
        'source': repository.get('input') or pipeline.get('source'),
        'pipeline': {'stage': pipeline.get('stage'), 'status': pipeline.get('status'),
                     'exit_code': pipeline.get('exit_code')},
        'functions': functions,
        'theorems': theorems,
        'cases': cases,
        'summary': {
            'functions': len(functions),
            'hole_free': sum(1 for f in functions.values() if not f['holes']),
            'theorems': len(theorems),
            'proved': sum(1 for t in theorems.values() if t['proved']),
            'cases': len(cases),
            'agree': sum(1 for c in cases.values() if c['comparison'] == 'agree'),
            'diverge': sum(1 for c in cases.values() if c['comparison'] == 'diverge'),
        },
    }


def _finding(kind, subject, detail, **extra):
    return dict(kind=kind, subject=subject, detail=detail, **extra)


def compare(base, head):
    """Diff two profiles. Pure; the result is JSON-serializable."""
    regressions, improvements, behavior, added, removed, notes = [], [], [], [], [], []

    if base['pipeline'].get('status') == 'passed' and head['pipeline'].get('status') != 'passed':
        regressions.append(_finding(
            'pipeline', head['module'],
            f"the pipeline passed at base but reached stage {head['pipeline'].get('stage')!r} "
            f"with status {head['pipeline'].get('status')!r} at head"))
    elif base['pipeline'].get('status') != 'passed' and head['pipeline'].get('status') == 'passed':
        improvements.append(_finding('pipeline', head['module'], 'the pipeline now passes'))

    base_fns, head_fns = base['functions'], head['functions']
    for name in sorted(set(base_fns) - set(head_fns)):
        lost = sorted(t for t, rec in base['theorems'].items() if rec['subject'] == name and rec['proved'])
        removed.append(dict(subject=name, file=base_fns[name].get('file'), proved_theorems_lost=lost))
    for name in sorted(set(head_fns) - set(base_fns)):
        added.append(dict(subject=name, file=head_fns[name].get('file'),
                          holes=head_fns[name]['holes']))
    for name in sorted(set(base_fns) & set(head_fns)):
        before, after = base_fns[name], head_fns[name]
        if not before['holes'] and after['holes']:
            regressions.append(_finding(
                'translation', name,
                'translated without holes at base; at head it holes: ' + ', '.join(sorted(set(after['holes']))),
                holes=after['holes']))
        elif before['holes'] and not after['holes']:
            improvements.append(_finding('translation', name, 'holes closed: ' + ', '.join(sorted(set(before['holes'])))))
        elif set(before['holes']) != set(after['holes']):
            notes.append(_finding('translation', name, 'hole labels changed',
                                  base=sorted(set(before['holes'])), head=sorted(set(after['holes']))))
        if before['cases']['diverge'] == 0 and before['cases']['agree'] > 0 and after['cases']['diverge'] > 0:
            regressions.append(_finding(
                'conformance', name,
                f"every recorded case agreed with the runtime at base ({before['cases']['agree']}); "
                f"{after['cases']['diverge']} diverge at head", cases=after['cases']))
        elif before['cases']['diverge'] > 0 and after['cases']['diverge'] == 0 and after['cases']['agree'] > 0:
            improvements.append(_finding('conformance', name, 'no recorded case diverges at head', cases=after['cases']))

    base_thms, head_thms = base['theorems'], head['theorems']
    for identifier in sorted(set(base_thms) | set(head_thms)):
        before, after = base_thms.get(identifier), head_thms.get(identifier)
        subject = (before or after)['subject']
        if before and after:
            if before['proved'] and not after['proved']:
                regressions.append(_finding('proof', subject,
                                            f"{identifier}: proved at base, {after['status']!r} at head",
                                            theorem=identifier, family=after['family']))
            elif after['proved'] and not before['proved']:
                improvements.append(_finding('proof', subject,
                                             f"{identifier}: {before['status']!r} at base, proved at head",
                                             theorem=identifier, family=after['family']))
        elif before and before['proved'] and subject in head_fns:
            regressions.append(_finding('proof', subject,
                                        f"{identifier}: proved at base, not emitted at head",
                                        theorem=identifier, family=before['family']))
        elif after and after['proved'] and subject in base_fns and not before:
            improvements.append(_finding('proof', subject, f"{identifier}: newly proved at head",
                                         theorem=identifier, family=after['family']))

    def proved_for(profile_, name):
        return any(t['proved'] and t['subject'] == name for t in profile_['theorems'].values())

    for key in sorted(set(base['cases']) & set(head['cases'])):
        before, after = base['cases'][key], head['cases'][key]
        if before['outcome'] != after['outcome']:
            name = after['name']
            behavior.append(dict(
                subject=name, inputs=json.loads(key)[1:], base=before['outcome'], head=after['outcome'],
                proven_both=proved_for(base, name) and proved_for(head, name),
                origin=after.get('origin')))

    verdict = ('regressed' if regressions else
               'behavior-changed' if behavior else 'no-regression')
    return {
        'schema_version': SCHEMA_VERSION,
        'generated_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'module': head['module'],
        'base': {'commit': base['commit'], 'source': base['source'], 'report_dir': base['report_dir'],
                 'pipeline': base['pipeline'], 'summary': base['summary']},
        'head': {'commit': head['commit'], 'source': head['source'], 'report_dir': head['report_dir'],
                 'pipeline': head['pipeline'], 'summary': head['summary']},
        'verdict': verdict,
        'regressions': regressions,
        'improvements': improvements,
        'behavior_changes': behavior,
        'added': added,
        'removed': removed,
        'notes': notes,
        'scope': ('Facts are limited to what the pipeline recorded at each commit: holes in the '
                  'translation, theorems synthesized from recorded runtime cases, and those '
                  'cases themselves. A function the runtime never reached has no cases to '
                  'compare, and an outcome that changed on inputs recorded at only one commit '
                  'is not visible here.'),
    }


def render_markdown(result):
    lines = [f"# Regression report — `{result['module']}`", '']
    for label in ('base', 'head'):
        side = result[label]
        summary = side['summary']
        lines.append(f"- **{label}**: `{side['commit'] or side['source'] or '?'}` — pipeline "
                     f"{side['pipeline'].get('status')}; {summary['hole_free']}/{summary['functions']} "
                     f"functions hole-free; {summary['proved']}/{summary['theorems']} theorems proved; "
                     f"{summary['agree']} agreeing / {summary['diverge']} diverging cases")
    lines += ['', f"**Verdict: {result['verdict']}**", '']

    def section(title, items, fmt):
        if not items:
            return
        lines.append(f'## {title} ({len(items)})')
        lines.append('')
        lines.extend('- ' + fmt(item) for item in items)
        lines.append('')

    section('Regressions', result['regressions'], lambda f: f"`{f['subject']}` [{f['kind']}]: {f['detail']}")
    section('Behavior changes on identical inputs', result['behavior_changes'],
            lambda c: f"`{c['subject']}` {json.dumps(c['inputs'])}: {json.dumps(c['base'])} → "
                      f"{json.dumps(c['head'])}" + (' (proved in the kernel at both commits)' if c['proven_both'] else ''))
    section('Improvements', result['improvements'], lambda f: f"`{f['subject']}` [{f['kind']}]: {f['detail']}")
    section('Added functions', result['added'],
            lambda a: f"`{a['subject']}`" + (f" — holes: {', '.join(sorted(set(a['holes'])))}" if a['holes'] else ''))
    section('Removed functions', result['removed'],
            lambda r: f"`{r['subject']}`" + (f" — proved theorems lost: {', '.join(r['proved_theorems_lost'])}"
                                             if r['proved_theorems_lost'] else ''))
    section('Notes', result['notes'], lambda f: f"`{f['subject']}` [{f['kind']}]: {f['detail']}")
    lines += ['## Scope', '', result['scope'], '']
    return '\n'.join(lines)


def exit_code(result):
    return 1 if result['regressions'] or result['behavior_changes'] else 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0],
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='command', required=True)
    prof = sub.add_parser('profile', help='print the provable facts recorded by one run')
    prof.add_argument('report', help='a pipeline report directory (artifacts/pipeline/<Module>)')
    prof.add_argument('--module')
    comp = sub.add_parser('compare', help='diff the facts recorded by two runs')
    comp.add_argument('base', help='report directory of the earlier commit')
    comp.add_argument('head', help='report directory of the later commit')
    comp.add_argument('--module')
    comp.add_argument('--out', type=Path, help='write the JSON report here')
    comp.add_argument('--markdown', type=Path, help='write the Markdown summary here')
    comp.add_argument('--quiet', action='store_true', help='do not print the summary')
    args = parser.parse_args(argv)
    try:
        if args.command == 'profile':
            print(json.dumps(profile(args.report, args.module), indent=2))
            return 0
        result = compare(profile(args.base, args.module), profile(args.head, args.module))
    except ReportError as exc:
        print(f'regression: {exc}', file=sys.stderr)
        return 2
    text = render_markdown(result)
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(result, indent=2) + '\n')
    if args.markdown:
        args.markdown.parent.mkdir(parents=True, exist_ok=True)
        args.markdown.write_text(text)
    if not args.quiet:
        print(text)
    return exit_code(result)


if __name__ == '__main__':
    sys.exit(main())
