"""`autoform formalize` — the neural-symbolic formalization harness.

    autoform formalize MODULE [--source DIR] [--judge semif|heuristic|replay:FILE] ...
    autoform formalize diff OLD/report.json NEW/report.json
    autoform formalize bench fit-temperature jevbench.jsonl ... --out temps.json
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from . import bench, report
from .pipeline import Harness, Options

EXIT = dict(ok=0, refuted=1, error=2)


def _root(path):
    root = Path(path).resolve()
    if not (root / 'lakefile.toml').is_file() and not (root / 'lakefile.lean').is_file():
        raise SystemExit(f'autoform formalize: {root} is not a Lean project (use --root or --workspace)')
    return root


def main(argv=None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv[:1] == ['diff']:
        ap = argparse.ArgumentParser(prog='autoform formalize diff')
        ap.add_argument('old', type=Path)
        ap.add_argument('new', type=Path)
        ap.add_argument('--json', action='store_true')
        a = ap.parse_args(argv[1:])
        changes = report.diff(json.loads(a.old.read_text()), json.loads(a.new.read_text()))
        if a.json:
            print(json.dumps({k: [x if isinstance(x, dict) else {'before': x[0]['status'], 'after': x[1]['status'],
                                                              'id': x[0]['id']} for x in v]
                              if isinstance(v, list) and v and not isinstance(v[0], str) else v
                              for k, v in changes.items()}, indent=1, default=str))
        else:
            print(report.diff_markdown(changes))
        return 1 if changes['lost'] else 0
    if argv[:1] == ['bench']:
        return bench.main(argv[1:])
    ap = argparse.ArgumentParser(prog='autoform formalize',
                                 description='Generate candidate claims, rank them with a SemIf (OpenJev) judge, '
                                             'verify them in the Lean kernel, refine on counterexamples.')
    ap.add_argument('module', help='translated module name (Autoform/Generated/<Module>.lean)')
    ap.add_argument('--root', '--workspace', dest='root', default='.', help='Lean project root (default: .)')
    ap.add_argument('--source', type=Path, help='source directory (evidence, tests, native replay)')
    ap.add_argument('--ast', type=Path, help='Core AST (default: artifacts/pipeline/<M>/ast-<M>.json or ast-<M>.json)')
    ap.add_argument('--out', type=Path, help='output directory (default: <root>/artifacts/harness/<Module>)')
    ap.add_argument('--judge', default='semif', help='semif (default) | heuristic | replay:DECISIONS.jsonl')
    ap.add_argument('--judge-temperature', type=Path, help='per-task temperatures from `bench fit-temperature`')
    ap.add_argument('--generators', default='template', help='template, llm, or template,llm')
    ap.add_argument('--environment', type=Path, help='environment model and external summaries (JSON)')
    ap.add_argument('--function', action='append', default=[], help='restrict to these functions (repeatable)')
    ap.add_argument('--top-k', type=int, default=8, help='claims selected for proof per function')
    ap.add_argument('--max-refinements', type=int, default=5)
    ap.add_argument('--fuel', type=int, default=1000)
    ap.add_argument('--timeout', type=int, default=900, help='seconds per Lean run')
    ap.add_argument('--deep-proofs', action='store_true', help='use the full portfolio for universal proofs (slow)')
    ap.add_argument('--build', action='store_true', help='rebuild an out-of-date generated module first')
    ap.add_argument('--cache', type=Path, help='proof cache directory (default: <root>/.autoform-harness/cache)')
    ap.add_argument('--no-cache', action='store_true')
    ap.add_argument('--no-native', action='store_true', help='do not execute source code to replay witnesses')
    ap.add_argument('--baseline', type=Path, help='previous report.json: also write formalization-diff.md')
    a = ap.parse_args(argv)
    root = _root(a.root)
    opts = Options(root=root, module=a.module, ast=a.ast, source=a.source.resolve() if a.source else None,
                   out=a.out, judge=a.judge, generators=a.generators, environment=a.environment,
                   functions=a.function, top_k=a.top_k, max_refinements=a.max_refinements, fuel=a.fuel,
                   timeout=a.timeout, deep_proofs=a.deep_proofs, build=a.build,
                   cache=None if a.no_cache else (a.cache or root / '.autoform-harness/cache'),
                   temperature=a.judge_temperature, native=not a.no_native)
    try:
        h = Harness(opts)
        data = h.run()
    except (RuntimeError, FileNotFoundError, ValueError) as exc:
        print(f'autoform formalize: {exc}', file=sys.stderr)
        return EXIT['error']
    print((h.out / 'report.md').read_text().split('## Claims')[0].rstrip())
    print(f'\nFull report: {h.out / "report.md"}')
    if a.baseline:
        changes = report.diff(json.loads(a.baseline.read_text()), data)
        (h.out / 'formalization-diff.md').write_text(report.diff_markdown(changes))
        print(report.diff_markdown(changes))
        if changes['lost']:
            return EXIT['refuted']
    return EXIT['refuted'] if data['findings'] else EXIT['ok']


if __name__ == '__main__':
    sys.exit(main())
