"""SemIf (OpenJev) scoring worker. Runs under SemIf's own interpreter, never autoform's.

Protocol: one JSON object per stdin line, one JSON object per stdout line.
  request  {"rows": [{id, state, question, options: [{id, description}]}, ...], "shared": bool}
  response {"results": [...SemIf result rows...], "timing": {...}} | {"error": "..."}
The first stdout line is {"ready": true, "model": {...metadata...}} once weights are loaded.

This file must import nothing from autoform: it executes in a different environment
(torch / MLX) so that those stacks never enter the harness's process or trusted base.
"""
import argparse
import json
import platform
import sys


def load(args):
    if args.backend == 'mlx' or (args.backend == 'auto' and platform.system() == 'Darwin'
                                 and platform.machine() == 'arm64'):
        from semif_phase1 import mlx_backend
        model, tokenizer, metadata = mlx_backend.load_model(
            args.model, args.revision, args.bits, cache_limit_mib=args.cache_limit_mib)
        return model, tokenizer, metadata, mlx_backend.score, mlx_backend.score_shared
    from semif_phase1.core import load_causal_model
    from semif_phase1.direct import score
    from semif_phase1.shared import score_shared
    model, tokenizer, metadata = load_causal_model(args.model, args.revision, args.device, args.dtype)
    return model, tokenizer, metadata, score, score_shared


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--model', required=True)
    parser.add_argument('--revision', required=True)
    parser.add_argument('--backend', choices=('auto', 'mlx', 'torch'), default='auto')
    parser.add_argument('--bits', type=int, choices=(4, 8))
    parser.add_argument('--device', default='auto')
    parser.add_argument('--dtype', default='bfloat16')
    parser.add_argument('--cache-limit-mib', type=int, default=256)
    parser.add_argument('--max-tokens', type=int, default=8192)
    args = parser.parse_args()
    out = sys.stdout
    sys.stdout = sys.stderr  # library chatter must not corrupt the protocol stream
    try:
        model, tokenizer, metadata, score, score_shared = load(args)
    except Exception as exc:  # report and exit; the harness falls back or fails loudly
        out.write(json.dumps({'ready': False, 'error': f'{type(exc).__name__}: {exc}'}) + '\n')
        out.flush()
        return 1
    out.write(json.dumps({'ready': True, 'model': metadata}, default=str) + '\n')
    out.flush()
    for line in sys.stdin:
        if not line.strip():
            continue
        try:
            request = json.loads(line)
            rows = request['rows']
            if request.get('shared') and len(rows) > 1 and len({json.dumps(r['state'], sort_keys=True)
                                                                 for r in rows}) == 1:
                results, timing = score_shared(model, tokenizer, rows, metadata, args.max_tokens)
            else:
                results = [score(model, tokenizer, row, metadata, args.max_tokens) for row in rows]
                timing = {}
            out.write(json.dumps({'results': results, 'timing': timing}, default=str, allow_nan=False) + '\n')
        except Exception as exc:
            out.write(json.dumps({'error': f'{type(exc).__name__}: {exc}'}) + '\n')
        out.flush()
    return 0


if __name__ == '__main__':
    sys.exit(main())
