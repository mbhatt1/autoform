"""Coverage-guided differential fuzzing of model-stage Lean models (src/autoform/nl/fuzz.py).

Pure-Python tests: generator determinism and typing, shrinking to minimal counterexamples
(with Python oracles), coverage guidance on a real function run by the CPython runner,
and the hook in model.py's validation step (Lean replaced by a Python interpreter of the
candidate). The Lean-backed test (AUTOFORM_TEST_LEAN=1) runs a hand-written, subtly wrong
model that agrees on every traced and boundary input through the real stage and checks
that fuzzing catches it and shrinks the counterexample to (1, -3).
"""
from __future__ import annotations

import json
import os
import re
import sys
import textwrap
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'src'))

from autoform.nl import fuzz as F  # noqa: E402
from autoform.nl import model as M  # noqa: E402
from autoform.nl import pyvalues as pv  # noqa: E402
from autoform.nl import schema  # noqa: E402

LEAN = pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_LEAN') != '1', reason='set AUTOFORM_TEST_LEAN=1')


def write(root: Path, rel: str, text: str):
    p = root / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(textwrap.dedent(text))


def sig(*params, returns='Int'):
    return M.parse_sig([{'name': f'p{i}', 'type': t, 'kind': k, 'default': d}
                        for i, (t, k, d) in enumerate(params)], returns)


def pos(t, default=None):
    return (t, 'positional', default)


def ediv(a: int, b: int) -> int:
    """Lean's `Int./` (Euclidean division)."""
    r = a % abs(b)
    return (a - r) // b


# ------------------------------------------------------------------ generation

def test_generation_is_deterministic_by_seed_and_well_typed():
    params = F.Params.of(sig(pos('Int'), pos('String'), pos('List (Option Int)'), pos('Int × Bool', '(0, true)')))

    def draw(seed):
        g = F.ArgGen(params, seed, 'def f(a, s, xs, t=(0, True)):\n    return a if s == "k" else 12\n',
                     traced=[[3, 'k', [1, None], (2, False)]])
        out = [g.fresh() for _ in range(200)]
        out += [g.mutate(out[i]) for i in range(100)]
        return out
    a, b, c = draw(7), draw(7), draw(8)
    assert json.dumps([F.encode(x) for x in a]) == json.dumps([F.encode(x) for x in b])
    assert a != c
    fresh = a[:200]
    assert all(params.accepts(x) for x in a)
    ints = [x[0] for x in fresh]
    strs = [x[1] for x in fresh]
    assert any(i < 0 for i in ints) and any(abs(i) > 2 ** 64 for i in ints) and 0 in ints
    assert any(i in (12, 11, 13) for i in ints)                           # source literals
    assert '' in strs and any(s and not s.strip() for s in strs) and any(not s.isascii() for s in strs)
    assert {len(x[2]) for x in fresh} >= {0, 1, 2, 3} and any(None in x[2] for x in fresh)
    assert any(len(x) == 3 for x in fresh)                                 # defaulted parameter omitted


def test_val_parameters_follow_observed_shapes_and_mutation_changes_one_field():
    params = F.Params.of(sig(pos('Val'), pos('Int')))
    g = F.ArgGen(params, 1, traced=[[('a', 'b'), 5], [('c',), 6]])
    shapes = [F.shape(g.fresh()[0]) for _ in range(300)]
    assert shapes.count(('Tuple', 'String')) > 100                        # the observed shape dominates
    base = [('a', 'b'), 5]
    changed = [sum(1 for u, v in zip(base, g.mutate(base)) if u != v) for _ in range(200)]
    assert max(changed) == 1 and changed.count(1) > 150


def test_conformance_mirrors_the_lean_decoders():
    t = M.parse_type('List (Option Int) × String')
    assert F.conforms(([1, None], 'x'), t)
    assert not F.conforms(([True], 'x'), t)                                # bool is not Int
    assert not F.conforms(((1,), 'x'), t)                                  # a tuple is not a List
    assert F.conforms(object(), 'Val') is False and F.conforms(int, 'Val')


# ------------------------------------------------------------------ shrinking

def shrink_one(args, params, prop):
    [(out, steps)] = F.shrink_many([args], params, lambda cs: [bool(prop(*c)) for c in cs], rounds=40)
    # 1-minimal: no one-step simplification still fails
    assert not any(prop(*c) for c in F.shrink_candidates(out, params)), out
    return out, steps


def test_shrinking_reaches_minimal_counterexamples():
    ii = F.Params.of(sig(pos('Int'), pos('Int')))
    out, steps = shrink_one([2500, -101], ii, lambda a, b: b != 0 and a // b != ediv(a, b))
    assert out == [1, -2] and steps >= 3
    one = F.Params.of(sig(pos('Int')))
    assert shrink_one([12345050], one, lambda x: round(x, -2) != (x + 50) // 100 * 100)[0] == [50]
    s = F.Params.of(sig(pos('String')))
    assert shrink_one(['  hello\tworld  '], s, lambda x: x.split() != [w for w in x.split(' ') if w])[0] == ['\t']
    xs = F.Params.of(sig(pos('List Int')))
    assert shrink_one([[5, 7, -300, 2]], xs, lambda v: any(x < 0 for x in v))[0] == [[-1]]
    # dict entries are dropped and values simplified; defaulted arguments are dropped
    d = F.Params.of(sig(pos('Val'), pos('Int', '0')))
    out, _ = shrink_one([{'a': 1, 'k': [1, 2], 'z': 'x'}, 99], d, lambda v, n=0: isinstance(v, dict) and 'k' in v)
    assert out == [{'k': None}]


def test_shrinking_is_batched_in_lock_step_and_shares_verdicts():
    params = F.Params.of(sig(pos('Int')))
    calls = []

    def oracle(cs):
        calls.append(len(cs))
        return [c[0] >= 3 for c in cs]
    res = F.shrink_many([[703], [1053], [45]], params, oracle, rounds=20)
    assert [r[0] for r in res] == [[3], [3], [3]]
    assert len(calls) <= 12                        # one oracle call per round for all three


# ------------------------------------------------------------------ coverage guidance

@pytest.fixture
def branchy(tmp_path):
    root = tmp_path / 'repo'
    write(root, 'pkg/__init__.py', '')
    write(root, 'pkg/cls.py', '''
        def classify(n, s):
            if n > 1000:
                if s.startswith('x'):
                    return 'big-x'
                return 'big'
            if s == '':
                return 'empty'
            return 'small'
        ''')
    fns, _ = M._discover(root)
    return {f.info.source_name: f for f in fns}['classify'], tmp_path


def test_coverage_guidance_finds_and_prefers_new_branches(branchy):
    fn, tmp = branchy
    params = F.Params.of(sig(pos('Int'), pos('String'), returns='String'))
    runtime = M.Runtime(fn, tmp / 'rt')
    runner = F.CoverageRunner(fn, runtime, tmp / 'cov', 2.0)
    traced = [[pv.tag(1), pv.tag('a')]]
    g = F.ArgGen(params, 3, fn.info.source, [[1, 'a']])
    base, baseline, cases = F.explore(g, runner, 300, 100, traced)
    before, after = runner.coverage(base), runner.coverage(base | set().union(*(c.arcs for c in cases)))
    assert before['available'] and before['line_pct'] < 60 and after['line_pct'] == 100.0
    assert after['branch_pct'] == 100.0 and before['branch_pct'] < after['branch_pct']
    novel = [c for c in cases if c.novel]
    outcomes = {pv.display(pv.canon_outcome(c.outcome)) for c in novel}
    assert {"returns 'big-x'", "returns 'big'", "returns 'empty'"} <= outcomes
    assert len(novel) < 15                       # only inputs that reached something new
    # the Lean batch takes every novel input first
    chosen = F.select(cases, 20)
    assert chosen[:len(novel)] == novel
    # outcomes are shared with the model stage's runtime cache
    assert all(json.dumps(c.point) in runtime.cache for c in cases)


def test_select_prefers_novel_then_new_outcome_kinds():
    ok = {'k': 'ok', 'v': ['i', '1']}
    mk = lambda i, res, novel: F.Case([pv.tag(i)], [i], res, frozenset(), 'fresh', novel)  # noqa: E731
    cases = [mk(0, ok, 0), mk(1, ok, 0), mk(2, {'k': 'exn', 't': 'KeyError'}, 0), mk(3, ok, 2),
             mk(4, {'k': 'timeout'}, 5)]
    assert [c.args[0] for c in F.select(cases, 3)] == [3, 2, 0]     # timeout never selected


# ------------------------------------------------------------------ the hook in model.py

PLANTED = '''
    def percent_of(part, whole, scale=100):
        """part as a share of whole, in units of 1/scale, rounded down."""
        return part * scale // whole
    '''
PLANTED_TESTS = '''
    from planted.calc import percent_of

    def test_percent():
        assert percent_of(50, 200) == 25
        assert percent_of(1, 3) == 33
        assert percent_of(7, 8, 1000) == 875
    '''
WRONG_P = ('def py_percent_of (part whole scale : Int) : Except String Int :=\n'
           '  if whole = 0 then .error "ZeroDivisionError" else .ok (part * scale / whole)')
MINIMAL = {'(1, -3)', '(1, -2, 1)'}      # 1*100 // -3 = -34, Lean -33; 1*1 // -2 = -1, Lean 0
RIGHT_P = WRONG_P.replace('(part * scale / whole)', '(Int.fdiv (part * scale) whole)')


@pytest.fixture
def planted(tmp_path):
    root = tmp_path / 'planted-src'
    write(root, 'planted/__init__.py', '')
    write(root, 'planted/calc.py', PLANTED)
    write(root, 'tests/test_calc.py', PLANTED_TESTS)
    return root


def percent_answer(lean):
    return {'english': 'x', 'returns': 'Except String Int', 'lean': lean,
            'params': [{'name': 'part', 'type': 'Int', 'kind': 'positional', 'default': None},
                       {'name': 'whole', 'type': 'Int', 'kind': 'positional', 'default': None},
                       {'name': 'scale', 'type': 'Int', 'kind': 'positional', 'default': '100'}]}


def interp_evaluate(module, lean_root, work, stem, callee_src, cand, lean_name, qual, points, runtime,
                    kernel_points=M.KERNEL_POINTS, **_structs):
    """Python stand-in for the Lean run of the two percent_of candidates."""
    ev = M.Evaluation(elaborates=True)
    div = (lambda a, b: a // b) if 'Int.fdiv' in cand.data['lean'] else ediv
    for p in points:
        a, b, *rest = (pv.untag(t) for t in p)
        scale = rest[0] if rest else 100
        ev.outputs.append('exn ZeroDivisionError' if b == 0 else f'ok i:{div(a * scale, b)}')
    if runtime is not None:
        for i, (p, r) in enumerate(zip(points, runtime)):
            rt = pv.canon_outcome(r)
            if rt is None:
                ev.skipped += 1
                continue
            ev.compared += 1
            if rt != ev.outputs[i]:
                ev.disagreements.append({'point': i, 'inputs': pv.show_args(p), 'model': pv.display(ev.outputs[i]),
                                         'runtime': pv.display(rt)})
    return ev


def test_hook_feeds_shrunk_counterexamples_to_the_repair_loop(planted, tmp_path, monkeypatch):
    monkeypatch.setattr(M, 'evaluate', interp_evaluate)
    calls = []
    real_extend = F.extend
    monkeypatch.setattr(F, 'extend', lambda ev, **kw: calls.append(kw['stem']) or real_extend(ev, **kw))
    prompts = []

    def ask(prompt, keys, **kw):
        prompts.append(prompt)
        return percent_answer(RIGHT_P if 'rejected' in prompt else WRONG_P), 0.0

    # without fuzzing the wrong model passes every traced and boundary input
    monkeypatch.setattr(F.CONFIG, 'cases', 0)
    M.model(planted, tmp_path / 'off', tmp_path / 'lean', module='NLFuzzOff', ask=ask, do_build=False,
            repairs=2, second=False)
    off = schema.load(tmp_path / 'off' / 'models.json')[0]
    assert off['status'] == 'VALIDATED' and off['repairs'] == 0 and off['tests_run'] > 50
    assert not (tmp_path / 'off' / 'fuzz.json').exists() and calls == ['z0']

    # with fuzzing: caught, shrunk, repaired
    calls.clear()
    prompts.clear()
    monkeypatch.setattr(F.CONFIG, 'cases', 200)
    M.model(planted, tmp_path / 'on', tmp_path / 'lean', module='NLFuzzOn', ask=ask, do_build=False,
            repairs=2, second=False)
    on = schema.load(tmp_path / 'on' / 'models.json')[0]
    assert calls == ['z0', 'z1']
    assert on['status'] == 'VALIDATED' and on['repairs'] == 1
    repair = [p for p in prompts if 'rejected' in p][0]
    assert 'percent_of(1, -3): Python returns -34; Lean model returns -33' in repair
    fz = json.loads((tmp_path / 'on' / 'fuzz.json').read_text())
    [entry] = fz
    r0, r1 = entry['rounds']
    assert r0['disagreements_found'] > 0 and r0['cases_run'] == 200 and r0['seed'] == entry['seed']
    # both are 1-minimal (no single simplification still disagrees); (1, -3) is the global minimum
    assert {s['shrunk'] for s in r0['shrunk']} <= MINIMAL and '(1, -3)' in {s['shrunk'] for s in r0['shrunk']}
    assert all(s['size_after'] <= s['size_before'] for s in r0['shrunk'])
    assert r0['coverage']['with_fuzz']['line_pct'] == 100.0
    assert r1['disagreements_found'] == 0 and r1['cases_run'] > 200          # carried counterexamples re-checked
    assert entry['final_round_clean']

    # an unrepaired model ends DISAGREES with the minimal counterexample first
    M.model(planted, tmp_path / 'bad', tmp_path / 'lean', module='NLFuzzBad', ask=lambda p, k, **kw:
            (percent_answer(WRONG_P), 0.0), do_build=False, repairs=0, second=False)
    bad = schema.load(tmp_path / 'bad' / 'models.json')[0]
    assert bad['status'] == 'DISAGREES' and bad['disagreements'][0]['inputs'] in MINIMAL


def test_hook_is_reproducible_by_seed(planted, tmp_path, monkeypatch):
    monkeypatch.setattr(M, 'evaluate', interp_evaluate)
    monkeypatch.setattr(F.CONFIG, 'cases', 100)
    ask = lambda p, k, **kw: (percent_answer(WRONG_P), 0.0)  # noqa: E731
    runs = []
    for i in range(2):
        M.model(planted, tmp_path / f'r{i}', tmp_path / 'lean', module=f'NLFuzzSeed{i}', ask=ask, do_build=False,
                repairs=0, second=False)
        [e] = json.loads((tmp_path / f'r{i}' / 'fuzz.json').read_text())
        runs.append([(r['disagreements_found'], r['shrunk'], r['cases_run']) for r in e['rounds']])
    assert runs[0] == runs[1]


# ------------------------------------------------------------------ Lean-backed

@LEAN
def test_lean_subtly_wrong_model_is_caught_by_fuzzing_and_shrunk(planted, tmp_path, monkeypatch):
    root = Path(os.environ.get('AUTOFORM_LEAN_ROOT', ROOT))
    ask = lambda p, k, **kw: (percent_answer(WRONG_P), 0.0)  # noqa: E731
    monkeypatch.setattr(F.CONFIG, 'cases', 0)
    M.model(planted, tmp_path / 'off', root, module='NLTestFuzzOff', ask=ask, repairs=0, second=False,
            do_build=False)
    off = schema.load(tmp_path / 'off' / 'models.json')[0]
    assert off['status'] == 'VALIDATED' and off['tests_run'] > 50 and 'kernel-evaluated 3/3' in off['notes']

    monkeypatch.setattr(F.CONFIG, 'cases', 150)
    M.model(planted, tmp_path / 'on', root, module='NLTestFuzzOn', ask=ask, repairs=0, second=False,
            do_build=False)
    on = schema.load(tmp_path / 'on' / 'models.json')[0]
    assert on['status'] == 'DISAGREES'
    first = on['disagreements'][0]
    assert first['inputs'] in MINIMAL
    assert '(1, -3)' in [d['inputs'] for d in on['disagreements']]
    d = [d for d in on['disagreements'] if d['inputs'] == '(1, -3)'][0]
    assert d['runtime'] == 'returns -34' and d['model'] == 'returns -33'
    [entry] = json.loads((tmp_path / 'on' / 'fuzz.json').read_text())
    assert entry['disagreements_found'] > 0 and entry['rounds'][0]['lean_runs'] >= 2
    assert all(re.fullmatch(r'\(-?\d+, -\d+(, -?\d+)?\)', s['original']) for s in entry['rounds'][0]['shrunk'])
