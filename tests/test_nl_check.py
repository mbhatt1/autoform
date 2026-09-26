"""Check stage of the NL autoformalizer (src/autoform/nl/check.py).

Pure-Python tests cover domain generation, runtime-outcome encoding, Lean file generation
and the CPython runner. Lean-backed tests (AUTOFORM_TEST_LEAN=1) run the real stage on the
PipelinePython fixture; AUTOFORM_LEAN_ROOT overrides the lake root holding the built model.
"""
from __future__ import annotations

import copy
import json
import os
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'src'))

from autoform.nl import check as K  # noqa: E402
from autoform.nl import schema  # noqa: E402

FIX = ROOT / 'tests/fixtures/nl'
LEAN = pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_LEAN') != '1', reason='set AUTOFORM_TEST_LEAN=1')


def load(name):
    return json.loads((FIX / name).read_text())


def statement(sid, post, pre='true', binders=None, fn='numbers.py:<module>.add'):
    binders = binders if binders is not None else [dict(name='a', type='Int', val='.int a'), dict(name='b', type='Int', val='.int b')]
    return dict(id=sid, function=fn, property='p', english='', lean_prop='', binders=binders, pre=pre,
                post=post, elaborates=True)


# --- domain ---------------------------------------------------------------------

def test_int_domain_has_zero_negatives_and_width_bounds():
    vals = K.binder_values('int', 'u8')
    assert {0, 1, 255, 254} <= set(vals)
    assert all(0 <= v <= 255 for v in vals)
    signed = K.binder_values('int', 'i32')
    assert {-2 ** 31, 2 ** 31 - 1, -1, 0} <= set(signed)
    assert all(-2 ** 31 <= v < 2 ** 31 for v in signed)
    plain = K.binder_values('int')
    assert {-1, 0, 1, -2} <= set(plain)
    assert all(v >= 0 for v in K.binder_values('nat'))


def test_source_literals_feed_the_domain():
    ints, strs = K.source_literals('def f(x):\n    return x == 42 or x == "secret"\n')
    assert 42 in ints and 'secret' in strs
    vals = K.binder_values('int', '', ints)
    assert {42, 41, 43} <= set(vals)
    c_ints, _ = K.source_literals('unsigned f(void) { return 0xff | 017; }', 'c')
    assert {255, 15} <= set(c_ints)
    assert 'secret' in K.binder_values('str', '', (), strs)


def test_domain_uses_c_widths_and_is_capped():
    tr = load('translation-PipelineC.json')
    fn = next(f for f in tr['functions'] if f['name'] == 'wrap')
    binders = [dict(name='a', type='Int', val='.int a'), dict(name='b', type='Int', val='.int b')]
    kinds, pts = K.domain(binders, fn, 'c', cap=64)
    assert kinds == ['int', 'int'] and 0 < len(pts) <= 64
    flat = {v for p in pts for v in p}
    assert 2 ** 32 - 1 in flat and all(0 <= v < 2 ** 32 for v in flat)
    kinds, pts = K.domain([], fn, 'c')
    assert pts == [[]]
    with pytest.raises(ValueError):
        K.domain([dict(name='xs', type='List Int', val='.list xs')], fn, 'c')


def test_domain_includes_diagonal_for_equality_properties():
    binders = [dict(name='o', type='String', val='.str o'), dict(name='c', type='String', val='.str c')]
    _, pts = K.domain(binders, None, 'python', cap=64)
    assert any(p[0] == p[1] for p in pts) and any(p[0] != p[1] for p in pts)


# --- runtime encoding ---------------------------------------------------------------

def test_encode_outcome():
    enc = K.encode_outcome
    assert enc({'kind': 'value', 'type': 'int', 'value': -3}) == 'EResult.val (Val.int (-3))'
    assert enc({'kind': 'value', 'type': 'bool', 'value': True}) == 'EResult.val (Val.bool true)'
    assert enc({'kind': 'value', 'type': 'str', 'value': 'a"b'}) == 'EResult.val (Val.str "a\\"b")'
    assert enc({'kind': 'value', 'type': 'NoneType'}) == 'EResult.val Val.unit'
    assert enc({'kind': 'exception', 'type': 'ZeroDivisionError'}) == \
        'EResult.exn (Val.str "ZeroDivisionError")'
    # no faithful literal: skipped, never approximated
    assert enc({'kind': 'value', 'type': 'float', 'repr': '3.5'}) is None
    assert enc({'kind': 'value', 'type': 'list', 'repr': '[1]'}) is None
    assert enc({'kind': 'timeout'}) is None
    assert enc({'kind': 'value', 'type': 'int', 'value': True}) is None


def test_runtime_runner_executes_real_function(tmp_path):
    src = tmp_path / 'm.py'
    src.write_text('print("noise")\ndef f(a, b):\n    print("more noise")\n    return a // b\n'
                   'def g(a):\n    return None if a else 1.5\n')
    tr = dict(language='python', source_root=str(tmp_path), call_template='runFunc P 10 {name} {args}')
    fn = dict(name='m.py:<module>.f', source_name='f', file='m.py', params=[], source='')
    plan = K.Plan(0, statement('s', 'true', fn='m.py:<module>.f'), fn, tr, 64)
    K.run_runtime(tr, fn, plan)
    assert plan.runtime is not None and len(plan.runtime) == len(plan.points)
    by_point = {tuple(plan.points[i]): (d, lit) for i, d, lit in plan.runtime}
    assert by_point[(1, 0)][1] == 'EResult.exn (Val.str "ZeroDivisionError")'
    assert by_point[(-1, 2)][1] == 'EResult.val (Val.int (-1))'
    assert by_point[(3, -2)][1] == 'EResult.val (Val.int (-2))'
    gfn = dict(name='m.py:<module>.g', source_name='g', file='m.py', params=[], source='')
    plan = K.Plan(0, statement('s', 'true', binders=[dict(name='a', type='Bool', val='.bool a')],
                               fn='m.py:<module>.g'), gfn, tr, 16)
    K.run_runtime(tr, gfn, plan)
    by_point = {tuple(plan.points[i]): lit for i, _, lit in plan.runtime}
    assert by_point == {(False,): None, (True,): 'EResult.val Val.unit'}


def test_runtime_skipped_for_other_languages_and_methods():
    tr = dict(language='c', source_root='/nonexistent')
    assert K.runtime_target(tr, dict(name='add', source_name='add', file='x.c'))[0] is None
    tr = dict(language='python', source_root='/nonexistent')
    path, why = K.runtime_target(tr, dict(name='m.py:<module>.C.f', source_name='f', file='m.py'))
    assert path is None and 'top-level' in why


# --- Lean file generation ---------------------------------------------------------------

def test_generated_file_shape():
    tr = load('translation-PipelinePython.json')
    fn = tr['functions'][0]
    plan = K.Plan(3, statement('numbers.py:<module>.add__p1', 'match r with | .val (.int x) => x == a + b | _ => false'),
                  fn, tr, 16)
    plan.runtime = [(0, {'kind': 'value', 'type': 'int', 'value': 0}, 'EResult.val (Val.int (0))')]
    defs, checks = plan.pass1()
    t = plan.tag
    assert t.startswith('s3_') and all(c.isalnum() or c == '_' for c in t)
    assert f'def chk_{t} (a : Int) (b : Int) : Bool := !(pre_{t} a b) || post_{t} a b ' \
           f'(runFunc Autoform.Generated.PipelinePython.program 1000 "numbers.py:<module>.add" [.int a, .int b])' in defs
    assert f'def dom_{t} : List (Int × Int) := [((0 : Int), (0 : Int)),' in defs
    assert f'def rt_{t} : List ((Int × Int) × EResult) := [(((0 : Int), (0 : Int)), EResult.val (Val.int (0)))]' in defs
    assert f'theorem bounded_{t} : (dom_{t}).all (fun p => chk_{t} p.1 p.2) = true := by\n  decide +kernel' in checks
    assert f'#print axioms bounded_{t}' in checks and f'theorem nonvac_{t}' in checks
    assert 'native_decide' not in defs + checks and 'sorry' not in defs + checks
    text, spans = K.assemble(tr['module'], [(t, defs, checks)])
    lines = text.splitlines()
    a, b, end = spans[t]
    assert lines[a - 1].startswith(f'def pre_{t}') and lines[b - 1].startswith(f'def rt_{t}')
    assert lines[end - 1].startswith(f'#print axioms nonvac_{t}')
    assert text.startswith('import Autoform.Generated.PipelinePython\n')
    refute = plan.pass2(1, 0)
    assert f'theorem refute_{t} : chk_{t} (0 : Int) (1 : Int) = false := by\n  decide +kernel' in refute
    assert f'theorem rtrefute_{t} : (!(pre_{t} (0 : Int) (0 : Int)) || post_{t} (0 : Int) (0 : Int) ' \
           f'(EResult.val (Val.int (0)))) = false' in refute


def test_zero_binder_statement_generation():
    tr = load('translation-PipelineC.json')
    fn = next(f for f in tr['functions'] if f['name'] == 'literal')
    plan = K.Plan(0, statement('literal__p1', 'true', binders=[], fn='literal'), fn, tr, 64)
    defs, checks = plan.pass1()
    assert f'def dom_{plan.tag} : List (Unit) := [()]' in defs
    assert f'(fun p => chk_{plan.tag})' in checks


def test_unelaborated_and_unknown_function_statements_are_not_checked(tmp_path):
    tr = load('translation-PipelinePython.json')
    st1 = dict(statement('x', 'true'), elaborates=False)
    st2 = statement('y', 'true', fn='nope')
    res = K.check(tr, [st1, st2], tmp_path, runtime=False)
    assert [r.status for r in res] == ['UNCHECKABLE', 'ERROR']
    assert json.loads((tmp_path / 'checks.json').read_text())[0]['statement'] == 'x'


def test_pre_post_must_be_single_terms():
    assert K.safe_term('match r with | .exn (.str "a)b") => true | _ => false')
    assert K.safe_term('match r with\n  | .val _ => true\n  | _ => false')
    assert not K.safe_term('true)\ntheorem bounded_x : True := trivial\n#check (1')
    assert not K.safe_term('true) (')
    assert not K.safe_term('true -- comment')
    tr = load('translation-PipelinePython.json')
    with pytest.raises(ValueError):
        K.Plan(0, statement('x', 'true)\naxiom bad : False\n#check (0'), tr['functions'][0], tr, 8)


def test_errors_by_line_attributes_errors():
    out = ('/w/f.lean:12:4: error: unknown identifier \'zz\'\n  more\n'
           '/w/g.lean:3:1: error: other file\n/w/f.lean:20:0: error: second\n')
    assert K.errors_by_line(out, Path('/w/f.lean')) == [(12, "unknown identifier 'zz'\n  more"), (20, 'second')]


# --- Lean-backed ------------------------------------------------------------------------

def lean_root(tr):
    return os.environ.get('AUTOFORM_LEAN_ROOT', tr['lean_root'])


@LEAN
def test_lean_bounded_refuted_model_and_runtime(tmp_path):
    tr = load('translation-PipelinePython.json')
    sts = {s['property']: s for s in load('statements-PipelinePython.json')
           if s['function'] == 'numbers.py:<module>.add'}
    res = {r.statement: r for r in K.check(tr, [sts['p1'], sts['p2']], tmp_path / 'a', lean_root=lean_root(tr))}
    holds = res[sts['p1']['id']]
    assert holds.status == 'BOUNDED_HOLDS' and holds.kernel_bounded_proof and holds.runtime_agrees is True
    refuted = res[sts['p2']['id']]
    assert refuted.status == 'REFUTED_MODEL' and refuted.runtime_agrees is False
    ce = refuted.counterexample
    a, b = ce['inputs']['a'], ce['inputs']['b']
    assert a - b != a + b and 'EResult.val' in ce['model'] and ce['runtime'] == f'returns {a + b} (int)'
    assert 'refute_' in refuted.detail
    # A "real program" that differs from the model: the statement holds on the model
    # but fails on CPython, so the runtime check refutes it.
    src = tmp_path / 'src'
    src.mkdir()
    (src / 'numbers.py').write_text('def add(a, b):\n    return a - b\n')
    tr2 = copy.deepcopy(tr)
    tr2['source_root'] = str(src)
    r = K.check(tr2, [sts['p1']], tmp_path / 'b', lean_root=lean_root(tr))[0]
    assert r.status == 'REFUTED_RUNTIME' and r.runtime_agrees is False
    assert r.counterexample['runtime'].startswith('returns ') and 'EResult.val' in r.counterexample['model']
    saved = json.loads((tmp_path / 'b' / schema.FILES['checks']).read_text())
    assert saved[0]['status'] == 'REFUTED_RUNTIME'


@LEAN
def test_lean_exception_statement_and_c_without_runtime(tmp_path):
    tr = load('translation-PipelinePython.json')
    st = next(s for s in load('statements-PipelinePython.json') if s['id'].endswith('quotient__p1'))
    r = K.check(tr, [st], tmp_path / 'q', lean_root=lean_root(tr))[0]
    assert r.status == 'BOUNDED_HOLDS' and r.runtime_agrees is True
    trc = load('translation-PipelineC.json')
    stc = next(s for s in load('statements-PipelineC.json') if s['id'] == 'wrap__p2')
    r = K.check(trc, [stc], tmp_path / 'c', lean_root=lean_root(trc))[0]
    assert r.status == 'REFUTED_MODEL' and r.runtime_agrees is None and 'Python only' in r.detail
