"""Emit stage of the NL autoformalizer (src/autoform/nl/emit.py) and the Lean -> Python
translation of pre/post (src/autoform/nl/pyprop.py).

Pure-Python tests cover the translation, the literal rendering, the survivor rule, the
generated files, the real pytest run of the emitted tests and the deduplication against
the target's own suite; Lean's evaluation of pre/post on real outcomes is replaced by the
Python translation (which mirrors it) except in the Lean-backed test (AUTOFORM_TEST_LEAN=1,
AUTOFORM_LEAN_ROOT overriding the lake root). No model is called.
"""
from __future__ import annotations

import json
import os
import shutil
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'src'))

from autoform.nl import check as K  # noqa: E402
from autoform.nl import emit as E  # noqa: E402
from autoform.nl import pipeline, pyprop, pyvalues as pv, schema  # noqa: E402

FIX = ROOT / 'tests/fixtures/nl'
LEAN = pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_LEAN') != '1', reason='set AUTOFORM_TEST_LEAN=1')
RUNTIME_NS: dict = {}
exec(pyprop.RUNTIME, RUNTIME_NS)  # noqa: S102


def ev(expr, names=('a', 'b'), **env):
    e = dict(RUNTIME_NS)
    e.update(env)
    return eval(pyprop.translate(expr, names), e)  # noqa: S307


# --- translation -------------------------------------------------------------------------

def test_translate_scalar_statements():
    post = 'match r with | .val (.int x) => x == a + b | _ => false'
    assert ev(post, a=1, b=2, r=('ok', 3)) is True
    assert ev(post, a=1, b=2, r=('ok', True)) is False          # bool is not .int
    assert ev(post, a=1, b=2, r=('exn', 'TypeError')) is False
    assert ev('r matches .exn (.str "ZeroDivisionError")', r=('exn', 'ZeroDivisionError')) is True
    assert ev('match r with | .val (.int x) => x == Int.fdiv a b | _ => false', a=-7, b=2, r=('ok', -4)) is True
    assert ev('match r with | .val (.int x) => x == a / b | _ => false', a=-7, b=2, r=('ok', -4)) is True   # Euclidean
    assert ev('match r with | .val (.int x) => x == a / b | _ => false', a=-7, b=-2, r=('ok', 4)) is True
    assert ev('match r with | .val (.int x) => x == a % b | _ => false', a=-7, b=2, r=('ok', 1)) is True
    assert ev('match r with | .val (.int x) => x == Int.tdiv a b | _ => false', a=-7, b=2, r=('ok', -3)) is True
    assert ev('b != 0 && decide (b > 1000000000000)', a=0, b=2) is False
    assert ev('match r with | .exn _ => false | _ => true', r=('ok', None)) is True
    assert ev('match r with | .val (.bool t) => t == (owner == caller) | _ => false', ('owner', 'caller'),
              owner='x', caller='x', r=('ok', True)) is True
    assert ev('match r with | .val (.int n) => n == (a + b) % 2^32 | _ => false', a=2 ** 32 - 1, b=1, r=('ok', 0)) is True
    assert ev('!(s.length == 0) && (s ++ t).length == s.length + t.length', ('s', 't'), s='ab', t='c') is True
    assert ev('let m := a * 2; if m > 3 then m == 4 else true', ('a',), a=2) is True
    assert ev('match r with | .val .unit => true | _ => false', r=('ok', None)) is True
    assert ev('match r with | .val (.list xs) => xs.all (fun v => v matches .int _) | _ => false',
              ('a',), r=('ok', [1, 2])) is True
    assert ev('match r with | .val (.tuple [k, _]) => k == 1 | _ => false', ('a',), r=('ok', (1, 'x'))) is True
    assert ev('match r with | .val (.str s) => s.length == a | _ => false', ('a',), a=2, r=('ok', 'hé')) is True
    # Option and the Val helpers
    o = type('Cache', (), {})()
    o.data = {1: 'one'}
    assert ev('match vGet (vField self "data") (.int 1) with | some v => Val.beq v (.str "one") | none => false',
              ('self',), self=o) is True
    assert ev('vHas (vField self "data") (.int 1) && vLen (vField self "data") == 1 && !(vHas (vField self "data") (.bool true))',
              ('self',), self=o) is True
    assert ev('(vKeys (vField self "data")).isEmpty', ('self',), self=o) is False


def test_translate_refuses_what_it_cannot_mirror():
    for bad in ('match r with | .val (.float x) => Fl.isNaN x | _ => false',   # floats: no Python form
                '((vKeys x).length) - 1 == 0',                                  # Nat subtraction truncates
                '(fun x => x) (· + ·)',                                          # cdot sections
                'Autoform.NLModel.M.dObj_S_C x',                                 # receiver guards
                'match r with | .val (.bobj "set" (.list xs)) => xs.length == 0 | _ => false'):
        with pytest.raises(pyprop.Unsupported):
            pyprop.translate(bad, ['x'])
    with pytest.raises(pyprop.Unsupported):
        pyprop.translate('nope x', ['x'])


def test_runtime_equality_is_exact():
    eq, beq = RUNTIME_NS['_eq'], RUNTIME_NS['_beq']
    assert eq(('ok', 1), ('ok', 1)) and not eq(('ok', 1), ('ok', True)) and not eq(('ok', 1), ('ok', 1.0))
    assert eq(float('nan'), float('nan')) and eq([1, (2, 'x')], [1, (2, 'x')]) and not eq([1], (1,))
    assert eq({'a': 1, 'b': 2}, {'a': 1, 'b': 2}) and not eq({'a': 1, 'b': 2}, {'b': 2, 'a': 1})   # dict order
    obj = RUNTIME_NS['_obj']
    x, y = obj('collections.OrderedDict', {}), obj('collections.OrderedDict', {})
    assert eq(x, y)
    assert beq(1, 1.0) and not beq(1, True) and beq([1, 2], [1, 2]) and not beq([1], (1,)) and beq('a', 'a')
    assert RUNTIME_NS['_ediv'](7, 0) == 0 and RUNTIME_NS['_emod'](7, 0) == 7 and RUNTIME_NS['_fdiv'](-7, 2) == -4


def test_py_literal_round_trips_tags():
    from collections import OrderedDict

    class Thing:
        pass
    Thing.__module__, Thing.__qualname__ = 'tests.test_nl_emit', 'Thing'
    t = Thing()
    t.order = OrderedDict([(1, 'a')])
    t.n = 3
    values = [None, True, 0, -5, 2 ** 70, 1.5, float('inf'), float('nan'), 'a"b\n', b'\x00\xff', (1,), [1, [2]],
              {'k': (1, 2)}, {3, 1}, frozenset({'x'}), int, t]
    classes = {pv.class_name(Thing)}
    orig = RUNTIME_NS['_resolve']
    RUNTIME_NS['_resolve'] = lambda name: Thing if name.endswith('Thing') else orig(name)
    try:
        for v in values:
            tag = pv.tag(v, 0, classes)
            back = eval(E.py_literal(tag), RUNTIME_NS)  # noqa: S307
            assert pv.canon(pv.tag(back, 0, classes)) == pv.canon(tag), v
    finally:
        RUNTIME_NS['_resolve'] = orig
    assert E.outcome_literal({'k': 'exn', 't': 'KeyError'}) == "('exn', 'KeyError')"
    assert E.outcome_literal({'k': 'ok', 'v': ['i', '4']}) == "('ok', 4)"


# --- survivors -------------------------------------------------------------------------

def test_survivors_and_reasons():
    sts = [dict(id='f__p1', elaborates=True), dict(id='f__p2', elaborates=True), dict(id='f__p3', elaborates=False),
           dict(id='f__p4', elaborates=True), dict(id='f__p5', elaborates=True)]
    checks = [dict(statement='f__p1', status='BOUNDED_HOLDS'),
              dict(statement='f__p2', status='REFUTED_MODEL', counterexample={'inputs': {'a': 1}}),
              dict(statement='f__p4', status='UNCHECKABLE', detail='vacuous: no domain point satisfies the precondition; x')]
    adj = {'statements': [dict(id='f__p2_r1', elaborates=True)], 'checks': [dict(statement='f__p2_r1', status='BOUNDED_HOLDS')],
           'lineage': {'f__p2_r1': {'parent': 'f__p2'}}}
    keep, dropped = E.survivors(sts, checks, adj)
    assert [(s['id'], o) for s, _, o in keep] == [('f__p1', 'check'), ('f__p2_r1', 'repair')]
    assert 'refuted' in dropped['f__p2'] and '"a": 1' in dropped['f__p2'] and 'repaired as f__p2_r1' in dropped['f__p2']
    assert dropped['f__p3'] == 'the statement did not elaborate'
    assert dropped['f__p4'].startswith('not checkable: vacuous')
    assert dropped['f__p5'] == 'no check result for the statement'


# --- the stage, with the Python translation standing in for Lean ---------------------------------

def fake_rows(translation, plans, work, lean_root, stem):
    """What `evaluate_rows` asks Lean: pre and post on every real outcome."""
    out = {}
    for p in plans:
        names = [b['name'] for b in p.binders]
        pre_py, post_py = pyprop.translate(p.st.get('pre') or 'true', names), pyprop.translate(p.st['post'], names)
        by_idx = {i: d for i, d, _ in p.runtime}
        rows = []
        for idx, _ in p.rt_rows():
            env = dict(RUNTIME_NS, r=E.outcome_value(by_idx[idx]))
            env.update({pyprop.pyname(n): v for n, v in zip(p.names, p.points[idx])})
            pre = bool(eval(pre_py, env))  # noqa: S307
            rows.append((pre, bool(eval(post_py, env)) if pre else True))  # noqa: S307
        out[p.id] = rows
    return out


def arith_source(tmp_path, body='def add(a, b):\n    return a + b\n', with_tests=True):
    src = tmp_path / 'src'
    src.mkdir(exist_ok=True)
    (src / 'arith.py').write_text(body + '\n\ndef quotient(a, b):\n    return a // b\n')
    if with_tests:
        (src / 'tests').mkdir(exist_ok=True)
        (src / 'tests' / 'test_arith.py').write_text(
            'import pytest\nfrom arith import add, quotient\n\n\ndef test_add():\n    assert add(1, 2) == 3\n'
            '    with pytest.raises(ZeroDivisionError):\n        quotient(3, 0)\n')
    return src


def translation_for(src):
    t = json.loads((FIX / 'translation-PipelinePython.json').read_text())
    t['source_root'] = str(src)
    t['lean_root'] = str(ROOT)
    for f in t['functions']:
        f['name'] = f['name'].replace('numbers.py', 'arith.py')
        f['file'] = 'arith.py'
    return t


BINDERS = [{'name': 'a', 'type': 'Int', 'val': '.int a'}, {'name': 'b', 'type': 'Int', 'val': '.int b'}]


def statement(sid, fn, prop, english, pre, post, **kw):
    return dict(id=sid, function=f'arith.py:<module>.{fn}', property=prop, english=english, lean_prop='',
                binders=list(BINDERS), pre=pre, post=post, elaborates=True, elaboration_log='', attempts=1,
                entry='', prompt_hash=kw.get('prompt_hash', 'abc123'))


def statements():
    return [
        statement('add__p1', 'add', 'p1', 'add returns the sum of its arguments.', 'true',
                  'match r with | .val (.int x) => x == a + b | _ => false'),
        statement('add__p2', 'add', 'p2', 'add returns the difference.', 'true',
                  'match r with | .val (.int x) => x == a - b | _ => false'),
        statement('quotient__p1', 'quotient', 'p1', 'If b is 0, quotient raises ZeroDivisionError.', 'b == 0',
                  'r matches .exn (.str "ZeroDivisionError")'),
        statement('quotient__p3', 'quotient', 'p3', 'quotient is Euclidean.', 'b != 0',
                  'match r with | .val (.int x) => x == a / b | _ => false'),
    ]


def checks():
    return [schema.CheckResult('add__p1', 'BOUNDED_HOLDS', 64, runtime_agrees=True, kernel_bounded_proof=True),
            schema.CheckResult('add__p2', 'REFUTED_MODEL', 64, counterexample={'inputs': {'a': 1, 'b': 1}}),
            schema.CheckResult('quotient__p1', 'BOUNDED_HOLDS', 64, runtime_agrees=True, kernel_bounded_proof=True),
            schema.CheckResult('quotient__p3', 'UNCHECKABLE', detail='vacuous')]


def test_emit_writes_runs_and_deduplicates(tmp_path, monkeypatch):
    monkeypatch.setattr(E, 'evaluate_rows', fake_rows)
    src, out = arith_source(tmp_path), tmp_path / 'run'
    out.mkdir()
    tr = translation_for(src)
    proofs = [schema.ProofResult('add__p1', 'PROVED', certificate='x.lean')]
    english = [schema.EnglishSpec('arith.py:<module>.add', 's', [schema.EnglishProperty('p1', 'x', 'postcondition')],
                                  model='claude-test')]
    res = E.emit(tr, statements(), checks(), out, proofs=proofs, english=english,
                 run_info={'source': str(src), 'module': 'Arith', 'started': 'now'})
    gen = src / 'tests/autoform_generated'
    assert sorted(p.name for p in gen.iterdir()) == ['__init__.py', 'test_arith.py', 'test_arith_properties.py']
    text = (gen / 'test_arith.py').read_text()
    assert text.startswith('"""' + E.MARKER) and "_m = _il.import_module('arith')" in text
    assert 'add returns the sum of its arguments.' in text and 'kernel-proved for all inputs' in text
    assert f"autoform run {E.run_id({'source': str(src), 'module': 'Arith', 'started': 'now'})}; model claude-test; prompt abc123" in text
    assert "_call(_m.add, a, b)" in text and "assert _eq(r, ('ok', " in text
    assert "assert _eq(r, ('exn', 'ZeroDivisionError'))" in text
    props = (gen / 'test_arith_properties.py').read_text()
    assert "pytest.importorskip('hypothesis')" in props and '@given(a=st.integers(), b=st.integers())' in props
    assert 'def test_add__p1__property(a, b):' in props and 'def test_quotient__p1__property(a, b):' in props
    assert 'assume(_beq(b, 0))' in props
    by = {r['statement']: r for r in res['statements']}
    assert by['add__p1']['status'] == 'EMITTED' and by['quotient__p1']['status'] == 'EMITTED'
    assert by['add__p2']['status'] == 'NOT_EMITTED' and 'refuted' in by['add__p2']['reason']
    assert by['quotient__p3']['status'] == 'NOT_EMITTED' and by['quotient__p3']['reason'].startswith('not checkable')
    # (1, 2) and (3, 0) are what the suite already produces: not emitted, counted
    assert by['add__p1']['points_deduplicated'] == 1 and by['quotient__p1']['points_deduplicated'] == 1
    names = {t['name'] for t in by['add__p1']['tests']}
    pts = {tuple(t['point']) for t in by['add__p1']['tests'] if t['kind'] == 'concrete'}
    assert (1, 2) not in pts and (0, 0) in pts and 'test_add__p1__property' in names
    q = by['quotient__p1']
    assert q['points_outside_pre'] > 0 and all(t['point'] is None or t['point'][1] == 0 for t in q['tests'])
    assert q['hypothesis'] == 'emitted' and by['add__p1']['hypothesis'] == 'emitted'
    # every emitted test ran under the real interpreter and passed
    results = {t['result'] for r in res['statements'] for t in r['tests']}
    assert results == {'passed'}, res['pytest']
    c = res['counts']
    assert c['tests'] == c['tests_passed'] > 2 and c['tests_hypothesis'] == 2 and c['failing'] == 0
    assert c['emitted'] == 2 and c['not_emitted'] == 2 and c['points_deduplicated'] == 2
    assert res['dedupe']['functions_traced'] == 2 and res['dedupe']['tuples_traced'] == 2
    saved = json.loads((out / schema.FILES['emit']).read_text())
    assert saved['counts'] == c and saved['files'] == res['files']
    # a second emission replaces the previous files and does not deduplicate against them
    res2 = E.emit(tr, statements(), checks(), out, run_info={'source': str(src)})
    assert res2['counts']['points_deduplicated'] == 2 and 'removed 3 previously generated' in res2['notes'][0]


def test_failing_emitted_test_is_a_finding(tmp_path, monkeypatch):
    """A property that holds on the check domain but not elsewhere: the hypothesis test fails,
    and the stage reports it instead of dropping it."""
    monkeypatch.setattr(E, 'evaluate_rows', fake_rows)
    body = ('def add(a, b):\n    if 11 <= abs(a) <= 99 or 257 <= abs(a) <= 2 ** 31 - 2 or abs(a) > 2 ** 31:\n'
            '        return 0\n    return a + b\n')
    src, out = arith_source(tmp_path, body, with_tests=False), tmp_path / 'run'
    out.mkdir()
    res = E.emit(translation_for(src), statements()[:1], checks()[:1], out, run_info={})
    r = res['statements'][0]
    assert r['status'] == 'FAILING' and r['hypothesis'] == 'emitted'
    concrete = [t for t in r['tests'] if t['kind'] == 'concrete']
    prop = [t for t in r['tests'] if t['kind'] == 'hypothesis']
    assert concrete and all(t['result'] == 'passed' for t in concrete)
    assert len(prop) == 1 and prop[0]['result'] == 'failed' and 'AssertionError' in prop[0]['detail']
    assert res['counts']['failing'] == 1 and res['counts']['tests_failed'] == 1


def test_hypothesis_withheld_when_translation_disagrees(tmp_path, monkeypatch):
    """Lean says post holds where the Python form says it does not: no property test."""
    def rows_all_true(translation, plans, work, lean_root, stem):
        return {p.id: [(True, True)] * len(p.rt_rows()) for p in plans}
    monkeypatch.setattr(E, 'evaluate_rows', rows_all_true)
    src, out = arith_source(tmp_path, with_tests=False), tmp_path / 'run'
    out.mkdir()
    st = statement('add__p9', 'add', 'p9', 'nonsense', 'true', 'match r with | .val (.int x) => x == a - b | _ => false')
    res = E.emit(translation_for(src), [st], [schema.CheckResult('add__p9', 'BOUNDED_HOLDS', 64)], out, run_info={})
    r = res['statements'][0]
    assert r['status'] == 'EMITTED' and r['hypothesis'].startswith('Python form of post disagrees with Lean')
    assert all(t['kind'] == 'concrete' for t in r['tests']) and res['counts']['hypothesis_withheld'] == 1


def test_nothing_emitted_without_real_outcomes(tmp_path):
    src, out = arith_source(tmp_path, with_tests=False), tmp_path / 'run'
    out.mkdir()
    tr = translation_for(src)
    res = E.emit(tr, statements()[:1], checks()[:1], out, runtime=False)
    assert res['statements'][0]['status'] == 'NOT_EMITTED' and '--no-runtime' in res['statements'][0]['reason']
    res = E.emit(dict(tr, language='c'), statements()[:1], checks()[:1], out)
    assert 'Python only' in res['statements'][0]['reason'] and not (src / 'tests').exists()
    res = E.emit(tr, statements()[1:2], checks()[1:2], out)
    assert res['counts']['survivors'] == 0 and 'nothing to emit' in res['notes'][0]


def test_pipeline_wiring():
    for stages in (pipeline.MODEL_STAGES, pipeline.DEEP_STAGES, pipeline.DEEP_TOO_STAGES):
        assert stages[-1] == 'emit' and stages.index('emit') > stages.index('prove')
    assert pipeline.NEEDS['emit'] == ('translation', 'statements', 'checks') and pipeline.OUTPUT['emit'] == 'emit'
    assert schema.FILES['emit'] == 'emit.json'
    assert pipeline.with_judge(pipeline.MODEL_STAGES)[-1] == 'emit'


# --- Lean-backed ------------------------------------------------------------------------

@LEAN
def test_lean_evaluates_pre_and_post_on_real_outcomes(tmp_path):
    tr = json.loads((FIX / 'translation-PipelinePython.json').read_text())
    root = Path(os.environ.get('AUTOFORM_LEAN_ROOT', tr['lean_root']))
    sts = {s['property']: s for s in json.loads((FIX / 'statements-PipelinePython.json').read_text())
           if s['function'] == 'numbers.py:<module>.quotient'}
    fn = next(f for f in tr['functions'] if f['name'] == 'numbers.py:<module>.quotient')
    plans = [K.Plan(0, sts['p1'], fn, tr, 64), K.Plan(1, sts['p2'], fn, tr, 64)]
    for p in plans:
        K.run_runtime(tr, fn, p, work=tmp_path / 'rt')
    rows = E.evaluate_rows(tr, plans, tmp_path, root, 'q')
    for p in plans:
        got = rows[p.id]
        assert isinstance(got, list) and len(got) == len(p.rt_rows())
        for (idx, _), (pre, post) in zip(p.rt_rows(), got):
            a, b = p.points[idx]
            assert pre == ((b == 0) if p is plans[0] else (b != 0))
            assert post is True or not pre            # post is only meaningful where pre holds


@LEAN
def test_lean_emit_end_to_end(tmp_path):
    tr = json.loads((FIX / 'translation-PipelinePython.json').read_text())
    root = os.environ.get('AUTOFORM_LEAN_ROOT', tr['lean_root'])
    src = tmp_path / 'src'
    shutil.copytree(tr['source_root'], src)
    (src / 'numbers.py').rename(src / 'arith.py')      # `numbers` is a stdlib module: not importable by name
    tr['source_root'] = str(src)
    for f in tr['functions']:
        f['file'] = 'arith.py'
        f['name'] = f['name'].replace('numbers.py', 'arith.py')
    sts = [s for s in json.loads((FIX / 'statements-PipelinePython.json').read_text()) if s['id'].endswith(('add__p1', 'quotient__p1'))]
    for s in sts:
        s['function'] = s['function'].replace('numbers.py', 'arith.py')
    chk = [schema.CheckResult(s['id'], 'BOUNDED_HOLDS', 64, runtime_agrees=True, kernel_bounded_proof=True) for s in sts]
    res = E.emit(tr, sts, chk, tmp_path / 'run', run_info={}, lean_root=root)
    assert res['counts']['failing'] == 0 and res['counts']['tests_passed'] == res['counts']['tests'] > 0
    assert res['counts']['tests_hypothesis'] == 2
