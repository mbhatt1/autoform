"""Model stage of the NL autoformalizer (src/autoform/nl/model.py, pyvalues.py).

Pure-Python tests cover discovery, the purity screen, value encoding, dispatcher
generation, the CPython runner and tracer, and the disagreement -> repair loop (with the
language model and Lean replaced by stubs). Lean-backed tests (AUTOFORM_TEST_LEAN=1) build a
hand-written model of numbers.py through the real stage, check that `call` agrees with
CPython, and that a wrong `quotient` (Lean `/` instead of floor division) is caught.
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

from autoform.nl import check as K  # noqa: E402
from autoform.nl import model as M  # noqa: E402
from autoform.nl import prove as P  # noqa: E402
from autoform.nl import pyvalues as pv  # noqa: E402
from autoform.nl import schema  # noqa: E402

LEAN = pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_LEAN') != '1', reason='set AUTOFORM_TEST_LEAN=1')
NUMBERS = ROOT / 'examples/source/python'


def write(root: Path, rel: str, text: str):
    p = root / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(textwrap.dedent(text))


@pytest.fixture
def repo(tmp_path):
    root = tmp_path / 'repo'
    write(root, 'pkg/__init__.py', '')
    write(root, 'pkg/core.py', '''
        import time
        import random as rnd
        from .helpers import clamp
        CACHE = []

        def add(a: int, b: int) -> int:
            """Sum."""
            return a + b

        def scaled(x, k=2):
            return clamp(x * k)

        def stamp(x):
            return (x, time.time())

        def shout(s):
            print(s)
            return s

        def remember(x):
            CACHE.append(x)
            return x

        def gen(n):
            yield n

        def make(n):
            def inner():
                return n
            return inner

        def pick(xs):
            return rnd.choice(xs)

        def uses_stamp(x):
            return stamp(x)

        def keyed(*args, **kwargs):
            return args

        class Box:
            def __init__(self, v):
                self.v = v

            def get(self):
                return self.v

            @staticmethod
            def double(v):
                return 2 * v

            def __private(self):
                return 1
        ''')
    write(root, 'pkg/helpers.py', '''
        def clamp(x):
            return max(0, min(10, x))
        ''')
    write(root, 'tests/__init__.py', '')
    write(root, 'tests/test_core.py', '''
        from pkg import core
        from pkg.core import add

        def test_add():
            assert add(1, 2) == 3
            assert core.scaled(3) == 6
            assert core.scaled(-4, 3) == 0
            assert core.keyed(1, 'a') == (1, 'a')
            assert core.Box.double(4) == 8

        def test_unrelated():
            def add(x):
                return x
            assert add(1) == 1
        ''')
    return root


# ------------------------------------------------------------------ discovery and screening

def test_discovery_names_params_tests_and_callers(repo):
    infos = {f.name: f for f in M.discover(repo)}
    add = infos['pkg/core.py:<module>.add']
    assert add.source_name == 'add' and add.file == 'pkg/core.py' and add.line == 7
    assert [(p.name, p.sort) for p in add.params] == [('a', 'int'), ('b', 'int')]
    assert add.returns == 'int' and add.doc == 'Sum.'
    assert add.source.startswith('def add(a: int, b: int) -> int:')
    assert any('add(1, 2)' in t['text'] for t in add.tests)
    assert all(t['location'].startswith('tests/test_core.py:') for t in add.tests)
    # methods and staticmethods get dotted names; private names are mangled like CPython
    assert 'pkg/core.py:<module>.Box.get' in infos
    assert 'pkg/core.py:<module>.Box._Box__private' in infos
    # varargs is one parameter; **kwargs is dropped (it is always passed empty)
    assert [p.name for p in infos['pkg/core.py:<module>.keyed'].params] == ['args']
    # callers across modules through `from .helpers import clamp`
    assert infos['pkg/helpers.py:<module>.clamp'].callers == ['pkg/core.py:<module>.scaled']
    # test files are not discovered as source
    assert not any(n.startswith('tests/') for n in infos)


def test_purity_screen_reasons(repo):
    fns, _ = M._discover(repo)
    why = {f.info.name.split('.')[-1] if '<module>.Box' not in f.info.name else f.qual: f.reason for f in fns}
    assert why['add'] is None and why['scaled'] is None and why['keyed'] is None and why['clamp'] is None
    assert why['Box.double'] is None                               # staticmethod: a plain function
    assert 'time' in why['stamp']
    assert 'print' in why['shout']
    assert 'module-level state' in why['remember']
    assert 'generator' in why['gen']
    assert 'closure' in why['make']
    assert 'random' in why['pick']
    assert 'stamp' in why['uses_stamp']                            # impurity is transitive
    assert why['Box.get'] is None                                  # methods are attempted now
    by = {f.info.name: f.info for f in fns}
    assert by['pkg/core.py:<module>.add'].hole_free and by['pkg/core.py:<module>.add'].call_closed
    assert not by['pkg/core.py:<module>.stamp'].hole_free


def test_discovery_filter_and_numbers_example():
    infos = M.discover(NUMBERS, functions=['quotient'])
    assert [f.name for f in infos] == ['numbers.py:<module>.quotient']
    assert infos[0].hole_free


# ------------------------------------------------------------------ values

def test_value_tags_canon_and_lean_literals():
    assert pv.tag(True) == ['b', True] and pv.tag(1) == ['i', '1']      # bool is not int
    assert pv.canon(pv.tag((1, 'ab', None, [True], {'k': 2.0}))) == \
        f"T(i:1,s:[97, 98],none,L(b:true,),D(s:[107]=f:{pv.float_bits(2.0)};),)"
    assert pv.canon(pv.tag(float('nan'))) == 'f:nan'
    assert pv.canon(pv.tag(int)) == 'F:int'

    class T(tuple):
        pass
    assert pv.tag(T((1,))) == ['t', [['i', '1']]]                    # tuple subclasses encode as tuples
    with pytest.raises(pv.Unencodable):
        pv.tag(object())
    assert pv.tag({2, 1}) == ['S', [['i', '1'], ['i', '2']], 'set']   # sets: canonical order
    assert pv.lean_lit(pv.tag(-3)) == '(Val.int (-3))'
    assert pv.lean_lit(pv.tag('a"\n')) == '(Val.str "a\\"\\n")'
    assert pv.lean_lit(pv.tag((None,))) == '(Val.tuple [Val.unit])'
    v = ('x', [1, -2], {'a': None}, 2.5, float)
    assert pv.untag(json.loads(json.dumps(pv.tag(v)))) == v
    assert pv.canon_outcome({'k': 'exn', 't': 'ZeroDivisionError'}) == 'exn ZeroDivisionError'
    assert pv.canon_outcome({'k': 'timeout'}) is None
    assert pv.display('ok ' + pv.canon(pv.tag(('a', 1)))) == "returns ('a', 1)"
    assert pv.display('exn KeyError') == 'raises KeyError'


# ------------------------------------------------------------------ dispatcher generation

def test_parse_type_and_signature_errors():
    assert M.parse_type('List (Option Int) × String') == ('Prod', [('List', ('Option', 'Int')), 'String'])
    assert M.parse_type('Except String (Int × Bool)') == ('Except', ('Prod', ['Int', 'Bool']))
    for bad, msg in (('Nat', 'use Int'), ('Float', 'Fl'), ('Except Nat Int', 'Except String'), ('List', 'truncated')):
        with pytest.raises(M.TypeError_, match=msg):
            M.parse_type(bad)
    with pytest.raises(M.TypeError_, match='varargs'):
        M.parse_sig([{'name': 'xs', 'type': 'Int', 'kind': 'varargs'}], 'Int')
    with pytest.raises(M.TypeError_, match='default'):
        M.parse_sig([{'name': 'a', 'type': 'Int', 'default': '0'}, {'name': 'b', 'type': 'Int'}], 'Int')
    with pytest.raises(M.TypeError_, match='outermost'):
        M.parse_sig([], 'Option (Except String Int)')


def test_wrapper_decodes_runs_and_encodes():
    w = M.wrapper('py_q', M.parse_sig([{'name': 'a', 'type': 'Int'}, {'name': 'b', 'type': 'Int'}],
                                      'Except String Int'))
    assert w.splitlines()[0] == 'def call_py_q : List Val → EResult'
    assert '| [a0, a1] =>' in w and 'match dInt a0, dInt a1 with' in w
    assert '| some x0, some x1 => resE Val.int (py_q x0 x1)' in w
    assert '| _, _ => .hole "nl:arg-type"' in w and w.rstrip().endswith('.hole "nl:arg-count"')
    # defaults: one alternative per accepted arity, the default term filled in
    w = M.wrapper('py_s', M.parse_sig([{'name': 'x', 'type': 'Int'}, {'name': 'k', 'type': 'Int', 'default': '2'}],
                                      'Option (List String)'))
    assert '| [a0] =>' in w and 'resV (eOpt (eList Val.str)) (py_s x0 (2))' in w
    # varargs only: the whole list, no arity fallback (it would be a redundant alternative)
    w = M.wrapper('py_k', M.parse_sig([{'name': 'args', 'type': 'List Val', 'kind': 'varargs'}], 'Val'))
    assert '| rest =>' in w and 'dListAux dVal rest' in w and 'arg-count' not in w
    w = M.wrapper('py_m', M.parse_sig([{'name': 's', 'type': 'Val'},
                                       {'name': 'args', 'type': 'List Val', 'kind': 'varargs'}], 'Int × Bool'))
    assert '| a0 :: rest =>' in w and 'resV (eTup2 Val.int Val.bool) (py_m x0 xs)' in w and 'arg-count' in w
    # no parameters
    w = M.wrapper('py_z', M.parse_sig([], 'Unit'))
    assert '| [] => resV eUnit py_z' in w
    d = M.dispatcher([('m.py:<module>.f', 'py_f')])
    assert '| "m.py:<module>.f" => call_py_f args' in d and '.hole "nl:unknown-function"' in d


def test_model_text_is_checked_before_lean():
    assert M.lean_problems('def py_f (a : Int) : Int := a', 'py_f') == []
    assert M.lean_problems('def py_f_aux : Int := 1\ndef py_f : Int := py_f_aux', 'py_f') == []
    assert any('partial' in p for p in M.lean_problems('partial def py_f (a : Int) : Int := a', 'py_f'))
    assert any('sorry' in p for p in M.lean_problems('def py_f : Int := sorry', 'py_f'))
    assert any('named exactly' in p for p in M.lean_problems('def f : Int := 1', 'py_f'))
    assert any('helper' in p for p in M.lean_problems('def g : Int := 1\ndef py_f : Int := g', 'py_f'))
    assert any('only `def`' in p for p in M.lean_problems('theorem py_f_t : True := trivial\ndef py_f : Int := 1',
                                                         'py_f'))
    assert any('Float' in p for p in M.lean_problems('def py_f : Float := 1.0', 'py_f'))
    # strings and comments do not trip the screen
    assert M.lean_problems('def py_f : String := "sorry partial" -- IO', 'py_f') == []
    # a char literal '"' does not open a string that swallows the next definition
    assert M.lean_problems("def py_f_q : Char := '\"'\ndef py_f (x' : Nat) : Char := py_f_q", 'py_f') == []


def test_boundary_points_are_typed():
    sig = M.parse_sig([{'name': 'a', 'type': 'Int'}, {'name': 'b', 'type': 'Bool'}], 'Int')
    pts = M.boundary_points(sig, 'def f(a, b):\n    return a if b else 41\n')
    assert all(p[0][0] == 'i' and p[1][0] == 'b' for p in pts)
    assert ['i', '41'] in [p[0] for p in pts] and ['i', str(-2 ** 63 - 1)] in [p[0] for p in pts]
    sig = M.parse_sig([{'name': 'args', 'type': 'List Val', 'kind': 'varargs'}], 'Val')
    lens = {len(p) for p in M.boundary_points(sig, '')}
    assert 0 in lens and max(lens) >= 2


def test_lean_imports_for_model_and_deep_translations():
    model_tr = {'module': 'NLx', 'call_template': 'Autoform.NLModel.NLx.call {name} {args}'}
    deep_tr = {'module': 'NLx', 'call_template': 'runFunc Autoform.Generated.NLx.program 1000 {name} {args}'}
    entry_tr = {'module': 'NLx', 'call_template': 'Autoform.NL.NLx.callF 900 {name} {args}'}
    assert schema.lean_imports(model_tr) == ['Autoform.NLModel.NLx']
    assert schema.lean_imports(deep_tr) == ['Autoform.Generated.NLx']
    assert schema.lean_imports(entry_tr) == ['Autoform.Generated.NLx', 'Autoform.NL.NLx']
    assert K.header(model_tr).startswith('import Autoform.NLModel.NLx\nimport Lean.Data.Json\n')
    assert K.header('NLx').startswith('import Autoform.Generated.NLx\n')
    ph = P.header(model_tr)
    assert ph.startswith('import Autoform.NLModel.NLx\n') and 'Autoform.Generated' not in ph
    assert 'import Autoform.Tactics.Portfolio' in ph


# ------------------------------------------------------------------ CPython side

def test_runtime_runner_outcomes(repo, tmp_path):
    fns, _ = M._discover(repo)
    by = {f.info.name: f for f in fns}
    rt = M.Runtime(by['pkg/core.py:<module>.scaled'], tmp_path / 'rt')
    out = rt.run([[pv.tag(3)], [pv.tag(3), pv.tag(-1)], [pv.tag('a')], [pv.tag(3)]])
    assert out[0] == {'k': 'ok', 'v': ['i', '6']} and out[1] == {'k': 'ok', 'v': ['i', '0']}
    assert out[2] == {'k': 'exn', 't': 'TypeError'}       # 'aa' compared with int
    assert rt.calls == 1                                   # the repeated point came from the cache
    rt2 = M.Runtime(by['pkg/core.py:<module>.Box.double'], tmp_path / 'rt2')
    assert rt2.run([[pv.tag((1,))]]) == [{'k': 'ok', 'v': ['t', [['i', '1'], ['i', '1']]]}]


def test_tracer_records_calls_from_the_suite(repo, tmp_path):
    fns, _ = M._discover(repo)
    att = [f for f in fns if f.reason is None]
    rec, stats = M.trace_tests(att, repo, M._test_dirs(repo), tmp_path / 'trace')
    assert stats['runs'][0]['rc'] == 0, stats
    assert [['i', '1'], ['i', '2']] in rec['pkg/core.py:<module>.add']
    assert [['i', '3'], ['i', '2']] in rec['pkg/core.py:<module>.scaled']     # default filled in
    assert [['i', '1'], ['s', 'a']] in rec['pkg/core.py:<module>.keyed']      # *args spread
    assert [['i', '6']] in rec['pkg/helpers.py:<module>.clamp']               # reached indirectly
    assert [['i', '4']] in rec['pkg/core.py:<module>.Box.double']


# ------------------------------------------------------------------ repair loop (stubs)

WRONG_Q = 'def py_quotient (a b : Int) : Except String Int :=\n  if b = 0 then .error "ZeroDivisionError" else .ok (a / b)'
RIGHT_Q = WRONG_Q.replace('(a / b)', '(Int.fdiv a b)')
ADD = 'def py_add (a b : Int) : Int := a + b'


def answer(lean, english='x'):
    return {'english': english, 'params': [{'name': 'a', 'type': 'Int', 'kind': 'positional', 'default': None},
                                           {'name': 'b', 'type': 'Int', 'kind': 'positional', 'default': None}],
            'returns': 'Int' if 'py_add' in lean else 'Except String Int', 'lean': lean}


def fake_evaluate(module, lean_root, work, stem, callee_src, cand, lean_name, qual, points, runtime,
                  kernel_points=M.KERNEL_POINTS, **kw):
    """Python stand-in for the Lean run: interpret the two candidate shapes used here."""
    ev = M.Evaluation(elaborates=True)
    for p in points:
        a, b = (pv.untag(t) for t in p)
        if 'py_add' in cand.data['lean']:
            ev.outputs.append(f'ok i:{a + b}')
        elif b == 0:
            ev.outputs.append('exn ZeroDivisionError')
        elif 'Int.fdiv' in cand.data['lean']:
            ev.outputs.append(f'ok i:{a // b}')
        else:   # Lean's `/` on Int: Euclidean division
            q = a // b if b > 0 else -(a // -b)
            q = q if a - b * q >= 0 else q + (1 if b < 0 else -1)
            ev.outputs.append(f'ok i:{q}')
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
    ev.kernel_checked = kernel_points
    return ev


def test_disagreement_is_repaired_with_counterexamples(tmp_path, monkeypatch):
    monkeypatch.setattr(M, 'evaluate', fake_evaluate)
    prompts = []

    def ask(prompt, keys, **kw):
        prompts.append((keys, prompt))
        if 'NAME: py_add' in prompt:
            return answer(ADD), 0.01
        if 'Independent re-implementation' in prompt:
            return answer(RIGHT_Q), 0.01
        return answer(RIGHT_Q if 'rejected' in prompt else WRONG_Q), 0.01

    tr = M.model(NUMBERS, tmp_path / 'out', tmp_path / 'lean', module='NLTestStub', functions=['add', 'quotient'],
                 ask=ask, do_build=False, repairs=2)
    models = {m['function']: m for m in schema.load(tmp_path / 'out' / 'models.json')}
    q = models['numbers.py:<module>.quotient']
    assert q['status'] == 'VALIDATED' and q['repairs'] == 1 and q['level'] == 'L0'
    assert q['second_translation'] == 'agrees' and q['tests_run'] > 50
    repair = [p for k, p in prompts if 'NAME: py_quotient' in p and 'rejected' in p][0]
    assert 'Differential test:' in repair and 'Python returns' in repair
    assert re.search(r'quotient\(-?\d+, -\d+\): Python returns -?\d+; Lean model returns -?\d+', repair)
    assert models['numbers.py:<module>.add']['status'] == 'VALIDATED'
    assert tr.call_template == 'Autoform.NLModel.NLTestStub.call {name} {args}'
    assert tr.ast == '' and tr.program_const == '' and tr.fuel == 0 and tr.language == 'python'
    assert {f.name for f in tr.functions} == {'numbers.py:<module>.add', 'numbers.py:<module>.quotient'}
    assert all(f.hole_free and not f.needs_init for f in tr.functions)
    assert [p.sort for p in tr.functions[0].params] == ['int', 'int']
    text = (tmp_path / 'lean/Autoform/NLModel/NLTestStub.lean').read_text()
    assert text.startswith(M.MODULE_MARK) and 'import Autoform.Lang.Core.Syntax' in text
    assert '-- model of numbers.py:<module>.quotient: VALIDATED (L0)' in text and 'Int.fdiv' in text
    assert not re.search(r'\b(sorry|partial|native_decide|axiom)\b', text)
    saved = schema.load(tmp_path / 'out' / 'translation.json')
    assert saved['module'] == 'NLTestStub' and saved['functions'][0]['name'].startswith('numbers.py:')


def test_unrepaired_disagreement_and_disagreeing_second_translation(tmp_path, monkeypatch):
    monkeypatch.setattr(M, 'evaluate', fake_evaluate)

    def ask(prompt, keys, **kw):
        if 'Independent re-implementation' in prompt:
            return answer(WRONG_Q), 0.0     # B is wrong, A is right: keep A, record it
        return answer(WRONG_Q if 'NAME: py_quotient' in prompt and 'Differential' not in prompt else RIGHT_Q), 0.0

    M.model(NUMBERS, tmp_path / 'o1', tmp_path / 'lean', module='NLTestStub2', functions=['quotient'], ask=ask,
            do_build=False, repairs=1)
    q = schema.load(tmp_path / 'o1' / 'models.json')[0]
    assert q['status'] == 'VALIDATED' and q['second_translation'] == 'disagrees' and q['level'] == 'none'
    assert 'B also disagrees with CPython' in q['notes']

    tr = M.model(NUMBERS, tmp_path / 'o2', tmp_path / 'lean', module='NLTestStub3', functions=['quotient'],
                 ask=lambda p, k, **kw: (answer(WRONG_Q), 0.0), do_build=False, repairs=1, second=False)
    q = schema.load(tmp_path / 'o2' / 'models.json')[0]
    assert q['status'] == 'DISAGREES' and q['repairs'] == 1 and q['disagreements']
    assert q['level'] == 'none' and q['second_translation'] == 'not_run'
    assert tr.functions[0].hole_free is False and tr.functions[0].holes == ['nl:model-disagrees']


def test_rejected_text_is_fed_back_and_failure_recorded(tmp_path, monkeypatch):
    monkeypatch.setattr(M, 'evaluate', fake_evaluate)
    seen = []

    def ask(prompt, keys, **kw):
        seen.append(prompt)
        return answer('partial def py_add (a b : Int) : Int := a + b'), 0.0

    tr = M.model(NUMBERS, tmp_path / 'o', tmp_path / 'lean', module='NLTestStub4', functions=['add'], ask=ask,
                 do_build=False, repairs=1)
    rec = schema.load(tmp_path / 'o' / 'models.json')[0]
    assert rec['status'] == 'FAILED' and len(seen) == 2 and 'forbidden construct `partial`' in seen[1]
    assert tr.functions == [] and any(n.startswith('FAILED numbers.py:<module>.add') for n in tr.notes)
    assert not (tmp_path / 'lean/Autoform/NLModel/NLTestStub4.lean').exists()


def test_refuses_to_overwrite_a_module_it_did_not_write(tmp_path):
    d = tmp_path / 'Autoform/NLModel'
    d.mkdir(parents=True)
    (d / 'Hand.lean').write_text('-- hand written\n')
    with pytest.raises(RuntimeError, match='not written by the model stage'):
        M.write_module(tmp_path, 'Hand', M.MODULE_MARK + '\n')


# ------------------------------------------------------------------ Lean-backed

HAND = {'py_add': ADD, 'py_quotient': RIGHT_Q}


@LEAN
def test_lean_hand_written_models_build_and_agree_with_cpython(tmp_path):
    root = Path(os.environ.get('AUTOFORM_LEAN_ROOT', ROOT))

    def ask(prompt, keys, **kw):
        name = re.search(r'NAME: (\w+)', prompt).group(1)
        return answer(HAND[name]), 0.0

    tr = M.model(NUMBERS, tmp_path / 'out', root, module='NLTestHand', functions=['add', 'quotient'], ask=ask,
                 repairs=0)
    meta = json.loads((tmp_path / 'out' / 'model.meta.json').read_text())
    assert meta['build']['ok'] and meta['build']['smoke_mismatches'] == []
    models = {m['function']: m for m in schema.load(tmp_path / 'out' / 'models.json')}
    for m in models.values():
        assert m['status'] == 'VALIDATED' and m['level'] == 'L0' and m['tests_run'] >= 100
        assert 'kernel-evaluated 3/3' in m['notes']
    assert len(tr.functions) == 2
    # the check stage's own file shape imports the model module and evaluates `call` in the kernel
    text = K.header(schema.load(tmp_path / 'out' / 'translation.json'))
    probe = tmp_path / 'probe.lean'
    probe.write_text(text + 'example : Autoform.NLModel.NLTestHand.call "numbers.py:<module>.quotient" '
                            '[.int 7, .int (-2)] matches .val (.int (-4)) := by decide +kernel\n'
                            'example : Autoform.NLModel.NLTestHand.call "numbers.py:<module>.quotient" '
                            '[.int 7, .int 0] matches .exn (.str "ZeroDivisionError") := by decide +kernel\n')
    code, log, _ = M.run_lean(root, probe)
    assert code == 0, log


@LEAN
def test_lean_wrong_quotient_is_caught_at_a_negative_divisor(tmp_path):
    root = Path(os.environ.get('AUTOFORM_LEAN_ROOT', ROOT))
    M.model(NUMBERS, tmp_path / 'out', root, module='NLTestWrong', functions=['quotient'],
            ask=lambda p, k, **kw: (answer(WRONG_Q), 0.0), repairs=0, second=False, do_build=False)
    q = schema.load(tmp_path / 'out' / 'models.json')[0]
    assert q['status'] == 'DISAGREES' and q['level'] == 'none'
    neg = [d for d in q['disagreements'] if re.search(r', -\d+\)$', d['inputs'])]
    assert neg, q['disagreements']
    d = neg[0]
    a, b = (int(x) for x in d['inputs'].strip('()').split(', '))
    assert d['runtime'] == f'returns {a // b}' and d['model'] != d['runtime']


def test_samples_spread_across_receivers_members_first():
    empty = ['O', 'C', [['data', ['d', []]]]]
    full = ['O', 'C', [['data', ['d', [[['i', '5'], ['i', '50']]]]]]]
    pts = [[empty, ['i', str(k)]] for k in range(30)] + [[full, ['i', '1']], [full, ['i', '5']]]
    got = M.spread_samples(pts, 6)
    assert len(got) == 6
    assert got[1] == [full, ['i', '5']] and got[3] == [full, ['i', '1']]   # alternates; the member key first
    every = M.spread_samples(pts, 100)
    assert len(every) == 32 and sorted(map(str, every)) == sorted(map(str, pts))   # nothing lost or duplicated
    assert M.spread_samples([[['i', '1']], [['i', '2']]], 5) == [[['i', '1']], [['i', '2']]]   # single argument
