"""Methods, objects and rich data types in the NL model stage (autoform.nl.model/pyvalues/check).

Pure-Python tests: class discovery and the method screen, structure inference, signature
and dispatcher generation for methods (state threading), the encoding of every data type
in both directions, the tracer recording receivers and constructor arguments, and the
CPython runner rebuilding receivers. Lean-backed tests (AUTOFORM_TEST_LEAN=1) run the real
model stage on a small Stack/Counter package with hand-written models (stubbed language
model): they validate against CPython, a wrong push (right result, unchanged receiver) is
caught on the post-state, the built dispatcher round-trips every type, and the check stage
compares a post-state statement with real executions.
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
from autoform.nl import formalize as F  # noqa: E402
from autoform.nl import model as M  # noqa: E402
from autoform.nl import pyvalues as pv  # noqa: E402
from autoform.nl import schema  # noqa: E402

LEAN = pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_LEAN') != '1', reason='set AUTOFORM_TEST_LEAN=1')

STACK = '''
from collections import OrderedDict
from collections.abc import MutableMapping


class Stack:
    """A bounded stack."""

    def __init__(self, limit):
        self.items = []
        self.limit = limit

    def push(self, x):
        if len(self.items) >= self.limit:
            raise OverflowError("full")
        self.items.append(x)
        return len(self.items)

    def peek(self):
        if not self.items:
            raise IndexError("empty")
        return self.items[-1]

    @property
    def size(self):
        return len(self.items)

    def push_twice(self, x):
        self.push(x)
        return self.push(x)


class Counter:
    def __init__(self):
        self.count = 0
        self.seen = set()
        self.log = {}

    def hit(self, key):
        self.count += 1
        self.seen.add(key)
        self.log[key] = self.log.get(key, 0) + 1
        return (self.count, key)


class Bag(MutableMapping):
    __marker = object()

    def __init__(self):
        self._store = OrderedDict()

    def __getitem__(self, k):
        return self._store[k]

    def __setitem__(self, k, v):
        self._store[k] = v

    def __delitem__(self, k):
        del self._store[k]

    def __iter__(self):
        return iter(self._store)

    def __len__(self):
        return len(self._store)

    def take(self, k, default=__marker):
        if k in self:
            return self.pop(k)
        if default is self.__marker:
            raise KeyError(k)
        return default


class Loud(dict):
    def shout(self):
        return 1

    @classmethod
    def make(cls):
        return cls()
'''

TESTS = '''
import pytest
from pkg.stack import Stack, Counter, Bag


def test_stack():
    s = Stack(3)
    assert s.push(1) == 1
    assert s.push(2) == 2
    assert s.peek() == 2
    assert s.size == 2
    s.push(5)
    with pytest.raises(OverflowError):
        s.push(9)
    with pytest.raises(IndexError):
        Stack(1).peek()
    assert Stack(5).push_twice(4) == 2


def test_counter():
    c = Counter()
    c.hit('a')
    c.hit('b')
    assert c.hit('a') == (3, 'a')


def test_bag():
    b = Bag()
    b['x'] = 1
    b['y'] = 2
    assert b.take('x') == 1
    assert b.take('z', 0) == 0
    with pytest.raises(KeyError):
        b.take('z')
'''


def write(root: Path, rel: str, text: str):
    p = root / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(textwrap.dedent(text))


@pytest.fixture
def repo(tmp_path):
    root = tmp_path / 'repo'
    write(root, 'pkg/__init__.py', '')
    write(root, 'pkg/stack.py', STACK)
    return root


@pytest.fixture
def suite(tmp_path):
    """Tests OUTSIDE the source tree (the --tests case)."""
    d = tmp_path / 'suite' / 'tests'
    write(d, '__init__.py', '')
    write(d, 'test_stack.py', TESTS)
    return d


N = 'pkg/stack.py:<module>.'


# ------------------------------------------------------------------ discovery and screen

def test_classes_methods_kinds_and_screen(repo):
    fns, mods = M._discover(repo)
    by = {f.qual: f for f in fns}
    assert by['Stack.__init__'].kind == 'constructor' and by['Stack.push'].kind == 'method'
    assert by['Stack.size'].kind == 'property' and by['Stack.push'].reason is None
    assert by['Stack.size'].reason is None and by['Counter.hit'].reason is None
    # a constructor's params omit the receiver; a method's receiver has sort 'object'
    assert [p.name for p in by['Stack.__init__'].info.params] == ['limit']
    assert [(p.name, p.sort) for p in by['Stack.push'].info.params] == [('self', 'object'), ('x', 'any')]
    assert by['Stack.push'].info.receiver == 'pkg.stack.Stack'
    # builtin base and classmethod stay out, with explicit reasons
    assert 'builtin base (dict)' in by['Loud.shout'].reason
    assert 'builtin base' in by['Loud.make'].reason or 'classmethod' in by['Loud.make'].reason
    # external base: `self.pop` is a MutableMapping mixin -> unmodelled, not a callee
    take = by['Bag.take']
    assert take.reason is None
    assert any('self.pop' in u and 'collections.abc.MutableMapping' in u for u in take.unmodelled)
    assert N + 'Bag.__contains__' not in take.callees          # not defined in the repo either
    assert not any('__marker' in u for u in take.unmodelled)   # a class attribute, not a method
    cls = mods['pkg/stack.py'].classes['Bag']
    assert cls.bases == [('external', 'collections.abc.MutableMapping')]
    assert M.static_fields(mods['pkg/stack.py'].classes['Counter']) == ['count', 'seen', 'log']


def test_receiver_uses_and_callees(tmp_path):
    root = tmp_path / 'r'
    write(root, 'm.py', '''
        class Base:
            def __init__(self):
                self.d = {}
            def __contains__(self, k):
                return k in self.d
            def get(self, k):
                return self.d[k] if k in self else None

        class Child(Base):
            def __init__(self):
                Base.__init__(self)
                self.n = 0
            def put(self, k, v, base_get=Base.get):
                self.d[k] = v
                self.n += 1
                return base_get(self, k)
        ''')
    by = {f.qual: f for f in M._discover(root)[0]}
    assert by['Base.get'].callees == ['m.py:<module>.Base.__contains__']
    assert 'm.py:<module>.Base.get' in by['Child.put'].callees          # default-argument alias
    assert 'm.py:<module>.Base.__init__' in by['Child.__init__'].callees
    assert by['Child.put'].cls.mro()[1].name == 'Base'


# ------------------------------------------------------------------ values

def test_every_type_both_ways():
    class Obj:
        __slots__ = ('a', '__b')

    o = Obj()
    o.a = (1, 'x')
    o._Obj__b = {3, 1}
    values = [None, True, -7, 2 ** 70, 0.1, float('-inf'), 'é"\n', b'\x00\xffA', (), (1,), (1, 2.5, None),
              [1, [2]], {'k': [1], 2: None}, {'b', 'a'}, frozenset({2, 1}), {2: {1}}, int]
    for v in values:
        t = pv.tag(v)
        back = pv.untag(json.loads(json.dumps(t)))
        assert back == v and type(back) is type(v), (v, back)
        # canonical string <-> display agree with Python's view
        text = pv.display('ok ' + pv.canon(t))
        assert text.startswith('returns ')
    assert pv.canon(pv.tag(b'\x01')) == 'X:bytes(L(i:1,))'
    assert pv.lean_lit(pv.tag(b'\x01')) == '(Val.bobj "bytes" (Val.list [(Val.int 1)]))'
    # sets: canonical order (by canonical string), independent of insertion order
    assert pv.tag({10, 2}) == pv.tag({2, 10}) == ['S', [['i', '10'], ['i', '2']], 'set']
    assert pv.lean_lit(pv.tag(frozenset())) == '(Val.bobj "frozenset" (Val.list []))'
    with pytest.raises(pv.Unencodable):
        pv.tag(bytearray(b'a'))
    # objects only for modelled classes; slots mangled like CPython
    with pytest.raises(pv.Unencodable):
        pv.tag(o)
    t = pv.tag(o, classes={pv.class_name(Obj)})
    assert t[0] == 'O' and [a for a, _ in t[2]] == ['_Obj__b', 'a']
    assert pv.canon(t).startswith('X:obj:') and 'obj:' in pv.lean_lit(t)


def test_object_restore_keeps_container_types():
    import collections
    import importlib
    mod = type(sys)('af_objmod')
    exec('import collections\nclass C:\n    pass\n', mod.__dict__)
    sys.modules['af_objmod'] = mod
    try:
        c = mod.C()
        c.order = collections.OrderedDict([('b', 1), ('a', 2)])
        c.n = 3
        t = json.loads(json.dumps(pv.tag(c, classes={'af_objmod.C'})))
        assert t[3] == {'order': 'collections.OrderedDict'}
        back = pv.untag(t)
        assert type(back) is mod.C and type(back.order) is collections.OrderedDict
        assert list(back.order) == ['b', 'a'] and back.n == 3
        back.order.move_to_end('b')                     # an OrderedDict method works again
        assert pv.show(t).startswith('<af_objmod.C ')
        assert importlib.import_module('af_objmod') is mod
    finally:
        del sys.modules['af_objmod']


def test_outcomes_with_post_state():
    r = {'k': 'ok', 'v': pv.tag(2), 'post': pv.tag([1, 2])}
    assert pv.canon_outcome(r) == 'ok T(i:2,L(i:1,i:2,),)'
    assert pv.lean_outcome(r) == '(EResult.val (Val.tuple [(Val.int (2)), (Val.list [(Val.int (1)), (Val.int (2))])]))'
    assert pv.canon_outcome({'k': 'exn', 't': 'KeyError', 'post': pv.tag(1)}) == 'exn KeyError'


# ------------------------------------------------------------------ types, structures, wrappers

def test_rich_types_parse_decode_encode():
    t = M.parse_type('Dict String (PySet Int) × Tuple Bytes', structs={'S_X'})
    assert t == ('Prod', [('Dict', 'String', ('PySet', 'Int')), ('Tuple', 'Bytes')])
    assert M.decoder(t) == '(dTup2 (dDict dStr (dSet dInt)) (dTuple dBytes))'
    assert M.encoder(t) == '(eTup2 (eDict Val.str (eSet Val.int)) (eTuple eBytes))'
    assert M.parse_type('Option S_X', structs={'S_X'}) == ('Option', ('Struct', 'S_X'))
    assert M.decoder(('Struct', 'S_X')) == 'dObj_S_X' and M.sort_of(('Struct', 'S_X')) == 'object'
    assert M.show_type(t) == 'Dict String (PySet Int) × Tuple Bytes'
    with pytest.raises(M.TypeError_, match='PySet'):
        M.parse_type('Set Int')
    with pytest.raises(M.TypeError_, match='unsupported'):
        M.parse_type('S_Y', structs={'S_X'})


def test_structure_inference_joins_types_and_counts_misfits():
    import ast
    node = ast.parse('class C:\n    def __init__(self):\n        self.z = 1\n').body[0]
    cls = M._Class('C', 'C', M._Module('m.py', Path('m.py'), '', None, 'm', Path('.')), node,
                   methods={'__init__': node.body[0]})

    def state(**kw):
        return ['O', 'm.C', [[k, pv.tag(v)] for k, v in sorted(kw.items())]]
    states = [state(n=1, xs=[], d={}, s=set(), o=None, t=(1, 'a'), v=1),
              state(n=2, xs=[1], d={'a': 1}, s={'x'}, o=3, t=(2, 'b'), v='a'),
              state(n=3, xs=[2], d={'b': 2}, s=set(), o=None, t=(3, 'c'), v=None),
              state(n=4, extra=1)]
    st = M.infer_structure(cls, states, 'S_C')
    types = {a: M.show_type(t) for a, _, t in st.fields}
    assert types == {'d': 'Dict String Int', 'n': 'Int', 'o': 'Option Int', 's': 'PySet String',
                     't': 'Int × String', 'v': 'Val', 'xs': 'List Int'}
    assert st.observed == 4 and st.decodable == 3 and not st.fits(states[3])
    text = st.text()
    assert 'structure S_C where' in text and 'f_d : Dict String Int' in text
    assert 'if n == "obj:m.C" && kvs.length == 7 then' in text
    assert '(dField "o" kvs).bind (dOpt dInt)' in text
    assert 'def eObj_S_C (s : S_C) : Val := .bobj "obj:m.C" (.dict [(.str "d", (eDict Val.str Val.int) s.f_d)' in text
    # no observations: the class's own attributes, typed Val
    empty = M.infer_structure(cls, [], 'S_E')
    assert empty.source == 'static' and empty.fields == [('z', 'f_z', 'Val')]


def test_method_signatures_and_state_threading_wrappers():
    S = {'S_Stack'}
    self_p = {'name': 'self', 'type': 'S_Stack'}
    push = M.parse_sig([self_p, {'name': 'x', 'type': 'Int'}], 'Except String (Int × S_Stack)', structs=S,
                       kind='method', struct='S_Stack', mutates=True)
    assert push.mutates and push.result == 'Int'
    w = M.wrapper('py_push', push)
    assert 'def call_py_push : List Val → EResult' in w and 'def call_py_push_post : List Val → EResult' in w
    assert 'match dObj_S_Stack a0, dInt a1 with' in w
    assert 'resE (eFst Val.int) (py_push x0 x1)' in w                  # the Python result only
    assert 'resE (eTup2 Val.int eObj_S_Stack) (py_push x0 x1)' in w    # result and receiver after
    peek = M.parse_sig([self_p], 'Except String Int', structs=S, kind='method', struct='S_Stack')
    w = M.wrapper('py_peek', peek)
    assert 'resE (ePure Val.int eObj_S_Stack x0) (py_peek x0)' in w     # unchanged receiver
    init = M.parse_sig([{'name': 'limit', 'type': 'Int'}], 'S_Stack', structs=S, kind='constructor',
                       struct='S_Stack')
    assert 'resV eObj_S_Stack (py_init x0)' in M.wrapper('py_init', init)
    d = M.dispatcher([('m.py:<module>.Stack.push', 'py_push', 'method'), ('m.py:<module>.f', 'py_f', 'function')])
    assert '| "m.py:<module>.Stack.push#post" => call_py_push_post args' in d
    assert '"m.py:<module>.f#post"' not in d
    for bad, kw, msg in (
            ([{'name': 'x', 'type': 'Int'}], dict(returns='Int', kind='method'), 'receiver'),
            ([self_p], dict(returns='Int', kind='method', mutates=True), 'mutating method'),
            ([self_p], dict(returns='Int × Int × S_Stack', kind='method', mutates=True), 'parentheses'),
            ([self_p], dict(returns='S_Stack', kind='constructor'), 'does not take'),
            ([], dict(returns='Int', kind='constructor'), 'returns the new object'),
            ([], dict(returns='Int', kind='function', mutates=True), 'only for methods')):
        with pytest.raises(M.TypeError_, match=msg):
            M.parse_sig(bad, kw['returns'], structs=S, kind=kw['kind'], struct='S_Stack',
                        mutates=kw.get('mutates', False))
    assert M.entry_name('q', 'method') == 'q#post' and M.entry_name('q', 'constructor') == 'q'


def test_boundary_points_for_rich_types_and_receivers():
    recv = ['O', 'm.C', [['n', ['i', '1']]]]
    sig = M.parse_sig([{'name': 'self', 'type': 'S_C'}, {'name': 'd', 'type': 'Dict String (PySet Int)'},
                       {'name': 'b', 'type': 'Bytes'}], 'Unit', structs={'S_C'}, kind='method', struct='S_C')
    pts = M.boundary_points(sig, "def f(self, d, b): return 'k'", receivers=[recv])
    assert pts and all(p[0] == recv and p[1][0] == 'd' and p[2][0] == 'y' for p in pts)
    assert any(p[1][1] and p[1][1][0][1][0] == 'S' for p in pts)
    # no receiver states: nothing to test a method on
    assert M.boundary_points(sig, '', receivers=[]) == []


# ------------------------------------------------------------------ CPython side

def test_tracer_records_receivers_constructor_args_and_drops_sentinel_defaults(repo, suite, tmp_path):
    fns, _ = M._discover(repo, tests=[suite])
    att = [f for f in fns if f.reason is None]
    rec, stats = M.trace_tests(att, repo, M._test_dirs(repo, [suite]), tmp_path / 'trace')
    assert stats['runs'][0]['rc'] == 0, stats
    assert [pv.tag(3)] in rec[N + 'Stack.__init__']                    # constructor: args only
    push = rec[N + 'Stack.push']
    assert all(p[0][0] == 'O' and p[0][1] == 'pkg.stack.Stack' for p in push)
    first = next(p for p in push if p[1] == ['i', '1'])
    assert dict(first[0][2]) == {'items': ['l', []], 'limit': ['i', '3']}   # state BEFORE the call
    assert any(p[1] == ['s', 'a'] for p in rec[N + 'Counter.hit'])
    assert rec[N + 'Stack.size']                                           # property getter
    # `take(k)` passes the sentinel default: it is dropped, so the call replays with the default
    take = rec[N + 'Bag.take']
    assert any(len(p) == 2 for p in take) and any(len(p) == 3 for p in take)
    assert stats['defaults_dropped'] >= 1
    # push() called from inside push_twice() on the same object is nested: recorded as an
    # input, but its receiver state does not join the pool (it may be mid-update)
    nested = stats['nested'][N + 'Stack.push']
    assert nested and all(p in push for p in nested)
    assert all(p not in nested for p in push if p[1] == ['i', '1'])
    states = stats['states']
    assert any(dict(s[2])['items'] == ['l', [['i', '1'], ['i', '2']]] for s in states['pkg.stack.Stack'])
    bag = states['pkg.stack.Bag'][0]
    assert bag[3] == {'_store': 'collections.OrderedDict'}          # exact container type kept
    # tests next to the source are found too; the extra dir is what makes them visible here
    assert M._test_dirs(repo) == [] and M._test_dirs(repo, [suite]) == [suite.resolve()]


def test_runner_rebuilds_receiver_and_reports_post_state(repo, tmp_path):
    by = {f.qual: f for f in M._discover(repo)[0]}
    recv = ['O', 'pkg.stack.Stack', [['items', ['l', [['i', '1']]]], ['limit', ['i', '2']]]]
    rt = M.Runtime(by['Stack.push'], tmp_path / 'rt')
    out = rt.run([[recv, pv.tag(7)], [['O', 'pkg.stack.Stack', [['items', ['l', [['i', '1'], ['i', '2']]]],
                                                                 ['limit', ['i', '2']]]], pv.tag(7)]])
    assert out[0] == {'k': 'ok', 'v': ['i', '2'],
                      'post': ['O', 'pkg.stack.Stack', [['items', ['l', [['i', '1'], ['i', '7']]]],
                                                        ['limit', ['i', '2']]]]}
    assert out[1] == {'k': 'exn', 't': 'OverflowError'}
    size = M.Runtime(by['Stack.size'], tmp_path / 'rs').run([[recv]])[0]
    assert size['v'] == ['i', '1'] and size['post'] == recv
    init = M.Runtime(by['Stack.__init__'], tmp_path / 'ri').run([[pv.tag(4)]])[0]
    assert init == {'k': 'ok', 'v': ['O', 'pkg.stack.Stack', [['items', ['l', []]], ['limit', ['i', '4']]]]}
    wrong = M.Runtime(by['Stack.peek'], tmp_path / 'rw').run([[['O', 'pkg.stack.Counter', []]]])[0]
    assert wrong['k'] == 'bad-input'


# ------------------------------------------------------------------ formalize / check shapes

def test_formalize_and_check_accept_val_binders_and_post_entry():
    fn = {'name': N + 'Stack.push', 'kind': 'method', 'params': [{'name': 'self', 'sort': 'object'},
                                                               {'name': 'x', 'sort': 'int'}],
          'samples': [[['O', 'pkg.stack.Stack', [['items', ['l', []]], ['limit', ['i', '2']]]], ['i', '5']]]}
    cand = F.parse_candidate({'binders': [{'name': 's', 'type': 'Val'}, {'name': 'x', 'type': 'Int'}],
                              'pre': 'true', 'post': 'r matches .val _', 'observe': 'post'})
    assert cand['entry'] == 'post' and cand['binders'][0]['val'] == 's' and cand['binders'][1]['val'] == '.int x'
    assert F.shape_problems(fn, cand) == []
    bad = dict(cand, binders=[{'name': 's', 'type': 'Int', 'val': '.int s'}, cand['binders'][1]])
    assert any('must have type Val' in p for p in F.shape_problems(fn, bad))
    assert any('only for methods' in p for p in F.shape_problems(dict(fn, kind='function'), cand))
    st = dict(id='s1', function=fn['name'], property='p', english='', lean_prop='', binders=cand['binders'],
              pre='true', post='r matches .val _', elaborates=True, entry='post')
    tr = {'module': 'NLx', 'call_template': 'Autoform.NLModel.NLx.call {name} {args}', 'language': 'python'}
    plan = K.Plan(0, st, fn, tr, 8)
    assert '"pkg/stack.py:<module>.Stack.push#post" [s, .int x]' in plan.call
    assert plan.kinds == ['val', 'int'] and all(p[0] == fn['samples'][0][0] for p in plan.points)
    assert K.python_point(plan, plan.points[0])[0][0] == 'O'
    defs = plan.pass1()[0]
    assert 'def dom_' in defs and '(Val.bobj "obj:pkg.stack.Stack"' in defs and 'List (Val × Int)' in defs
    assert K.safe_term('default') and not K.safe_term('def x := 1')   # a binder may be named `default`
    assert K.header(tr).count('open Autoform.NLModel.NLx (vField vGet vHas vLen vKeys vElems)') == 1
    with pytest.raises(ValueError, match='sample'):
        K.Plan(0, st, dict(fn, samples=[]), tr, 8)


# ------------------------------------------------------------------ Lean-backed (hand-written models)

STACK_MODELS = {
    'py_Stack_init': ('[{"name": "limit", "type": "Int"}]', 'S_Stack', False,
                      'def py_Stack_init (limit : Int) : S_Stack := { f_items := [], f_limit := limit }'),
    'py_Stack_push': ('[{"name": "self", "type": "S_Stack"}, {"name": "x", "type": "Int"}]',
                      'Except String (Int × S_Stack)', True,
                      'def py_Stack_push (self : S_Stack) (x : Int) : Except String (Int × S_Stack) :=\n'
                      '  if (self.f_items.length : Int) ≥ self.f_limit then .error "OverflowError"\n'
                      '  else .ok ((self.f_items.length + 1 : Nat), { self with f_items := self.f_items ++ [x] })'),
    'py_Stack_peek': ('[{"name": "self", "type": "S_Stack"}]', 'Except String Int', False,
                      'def py_Stack_peek (self : S_Stack) : Except String Int :=\n'
                      '  match self.f_items.getLast? with\n  | some x => .ok x\n  | none => .error "IndexError"'),
    'py_Stack_size': ('[{"name": "self", "type": "S_Stack"}]', 'Int', False,
                      'def py_Stack_size (self : S_Stack) : Int := self.f_items.length'),
    'py_Counter_init': ('[]', 'S_Counter', False,
                        'def py_Counter_init : S_Counter := { f_count := 0, f_log := [], f_seen := [] }'),
    'py_Counter_hit': ('[{"name": "self", "type": "S_Counter"}, {"name": "key", "type": "String"}]',
                       '(Int × String) × S_Counter', True,
                       'def py_Counter_hit_upd (k : String) : List (String × Int) → List (String × Int)\n'
                       '  | [] => [(k, 1)]\n'
                       '  | (k2, v) :: r => if k2 == k then (k2, v + 1) :: r else (k2, v) :: py_Counter_hit_upd k r\n'
                       'def py_Counter_hit (self : S_Counter) (key : String) : (Int × String) × S_Counter :=\n'
                       '  ((self.f_count + 1, key), { self with f_count := self.f_count + 1, '
                       'f_seen := key :: self.f_seen, f_log := py_Counter_hit_upd key self.f_log })'),
}
# right result, but the receiver is not updated: only the post-state comparison can catch it
WRONG_PUSH = ('def py_Stack_push (self : S_Stack) (x : Int) : Except String (Int × S_Stack) :=\n'
              '  if (self.f_items.length : Int) ≥ self.f_limit then .error "OverflowError"\n'
              '  else .ok ((self.f_items.length + 1 : Nat), self)')


def stub(models):
    def ask(prompt, keys, **kw):
        name = re.search(r'NAME: (\w+)', prompt).group(1)
        params, returns, mutates, lean = models[name]
        return {'english': 'x', 'params': json.loads(params), 'returns': returns, 'mutates': mutates,
                'lean': lean}, 0.0
    return ask


def _lean_root():
    return Path(os.environ.get('AUTOFORM_LEAN_ROOT', ROOT))


@LEAN
def test_lean_hand_written_class_models_validate_against_cpython(repo, suite, tmp_path):
    fns = ['Stack.__init__', 'Stack.push', 'Stack.peek', 'Stack.size', 'Counter.__init__', 'Counter.hit']
    tr = M.model(repo, tmp_path / 'out', _lean_root(), module='NLTestObjects', functions=fns, tests=[suite],
                 ask=stub(STACK_MODELS), repairs=0)
    meta = json.loads((tmp_path / 'out' / 'model.meta.json').read_text())
    st = meta['structures']
    assert st['pkg.stack.Stack']['fields'] == [['items', 'f_items', 'List Int'], ['limit', 'f_limit', 'Int']]
    assert st['pkg.stack.Counter']['fields'] == [['count', 'f_count', 'Int'], ['log', 'f_log', 'Dict String Int'],
                                                ['seen', 'f_seen', 'PySet String']]
    for c in st.values():      # every observed state round-trips through the Lean decoder/encoder
        assert c['roundtrip_checked'] > 0 and c['roundtrip_ok'] == c['roundtrip_checked']
    assert meta['build']['ok'] and meta['build']['smoke_mismatches'] == []
    models = {m['function']: m for m in schema.load(tmp_path / 'out' / 'models.json')}
    for name in fns:
        m = models[N + name]
        assert m['status'] == 'VALIDATED', (name, m['notes'], m['disagreements'])
        assert m['tests_run'] >= (1 if name == 'Counter.__init__' else 2) and m['level'] == 'L0', (name, m)
    assert models[N + 'Stack.push']['tests_run'] >= 20       # traced + receivers x boundary values
    assert 'outcomes compared as (result, receiver after the call); mutates=True' in models[N + 'Stack.push']['notes']
    info = {f.name: f for f in tr.functions}
    assert info[N + 'Stack.push'].mutates and info[N + 'Stack.push'].kind == 'method'
    assert info[N + 'Stack.push'].lean_types == ['S_Stack', 'Int'] and info[N + 'Stack.push'].samples
    # the built module: kernel evaluation of a method's #post entry and a constructor
    ns = 'Autoform.NLModel.NLTestObjects'
    probe = tmp_path / 'probe.lean'
    obj = '(.bobj "obj:pkg.stack.Stack" (.dict [(.str "items", .list [.int 1]), (.str "limit", .int 2)]))'
    def val_is(call, canon):
        return (f'example : (match {ns}.call {call} with | .val v => {ns}.canonV v | _ => "") = '
                f'{pv.lean_str(canon)} := by decide +kernel\n')
    after = pv.canon(['O', 'pkg.stack.Stack', [['items', ['l', [['i', '1'], ['i', '5']]]], ['limit', ['i', '2']]]])
    fresh = pv.canon(['O', 'pkg.stack.Stack', [['items', ['l', []]], ['limit', ['i', '3']]]])
    probe.write_text(
        K.header(schema.load(tmp_path / 'out' / 'translation.json')) +
        val_is(f'"{N}Stack.push#post" [{obj}, .int 5]', f'T(i:2,{after},)') +
        val_is(f'"{N}Stack.push" [{obj}, .int 5]', 'i:2') +
        val_is(f'"{N}Stack.__init__" [.int 3]', fresh) +
        f'example : vLen (vField {obj} "items") = 1 := by decide +kernel\n')
    code, log, _ = M.run_lean(_lean_root(), probe)
    assert code == 0, log
    # the check stage: a post-state statement, bounded over recorded receivers and compared with CPython
    trj = schema.load(tmp_path / 'out' / 'translation.json')
    post = ('match r with | .val (.tuple [.int n, s2]) => vLen (vField s2 "items") == vLen (vField s "items") + 1 '
            '&& n == vLen (vField s2 "items") | .exn (.str "OverflowError") => true | _ => false')
    st = dict(id='push_grows', function=N + 'Stack.push', property='p', english='', lean_prop='',
              binders=[{'name': 's', 'type': 'Val', 'val': 's'}, {'name': 'x', 'type': 'Int', 'val': '.int x'}],
              pre='true', post=post, elaborates=True, entry='post')
    wrong = dict(st, id='push_keeps', post=post.replace('+ 1', '+ 0'))
    # the formalize stage restricts the receiver to real Stacks; the guard elaborates and checks
    from autoform.nl import formalize as F
    trd = json.loads((tmp_path / 'out' / 'translation.json').read_text())
    fn_push = next(f for f in trd['functions'] if f['name'] == N + 'Stack.push')
    g = F.with_receiver_guard(fn_push, dict(st), trd)
    assert g['pre'] == f'({ns}.dObj_S_Stack s).isSome'
    call = F.build_call(trd['call_template'], N + 'Stack.push#post', [b['val'] for b in g['binders']])
    scratch = tmp_path / 'guard.lean'
    scratch.write_text(F.scratch_text(trd, 'stmt_guard', g, F.assemble(g['binders'], g['pre'], g['post'], call)))
    ok, log = F.run_lean(str(_lean_root()), scratch)
    assert ok, log
    guarded = dict(st, id='push_grows_guarded', pre=g['pre'])
    res = {r.statement: r for r in K.check(trj, [st, wrong, guarded], tmp_path / 'chk', domain_size=24)}
    assert res['push_grows_guarded'].status == 'BOUNDED_HOLDS', res['push_grows_guarded']
    assert res['push_grows'].status == 'BOUNDED_HOLDS' and res['push_grows'].runtime_agrees is True, res['push_grows']
    assert res['push_keeps'].status == 'REFUTED_MODEL' and res['push_keeps'].runtime_agrees is False


@LEAN
def test_lean_wrong_post_state_is_caught(repo, suite, tmp_path):
    models = dict(STACK_MODELS)
    models['py_Stack_push'] = models['py_Stack_push'][:3] + (WRONG_PUSH,)
    M.model(repo, tmp_path / 'out', _lean_root(), module='NLTestObjectsWrong', functions=['Stack.push'],
            tests=[suite], ask=stub(models), repairs=0, second=False, do_build=False)
    m = schema.load(tmp_path / 'out' / 'models.json')[0]
    assert m['status'] == 'DISAGREES' and m['level'] == 'none'
    d = next(d for d in m['disagreements'] if d['runtime'].startswith('returns ('))
    # same Python result, different receiver after the call
    py = re.match(r'returns \((\d+), <pkg.stack.Stack (.*)>\)$', d['runtime'])
    lean = re.match(r'returns \((\d+), <pkg.stack.Stack (.*)>\)$', d['model'])
    assert py and lean and py.group(1) == lean.group(1) and py.group(2) != lean.group(2), d


@LEAN
def test_lean_dispatcher_round_trips_every_type(tmp_path):
    """One identity model per type: the dispatcher decodes and re-encodes exactly as CPython tags."""
    root = tmp_path / 'r'
    write(root, 'ids.py', 'def ident(x):\n    return x\n')
    types = ['Tuple Int', 'Dict String (Option Int)', 'PySet Int', 'FrozenSet String', 'Bytes',
             'Option (List Fl)', 'Int × String × Bool', 'Unit']
    for i, typ in enumerate(types):
        ask = (lambda p, k, typ=typ, **kw: ({'english': 'x', 'params': [{'name': 'x', 'type': typ}], 'returns': typ,
                                             'lean': f'def py_ident (x : {typ}) : {typ} := x'}, 0.0))
        M.model(root, tmp_path / f'o{i}', _lean_root(), module=f'NLTestIdent{i}', ask=ask, repairs=0,
                second=False, do_build=False, functions=['ident'])
        m = schema.load(tmp_path / f'o{i}' / 'models.json')[0]
        # every boundary value of the type went CPython -> tag -> Lean literal -> decode ->
        # encode -> canonical string and matched CPython's own canonical string
        assert m['status'] == 'VALIDATED' and m['tests_run'] >= 1, (typ, m['notes'], m['disagreements'])
