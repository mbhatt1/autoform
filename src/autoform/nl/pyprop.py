"""Lean `pre`/`post` expressions (formalize.py's vocabulary) → Python expressions.

The emit stage writes a `hypothesis` property test for a statement whose binders are all
Int/Nat/Bool/String. Such a test needs the statement's `pre` and `post` as Python, and
nothing in the run has them in that form: they are Lean `Bool` terms over the binders and
`r : EResult`. This module translates the subset of Lean the formalize prompt teaches
(`match` on `EResult`/`Val`/`Option`/list patterns, `matches`, `&&`/`||`/`!`, `decide`,
comparisons, Int arithmetic with the Euclidean `/`/`%` and `Int.fdiv`/`fmod`/`tdiv`/`tmod`,
strings, lists with `.length`/`.all`/`.any`/`.map`/`.filter`/`.head?`/`.getLast?`,
`if`/`let`/`fun`, `some`/`none`, and the `vField`/`vGet`/`vHas`/`vLen`/`vKeys`/`vElems`
helpers). Anything else raises `Unsupported` with the construct named, and the emit stage
records that reason instead of guessing.

The translation is NOT trusted on its own. The emit stage evaluates the Python `pre`/`post`
on every concrete domain point whose CPython outcome it has, next to the Lean evaluation of
the same `pre`/`post` on the same outcome, and refuses the hypothesis test of any statement
where the two disagree (or where no point satisfied `pre`, so `post` was never exercised).

Value representation on the Python side (`RUNTIME` below is written into every emitted
test file and used for the agreement check):
    EResult      ('ok', value) | ('exn', 'ExceptionName')
    Val          the Python value itself (bool is not int; None is `.unit`)
    Option α     None | (value,)
    List α       a Python list;  `.dict kvs` binds `list(d.items())`
"""
from __future__ import annotations

import keyword
import re

__all__ = ['Unsupported', 'translate', 'pyname', 'RUNTIME']


class Unsupported(ValueError):
    """The expression uses a construct this translator does not cover."""


# ---------------------------------------------------------------- the Python-side runtime

RUNTIME = r'''
import builtins as _builtins
import importlib as _importlib
import math as _math


def _resolve(name):
    """'collections.OrderedDict' / 'pkg.mod.Outer.Inner' -> the object."""
    parts = name.split('.')
    for i in range(len(parts) - 1, 0, -1):
        try:
            obj = _importlib.import_module('.'.join(parts[:i]))
        except ImportError:
            continue
        try:
            for p in parts[i:]:
                obj = getattr(obj, p)
            return obj
        except AttributeError:
            continue
    raise ValueError('cannot resolve %r' % name)


def _obj(cls_name, attrs, types=None):
    """An instance rebuilt from its recorded attributes, without running __init__."""
    cls = _resolve(cls_name)
    obj = cls.__new__(cls)
    for attr, val in attrs.items():
        if types and attr in types:
            val = _resolve(types[attr])(val)
        object.__setattr__(obj, attr, val)
    return obj


def _slot_names(cls):
    out = []
    for c in cls.__mro__:
        slots = c.__dict__.get('__slots__', ())
        if isinstance(slots, str):
            slots = (slots,)
        for s in slots:
            if s in ('__dict__', '__weakref__'):
                continue
            if s.startswith('__') and not s.endswith('__'):
                s = '_' + c.__name__.lstrip('_') + s
            out.append(s)
    return out


def _state(o):
    """The instance attributes of an object (its __dict__ plus every slot that is set)."""
    state = dict(getattr(o, '__dict__', None) or {})
    for s in _slot_names(type(o)):
        try:
            state[s] = object.__getattribute__(o, s)
        except AttributeError:
            pass
    return state


def _fget(cls, name):
    for c in cls.__mro__:
        if name in c.__dict__:
            return c.__dict__[name].fget
    raise AttributeError(name)


def _call(f, *args):
    """('ok', result) or ('exn', exception class name): the outcome the check stage compared."""
    try:
        return ('ok', f(*args))
    except BaseException as exc:  # noqa: BLE001 - the outcome is the point
        return ('exn', type(exc).__name__)


def _kind(v):
    if v is None:
        return 'none'
    if isinstance(v, bool):
        return 'bool'
    if isinstance(v, int):
        return 'int'
    if isinstance(v, float):
        return 'float'
    if isinstance(v, str):
        return 'str'
    if isinstance(v, bytes):
        return 'bytes'
    if isinstance(v, tuple):
        return 'tuple'
    if isinstance(v, list):
        return 'list'
    if isinstance(v, dict):
        return 'dict'
    if isinstance(v, frozenset):
        return 'frozenset'
    if isinstance(v, set):
        return 'set'
    if isinstance(v, type):
        return 'type'
    return 'object'


def _eq(a, b):
    """Exact equality of outcomes: same kind (bool is not int, 1 is not 1.0), same contents;
    nan equals nan; objects compare by class and recorded state."""
    ka, kb = _kind(a), _kind(b)
    if ka != kb:
        return False
    if ka == 'float':
        return (_math.isnan(a) and _math.isnan(b)) or a == b
    if ka in ('tuple', 'list'):
        return len(a) == len(b) and all(_eq(x, y) for x, y in zip(a, b))
    if ka == 'dict':
        return list(a.keys()) == list(b.keys()) and all(_eq(a[k], b[k]) for k in a)
    if ka in ('set', 'frozenset'):
        return a == b
    if ka == 'object':
        sa, sb = _state(a), _state(b)
        return type(a) is type(b) and set(sa) == set(sb) and all(_eq(sa[k], sb[k]) for k in sa)
    return a == b


def _beq(a, b):
    """Python-style value equality as `Val.beq`: bool only equals bool; 1 == 1.0."""
    if isinstance(a, bool) or isinstance(b, bool):
        return isinstance(a, bool) and isinstance(b, bool) and a == b
    ka, kb = _kind(a), _kind(b)
    if ka in ('tuple', 'list') or kb in ('tuple', 'list'):
        return ka == kb and len(a) == len(b) and all(_beq(x, y) for x, y in zip(a, b))
    if ka == 'object' or kb == 'object':
        return ka == kb and type(a) is type(b) and _beq(_state(a), _state(b))
    if ka == 'dict' and kb == 'dict':
        return a.keys() == b.keys() and all(_beq(a[k], b[k]) for k in a)
    return a == b


def _is_int(v):
    return isinstance(v, int) and not isinstance(v, bool)


def _ediv(a, b):
    """Lean `Int./` (Euclidean division; x / 0 = 0)."""
    if b == 0:
        return 0
    q = a // b if b > 0 else -(a // -b)
    return q


def _emod(a, b):
    return a - b * _ediv(a, b) if b != 0 else a


def _fdiv(a, b):
    return 0 if b == 0 else a // b


def _fmod(a, b):
    return a if b == 0 else a % b


def _tdiv(a, b):
    return 0 if b == 0 else int(a / b) if abs(a) < 2 ** 52 and abs(b) < 2 ** 52 else (abs(a) // abs(b)) * (1 if (a < 0) == (b < 0) else -1)


def _tmod(a, b):
    return a if b == 0 else a - b * _tdiv(a, b)


def _head(xs):
    return (xs[0],) if xs else None


def _last(xs):
    return (xs[-1],) if xs else None


def _nth(xs, i):
    return (xs[i],) if 0 <= i < len(xs) else None


def _vfield(o, attr):
    return _state(o).get(attr) if _kind(o) == 'object' else None


def _velems(v):
    k = _kind(v)
    if k in ('list', 'tuple'):
        return list(v)
    if k == 'dict':
        return list(v.keys())
    if k in ('set', 'frozenset'):
        return list(v)
    if k == 'str':
        return list(v)
    return []


def _vkeys(d):
    return _velems(d)


def _vhas(d, k):
    return any(_beq(k, e) for e in _velems(d))


def _vget(d, k):
    if _kind(d) != 'dict':
        return None
    for key, v in d.items():
        if _beq(k, key):
            return (v,)
    return None


def _vlen(v):
    return len(v) if _kind(v) == 'str' else len(_velems(v))


def _nomatch():
    raise AssertionError('no match arm applies (the Lean statement is exhaustive; translation bug)')
'''


# ---------------------------------------------------------------- tokens

TOKEN_RE = re.compile(r'''
  (?P<ws>\s+)
 |(?P<str>"(?:[^"\\]|\\.)*")
 |(?P<num>\d+)
 |(?P<dotid>\.[A-Za-z_](?:[\w']|[?!](?!=))*)
 |(?P<id>[A-Za-z_](?:[\w']|[?!](?!=))*(?:\.[A-Za-z_](?:[\w']|[?!](?!=))*)*)
 |(?P<op>::|=>|:=|&&|\|\||==|!=|<=|>=|\+\+|[()\[\],|:!<>+\-*/%;^]|≠|≤|≥|∧|∨|¬|→|·|λ|⟨|⟩)
''', re.X)

KEYWORDS = {'fun', 'match', 'with', 'if', 'then', 'else', 'let', 'in', 'matches', 'true', 'false',
            'some', 'none', 'decide', 'not'}
BINARY = {   # token -> (precedence, associativity)
    '||': (30, 'right'), '∨': (30, 'right'), '&&': (35, 'right'), '∧': (35, 'right'),
    '==': (50, 'none'), '!=': (50, 'none'), '≠': (50, 'none'), '<': (50, 'none'), '>': (50, 'none'),
    '<=': (50, 'none'), '≤': (50, 'none'), '>=': (50, 'none'), '≥': (50, 'none'), 'matches': (50, 'none'),
    '++': (65, 'right'), '::': (67, 'right'), '+': (65, 'left'), '-': (65, 'left'),
    '*': (70, 'left'), '/': (70, 'left'), '%': (70, 'left'), '^': (75, 'right'),
}
CMP = {'<': '<', '>': '>', '<=': '<=', '≤': '<=', '>=': '>=', '≥': '>='}
NAT_FUNS = {'Int.natAbs', 'Int.toNat', 'String.length', 'List.length'}
VAL_CTORS = {'int', 'str', 'bool', 'float', 'unit', 'list', 'tuple', 'dict', 'fn', 'bobj', 'ref', 'clos'}
ERESULT_CTORS = {'val', 'exn', 'hole', 'outOfFuel'}
ATOM_STARTS = ('id', 'num', 'str', 'dotid')


def pyname(name: str) -> str:
    """A Python identifier for a Lean binder name (keywords, primes and the runtime's `_`
    prefix renamed)."""
    n = name.replace("'", '_').replace('?', '_q').replace('!', '_x')
    if keyword.iskeyword(n) or n in ('None', 'True', 'False') or n.startswith('_'):
        n += '_'
    return n


def _tokenize(text: str) -> list:
    out, pos, adjacent = [], 0, False
    while pos < len(text):
        m = TOKEN_RE.match(text, pos)
        if not m:
            raise Unsupported(f'cannot tokenize {text[pos:pos + 20]!r}')
        pos = m.end()
        kind = m.lastgroup
        if kind == 'ws':
            adjacent = False
            continue
        val = m.group(kind)
        if kind == 'id' and val in KEYWORDS:
            kind = 'kw'
        out.append((kind, val, adjacent))
        adjacent = True
    out.append(('eof', '', False))
    return out


def _lean_string(lit: str) -> str:
    body, out, i = lit[1:-1], [], 0
    while i < len(body):
        ch = body[i]
        if ch != '\\':
            out.append(ch)
            i += 1
            continue
        i += 1
        esc = body[i] if i < len(body) else ''
        simple = {'n': '\n', 't': '\t', 'r': '\r', '\\': '\\', '"': '"', "'": "'", '0': '\0'}
        if esc in simple:
            out.append(simple[esc])
            i += 1
        elif esc == 'x' and i + 2 < len(body) + 1:
            out.append(chr(int(body[i + 1:i + 3], 16)))
            i += 3
        elif esc == 'u' and body[i + 1:i + 2] == '{':
            j = body.index('}', i)
            out.append(chr(int(body[i + 2:j], 16)))
            i = j + 1
        else:
            raise Unsupported(f'string escape \\{esc}')
    return ''.join(out)


# ---------------------------------------------------------------- expressions

class _E:
    """A translated expression: Python source plus a `nat` flag (Nat-typed in Lean, where
    subtraction truncates and is refused)."""
    __slots__ = ('py', 'nat')

    def __init__(self, py: str, nat: bool = False):
        self.py, self.nat = py, nat


class _Head:
    """An application head: a constructor, a known function, a bound name or a method."""
    def __init__(self, kind, name, obj=None):
        self.kind, self.name, self.obj = kind, name, obj


class Translator:
    def __init__(self, text: str, names, nat_names=()):
        self.toks = _tokenize(text)
        self.i = 0
        self.scopes = [set(names)]
        self.nat_names = set(nat_names)

    # -- token helpers
    def peek(self, k=0):
        return self.toks[min(self.i + k, len(self.toks) - 1)]

    def next(self):
        t = self.toks[self.i]
        self.i += 1
        return t

    def at(self, kind, val=None) -> bool:
        k, v, _ = self.peek()
        return k == kind and (val is None or v == val)

    def expect(self, kind, val=None):
        k, v, _ = self.peek()
        if k != kind or (val is not None and v != val):
            raise Unsupported(f'expected {val or kind}, found {v!r}')
        return self.next()

    def bound(self, name) -> bool:
        return any(name in s for s in self.scopes)

    # -- entry
    def translate(self) -> str:
        e = self.expr()
        if not self.at('eof'):
            raise Unsupported(f'unexpected {self.peek()[1]!r} after the expression')
        return e.py

    # -- expressions with precedence climbing
    def expr(self, min_prec: int = 0) -> _E:
        k, v, _ = self.peek()
        if k == 'kw' and v == 'fun' or k == 'op' and v == 'λ':
            return self.fun()
        if k == 'kw' and v == 'match':
            return self.match()
        if k == 'kw' and v == 'if':
            return self.ifte()
        if k == 'kw' and v == 'let':
            return self.let()
        left = self.unary()
        while True:
            k, v, _ = self.peek()
            op = v if (k == 'op' or (k == 'kw' and v == 'matches')) and v in BINARY else None
            if op is None:
                return left
            prec, assoc = BINARY[op]
            if prec < min_prec:
                return left
            self.next()
            if op == 'matches':
                pat = self.pattern()
                cond, _ = self.compile_pattern(pat, '_v')
                left = _E(f'(lambda _v: {cond})({left.py})')
                continue
            right = self.expr(prec + 1 if assoc in ('left', 'none') else prec)
            left = self.binary(op, left, right)

    def binary(self, op, a: _E, b: _E) -> _E:
        if op in ('&&', '∧'):
            return _E(f'({a.py} and {b.py})')
        if op in ('||', '∨'):
            return _E(f'({a.py} or {b.py})')
        if op == '==':
            return _E(f'_beq({a.py}, {b.py})')
        if op in ('!=', '≠'):
            return _E(f'(not _beq({a.py}, {b.py}))')
        if op in CMP:
            return _E(f'({a.py} {CMP[op]} {b.py})')
        if op == '++':
            return _E(f'({a.py} + {b.py})')
        if op == '::':
            return _E(f'([{a.py}] + {b.py})')
        if op == '+':
            return _E(f'({a.py} + {b.py})', a.nat and b.nat)
        if op == '-':
            if a.nat:
                raise Unsupported('subtraction on a Nat-typed term (truncates in Lean); ascribe it `(… : Int)`')
            return _E(f'({a.py} - {b.py})')
        if op == '*':
            return _E(f'({a.py} * {b.py})', a.nat and b.nat)
        if op == '/':
            if a.nat and b.nat:
                return _E(f'({a.py} // {b.py} if {b.py} != 0 else 0)', True)
            return _E(f'_ediv({a.py}, {b.py})')
        if op == '%':
            if a.nat and b.nat:
                return _E(f'({a.py} % {b.py} if {b.py} != 0 else {a.py})', True)
            return _E(f'_emod({a.py}, {b.py})')
        if op == '^':
            return _E(f'({a.py} ** {b.py})', a.nat)
        raise Unsupported(f'operator {op}')

    def unary(self) -> _E:
        k, v, _ = self.peek()
        if k == 'op' and v in ('!', '¬'):
            self.next()
            return _E(f'(not {self.expr(40).py})')
        if k == 'op' and v == '-':
            self.next()
            return _E(f'(-{self.expr(75).py})')
        return self.application()

    # -- application
    def application(self) -> _E:
        head = self.head()
        args = []
        while self.arg_follows():
            args.append(self.atom())
        return self.apply(head, args)

    def arg_follows(self) -> bool:
        k, v, adj = self.peek()
        if k in ('num', 'str', 'id'):
            return True
        if k == 'kw' and v in ('true', 'false', 'none'):
            return True
        if k == 'dotid':
            return not adj             # `.int 0` as an argument; an adjacent `.f` is a method
        if k == 'op' and v in ('(', '['):
            return True
        return False

    def head(self) -> _Head | _E:
        k, v, adj = self.peek()
        if k == 'kw' and v == 'decide':
            self.next()
            return _Head('fn', 'decide')
        if k == 'kw' and v == 'not':
            self.next()
            return _Head('fn', 'not')
        if k == 'kw' and v == 'some':
            self.next()
            return _Head('fn', 'some')
        if k == 'dotid':
            self.next()
            return _Head('ctor', v[1:])
        if k == 'id':
            first = v.split('.')[0]
            if v.startswith(('Val.', 'EResult.')) and v.count('.') == 1 and v.split('.')[1] in VAL_CTORS | ERESULT_CTORS:
                self.next()
                return _Head('ctor', v.split('.')[1])
            if self.bound(first):
                self.next()
                node = self.postfix(_E(pyname(first), first in self.nat_names), v.split('.')[1:])
                return node
            if v in FUNCTIONS:
                self.next()
                return _Head('fn', v)
            raise Unsupported(f'unknown identifier {v}')
        return self.postfix(self.atom(), [])

    def postfix(self, node, fields: list):
        """`node.f.g` (fields from a dotted identifier, then adjacent `.f` tokens): the last
        field may take arguments, so it is returned as a method head."""
        fields = list(fields)
        while self.at('dotid') and self.peek()[2]:
            fields.append(self.next()[1][1:])
        if isinstance(node, _Head):
            node = self.apply(node, [])
        for f in fields[:-1]:
            node = self.method(node, f, [])
        if fields:
            return _Head('method', fields[-1], node)
        return node

    def atom(self) -> _E:
        k, v, _ = self.peek()
        if k == 'num':
            self.next()
            return self.postfix(_E(v, True), [])
        if k == 'str':
            self.next()
            return self.postfix(_E(repr(_lean_string(v))), [])
        if k == 'kw' and v in ('true', 'false'):
            self.next()
            return _E('True' if v == 'true' else 'False')
        if k == 'kw' and v == 'none':
            self.next()
            return _E('None')
        if k == 'id':
            h = self.head()
            return self.apply(h, []) if isinstance(h, _Head) else h
        if k == 'dotid':
            self.next()
            return self.apply(_Head('ctor', v[1:]), [])
        if k == 'op' and v == '(':
            self.next()
            if self.at('op', ')'):
                self.next()
                return _E('()')
            if self.at('op', '·'):
                raise Unsupported('`·` section')
            first = self.expr()
            if self.at('op', ':'):           # type ascription
                self.next()
                depth = 0
                while not (depth == 0 and self.at('op', ')')):
                    kk, vv, _ = self.next()
                    if kk == 'eof':
                        raise Unsupported('unbalanced parentheses')
                    depth += (kk == 'op' and vv == '(') - (kk == 'op' and vv == ')')
                self.expect('op', ')')
                return self.postfix(_E(f'({first.py})', False), [])
            items = [first]
            while self.at('op', ','):
                self.next()
                items.append(self.expr())
            self.expect('op', ')')
            if len(items) == 1:
                return self.postfix(_E(f'({first.py})', first.nat), [])
            return self.postfix(_E('(' + ', '.join(x.py for x in items) + ',)'), [])
        if k == 'op' and v == '[':
            self.next()
            items = []
            while not self.at('op', ']'):
                items.append(self.expr())
                if self.at('op', ','):
                    self.next()
            self.expect('op', ']')
            return self.postfix(_E('[' + ', '.join(x.py for x in items) + ']'), [])
        raise Unsupported(f'unexpected {v!r}')

    def apply(self, head, args: list) -> _E:
        if isinstance(head, _E):
            if args:
                raise Unsupported(f'application of a value ({head.py[:30]}) to arguments')
            return head
        if head.kind == 'ctor':
            return self.ctor(head.name, args)
        if head.kind == 'method':
            return self.method(head.obj, head.name, args)
        return self.function(head.name, args)

    def ctor(self, name, args) -> _E:
        n = len(args)
        if name == 'unit' and n == 0:
            return _E('None')
        if name in ('int', 'str', 'bool', 'float') and n == 1:
            return args[0]
        if name == 'list' and n == 1:
            return _E(f'list({args[0].py})')
        if name == 'tuple' and n == 1:
            return _E(f'tuple({args[0].py})')
        if name == 'dict' and n == 1:
            return _E(f'dict({args[0].py})')
        if name == 'val' and n == 1:
            return _E(f"('ok', {args[0].py})")
        if name == 'exn' and n == 1:
            return _E(f"('exn', {args[0].py})")
        raise Unsupported(f'constructor .{name} with {n} argument(s)')

    def function(self, name, args) -> _E:
        n = len(args)
        spec = FUNCTIONS.get(name)
        if spec is None:
            raise Unsupported(f'function {name}')
        arity, fmt, nat = spec
        if n != arity:
            raise Unsupported(f'{name} applied to {n} argument(s), expects {arity}')
        return _E(fmt.format(*[a.py for a in args]), nat)

    def method(self, obj: _E, name, args) -> _E:
        n = len(args)
        spec = METHODS.get((name, n))
        if spec is None:
            raise Unsupported(f'method .{name} with {n} argument(s)')
        fmt, nat = spec
        return _E(fmt.format(obj.py, *[a.py for a in args]), nat)

    # -- binders
    def fun(self) -> _E:
        self.next()
        params = []
        while not self.at('op', '=>'):
            if self.at('op', '('):
                self.next()
                while not self.at('op', ':'):
                    params.append(self.expect('id')[1])
                self.next()
                while not self.at('op', ')'):
                    self.next()
                self.next()
            elif self.at('id'):
                params.append(self.next()[1])
            else:
                raise Unsupported(f'fun parameter {self.peek()[1]!r}')
        self.expect('op', '=>')
        self.scopes.append(set(params))
        body = self.expr()
        self.scopes.pop()
        return _E(f'(lambda {", ".join(pyname(p) for p in params)}: {body.py})')

    def let(self) -> _E:
        self.next()
        name = self.expect('id')[1]
        if self.at('op', '('):           # let f (x : T) := ... : not supported
            raise Unsupported('let with parameters')
        self.expect('op', ':=')
        value = self.expr()
        if self.at('op', ';'):
            self.next()
        self.scopes.append({name})
        body = self.expr()
        self.scopes.pop()
        return _E(f'(lambda {pyname(name)}: {body.py})({value.py})')

    def ifte(self) -> _E:
        self.next()
        cond = self.expr()
        self.expect('kw', 'then')
        a = self.expr()
        self.expect('kw', 'else')
        b = self.expr()
        return _E(f'({a.py} if {cond.py} else {b.py})', a.nat and b.nat)

    # -- match
    def match(self) -> _E:
        self.next()
        scrutinees = [self.expr()]
        while self.at('op', ','):
            self.next()
            scrutinees.append(self.expr())
        self.expect('kw', 'with')
        vars_ = [f'_m{i}' for i in range(len(scrutinees))]
        arms = []
        while self.at('op', '|'):
            self.next()
            pats = [self.pattern()]
            while self.at('op', ','):
                self.next()
                pats.append(self.pattern())
            if len(pats) != len(scrutinees):
                raise Unsupported('match arm arity differs from the scrutinees')
            self.expect('op', '=>')
            conds, binds = [], []
            for p, v in zip(pats, vars_):
                c, b = self.compile_pattern(p, v)
                conds.append(c)
                binds += b
            names = [b[0] for b in binds]
            self.scopes.append(set(names))
            body = self.expr()
            self.scopes.pop()
            if binds:
                body_py = f'(lambda {", ".join(pyname(n) for n in names)}: {body.py})({", ".join(b[1] for b in binds)})'
            else:
                body_py = body.py
            arms.append((' and '.join(conds) if conds else 'True', body_py))
        if not arms:
            raise Unsupported('match without arms')
        out = '_nomatch()'
        for cond, body in reversed(arms):
            out = f'({body} if ({cond}) else {out})'
        return _E(f'(lambda {", ".join(vars_)}: {out})({", ".join(s.py for s in scrutinees)})')

    # -- patterns: ('wild',) | ('var', name) | ('lit', py) | ('ctor', name, [pats]) | ('list', [pats])
    #              | ('cons', head, tail) | ('tuple', [pats]) | ('some', pat) | ('none',)
    def pattern(self):
        p = self.pattern_app()
        if self.at('op', '::'):
            self.next()
            return ('cons', p, self.pattern())
        return p

    def pattern_app(self):
        k, v, _ = self.peek()
        if k == 'dotid' or (k == 'id' and v.startswith(('Val.', 'EResult.'))):
            self.next()
            name = v.split('.')[-1]
            args = []
            while self.pattern_arg_follows():
                args.append(self.pattern_atom())
            return ('ctor', name, args)
        if k == 'kw' and v == 'some':
            self.next()
            return ('some', self.pattern_atom())
        return self.pattern_atom()

    def pattern_arg_follows(self) -> bool:
        k, v, adj = self.peek()
        return k in ('num', 'str', 'id') or (k == 'kw' and v in ('true', 'false', 'none')) \
            or (k == 'dotid' and not adj) or (k == 'op' and v in ('(', '['))

    def pattern_atom(self):
        k, v, _ = self.peek()
        if k == 'id' and v == '_':
            self.next()
            return ('wild',)
        if k == 'id':
            self.next()
            if '.' in v:
                raise Unsupported(f'pattern {v}')
            return ('var', v)
        if k == 'num':
            self.next()
            return ('lit', v)
        if k == 'str':
            self.next()
            return ('lit', repr(_lean_string(v)))
        if k == 'kw' and v in ('true', 'false'):
            self.next()
            return ('lit', 'True' if v == 'true' else 'False')
        if k == 'kw' and v == 'none':
            self.next()
            return ('none',)
        if k == 'dotid':
            self.next()
            return ('ctor', v[1:], [])
        if k == 'op' and v == '(':
            self.next()
            items = [self.pattern()]
            while self.at('op', ','):
                self.next()
                items.append(self.pattern())
            self.expect('op', ')')
            return items[0] if len(items) == 1 else ('tuple', items)
        if k == 'op' and v == '[':
            self.next()
            items = []
            while not self.at('op', ']'):
                items.append(self.pattern())
                if self.at('op', ','):
                    self.next()
            self.expect('op', ']')
            return ('list', items)
        raise Unsupported(f'pattern {v!r}')

    def compile_pattern(self, p, s: str):
        """(condition over the Python value `s`, [(lean name, access expression)])."""
        kind = p[0]
        if kind == 'wild':
            return 'True', []
        if kind == 'var':
            return 'True', [(p[1], s)]
        if kind == 'lit':
            return f'_beq({s}, {p[1]})', []
        if kind == 'none':
            return f'({s} is None)', []
        if kind == 'some':
            c, b = self.compile_pattern(p[1], f'{s}[0]')
            return f'({s} is not None and {c})', b
        if kind == 'tuple':
            conds, binds = [f'(isinstance({s}, tuple) and len({s}) == {len(p[1])})'], []
            for i, q in enumerate(p[1]):
                c, b = self.compile_pattern(q, f'{s}[{i}]')
                conds.append(c)
                binds += b
            return '(' + ' and '.join(conds) + ')', binds
        if kind == 'list':
            conds, binds = [f'(isinstance({s}, list) and len({s}) == {len(p[1])})'], []
            for i, q in enumerate(p[1]):
                c, b = self.compile_pattern(q, f'{s}[{i}]')
                conds.append(c)
                binds += b
            return '(' + ' and '.join(conds) + ')', binds
        if kind == 'cons':
            c1, b1 = self.compile_pattern(p[1], f'{s}[0]')
            c2, b2 = self.compile_pattern(p[2], f'{s}[1:]')
            return f'(isinstance({s}, list) and len({s}) >= 1 and {c1} and {c2})', b1 + b2
        if kind == 'ctor':
            return self.compile_ctor(p[1], p[2], s)
        raise Unsupported(f'pattern kind {kind}')

    def compile_ctor(self, name, args, s):
        n = len(args)
        if name == 'val' and n == 1:
            c, b = self.compile_pattern(args[0], f'{s}[1]')
            return f"({s}[0] == 'ok' and {c})", b
        if name == 'exn' and n == 1:
            c, b = self.compile_pattern(args[0], f'{s}[1]')
            return f"({s}[0] == 'exn' and {c})", b
        if name in ('hole', 'outOfFuel'):
            return 'False', []                   # a CPython outcome is never a hole
        if name == 'unit' and n == 0:
            return f'({s} is None)', []
        tests = {'int': f'_is_int({s})', 'bool': f'isinstance({s}, bool)', 'str': f'isinstance({s}, str)',
                 'float': f'isinstance({s}, float)', 'list': f'isinstance({s}, list)',
                 'tuple': f'isinstance({s}, tuple)', 'dict': f'isinstance({s}, dict)'}
        if name in tests and n == 1:
            inner = f'list({s}.items())' if name == 'dict' else f'list({s})' if name in ('list', 'tuple') else s
            c, b = self.compile_pattern(args[0], inner)
            return f'({tests[name]} and {c})', b
        if name == 'bobj' and n == 2 and args[0][0] == 'lit' and args[1][0] == 'wild':
            tag = args[0][1]
            if tag == "'set'":
                return f'isinstance({s}, set)', []
            if tag == "'frozenset'":
                return f'isinstance({s}, frozenset)', []
            if tag == "'bytes'":
                return f'isinstance({s}, bytes)', []
            if tag.startswith("'obj:"):
                return f"(_kind({s}) == 'object')", []
        raise Unsupported(f'pattern .{name} with {n} argument(s)')


# name -> (arity, format, result is Nat)
FUNCTIONS = {
    'decide': (1, '{0}', False), 'not': (1, '(not {0})', False), 'some': (1, '({0},)', False),
    'min': (2, 'min({0}, {1})', False), 'max': (2, 'max({0}, {1})', False),
    'Int.fdiv': (2, '_fdiv({0}, {1})', False), 'Int.fmod': (2, '_fmod({0}, {1})', False),
    'Int.tdiv': (2, '_tdiv({0}, {1})', False), 'Int.tmod': (2, '_tmod({0}, {1})', False),
    'Int.ediv': (2, '_ediv({0}, {1})', False), 'Int.emod': (2, '_emod({0}, {1})', False),
    'Int.natAbs': (1, 'abs({0})', True), 'Int.toNat': (1, 'max({0}, 0)', True), 'Int.ofNat': (1, '{0}', False),
    'String.length': (1, 'len({0})', True), 'List.length': (1, 'len({0})', True),
    'Val.beq': (2, '_beq({0}, {1})', False),
    'vField': (2, '_vfield({0}, {1})', False), 'vGet': (2, '_vget({0}, {1})', False),
    'vHas': (2, '_vhas({0}, {1})', False), 'vLen': (1, '_vlen({0})', False),
    'vKeys': (1, '_vkeys({0})', False), 'vElems': (1, '_velems({0})', False),
}
# (name, arity) -> (format with {0} the object, result is Nat)
METHODS = {
    ('length', 0): ('len({0})', True), ('isEmpty', 0): ('(len({0}) == 0)', False),
    ('all', 1): ('all(({1})(_e) for _e in {0})', False), ('any', 1): ('any(({1})(_e) for _e in {0})', False),
    ('map', 1): ('[({1})(_e) for _e in {0}]', False), ('filter', 1): ('[_e for _e in {0} if ({1})(_e)]', False),
    ('contains', 1): ('any(_beq(_e, {1}) for _e in {0})', False), ('elem', 1): ('any(_beq(_e, {1}) for _e in {0})', False),
    ('head?', 0): ('_head({0})', False), ('getLast?', 0): ('_last({0})', False), ('get?', 1): ('_nth({0}, {1})', False),
    ('reverse', 0): ('list(reversed({0}))', False), ('toList', 0): ('list({0})', False),
    ('sum', 0): ('sum({0})', False), ('isSome', 0): ('({0} is not None)', False),
    ('isNone', 0): ('({0} is None)', False), ('getD', 1): ('({0}[0] if {0} is not None else {1})', False),
    ('toNat', 0): ('max({0}, 0)', True), 'natAbs': None, ('natAbs', 0): ('abs({0})', True),
    ('append', 1): ('({0} + {1})', False), ('push', 1): ('({0} + [{1}])', False),
    ('startsWith', 1): ('{0}.startswith({1})', False), ('endsWith', 1): ('{0}.endswith({1})', False),
    ('toUpper', 0): ('{0}.upper()', False), ('toLower', 0): ('{0}.lower()', False),
    ('trim', 0): ('{0}.strip()', False), ('fst', 0): ('{0}[0]', False), ('snd', 0): ('{0}[1]', False),
}
METHODS.pop('natAbs')


def translate(text: str, names, nat_names=()) -> str:
    """Python source for the Lean Bool expression `text` over the binder `names` (and `r`).

    Int/Bool/String binders are plain Python values under `pyname`; `r` is ('ok', v) or
    ('exn', name). Raises `Unsupported`."""
    return Translator(text, list(names) + ['r'], nat_names).translate()
