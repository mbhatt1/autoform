"""Python values ↔ tagged JSON ↔ Lean `Val` literals ↔ canonical outcome strings.

Used by the model stage (model.py) on both sides of a differential test, and by the check
stage's runtime comparison. This file has no imports from the package: the tracer and the
CPython runner load it by path inside a subprocess whose `sys.path` belongs to the
repository under test.

Tagged JSON (transport between processes; exact, no approximation):
    None → ["n"]   bool → ["b", true]   int → ["i", "123"]   float → ["f", "<ieee bits>"]
    str → ["s", "..."]   tuple → ["t", [...]]   list → ["l", [...]]
    dict → ["d", [[k, v], ...]]  (insertion order)   builtin type object → ["F", "int"]
    bytes → ["y", "<hex>"]
    set / frozenset → ["S", [...], "set"|"frozenset"]  (elements in canonical order)
    object of a modelled class → ["O", "<module>.<Class>", [[attr, v], ...], {attr: type}]
        attributes sorted by name; the optional map names the exact container type of an
        attribute whose value is a dict/list/set subclass (e.g. collections.OrderedDict) so
        the CPython side can restore it. Objects are encoded only for the classes `tag` is
        given (`classes`); a class's instances are rebuilt by `untag` without running
        `__init__` (`__new__`, then every recorded attribute is set).
Tuple/list/str/dict subclasses are encoded as their base (Python equality agrees with the
base); anything else (other objects, bytearray, lone surrogates, huge values) is
`Unencodable`.

Lean `Val` (`lean_lit`): the scalars, `.list`, `.tuple`, `.dict` (association list in
insertion order) as they are; bytes are `.bobj "bytes" (.list [.int b, ...])`; sets are
`.bobj "set" (.list elems)` / `.bobj "frozenset" (.list elems)` with the elements sorted by
their canonical strings and duplicates removed, so equal sets have equal encodings (the
generated dispatcher normalizes a model's set the same way); objects are
`.bobj "obj:<module>.<Class>" (.dict [(.str attr, v), ...])`.

Canonical outcome strings are what the Lean side prints for `EResult` (see RENDER in
model.py) and what `canon_outcome` computes for a CPython outcome; two outcomes agree iff
the strings are equal:
    ok i:-4 | ok b:true | ok s:[97, 98] | ok none | ok f:<bits>|f:nan | ok T(i:1,i:2,)
    ok L(...) | ok D(k=v;...) | ok F:int | ok X:bytes(L(i:1,)) | ok X:set(L(...))
    ok X:obj:pkg.C(D(s:[..]=v;...)) | exn ZeroDivisionError | hole nl:arg-type
A method's outcome also carries the receiver after the call: the runner returns
{"k": "ok", "v": result, "post": receiver} and the canonical string is
`ok T(<result>,<receiver>,)`, which is what the dispatcher's `<name>#post` entry returns.
"""
from __future__ import annotations

import builtins
import importlib
import math
import struct

MAX_DEPTH = 8
MAX_ELEMS = 256
MAX_STR = 4000
MAX_INT_BITS = 4096


class Unencodable(Exception):
    pass


def float_bits(x: float) -> int:
    return struct.unpack('<Q', struct.pack('<d', x))[0]


def bits_float(n: int) -> float:
    return struct.unpack('<d', struct.pack('<Q', n))[0]


def class_name(cls) -> str:
    return f'{cls.__module__}.{cls.__qualname__}'


def _slot_names(cls) -> list:
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


def obj_state(v) -> dict:
    """The instance attributes of an object: its __dict__ plus every slot that is set."""
    state = dict(getattr(v, '__dict__', None) or {})
    for s in _slot_names(type(v)):
        try:
            state[s] = object.__getattribute__(v, s)
        except AttributeError:
            pass
    return state


def tag(v, depth: int = 0, classes=None):
    """`classes`: class_name()s of modelled classes whose instances are encoded as objects."""
    if depth > MAX_DEPTH:
        raise Unencodable('nested too deeply')
    if v is None:
        return ['n']
    if isinstance(v, bool):
        return ['b', bool(v)]
    if isinstance(v, int):
        if int(v).bit_length() > MAX_INT_BITS:
            raise Unencodable('int too large')
        return ['i', str(int(v))]
    if isinstance(v, float):
        return ['f', str(float_bits(float(v)))]
    if isinstance(v, str):
        s = str(v)
        if len(s) > MAX_STR:
            raise Unencodable('str too long')
        try:
            s.encode('utf-8')
        except UnicodeEncodeError:
            raise Unencodable('str with lone surrogates')
        return ['s', s]
    if type(v) is bytes:
        if len(v) > MAX_STR:
            raise Unencodable('bytes too long')
        return ['y', v.hex()]
    if classes and class_name(type(v)) in classes:
        state = obj_state(v)
        if len(state) > MAX_ELEMS:
            raise Unencodable('object with too many attributes')
        fields, types = [], {}
        for k in sorted(state):
            x = state[k]
            fields.append([k, tag(x, depth + 1, classes)])
            if isinstance(x, (dict, list, set)) and type(x) not in (dict, list, set):
                types[k] = class_name(type(x))
        return ['O', class_name(type(v)), fields] + ([types] if types else [])
    if isinstance(v, (tuple, list)):
        if len(v) > MAX_ELEMS:
            raise Unencodable('sequence too long')
        return ['t' if isinstance(v, tuple) else 'l', [tag(x, depth + 1, classes) for x in v]]
    if isinstance(v, dict):
        if len(v) > MAX_ELEMS:
            raise Unencodable('dict too long')
        return ['d', [[tag(k, depth + 1, classes), tag(x, depth + 1, classes)] for k, x in v.items()]]
    if type(v) in (set, frozenset):
        if len(v) > MAX_ELEMS:
            raise Unencodable('set too long')
        elems = sorted((tag(x, depth + 1, classes) for x in v), key=canon)
        keys = [canon(e) for e in elems]
        if len(set(keys)) != len(keys):
            raise Unencodable('set with equal elements of different types')
        return ['S', elems, type(v).__name__]
    if isinstance(v, type) and getattr(builtins, v.__name__, None) is v:
        return ['F', v.__name__]
    raise Unencodable(type(v).__name__)


def resolve(name: str):
    """'collections.OrderedDict' / 'pkg.mod.Outer.Inner' → the object (longest importable prefix)."""
    parts = name.split('.')
    for i in range(len(parts) - 1, 0, -1):
        try:
            obj = importlib.import_module('.'.join(parts[:i]))
        except ImportError:
            continue
        try:
            for p in parts[i:]:
                obj = getattr(obj, p)
            return obj
        except AttributeError:
            continue
    raise ValueError(f'cannot resolve {name!r}')


def untag(t, resolver=None):
    k = t[0]
    if k == 'n':
        return None
    if k == 'b':
        return bool(t[1])
    if k == 'i':
        return int(t[1])
    if k == 'f':
        return bits_float(int(t[1]))
    if k == 's':
        return t[1]
    if k == 'y':
        return bytes.fromhex(t[1])
    if k == 't':
        return tuple(untag(x, resolver) for x in t[1])
    if k == 'l':
        return [untag(x, resolver) for x in t[1]]
    if k == 'd':
        return {untag(a, resolver): untag(b, resolver) for a, b in t[1]}
    if k == 'S':
        elems = [untag(x, resolver) for x in t[1]]
        return frozenset(elems) if t[2] == 'frozenset' else set(elems)
    if k == 'O':
        res = resolver or resolve
        cls = res(t[1])
        obj = cls.__new__(cls)
        types = t[3] if len(t) > 3 else {}
        for attr, x in t[2]:
            val = untag(x, resolver)
            if attr in types:
                val = res(types[attr])(val)
            object.__setattr__(obj, attr, val)
        return obj
    if k == 'F':
        v = getattr(builtins, t[1], None)
        if isinstance(v, type):
            return v
    raise ValueError(f'bad tag {t!r}')


def lean_str(s: str) -> str:
    out = ['"']
    for ch in s:
        o = ord(ch)
        if ch in '"\\':
            out.append('\\' + ch)
        elif ch == '\n':
            out.append('\\n')
        elif ch == '\t':
            out.append('\\t')
        elif ch == '\r':
            out.append('\\r')
        elif o < 0x20 or o == 0x7f:
            out.append('\\x%02x' % o)
        else:
            out.append(ch)
    out.append('"')
    return ''.join(out)


def set_elems(t) -> list:
    """Elements of a set tag in canonical order, duplicates (equal canonical strings) removed."""
    out, seen = [], set()
    for x in sorted(t[1], key=canon):
        c = canon(x)
        if c not in seen:
            seen.add(c)
            out.append(x)
    return out


def lean_lit(t) -> str:
    """A Lean term of type `Val` (Autoform.Core open)."""
    k = t[0]
    if k == 'n':
        return 'Val.unit'
    if k == 'b':
        return f'(Val.bool {"true" if t[1] else "false"})'
    if k == 'i':
        return f'(Val.int ({t[1]}))'
    if k == 'f':
        return f'(Val.float (Fl.ofBits {t[1]}))'
    if k == 's':
        return f'(Val.str {lean_str(t[1])})'
    if k in ('t', 'l'):
        ctor = 'tuple' if k == 't' else 'list'
        return f'(Val.{ctor} [' + ', '.join(lean_lit(x) for x in t[1]) + '])'
    if k == 'd':
        return '(Val.dict [' + ', '.join(f'({lean_lit(a)}, {lean_lit(b)})' for a, b in t[1]) + '])'
    if k == 'F':
        return f'(Val.fn {lean_str(t[1])})'
    if k == 'y':
        return '(Val.bobj "bytes" (Val.list [' + ', '.join(f'(Val.int {b})' for b in bytes.fromhex(t[1])) + ']))'
    if k == 'S':
        return f'(Val.bobj {lean_str(t[2])} (Val.list [' + ', '.join(lean_lit(x) for x in set_elems(t)) + ']))'
    if k == 'O':
        return (f'(Val.bobj {lean_str("obj:" + t[1])} (Val.dict ['
                + ', '.join(f'(Val.str {lean_str(a)}, {lean_lit(x)})' for a, x in t[2]) + ']))')
    raise ValueError(f'bad tag {t!r}')


def canon(t) -> str:
    k = t[0]
    if k == 'n':
        return 'none'
    if k == 'b':
        return 'b:true' if t[1] else 'b:false'
    if k == 'i':
        return 'i:' + str(int(t[1]))
    if k == 'f':
        return 'f:nan' if math.isnan(bits_float(int(t[1]))) else 'f:' + str(int(t[1]))
    if k == 's':
        return 's:' + str([ord(c) for c in t[1]])
    if k in ('t', 'l'):
        return ('T(' if k == 't' else 'L(') + ''.join(canon(x) + ',' for x in t[1]) + ')'
    if k == 'd':
        return 'D(' + ''.join(canon(a) + '=' + canon(b) + ';' for a, b in t[1]) + ')'
    if k == 'F':
        return 'F:' + t[1]
    if k == 'y':
        return 'X:bytes(L(' + ''.join(f'i:{b},' for b in bytes.fromhex(t[1])) + '))'
    if k == 'S':
        return f'X:{t[2]}(L(' + ''.join(canon(x) + ',' for x in set_elems(t)) + '))'
    if k == 'O':
        return (f'X:obj:{t[1]}(D(' + ''.join(canon(['s', a]) + '=' + canon(x) + ';' for a, x in t[2])
                + '))')
    raise ValueError(f'bad tag {t!r}')


def canon_outcome(res: dict):
    """A runner result → canonical string, or None when it has no faithful encoding.
    A result with a post-state (`post`, methods) is `ok T(<result>,<receiver after>,)`."""
    if res.get('k') == 'ok':
        if 'post' in res:
            return 'ok T(' + canon(res['v']) + ',' + canon(res['post']) + ',)'
        return 'ok ' + canon(res['v'])
    if res.get('k') == 'exn':
        return 'exn ' + res['t']
    return None


def lean_outcome(res: dict):
    """A runner result → Lean `EResult` literal, or None."""
    if res.get('k') == 'ok':
        if 'post' in res:
            return f'(EResult.val (Val.tuple [{lean_lit(res["v"])}, {lean_lit(res["post"])}]))'
        return f'(EResult.val {lean_lit(res["v"])})'
    if res.get('k') == 'exn':
        return f'(EResult.exn (Val.str {lean_str(res["t"])}))'
    return None


# --- display: canonical strings back to Python-looking text ---------------------------

def _parse(s: str, i: int):
    """Parse one canonical value at s[i:]; return (python repr text, next index)."""
    if s.startswith('none', i):
        return 'None', i + 4
    if s.startswith('b:true', i):
        return 'True', i + 6
    if s.startswith('b:false', i):
        return 'False', i + 7
    if s.startswith('s:[', i):
        j = s.index(']', i)
        body = s[i + 3:j]
        text = ''.join(chr(int(x)) for x in body.split(',') if x.strip())
        return repr(text), j + 1
    if s.startswith('X:', i):
        j = s.index('(', i)
        name = s[i + 2:j]
        if name == 'bytes':
            k = s.index(')', j + 1)
            data = bytes(int(x[2:]) for x in s[j + 3:k].split(',') if x.strip())
            assert s[k + 1] == ')'
            return repr(data), k + 2
        inner, k = _parse(s, j + 1)
        assert s[k] == ')'
        if name in ('set', 'frozenset'):
            body = inner[1:-1]
            text = ('{' + body + '}' if body else 'set()') if name == 'set' else 'frozenset({' + body + '})'
        elif name.startswith('obj:'):
            text = f'<{name[4:]} {inner}>'
        else:
            text = f'{name}({inner})'
        return text, k + 1
    if s[i:i + 2] in ('T(', 'L(', 'D('):
        kind, i = s[i], i + 2
        items = []
        while s[i] != ')':
            a, i = _parse(s, i)
            if kind == 'D':
                assert s[i] == '='
                b, i = _parse(s, i + 1)
                a = f'{a}: {b}'
            assert s[i] in ',;', s[i:]
            items.append(a)
            i += 1
        body = ', '.join(items)
        if kind == 'T':
            return '(' + body + (',)' if len(items) == 1 else ')'), i + 1
        return ('[' + body + ']' if kind == 'L' else '{' + body + '}'), i + 1
    j = i
    while j < len(s) and s[j] not in ',;=)':
        j += 1
    tok = s[i:j]
    if tok.startswith('i:'):
        return tok[2:], j
    if tok == 'f:nan':
        return 'nan', j
    if tok.startswith('f:'):
        return repr(bits_float(int(tok[2:]))), j
    if tok.startswith('F:'):
        return f"<class '{tok[2:]}'>", j
    return tok, j


def display(outcome: str | None) -> str:
    """'ok i:3' → 'returns 3'; 'exn ValueError' → 'raises ValueError'."""
    if outcome is None:
        return 'no comparable outcome'
    if outcome.startswith('ok '):
        try:
            text, end = _parse(outcome, 3)
            if end == len(outcome):
                return 'returns ' + text
        except (AssertionError, IndexError, ValueError):
            pass
        return 'returns ' + outcome[3:]
    if outcome.startswith('exn '):
        return 'raises ' + outcome[4:]
    if outcome.startswith('hole nl:arg-type'):
        return 'the arguments do not decode into the Lean parameter types (nl:arg-type)'
    return outcome


def show(t) -> str:
    """Python-looking text of one tagged value (objects shown by their attributes)."""
    k = t[0]
    if k == 'O':
        return f'<{t[1]} ' + ', '.join(f'{a}={show(x)}' for a, x in t[2]) + '>'
    if k in ('t', 'l'):
        items = [show(x) for x in t[1]]
        if k == 't':
            return '(' + ', '.join(items) + (',)' if len(items) == 1 else ')')
        return '[' + ', '.join(items) + ']'
    if k == 'd':
        return '{' + ', '.join(f'{show(a)}: {show(b)}' for a, b in t[1]) + '}'
    if k == 'S':
        body = ', '.join(show(x) for x in set_elems(t))
        return ('{' + body + '}' if body else 'set()') if t[2] == 'set' else 'frozenset({' + body + '})'
    return repr(untag(t))


def show_args(point) -> str:
    try:
        return '(' + ', '.join(show(t) for t in point) + ')'
    except (ValueError, TypeError, KeyError, IndexError):
        return str(point)
