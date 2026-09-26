"""Python values ↔ tagged JSON ↔ Lean `Val` literals ↔ canonical outcome strings.

Used by the model stage (model.py) on both sides of a differential test. This file has no
imports from the package: the tracer and the CPython runner load it by path inside a
subprocess whose `sys.path` belongs to the repository under test.

Tagged JSON (transport between processes; exact, no approximation):
    None → ["n"]   bool → ["b", true]   int → ["i", "123"]   float → ["f", "<ieee bits>"]
    str → ["s", "..."]   tuple → ["t", [...]]   list → ["l", [...]]
    dict → ["d", [[k, v], ...]]   builtin type object → ["F", "int"]
Tuple/list/str subclasses are encoded as their base (Python equality agrees with the base);
anything else (objects, sets, bytes, lone surrogates, huge values) is `Unencodable`.

Canonical outcome strings are what the Lean side prints for `EResult` (see RENDER in
model.py) and what `canon_outcome` computes for a CPython outcome; two outcomes agree iff
the strings are equal:
    ok i:-4 | ok b:true | ok s:[97, 98] | ok none | ok f:<bits>|f:nan | ok T(i:1,i:2,)
    ok L(...) | ok D(k=v;...) | ok F:int | exn ZeroDivisionError | hole nl:arg-type
"""
from __future__ import annotations

import builtins
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


def tag(v, depth: int = 0):
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
    if isinstance(v, (tuple, list)):
        if len(v) > MAX_ELEMS:
            raise Unencodable('sequence too long')
        return ['t' if isinstance(v, tuple) else 'l', [tag(x, depth + 1) for x in v]]
    if isinstance(v, dict):
        if len(v) > MAX_ELEMS:
            raise Unencodable('dict too long')
        return ['d', [[tag(k, depth + 1), tag(x, depth + 1)] for k, x in v.items()]]
    if isinstance(v, type) and getattr(builtins, v.__name__, None) is v:
        return ['F', v.__name__]
    raise Unencodable(type(v).__name__)


def untag(t):
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
    if k == 't':
        return tuple(untag(x) for x in t[1])
    if k == 'l':
        return [untag(x) for x in t[1]]
    if k == 'd':
        return {untag(a): untag(b) for a, b in t[1]}
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
    raise ValueError(f'bad tag {t!r}')


def canon_outcome(res: dict):
    """A runner result → canonical string, or None when it has no faithful encoding."""
    if res.get('k') == 'ok':
        return 'ok ' + canon(res['v'])
    if res.get('k') == 'exn':
        return 'exn ' + res['t']
    return None


def lean_outcome(res: dict):
    """A runner result → Lean `EResult` literal, or None."""
    if res.get('k') == 'ok':
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


def show_args(point) -> str:
    try:
        return '(' + ', '.join(repr(untag(t)) for t in point) + ')'
    except (ValueError, TypeError):
        return str(point)
