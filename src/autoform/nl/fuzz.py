"""Coverage-guided differential fuzzing of the model stage's Lean models.

model.py validates an AI-written Lean model on the argument tuples its repository's tests
produce plus a small grid of typed boundary values. A model can agree on all of those and
still be wrong: Lean `/` instead of Python `//` on a negative divisor the grid never
reaches, round-half-up instead of Python's round-half-even, `.split(' ')` instead of
`.split()` on a tab. This module searches for such inputs:

  1. Generation (seeded, reproducible). Property-based inputs from the Lean signature the
     model declared (Int, Bool, String, Unit, Fl, Option/List/tuples, Val), narrowed by the
     Python annotations and by the *shapes* of the traced test inputs where the signature
     says `Val`, plus one-field mutations of observed inputs. Integers: small, boundary,
     large, negative, powers of two (±1), decimal halfway points, literals of the source.
     Strings: empty, unicode, whitespace of every kind, digits, repetitions, separators.
     Containers of those with 0–5 elements. Only inputs of the declared Lean types are
     used (the model's domain), so decoding never fails.
  2. Coverage guidance. The real function runs in CPython under `sys.settrace` (the repo's
     venv has no `coverage` package; none is added) inside model.py's own RUNNER script,
     recording line arcs in every file of the repository under test. Inputs reaching new
     arcs join the corpus and are mutated further; the Lean batch takes novel-coverage
     inputs first, then inputs with a not-yet-seen outcome kind, then the rest. Line and
     (bytecode-approximate) branch coverage of the function are reported for the traced
     inputs alone and with the fuzz inputs.
  3. Differential run. The selected inputs (default 300; ~3x as many are run in CPython
     for coverage) go through model.py's `evaluate` — one batched Lean `#eval` — and are
     compared with the CPython outcomes by model.py's canonical encodings. Points whose
     CPython outcome has no faithful encoding (timeout, unencodable value) are counted and
     never compared; a Lean `hole` (argument did not decode) is counted as off-domain.
  4. Shrinking. Disagreeing inputs (up to `max_shrink`, of distinct disagreement kinds) are
     shrunk greedily in lock-step batches — ints toward 0 (halving, subtracting powers of
     two and 1/2/5·10^k), strings and lists shorter and plainer, dict entries and defaulted
     arguments dropped — each round one CPython batch and one Lean batch, keeping the
     smallest candidate that still disagrees. The result is 1-minimal for those moves.
  5. Hand-off. `extend` — the one call site in model.py, right after a candidate has
     passed the traced + boundary comparison — splices the minimal counterexamples (and the
     novel-coverage corpus, which agreed) into that round's points, runtime outcomes and
     Evaluation. model.py's existing repair loop then shows the counterexamples to the
     model exactly as it shows any disagreement, the smoke re-run and translation B cover
     the added points, and an unrepaired model ends DISAGREES. Minimal counterexamples are
     carried over and re-checked first in later rounds of the same function.

Records go to `<out>/fuzz.json` (next to models.json; schema.py is unchanged): per
function, per round — seed, cases generated/run, unencodable, off-domain, coverage,
disagreements found, the shrunk counterexamples with their sizes, and a `warning`
when even the fuzzed inputs reach under half of the function's lines (a model whose
declared domain makes it agree vacuously, e.g. every input raising on line 1).

Configuration: `CONFIG` (env AUTOFORM_NL_FUZZ_CASES / _SEED / _TIMEOUT; model.py's CLI
`--fuzz-cases N --fuzz-seed S --fuzz-timeout T`). `--fuzz-cases 0` disables fuzzing.
"""
from __future__ import annotations

import json
import math
import os
import random
import re
import threading
import time
import weakref
import zlib
from dataclasses import asdict, dataclass, field
from pathlib import Path

from . import pyvalues as pv


def _model():
    from . import model   # lazy: model.py imports this module
    return model


# ---------------------------------------------------------------- configuration

@dataclass
class Config:
    cases: int = 300               # inputs compared with the Lean model per round (0: off)
    seed: int = 0
    per_call: float = 2.0          # seconds per real CPython call
    cpython_factor: int = 3        # inputs run in CPython (for coverage) per Lean case
    batch: int = 150               # CPython inputs per coverage-runner subprocess
    max_shrink: int = 3            # disagreements shrunk per round (distinct kinds first)
    shrink_rounds: int = 16        # Lean batches per shrink
    shrink_candidates: int = 160   # candidates per shrink round (all shrinks together)
    keep_corpus: int = 40          # novel-coverage points kept as evidence in the model's points

    @classmethod
    def from_env(cls) -> 'Config':
        c = cls()
        for key, attr, conv in (('CASES', 'cases', int), ('SEED', 'seed', int), ('TIMEOUT', 'per_call', float)):
            v = os.environ.get(f'AUTOFORM_NL_FUZZ_{key}')
            if v not in (None, ''):
                setattr(c, attr, conv(v))
        return c


CONFIG = Config.from_env()
LOW_COVERAGE = 50.0     # % of the function's lines: below this a round records a warning


def add_arguments(ap):
    ap.add_argument('--fuzz-cases', type=int, default=None,
                    help=f'fuzz inputs compared per function and round (default {CONFIG.cases}; 0 disables)')
    ap.add_argument('--fuzz-seed', type=int, default=None, help='fuzzing seed (default 0)')
    ap.add_argument('--fuzz-timeout', type=float, default=None, help='seconds per real call while fuzzing')


def configure(args) -> Config:
    for attr, name in (('cases', 'fuzz_cases'), ('seed', 'fuzz_seed'), ('per_call', 'fuzz_timeout')):
        v = getattr(args, name, None)
        if v is not None:
            setattr(CONFIG, attr, v)
    return CONFIG


def function_seed(seed: int, name: str) -> int:
    return zlib.crc32(f'{seed}:{name}'.encode())


# ---------------------------------------------------------------- types and values
#
# Types are model.parse_type's forms: 'Int' 'Bool' 'String' 'Unit' 'Fl' 'Val',
# ('Option', t), ('List', t), ('Prod', [t, ...]); for shapes inferred under `Val` also
# ('Tuple', t) (a tuple of any length) and ('Dict', k, v).

def conforms(v, t) -> bool:
    """Does the Python value decode into Lean type `t` (mirrors the generated decoders)?"""
    if isinstance(t, str):
        if t == 'Int':
            return type(v) is int
        if t == 'Bool':
            return type(v) is bool
        if t == 'String':
            return type(v) is str
        if t == 'Unit':
            return v is None
        if t == 'Fl':
            return type(v) is float
        if t == 'Val':
            try:
                pv.tag(v)
                return True
            except pv.Unencodable:
                return False
        return False
    k = t[0]
    if k == 'Option':
        return v is None or conforms(v, t[1])
    if k == 'List':
        return type(v) is list and all(conforms(x, t[1]) for x in v)
    if k == 'Prod':
        return type(v) is tuple and len(v) == len(t[1]) and all(conforms(x, s) for x, s in zip(v, t[1]))
    if k == 'Tuple':
        return type(v) is tuple and all(conforms(x, t[1]) for x in v)
    if k == 'Dict':
        return type(v) is dict and all(conforms(a, t[1]) and conforms(b, t[2]) for a, b in v.items())
    return False


def shape(v, depth: int = 0):
    """The generator type of an observed Python value (for parameters the model typed `Val`)."""
    if depth > 3:
        return 'Val'
    if v is None:
        return 'Unit'
    if isinstance(v, bool):
        return 'Bool'
    if isinstance(v, int):
        return 'Int'
    if isinstance(v, float):
        return 'Fl'
    if isinstance(v, str):
        return 'String'
    if isinstance(v, (list, tuple)):
        kinds = {repr(shape(x, depth + 1)): shape(x, depth + 1) for x in v}
        el = next(iter(kinds.values())) if len(kinds) == 1 else 'Val'
        return ('List', el) if isinstance(v, list) else ('Tuple', el)
    if isinstance(v, dict):
        ks = {repr(shape(x, depth + 1)): shape(x, depth + 1) for x in v}
        vs = {repr(shape(x, depth + 1)): shape(x, depth + 1) for x in v.values()}
        return ('Dict', next(iter(ks.values())) if len(ks) == 1 else 'Val',
                next(iter(vs.values())) if len(vs) == 1 else 'Val')
    return 'Val'


ANNOTATION_TYPES = {'int': 'Int', 'str': 'String', 'bool': 'Bool', 'float': 'Fl'}

INT_SPECIAL = [0, 1, -1, 2, -2, 3, -3, 7, -7, 9, 10, -10, 11, 16, 99, 100, -100, 127, 128, 255, 256, -256,
               1000, -1000, 1023, 1024, 65535, 65536, 2 ** 31 - 1, -2 ** 31, 2 ** 31, 2 ** 32, 2 ** 53,
               2 ** 53 + 1, 2 ** 63 - 1, -2 ** 63, 2 ** 63, 2 ** 64, -2 ** 64, 10 ** 18, -10 ** 18]
HALVES = [5, -5, 15, -15, 25, 50, -50, 150, -150, 250, 500, 1500, 2500, -250, 35, 45]   # decimal half-way
STR_SPECIAL = ['', ' ', '  ', '\t', '\n', '\r\n', '\r', ' a ', 'a  b', 'a\tb', 'a\nb', ' \t\n', ' ',
               ' x', '\x0b', '\x0c', '\x1c', '\x00', '0', '00', '007', '123', '-5', '+5', ' 7 ', '1.5',
               '1e3', '٣', '１２', '²', 'é', 'é', 'ß', 'İ', 'ǅ', 'Σ', 'ΣΑ', '日本語',
               '\U0001f642', 'ﬁ', 'aaaa', 'abab', 'AbC', 'A', 'a,b', 'a=b', 'a;b', 'a/b', 'a.b', 'a-b_c',
               '%41', '"', "'", '\\', 'a b c', 'Hello World', 'x' * 20]
FLOAT_SPECIAL = [0.0, -0.0, 0.5, -0.5, 1.5, 2.5, -2.5, 0.1, 1 / 3, 1.0, -1.0, 3.0, 1e-310, 1e300, -1e300,
                 float('inf'), float('-inf'), float('nan'), 2.0 ** 53, 0.125, 123.456]
ALPHABET = ('abcxyzABZ' '0189' ' \t\n' ',.;:=/-_%&?#' 'éß' ' 　' 'Σİ日' '\U0001f642')
SCALARS = ['Int', 'String', 'Bool', 'Unit', 'Fl']


def _literals(source: str):
    return _model()._literals(source)


class Gen:
    """Seeded generator of typed Python values and one-field mutations."""

    def __init__(self, seed: int, ints=(), strs=()):
        self.r = random.Random(seed)
        self.ints = list(dict.fromkeys(i for v in ints for i in (v, v - 1, v + 1, -v)))
        self.strs = list(strs)

    # --- scalars
    def int_(self) -> int:
        r = self.r
        x = r.random()
        if x < 0.25:
            return r.randint(-10, 10)
        if x < 0.45:
            return r.choice(INT_SPECIAL)
        if x < 0.53:
            return r.choice(HALVES)
        if x < 0.65:
            k = r.randint(0, 70)
            return r.choice((1, -1)) * (2 ** k + r.choice((-1, 0, 0, 1)))
        if x < 0.75:
            return r.choice((1, -1)) * r.getrandbits(r.randint(1, 128))
        if x < 0.85 and self.ints:
            return r.choice(self.ints)
        return r.randint(-1000, 1000)

    def str_(self) -> str:
        r = self.r
        x = r.random()
        if x < 0.35:
            return r.choice(STR_SPECIAL)
        if x < 0.5 and self.strs:
            s = r.choice(self.strs)
            return self.mutate_str(s) if r.random() < 0.5 else s
        if x < 0.6:
            unit = ''.join(r.choice(ALPHABET) for _ in range(r.randint(1, 3)))
            return unit * r.randint(2, 5)
        return ''.join(r.choice(ALPHABET) for _ in range(r.randint(0, 8)))

    def float_(self) -> float:
        r = self.r
        if r.random() < 0.5:
            return r.choice(FLOAT_SPECIAL)
        if r.random() < 0.3:
            return float(r.randint(-20, 20)) / 2
        return r.uniform(-1, 1) * 10 ** r.randint(-5, 20)

    # --- typed values
    def value(self, t, depth: int = 0):
        r = self.r
        if isinstance(t, str):
            if t == 'Int':
                return self.int_()
            if t == 'Bool':
                return r.random() < 0.5
            if t == 'String':
                return self.str_()
            if t == 'Unit':
                return None
            if t == 'Fl':
                return self.float_()
            # Val: any encodable value, mostly scalars
            if depth >= 2 or r.random() < 0.7:
                return self.value(r.choice(SCALARS), depth + 1)
            return self.value(r.choice([('List', 'Val'), ('Tuple', 'Val'), ('Dict', 'String', 'Val')]), depth + 1)
        k = t[0]
        if k == 'Option':
            return None if r.random() < 0.25 else self.value(t[1], depth + 1)
        if k in ('List', 'Tuple'):
            n = self.size()
            xs = [self.value(t[1], depth + 1) for _ in range(n)]
            return xs if k == 'List' else tuple(xs)
        if k == 'Prod':
            return tuple(self.value(s, depth + 1) for s in t[1])
        if k == 'Dict':
            return {self.value(t[1], depth + 1): self.value(t[2], depth + 1) for _ in range(self.size())
                    } if _hashable(t[1]) else {}
        return None

    def size(self) -> int:
        return self.r.choice((0, 1, 1, 2, 2, 3, 3, 4, 5))

    # --- mutation
    def mutate_str(self, s: str) -> str:
        r = self.r
        n = len(s)
        ops = ['ins', 'del', 'rep', 'case', 'dup', 'ws', 'cut', 'special', 'tab']
        op = r.choice(ops)
        c = r.choice(ALPHABET)
        i = r.randint(0, n)
        if op == 'ins':
            return s[:i] + c + s[i:]
        if op == 'del' and n:
            i = min(i, n - 1)
            return s[:i] + s[i + 1:]
        if op == 'rep' and n:
            i = min(i, n - 1)
            return s[:i] + c + s[i + 1:]
        if op == 'case':
            return s.swapcase()
        if op == 'dup':
            return s + s
        if op == 'ws':
            return r.choice((' ', '\t', '\n', ' ')) + s + r.choice(('', ' ', '\t'))
        if op == 'cut':
            return s[:i]
        if op == 'tab':
            return s.replace(' ', r.choice(('\t', '  ', '\n')), 1)
        return r.choice(STR_SPECIAL)

    def mutate(self, v, t, depth: int = 0):
        """A value of type `t` close to `v` (one change)."""
        r = self.r
        if depth > 3:
            return self.value(t)
        if t == 'Val':
            t2 = shape(v)
            if t2 != 'Val' and r.random() < 0.85:
                return self.mutate(v, t2, depth + 1)
            return self.value('Val')
        if t == 'Int' and type(v) is int:
            m = r.choice(('inc', 'dec', 'neg', 'zero', 'dbl', 'half', 'near', 'pow', 'special', 'half10'))
            if m == 'inc':
                return v + 1
            if m == 'dec':
                return v - 1
            if m == 'neg':
                return -v
            if m == 'zero':
                return 0
            if m == 'dbl':
                return v * 2
            if m == 'half':
                return v // 2
            if m == 'near':
                return v + r.randint(-100, 100)
            if m == 'pow':
                return v + r.choice((1, -1)) * 2 ** r.randint(0, 64)
            if m == 'half10':
                p = 10 ** r.randint(1, 3)
                return (v // p) * p + p // 2
            return self.int_()
        if t == 'String' and type(v) is str:
            return self.mutate_str(v)
        if t == 'Bool' and type(v) is bool:
            return not v
        if t == 'Fl' and type(v) is float:
            if not math.isfinite(v) or r.random() < 0.3:
                return self.float_()
            return r.choice((v + 1, -v, v / 2, v * 3, float(round(v)), v + 0.5))
        if isinstance(t, tuple):
            k = t[0]
            if k == 'Option':
                if v is None:
                    return self.value(t[1])
                return None if r.random() < 0.3 else self.mutate(v, t[1], depth + 1)
            if k in ('List', 'Tuple') and isinstance(v, (list, tuple)):
                xs = list(v)
                m = r.choice(('drop', 'dup', 'elem', 'elem', 'add', 'rev', 'empty'))
                if m == 'drop' and xs:
                    xs.pop(r.randrange(len(xs)))
                elif m == 'dup' and xs:
                    i = r.randrange(len(xs))
                    xs.insert(i, xs[i])
                elif m == 'elem' and xs:
                    i = r.randrange(len(xs))
                    xs[i] = self.mutate(xs[i], t[1], depth + 1)
                elif m == 'rev':
                    xs.reverse()
                elif m == 'empty':
                    xs = []
                else:
                    xs.insert(r.randint(0, len(xs)), self.value(t[1], depth + 1))
                return xs if k == 'List' else tuple(xs)
            if k == 'Prod' and isinstance(v, tuple) and len(v) == len(t[1]):
                xs = list(v)
                i = r.randrange(len(xs))
                xs[i] = self.mutate(xs[i], t[1][i], depth + 1)
                return tuple(xs)
            if k == 'Dict' and isinstance(v, dict):
                d = dict(v)
                keys = list(d)
                m = r.choice(('drop', 'val', 'add'))
                if m == 'drop' and keys:
                    d.pop(r.choice(keys))
                elif m == 'val' and keys:
                    key = r.choice(keys)
                    d[key] = self.mutate(d[key], t[2], depth + 1)
                elif _hashable(t[1]):
                    try:
                        d[self.value(t[1], depth + 1)] = self.value(t[2], depth + 1)
                    except TypeError:
                        pass
                return d
        return self.value(t)


def _hashable(t) -> bool:
    return not (isinstance(t, tuple) and t[0] in ('List', 'Dict')) and t != 'Val'


# ---------------------------------------------------------------- arguments

@dataclass
class Params:
    """The argument layout of a model signature (from model.Sig)."""
    fixed: list          # [(type, has_default)]
    var: object = None   # element type of *args, or None

    @classmethod
    def of(cls, sig) -> 'Params':
        fixed = [(p['type'], p['default'] is not None) for p in sig.params if p['kind'] == 'positional']
        var = next((p['type'][1] for p in sig.params if p['kind'] == 'varargs'), None)
        return cls(fixed, var)

    def type_at(self, i: int):
        if i < len(self.fixed):
            return self.fixed[i][0]
        return self.var

    def accepts(self, args: list) -> bool:
        n, fixed = len(args), self.fixed
        required = sum(1 for _, d in fixed if not d)
        if self.var is None:
            if not required <= n <= len(fixed):
                return False
        elif n < len(fixed):
            return False
        return all(conforms(a, self.type_at(i)) for i, a in enumerate(args))

    def droppable(self, args: list) -> bool:
        """Can the last argument be dropped (a defaulted parameter or a *args element)?"""
        n = len(args)
        if self.var is not None and n > len(self.fixed):
            return True
        return 0 < n <= len(self.fixed) and self.fixed[n - 1][1]


class ArgGen:
    """Argument tuples for one function: typed, hinted and mutated."""

    def __init__(self, params: Params, seed: int, source: str = '', traced=(), annotations=()):
        ints, strs = _literals(source) if source else ([], [])
        self.g = Gen(seed, ints, strs)
        self.p = params
        self.traced = [a for a in traced if params.accepts(a)]
        # generator type per position: the Lean type, narrowed where it is `Val`
        self.hints = {}
        n = max([len(params.fixed)] + [len(a) for a in self.traced])
        for i in range(n):
            t = params.type_at(i)
            if t != 'Val':
                continue
            seen = {}
            for a in self.traced:
                if i < len(a):
                    s = shape(a[i])
                    seen[repr(s)] = s
            opts = list(seen.values())
            if i < len(annotations) and annotations[i] in ANNOTATION_TYPES:
                opts.append(ANNOTATION_TYPES[annotations[i]])
            if opts:
                self.hints[i] = opts

    def _type(self, i: int):
        t = self.p.type_at(i)
        if i in self.hints and self.g.r.random() < 0.7:
            return self.g.r.choice(self.hints[i])
        return t

    def fresh(self) -> list:
        r = self.g.r
        n = len(self.p.fixed)
        if self.p.var is None:
            required = sum(1 for _, d in self.p.fixed if not d)
            if required < n and r.random() < 0.2:
                n = r.randint(required, n)
        else:
            n += self.g.size()
        return [self.g.value(self._type(i)) for i in range(n)]

    def mutate(self, args: list) -> list:
        args = list(args)
        r = self.g.r
        if not args or (self.p.var is not None and r.random() < 0.15):
            if self.p.var is not None:
                return args + [self.g.value(self.p.var)] if r.random() < 0.6 or not args else args[:-1]
            return self.fresh()
        i = r.randrange(len(args))
        t = self._type(i) if r.random() < 0.3 else self.p.type_at(i)
        args[i] = self.g.mutate(args[i], t)
        return args


def encode(args):
    try:
        return [pv.tag(a) for a in args]
    except (pv.Unencodable, RecursionError, ValueError):
        return None


def decode(point):
    return [pv.untag(t) for t in point]


# ---------------------------------------------------------------- size and shrinking

def _char_cost(c: str) -> int:
    return 1 if c == 'a' else 2 if c.isascii() and c.isalnum() else 3 if c.isascii() else 4


def size(v) -> int:
    """A well-founded size: shrinking only ever moves to strictly smaller values."""
    if v is None or v is False:
        return 0
    if v is True:
        return 1
    if isinstance(v, int):
        return 2 * abs(v) + (1 if v < 0 else 0)
    if isinstance(v, float):
        return 0 if v == 0 and math.copysign(1, v) > 0 else 1 + len(repr(v))
    if isinstance(v, str):
        return sum(1 + 2 * _char_cost(c) for c in v)
    if isinstance(v, (list, tuple)):
        return 1 + sum(1 + size(x) for x in v)
    if isinstance(v, dict):
        return 1 + sum(1 + size(a) + size(b) for a, b in v.items())
    return 1


def point_size(args) -> int:
    return len(args) + sum(size(a) for a in args)


def _int_candidates(v: int) -> list:
    if v == 0:
        return []
    out = [0]
    if v < 0:
        out.append(-v)
    s = 1 if v > 0 else -1
    a = abs(v)
    out.append(s * (a // 2))
    out.append(v - s)
    k, steps = 1, []
    while k < a:
        steps.append(k)
        k *= 2
    k = 1
    while k < a:
        steps += [k, 2 * k, 5 * k]
        k *= 10
    for m in sorted(set(steps), reverse=True):
        if m < a:
            out.append(v - s * m)
            if v < 0:
                out.append(a - m)
    if a.bit_length() > 8:
        out.append(s * (a >> (a.bit_length() // 2)))
    # keep only the low digits / bits (1554078250 -> 50 in one step)
    k = 10
    while k < a:
        out.append(s * (a % k))
        k *= 10
    for b in range(1, min(a.bit_length(), 128)):
        out.append(s * (a % (1 << b)))
    return out


def _str_candidates(s: str) -> list:
    n = len(s)
    if not n:
        return []
    out = ['', s[:n // 2], s[n // 2:], s.strip(), s[1:], s[:-1]]
    if n <= 24:
        out += [s[:i] + s[i + 1:] for i in range(n)]
        out += [s[:i] + 'a' + s[i + 1:] for i in range(n) if s[i] != 'a' and _char_cost(s[i]) > 1]
        out += [s[:i] + ' ' + s[i + 1:] for i in range(n) if not s[i].isascii()]
    else:
        q = max(1, n // 8)
        out += [s[:i] + s[i + q:] for i in range(0, n, q)]
    return out


def value_candidates(v, t) -> list:
    """Simpler values than `v` (not yet filtered by type or size)."""
    out = []
    if t == 'Val' or (isinstance(t, tuple) and t[0] == 'Option'):
        out += [None]
    if t == 'Val':
        out += [0, '', False]
        t = shape(v)
        if t == 'Val':
            return out
    if isinstance(t, tuple) and t[0] == 'Option':
        if v is None:
            return out
        t = t[1]
    if v is True:
        out.append(False)
    elif isinstance(v, int) and not isinstance(v, bool):
        out += _int_candidates(v)
    elif isinstance(v, float):
        if math.isfinite(v):
            out += [0.0, float(int(v)), v / 2, float(round(v, 1))]
        else:
            out += [0.0, 1.0]
    elif isinstance(v, str):
        out += _str_candidates(v)
    elif isinstance(v, (list, tuple)):
        xs = list(v)
        mk = list if isinstance(v, list) else tuple
        el = t[1] if isinstance(t, tuple) and t[0] in ('List', 'Tuple') else None
        comps = t[1] if isinstance(t, tuple) and t[0] == 'Prod' else None
        if comps is None:
            out += [mk([]), mk(xs[:len(xs) // 2]), mk(xs[len(xs) // 2:])]
            out += [mk(xs[:i] + xs[i + 1:]) for i in range(len(xs))]
        for i, x in enumerate(xs):
            et = comps[i] if comps and i < len(comps) else el if el is not None else 'Val'
            for c in value_candidates(x, et)[:12]:
                out.append(mk(xs[:i] + [c] + xs[i + 1:]))
    elif isinstance(v, dict):
        items = list(v.items())
        out.append({})
        out += [dict(items[:i] + items[i + 1:]) for i in range(len(items))]
        vt = t[2] if isinstance(t, tuple) and t[0] == 'Dict' else 'Val'
        for i, (k, x) in enumerate(items):
            for c in value_candidates(x, vt)[:8]:
                out.append(dict(items[:i] + [(k, c)] + items[i + 1:]))
    return out


def shrink_candidates(args: list, params: Params) -> list:
    """One-step simplifications of an argument tuple, smallest first, all well-typed."""
    base = point_size(args)
    raw = []
    if params.droppable(args):
        raw.append(args[:-1])
    if params.var is not None and len(args) > len(params.fixed):
        raw += [args[:i] + args[i + 1:] for i in range(len(params.fixed), len(args))]
    for i, a in enumerate(args):
        for c in value_candidates(a, params.type_at(i)):
            raw.append(args[:i] + [c] + args[i + 1:])
    out, seen = [], set()
    for c in raw:
        if not params.accepts(c):
            continue
        s = point_size(c)
        if s >= base:
            continue
        key = _key(c)
        if key is None or key in seen:
            continue
        seen.add(key)
        out.append((s, c))
    out.sort(key=lambda x: x[0])
    return [c for _, c in out]


def _key(args):
    t = encode(args)
    return json.dumps(t) if t is not None else None


def shrink_many(starts: list, params: Params, oracle, *, rounds: int = 12, per_round: int = 160) -> list:
    """Greedily shrink several failing argument tuples in lock-step.

    `oracle(list of arg lists) -> list of bool` (True: still disagrees) is called once per
    round with the candidates of every tuple still shrinking. Returns
    [(minimal args, steps)] in the order of `starts`."""
    cur = [list(s) for s in starts]
    steps = [0] * len(cur)
    active = set(range(len(cur)))
    known: dict = {}                  # candidate key -> oracle verdict (shared by all tuples)
    for _ in range(rounds):
        if not active:
            break
        share = max(8, per_round // len(active))
        per_owner, ask, asked = {}, [], set()
        for i in sorted(active):
            cands = shrink_candidates(cur[i], params)
            # verdicts already known cost nothing; the budget is spent on new candidates
            fresh = [c for c in cands if _key(c) not in known][:share]
            fresh_keys = {_key(c) for c in fresh}
            per_owner[i] = [c for c in cands if _key(c) in known or _key(c) in fresh_keys]
            for c in fresh:
                if _key(c) not in asked:
                    asked.add(_key(c))
                    ask.append(c)
        if ask:
            for c, ok in zip(ask, oracle(ask)):
                known[_key(c)] = bool(ok)
        moved = set()
        for i, cands in per_owner.items():             # candidates are smallest-first
            for c in cands:
                if known.get(_key(c)):
                    cur[i] = c
                    steps[i] += 1
                    moved.add(i)
                    break
        active = {i for i in active if i in moved}
    return list(zip(cur, steps))


# ---------------------------------------------------------------- CPython with coverage

COVER_PRELUDE = r'''
import sys as _afs, os as _afo, json as _afj
_af_cfg = _afj.load(open(_afs.argv[1]))
_af_root = _afo.path.realpath(_af_cfg['cover_root'])
_af_mark = _af_cfg['cover_mark']
_af_points, _af_cur, _af_files = [], [None], {}
def _af_global(frame, event, arg):
    if event != 'call' or _af_cur[0] is None:
        return None
    fn = frame.f_code.co_filename
    fid = _af_files.get(fn)
    if fid is None:
        rp = _afo.path.realpath(fn)
        fid = _af_files[fn] = rp if rp.startswith(_af_root + _afo.sep) else ''
    if not fid:
        return None
    cur = _af_cur[0]
    prev = [-frame.f_code.co_firstlineno]
    def _af_local(frame, event, arg):
        if event == 'line':
            cur.add((fid, prev[0], frame.f_lineno))
            prev[0] = frame.f_lineno
        elif event == 'return':
            cur.add((fid, prev[0], 0))
        return _af_local
    return _af_local
def _af_top(frame, event, arg):
    if event == 'line' and frame.f_lineno == _af_mark:
        _af_cur[0] = set()
        _af_points.append(_af_cur[0])
    return _af_top
_afs.settrace(_af_global)
_afs._getframe().f_trace = _af_top
'''

COVER_POSTLUDE = r'''
_afs.settrace(None)
_af_cur[0] = None
def _af_static():
    import dis, inspect
    f = getattr(obj, '__func__', obj)
    try:
        f = inspect.unwrap(f)
    except Exception:
        pass
    co = f.__code__
    def codes(c):
        yield c
        for k in c.co_consts:
            if isinstance(k, type(c)):
                yield from codes(k)
    lines, branches = set(), set()
    for c in codes(co):
        for _s, _e, ln in c.co_lines():
            if ln is not None and ln != co.co_firstlineno:
                lines.add(ln)
        ins = list(dis.get_instructions(c))
        at, last = {}, None
        for i in ins:
            pos = getattr(i, 'positions', None)
            ln = pos.lineno if pos is not None and pos.lineno else i.starts_line
            last = ln or last
            at[i.offset] = last
        for k, i in enumerate(ins):
            if ('_IF_' in i.opname or i.opname == 'FOR_ITER') and isinstance(i.argval, int):
                src = at.get(i.offset)
                for dst in (at.get(i.argval), at.get(ins[k + 1].offset) if k + 1 < len(ins) else None):
                    if src and dst and dst != src and dst in lines:
                        branches.add((src, dst))
    return _afo.path.realpath(co.co_filename), sorted(lines), sorted(branches)
try:
    _af_file, _af_lines, _af_br = _af_static()
except Exception as _af_e:
    _af_file, _af_lines, _af_br = '', [], []
_af_names = sorted({f for p in _af_points for f, _a, _b in p})
_af_ix = {f: i for i, f in enumerate(_af_names)}
_afj.dump({'file': _af_file, 'lines': _af_lines, 'branches': _af_br, 'files': _af_names,
           'points': [sorted([_af_ix[f], a, b] for f, a, b in p) for p in _af_points]},
          open(_af_cfg['cover_out'], 'w'))
'''


def cover_script() -> tuple:
    """(script, mark line): model.RUNNER wrapped with the tracer, unchanged in between."""
    runner = _model().RUNNER
    lines = runner.split('\n')
    try:
        i = next(k for k, ln in enumerate(lines) if re.match(r"\s*for point in cfg\['points'\]:", ln))
        j = next(k for k in range(i + 1, len(lines)) if lines[k].strip() not in ('', 'try:'))
    except StopIteration:
        return None, 0
    return COVER_PRELUDE + runner + COVER_POSTLUDE, COVER_PRELUDE.count('\n') + j + 1


@dataclass
class Static:
    file: str = ''
    lines: list = field(default_factory=list)
    branches: list = field(default_factory=list)


class CoverageRunner:
    """Runs a function's real code on input points; outcomes plus the arcs each point hit.

    Outcomes are also stored in the model stage's Runtime cache, so shrinking and later
    rounds never re-run a point."""

    def __init__(self, fn, runtime, work: Path, per_call: float, root: Path | None = None):
        self.fn, self.runtime, self.work, self.per_call = fn, runtime, Path(work), per_call
        self.root = Path(root or fn.mod.import_root).resolve()
        self.static = Static()
        self.available = True
        self.calls = 0
        self.error = ''

    def run(self, points: list) -> list:
        """[(outcome, frozenset of arcs)] per point (arcs empty when coverage is unavailable)."""
        M = _model()
        script, mark = cover_script()
        if not points:
            return []
        self.calls += 1
        if script is None:
            self.available = False
            return [(r, frozenset()) for r in self.runtime.run(points)]
        mod = self.fn.mod
        cover_out = (self.work / f'cover{self.calls}.cov.json').resolve()
        cfg = {'sys_path': [str(mod.import_root)], 'dotted': mod.dotted, 'path': str(mod.path),
               'qual': self.fn.qual, 'per': self.per_call, 'points': points,
               'cover_root': str(self.root), 'cover_mark': mark, 'cover_out': str(cover_out)}
        if cover_out.exists():
            cover_out.unlink()
        data, err = M._run_script(script, cfg, self.work, f'cover{self.calls}', M.RUNTIME_TIMEOUT,
                                  cwd=mod.import_root)
        if data is None or len(data) != len(points):
            self.error = err or 'coverage runner returned a wrong number of results'
            return [(r, frozenset()) for r in self.runtime.run(points)]
        for p, r in zip(points, data):
            self.runtime.cache.setdefault(json.dumps(p), r)
        cov = None
        if cover_out.is_file():
            try:
                cov = json.loads(cover_out.read_text())
            except ValueError:
                cov = None
        # one mark per point that reached the loop body; points that failed to decode still count
        if not cov or len(cov['points']) != len(points):
            self.available = False
            return [(r, frozenset()) for r in data]
        if cov.get('file') and not self.static.file:
            self.static = Static(cov['file'], cov['lines'], [tuple(b) for b in cov['branches']])
        files = cov['files']
        out = []
        for r, arcs in zip(data, cov['points']):
            out.append((r, frozenset((files[f], a, b) for f, a, b in arcs)))
        return out

    def coverage(self, arcs: set) -> dict:
        st = self.static
        if not self.available or not st.file:
            return {'available': False}
        mine = {(a, b) for f, a, b in arcs if f == st.file}
        hit = {b for _, b in mine} & set(st.lines)
        br = [b for b in st.branches if b in mine]
        return {'available': True, 'lines': f'{len(hit)}/{len(st.lines)}',
                'line_pct': round(100 * len(hit) / len(st.lines), 1) if st.lines else 100.0,
                'branches': f'{len(br)}/{len(st.branches)}',
                'branch_pct': round(100 * len(br) / len(st.branches), 1) if st.branches else 100.0}


# ---------------------------------------------------------------- exploration

@dataclass
class Case:
    point: list          # tagged args
    args: list           # Python args
    outcome: dict        # CPython runner result
    arcs: frozenset
    origin: str          # traced | fresh | mutant | carried
    novel: int = 0       # new arcs this input reached when it ran
    lean: str | None = None   # the model's canonical outcome, once evaluated


def outcome_kind(res: dict) -> str:
    c = pv.canon_outcome(res)
    if c is None:
        return 'none:' + str(res.get('k'))
    if c.startswith('exn '):
        return c
    body = c[3:]
    return 'ok ' + body[:2]


def explore(argen: ArgGen, runner, budget: int, batch: int = 150, traced_points=()) -> tuple:
    """Run ~budget generated inputs in CPython, coverage-guided. (baseline arcs, [Case])."""
    seen_keys = set()
    seen_arcs: set = set()
    corpus: list = []     # Case with novel coverage (mutation parents)
    baseline = []
    if traced_points:
        pts = [p for p in traced_points if json.dumps(p) not in seen_keys]
        for p in pts:
            seen_keys.add(json.dumps(p))
        for p, (res, arcs) in zip(pts, runner.run(pts)):
            c = Case(p, decode(p), res, arcs, 'traced', len(arcs - seen_arcs))
            seen_arcs |= arcs
            baseline.append(c)
            if c.novel:
                corpus.append(c)
    base_arcs = set(seen_arcs)
    cases: list = []
    r = argen.g.r
    generated, stale = 0, 0
    while generated < budget and stale < 5:
        todo = []
        attempts = 0
        while len(todo) < min(batch, budget - generated) and attempts < batch * 20:
            attempts += 1
            if corpus and r.random() < 0.55:
                # mutate a corpus entry; recent and more-novel entries are likelier parents
                w = [1 + c.novel + i / 4 for i, c in enumerate(corpus)]
                parent = r.choices(corpus, weights=w)[0]
                args, origin = argen.mutate(parent.args), 'mutant'
            elif argen.traced and r.random() < 0.3:
                args, origin = argen.mutate(r.choice(argen.traced)), 'mutant'
            else:
                args, origin = argen.fresh(), 'fresh'
            if not argen.p.accepts(args):
                continue
            p = encode(args)
            if p is None:
                continue
            k = json.dumps(p)
            if k in seen_keys:
                continue
            seen_keys.add(k)
            todo.append((p, args, origin))
        if not todo:
            stale += 1
            continue
        generated += len(todo)
        new_here = 0
        for (p, args, origin), (res, arcs) in zip(todo, runner.run([t[0] for t in todo])):
            c = Case(p, args, res, arcs, origin, len(arcs - seen_arcs))
            seen_arcs |= arcs
            cases.append(c)
            if c.novel:
                corpus.append(c)
                new_here += 1
        stale = 0 if new_here or len(todo) >= batch // 2 else stale + 1
    return base_arcs, baseline, cases


def select(cases: list, n: int) -> list:
    """Lean batch: novel-coverage inputs, then new outcome kinds, then the rest (stable order)."""
    chosen, picked = [], set()
    comparable = [c for c in cases if pv.canon_outcome(c.outcome) is not None]

    def take(c):
        if id(c) not in picked and len(chosen) < n:
            picked.add(id(c))
            chosen.append(c)
    for c in comparable:
        if c.novel:
            take(c)
    kinds = {outcome_kind(c.outcome) for c in chosen}
    for c in comparable:
        k = outcome_kind(c.outcome)
        if k not in kinds:
            kinds.add(k)
            take(c)
    for c in comparable:
        take(c)
    return chosen


# ---------------------------------------------------------------- the hook

_STATE: 'weakref.WeakKeyDictionary' = weakref.WeakKeyDictionary()   # Runtime -> per-function state
_LOCK = threading.Lock()


def _genuine(out, res) -> bool | None:
    """True: a real disagreement; False: agreement; None: not comparable (counted)."""
    rt = pv.canon_outcome(res)
    if rt is None or out is None or out.startswith(('hole ', 'fuel')):
        return None
    return out != rt


def _entry(args, point, out, res):
    rt = pv.canon_outcome(res)
    return {'inputs': pv.show_args(point), 'model': pv.display(out), 'runtime': pv.display(rt),
            'model_raw': out, 'runtime_raw': rt}


def lean_oracle(M, runtime, lean_kwargs: dict, stem: str, counter: list):
    """oracle(args list) -> [still disagrees] via one CPython batch and one Lean batch."""
    def oracle(cands):
        idx, pts = [], []
        for i, a in enumerate(cands):
            p = encode(a)
            if p is not None:
                idx.append(i)
                pts.append(p)
        flags = [False] * len(cands)
        if not pts:
            return flags
        counter[0] += 1
        rt = runtime.run(pts)
        ev = M.evaluate(stem=f'{stem}s{counter[0]}', points=pts, runtime=rt, kernel_points=0, **lean_kwargs)
        if not ev.elaborates:
            return flags
        for i, p, r, o in zip(idx, pts, rt, ev.outputs):
            flags[i] = bool(_genuine(o, r))
        return flags
    return oracle


def extend(ev, *, fn, cand, lean_name: str, module: str, lean_root, work, stem: str, callee_src: str,
           points: list, rt: list, runtime, traced=(), config: Config | None = None):
    """model.py's hook, called once per repair round after the traced + boundary comparison.

    When the candidate agreed on every point (and fuzzing is on), fuzz it; splice minimal
    counterexamples (first) and the novel-coverage corpus into `points`, `rt`, `ev.outputs`,
    `ev.disagreements` and `ev.compared` in place, so the repair loop, the record, the smoke
    re-run and translation B all see them. Returns the round's fuzz record (or None)."""
    cfg = config or CONFIG
    if (cfg.cases <= 0 or not ev.elaborates or ev.disagreements or ev.kernel_failures
            or getattr(cand, 'sig', None) is None):
        return None
    M = _model()
    t0 = time.time()
    work = Path(work)
    fwork = work / 'fuzz'
    fwork.mkdir(parents=True, exist_ok=True)
    state = _STATE.setdefault(runtime, {'carried': [], 'rounds': []})
    seed = function_seed(cfg.seed, fn.info.name)
    params = Params.of(cand.sig)
    traced_args = []
    for p in traced or ():
        try:
            traced_args.append(decode(p))
        except (ValueError, TypeError, KeyError):
            pass
    argen = ArgGen(params, seed, fn.info.source, traced_args, [p.sort for p in fn.info.params])
    runner = CoverageRunner(fn, runtime, fwork, cfg.per_call)
    typed_traced = [p for p, a in zip(traced or (), traced_args) if params.accepts(a)]
    base_arcs, baseline, cases = explore(argen, runner, cfg.cases * max(1, cfg.cpython_factor), cfg.batch,
                                         typed_traced)
    # previously found minimal counterexamples are re-checked first
    carried = [(encode(a), a) for a in state['carried'] if params.accepts(a)]
    carried = [(p, a) for p, a in carried if p is not None]
    carried = [Case(p, a, r, frozenset(), 'carried')
               for (p, a), r in zip(carried, runtime.run([p for p, _ in carried]) if carried else [])]
    chosen = carried + select(cases, cfg.cases)
    unencodable = sum(1 for c in cases if pv.canon_outcome(c.outcome) is None)
    all_arcs = set(base_arcs)
    for c in cases:
        all_arcs |= c.arcs
    rec = {'round': stem, 'seed': seed, 'config_seed': cfg.seed, 'cases_generated': len(cases),
           'cases_run': 0, 'unencodable': unencodable, 'off_domain': 0, 'traced_inputs': len(baseline),
           'corpus': sum(1 for c in cases if c.novel),
           'coverage': {'traced': runner.coverage(base_arcs), 'with_fuzz': runner.coverage(all_arcs)},
           'disagreements_found': 0, 'shrunk': [], 'lean_runs': 0}
    if runner.error:
        rec['runner_error'] = runner.error[:300]
    cov = rec['coverage']['with_fuzz']
    if cov.get('available') and cov['line_pct'] < LOW_COVERAGE:
        # agreeing on a domain that never reaches most of the code is weak evidence (e.g. a model
        # that types `headers` as a list, so every input raises AttributeError on line 1)
        rec['warning'] = (f"low coverage: the model's declared domain reaches {cov['lines']} lines of the "
                          'function even with fuzzing; its agreement says little about the rest')
    lean_kwargs = dict(module=module, lean_root=lean_root, work=fwork, callee_src=callee_src, cand=cand,
                       lean_name=lean_name, qual=fn.info.name)
    if chosen:
        pts = [c.point for c in chosen]
        fev = M.evaluate(stem=f'{stem}', points=pts, runtime=[c.outcome for c in chosen], kernel_points=0,
                         **lean_kwargs)
        rec['lean_runs'] = 1
        if not fev.elaborates:
            rec['error'] = 'fuzz batch did not evaluate: ' + (fev.errors or '')[:500]
            chosen = []
        else:
            for c, o in zip(chosen, fev.outputs):
                c.lean = o
    bad = []
    for c in chosen:
        g = _genuine(c.lean, c.outcome)
        if g is None:
            rec['off_domain'] += 1
        else:
            rec['cases_run'] += 1
            if g:
                bad.append(c)
    rec['disagreements_found'] = len(bad)
    # shrink up to max_shrink disagreements, distinct (Python kind, model kind) first
    starts, kinds = [], set()
    for c in bad:
        k = (outcome_kind(c.outcome), (c.lean or '')[:6])
        if k not in kinds and len(starts) < cfg.max_shrink:
            kinds.add(k)
            starts.append(c)
    for c in bad:
        if len(starts) >= cfg.max_shrink:
            break
        if c not in starts:
            starts.append(c)
    shrunk_cases = []
    if starts:
        counter = [0]
        oracle = lean_oracle(M, runtime, lean_kwargs, stem, counter)
        results = shrink_many([c.args for c in starts], params, oracle, rounds=cfg.shrink_rounds,
                              per_round=cfg.shrink_candidates)
        rec['lean_runs'] += counter[0]
        for c, (args, steps) in zip(starts, results):
            p = encode(args)
            if steps == 0 or p is None:
                p, args = c.point, c.args
            res = runtime.run([p])[0]
            # the minimal point's Lean output: one more (tiny) batch, same candidate
            if p is c.point:
                out = c.lean
            else:
                e = M.evaluate(stem=f'{stem}m{len(shrunk_cases)}', points=[p], runtime=[res], kernel_points=0,
                               **lean_kwargs)
                rec['lean_runs'] += 1
                out = e.outputs[0] if e.elaborates and e.outputs else None
            if not _genuine(out, res):      # defensive: never report a non-disagreement
                p, args, res, out = c.point, c.args, c.outcome, c.lean
            shrunk_cases.append((p, args, res, out))
            rec['shrunk'].append({'original': pv.show_args(c.point), 'shrunk': pv.show_args(p),
                                  'size_before': point_size(c.args), 'size_after': point_size(args),
                                  'steps': steps, 'python': pv.display(pv.canon_outcome(res)),
                                  'model': pv.display(out), 'origin': c.origin})
        state['carried'] = [a for _, a, _, _ in shrunk_cases][:cfg.max_shrink]
    # splice: counterexamples first (they are what the repair prompt shows), then the corpus
    have = {json.dumps(p) for p in points}
    new_disagreements = []
    for p, args, res, out in shrunk_cases:
        k = json.dumps(p)
        if k in have:
            continue
        have.add(k)
        points.append(p)
        rt.append(res)
        ev.outputs.append(out)
        ev.compared += 1
        e = _entry(args, p, out, res)
        e['point'] = len(points) - 1
        e['fuzz'] = True
        new_disagreements.append(e)
    ev.disagreements[:0] = new_disagreements
    kept = 0
    for c in chosen:
        if kept >= cfg.keep_corpus:
            break
        if c.novel and _genuine(c.lean, c.outcome) is False and json.dumps(c.point) not in have:
            have.add(json.dumps(c.point))
            points.append(c.point)
            rt.append(c.outcome)
            ev.outputs.append(c.lean)
            ev.compared += 1
            kept += 1
    rec['added_points'] = {'counterexamples': len(new_disagreements), 'corpus': kept}
    rec['seconds'] = round(time.time() - t0, 1)
    state['rounds'].append(rec)
    record(work, fn.info.name, lean_name, state['rounds'])
    return rec


def _out_dir(work: Path) -> Path:
    work = Path(work)
    return work.parent.parent if work.parent.name == 'model-work' else work


def record(work: Path, function: str, lean_name: str, rounds: list):
    """Write the function's rounds to <work>/fuzz.json and merge them into <out>/fuzz.json."""
    last = rounds[-1]
    entry = {'function': function, 'lean_name': lean_name, 'seed': last['seed'],
             'cases_run': sum(r['cases_run'] for r in rounds),
             'disagreements_found': sum(r['disagreements_found'] for r in rounds),
             'shrunk': sum(len(r['shrunk']) for r in rounds),
             'coverage': last['coverage'], 'final_round_clean': last['disagreements_found'] == 0,
             'warning': last.get('warning', ''),
             'rounds': rounds}
    Path(work).mkdir(parents=True, exist_ok=True)
    (Path(work) / 'fuzz.json').write_text(json.dumps(entry, indent=1, ensure_ascii=False))
    path = _out_dir(work) / 'fuzz.json'
    with _LOCK:
        try:
            data = json.loads(path.read_text()) if path.is_file() else []
        except ValueError:
            data = []
        data = [d for d in data if d.get('function') != function] + [entry]
        data.sort(key=lambda d: d['function'])
        path.write_text(json.dumps(data, indent=1, ensure_ascii=False))
