"""Check stage: bounded kernel evidence and real-runtime evidence for each Statement.

For every statement that elaborates, over one finite domain of concrete inputs:

  model check    one Lean file per function (its statements batched). Per statement:
                   pre_<t>/post_<t>   the statement's `pre`/`post` as Bool functions
                   chk_<t>            !(pre) || post (<call>)       -- one point
                   dom_<t>            the domain as a list literal
                   #eval search       first failing point (a CANDIDATE only)
                   bounded_<t>        dom.all chk = true, by `decide +kernel`
                   nonvac_<t>         dom.any pre = true, by `decide +kernel`
                 A candidate is certified in a second file,
                   refute_<t> : chk_<t> <point> = false := by decide +kernel
                 REFUTED_MODEL needs the certificate; BOUNDED_HOLDS needs `bounded_` and
                 `nonvac_` accepted with standard axioms only.
  runtime check  (Python) the REAL function is run in CPython on the same points (the
                 model stage's runner: methods run on a receiver rebuilt from its recorded
                 state, constructors build the object); each outcome is encoded as an
                 `EResult` literal (autoform.nl.pyvalues: ints, bools, strs, None, floats
                 by IEEE bits, tuples, lists, dicts in insertion order, sets in canonical
                 order, bytes, objects of modelled classes; a `#post` statement sees
                 `.tuple [result, receiver after the call]`) and the statement's `post` is
                 evaluated on it in Lean. A failing real execution is certified like a
                 model witness (`rtrefute_<t>`) and gives REFUTED_RUNTIME unless the model
                 is refuted too. Outcomes with no faithful literal (other objects,
                 timeouts) are skipped, never guessed.

Binders are Int/Nat/Bool/String (finite domains built here) or Val, whose domain is the
function's validated sample inputs recorded by the model stage (`FunctionInfo.samples`:
receivers, containers, ... exactly as the tests produced them).

Soundness: BOUNDED_HOLDS is a statement about the translated program on the listed
points, nothing more. The Python encoding of runtime outcomes is trusted (small, total,
below), as is the assumption that `binders/pre/post` say the same thing as `lean_prop`
(the formalize stage produces both from one template).
"""
from __future__ import annotations

import itertools
import json
import re
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict
from pathlib import Path

from ..harness.compiler import accessors, lean_str
from ..harness.cpir import integer_range
from ..harness.verifier import axioms_of, certified, run_lean
from . import pyvalues as pv
from . import schema

MAX_PARALLEL = 2
LEAN_TIMEOUT = 900
RUNTIME_TIMEOUT = 120          # whole runtime batch for one function
POINT_TIMEOUT = 5              # one real call

INT_BASE = [0, 1, -1, 2, -2, 3, 10, -10, 100, 7, -7, 255, 256, 2 ** 31 - 1, -2 ** 31, 2 ** 31]
STR_BASE = ['', 'a', 'admin', 'root', 'A', ' ', 'ab']
LEAN_TYPES = {'Int': 'int', 'ℤ': 'int', 'Nat': 'nat', 'ℕ': 'nat', 'Bool': 'bool', 'String': 'str', 'Val': 'val'}
LEAN_TYPE_NAME = {'int': 'Int', 'nat': 'Nat', 'bool': 'Bool', 'str': 'String', 'val': 'Val'}
MAX_SAMPLE_ROWS = 24
VAL_RE = re.compile(r"^\s*\(?\s*(?:Val|Autoform\.Core\.Val)?\.(int|bool|str)\s+\(?\s*([A-Za-z_][\w']*)\s*\)?\s*\)?\s*$")


# --- Lean literals ---------------------------------------------------------------

def lean_value(kind: str, v) -> str:
    if kind == 'val':
        return pv.lean_lit(v)
    if kind == 'bool':
        return 'true' if v else 'false'
    if kind == 'int':
        return f'({v} : Int)'
    if kind == 'nat':
        return f'({v} : Nat)'
    return lean_str(v)


def tuple_lit(kinds, point) -> str:
    if not point:
        return '()'
    items = [lean_value(k, v) for k, v in zip(kinds, point)]
    return items[0] if len(items) == 1 else '(' + ', '.join(items) + ')'


def tuple_type(kinds) -> str:
    return ' × '.join(LEAN_TYPE_NAME[k] for k in kinds) if kinds else 'Unit'


def encode_outcome(desc: dict):   # the pre-model runner's format (kept for deep translations' tests)
    """A CPython outcome (as described by the runner) → Lean `EResult` literal, or None.

    Only outcomes with an unambiguous Core counterpart are encoded; everything else
    (floats, containers, objects, timeouts) is skipped rather than approximated."""
    if not isinstance(desc, dict):
        return None
    if desc.get('kind') == 'exception':
        name = desc.get('type')
        return f'EResult.exn (Val.str {lean_str(name)})' if isinstance(name, str) and name else None
    if desc.get('kind') != 'value':
        return None
    t, v = desc.get('type'), desc.get('value')
    if t == 'NoneType':
        return 'EResult.val Val.unit'
    if t == 'bool' and isinstance(v, bool):
        return f'EResult.val (Val.bool {"true" if v else "false"})'
    if t == 'int' and isinstance(v, int) and not isinstance(v, bool):
        return f'EResult.val (Val.int ({v}))'
    if t == 'str' and isinstance(v, str):
        return f'EResult.val (Val.str {lean_str(v)})'
    return None


def describe_outcome(desc) -> str:
    if not isinstance(desc, dict):
        return 'not run'
    if 'k' in desc:        # the model stage's runner (pyvalues tags)
        text = pv.display(pv.canon_outcome(desc)) if pv.canon_outcome(desc) else desc['k']
        if desc.get('k') == 'ok' and 'post' not in desc and desc['v'][0] != 'n':
            kinds = {'i': 'int', 'b': 'bool', 's': 'str', 'f': 'float', 't': 'tuple', 'l': 'list', 'd': 'dict',
                     'y': 'bytes', 'F': 'type'}
            name = kinds.get(desc['v'][0]) or (desc['v'][2] if desc['v'][0] == 'S' else desc['v'][1])
            text += f' ({name})'
        return text
    if desc.get('kind') == 'exception':
        return f"raises {desc.get('type')}"
    if desc.get('kind') == 'value':
        if desc.get('type') == 'NoneType':
            return 'returns None'
        v = desc.get('value', desc.get('repr'))
        return f"returns {v!r} ({desc.get('type')})"
    return desc.get('kind', 'unknown')


# --- domain ----------------------------------------------------------------------

def source_literals(source: str, language: str = 'python'):
    """Integer and string literals of the function text (bounded, deduplicated)."""
    ints, strs = [], []
    text = source or ''
    for m in re.finditer(r"(?<![\w.])(0[xX][0-9a-fA-F]+|0[bB][01]+|0[oO]?[0-7]+|\d+)(?![\w.])", text):
        tok = m.group(1)
        try:
            if tok[:2] in ('0x', '0X'):
                v = int(tok, 16)
            elif tok[:2] in ('0b', '0B'):
                v = int(tok, 2)
            elif tok[:2] in ('0o', '0O'):
                v = int(tok[2:], 8)
            elif len(tok) > 1 and tok[0] == '0' and language in ('c', 'cpp', 'c++', 'go', 'java'):
                v = int(tok, 8)
            else:
                v = int(tok)
        except ValueError:
            continue
        if v not in ints:
            ints.append(v)
    if language == 'python':
        text_wo_doc = re.sub(r'("""|\'\'\')[\s\S]*?\1', '', text)
    else:
        text_wo_doc = text
    for m in re.finditer(r'"((?:[^"\\\n]|\\.){0,40})"|\'((?:[^\'\\\n]|\\.){0,40})\'', text_wo_doc):
        s = m.group(1) if m.group(1) is not None else m.group(2)
        try:
            s = bytes(s, 'utf-8').decode('unicode_escape') if '\\' in s else s
        except UnicodeDecodeError:
            pass
        if s not in strs:
            strs.append(s)
    return ints[:8], strs[:6]


def binder_values(kind: str, integer_type: str = '', ints=(), strs=()) -> list:
    """Candidate values for one binder, most informative first (shrinking drops the tail)."""
    if kind == 'bool':
        return [False, True]
    if kind == 'str':
        return list(dict.fromkeys(list(strs) + STR_BASE))
    vals = []
    bounds = integer_range(integer_type) if integer_type else None
    head = [0, 1, -1]
    if bounds:
        lo, hi = bounds
        head += [lo, hi, 2, lo + 1, hi - 1]
    lit = []
    for v in ints:
        lit += [v, v - 1, v + 1, -v]
    for v in head + lit + INT_BASE:
        if v not in vals:
            vals.append(v)
    if bounds:
        vals = [v for v in vals if bounds[0] <= v <= bounds[1]]
    if kind == 'nat':
        vals = [v for v in vals if v >= 0]
    return vals


def product_capped(per: list, cap: int) -> list:
    per = [list(p) for p in per]
    while per and _count(per) > cap and max(len(p) for p in per) > 1:
        i = max(range(len(per)), key=lambda k: len(per[k]))
        per[i] = per[i][:-1]
    return [list(p) for p in itertools.product(*per)] if per else [[]]


def _count(per):
    n = 1
    for p in per:
        n *= len(p)
    return n


def domain(binders: list, fn: dict | None, language: str, cap: int = 64):
    """Returns (kinds, points) or raises ValueError for a binder type with no domain."""
    params = (fn or {}).get('params', [])
    by_name = {p.get('name'): p for p in params}
    ints, strs = source_literals((fn or {}).get('source', ''), language)
    kinds, per = [], []
    for i, b in enumerate(binders):
        kind = LEAN_TYPES.get(str(b.get('type', '')).strip())
        if kind is None:
            raise ValueError(f"binder {b.get('name')} : {b.get('type')} has no finite domain")
        p = by_name.get(b.get('name')) or (params[i] if i < len(params) else {})
        kinds.append(kind)
        per.append(binder_values(kind, p.get('integer_type', '') or '', ints, strs) if kind != 'val' else None)
    vals = [i for i, k in enumerate(kinds) if k == 'val']
    lean_types = (fn or {}).get('lean_types') or []
    if any(i < len(lean_types) and lean_types[i].startswith('*') for i in vals):
        raise ValueError('a Val binder for a *varargs parameter: the recorded samples spread their '
                         'arguments, so it has no domain')
    if not vals:
        return kinds, product_capped(per, max(1, cap))
    # Val binders range jointly over the validated sample inputs (a receiver together with
    # the arguments it was called with), crossed with the finite scalar domains.
    rows = []
    for smp in (fn or {}).get('samples') or []:
        if len(smp) == len(binders):
            row = [smp[i] for i in vals]
            if row not in rows:
                rows.append(row)
    if not rows:
        raise ValueError('a Val binder needs sample inputs of the same arity (none recorded)')
    scalars = [i for i, k in enumerate(kinds) if k != 'val']
    combos = product_capped([rows[:MAX_SAMPLE_ROWS]] + [per[i] for i in scalars], max(1, cap))
    points = []
    for c in combos:
        point = [None] * len(binders)
        for i, v in zip(vals, c[0]):
            point[i] = v
        for i, v in zip(scalars, c[1:]):
            point[i] = v
        points.append(point)
    return kinds, points


# --- per-statement Lean text ---------------------------------------------------------

COMMAND_RE = re.compile(r'(^|\n)\s*(theorem|lemma|def|abbrev|axiom|instance|example|macro|syntax|elab|'
                        r'attribute|set_option|open|namespace|section|end|import|variable|opaque|@\[|#)', re.M)


def safe_term(text: str) -> bool:
    """A pre/post must be ONE term: balanced brackets outside string literals, no comment
    and no command keyword starting a line (it is spliced into generated Lean text)."""
    body = re.sub(r'"(?:[^"\\]|\\.)*"', '""', text or '')
    depth = 0
    for ch in body:
        depth += ch in '([{'
        depth -= ch in ')]}'
        if depth < 0:
            return False
    return depth == 0 and not COMMAND_RE.search(body) and '/-' not in body and '--' not in body


def tag_of(index: int, sid: str) -> str:
    return f's{index}_' + re.sub(r'[^A-Za-z0-9_]', '_', sid)[:48]


class Plan:
    def __init__(self, index, st: dict, fn: dict | None, translation: dict, cap: int):
        self.st, self.fn = st, fn
        self.id = st['id']
        self.tag = tag_of(index, st['id'])
        self.binders = st.get('binders') or []
        for part in ('pre', 'post'):
            if not safe_term(st.get(part) or 'true'):
                raise ValueError(f'{part} is not a single Lean term')
        for b in self.binders:
            if not re.fullmatch(r"[A-Za-z_][\w']*", str(b.get('name', ''))) or not safe_term(b.get('val', '')):
                raise ValueError(f'binder {b.get("name")!r} is malformed')
        self.names = [b['name'] for b in self.binders]
        self.kinds, self.points = domain(self.binders, fn, translation.get('language', ''), cap)
        self.types = [LEAN_TYPE_NAME[k] for k in self.kinds]
        vals = [b.get('val', '') for b in self.binders if b.get('val', '').strip()]
        self.call = (translation['call_template']
                     .replace('{name}', lean_str(schema.call_name(st)))
                     .replace('{args}', '[' + ', '.join(vals) + ']'))
        self.runtime = None            # [(point_index, desc, lean literal or None)]
        self.runtime_note = ''

    # binder list "(a : Int) (b : Int)"
    def sig(self) -> str:
        return ' '.join(f'({n} : {t})' for n, t in zip(self.names, self.types))

    def args_of(self, var: str) -> str:
        return ' '.join(a.replace('p', var, 1) for a in accessors(len(self.names)))

    def args_point(self, point) -> str:
        return ' '.join(lean_value(k, v) for k, v in zip(self.kinds, point))

    def app(self, fn_name, args) -> str:
        return f'{fn_name} {args}'.strip()

    def call_at(self, point) -> str:
        """The call with the point substituted (for reporting the model outcome)."""
        args = self.args_point(point)
        return f'(fun {self.sig()} => {self.call}) {args}' if self.names else self.call

    def defs(self) -> str:
        t, sig = self.tag, self.sig()
        own = ' '.join(self.names)
        return (f'def pre_{t} {sig} : Bool := ({self.st.get("pre") or "true"})\n'
                f'def post_{t} {sig} (r : EResult) : Bool := ({self.st["post"]})\n'
                f'def chk_{t} {sig} : Bool := !({self.app("pre_" + t, own)}) || '
                f'{self.app("post_" + t, own)} ({self.call})\n')

    def dom_def(self) -> str:
        items = ', '.join(tuple_lit(self.kinds, p) for p in self.points)
        return f'def dom_{self.tag} : List ({tuple_type(self.kinds)}) := [{items}]\n'

    def rt_rows(self):
        return [(i, lit) for i, _, lit in (self.runtime or []) if lit is not None]

    def rt_def(self) -> str:
        rows = ', '.join(f'({tuple_lit(self.kinds, self.points[i])}, {lit})' for i, lit in self.rt_rows())
        return f'def rt_{self.tag} : List (({tuple_type(self.kinds)}) × EResult) := [{rows}]\n'

    def pass1(self) -> tuple[str, str]:
        """(definitions, checks). Errors inside the definitions mean the statement does not
        elaborate in the check context; errors in the checks are expected refutations."""
        t = self.tag
        defs = self.defs() + self.dom_def() + (self.rt_def() if self.rt_rows() else '')
        chk = self.app('chk_' + t, self.args_of('p'))
        pre = self.app('pre_' + t, self.args_of('p'))
        checks = [
            f'#eval IO.println ("AUTOFORM_CE {t} " ++ toString ((dom_{t}).findIdx? (fun p => !({chk}))))',
            f'#eval IO.println ("AUTOFORM_PRE {t} " ++ toString (((dom_{t}).filter (fun p => {pre})).length))',
        ]
        if self.rt_rows():
            qa = self.args_of('q.1')
            qpre, qpost = self.app('pre_' + t, qa), self.app('post_' + t, qa)
            checks += [
                f'#eval IO.println ("AUTOFORM_RT {t} " ++ toString ((rt_{t}).findIdx? '
                f'(fun q => !(!({qpre}) || {qpost} q.2))))',
                f'#eval IO.println ("AUTOFORM_RTPRE {t} " ++ toString (((rt_{t}).filter (fun q => {qpre})).length))',
            ]
        checks += [
            f'theorem bounded_{t} : (dom_{t}).all (fun p => {chk}) = true := by\n  decide +kernel',
            f'#print axioms bounded_{t}',
            f'theorem nonvac_{t} : (dom_{t}).any (fun p => {pre}) = true := by\n  decide +kernel',
            f'#print axioms nonvac_{t}',
        ]
        return defs, '\n'.join(checks) + '\n'

    def pass2(self, model_ce: int | None, rt_ce: int | None) -> str:
        t = self.tag
        out = [self.defs()]
        for which, idx in (('model', model_ce), ('runtime', rt_ce)):
            if idx is None:
                continue
            point = self.points[idx]
            args = self.args_point(point)
            if which == 'model':
                out.append(f'theorem refute_{t} : {self.app("chk_" + t, args)} = false := by\n  decide +kernel\n'
                           f'#print axioms refute_{t}\n')
            else:
                lit = dict(self.rt_rows())[idx]
                out.append(f'theorem rtrefute_{t} : (!({self.app("pre_" + t, args)}) || '
                           f'{self.app("post_" + t, args)} ({lit})) = false := by\n  decide +kernel\n'
                           f'#print axioms rtrefute_{t}\n')
            out.append(f'#eval IO.println ("AUTOFORM_OUTCOME {which} {t} " ++ '
                       f'(Lean.toJson (toString (repr ({self.call_at(point)})))).compress)\n')
        return '\n'.join(out)


def header(module) -> str:
    """`module` is the Translation (its call_template decides the imports, see
    schema.lean_imports: an AI model imports Autoform.NLModel.<M>) or a deep module suffix."""
    mods = schema.lean_imports(module) if isinstance(module, dict) else [f'Autoform.Generated.{module}']
    opens = schema.lean_opens(module) if isinstance(module, dict) else ''
    return (''.join(f'import {m}\n' for m in mods) + 'import Lean.Data.Json\n'
            'set_option autoImplicit false\nset_option maxRecDepth 100000\n'
            'set_option maxHeartbeats 4000000\nset_option linter.all false\nset_option maxErrors 100000\n'
            'open Autoform.Core\n' + opens + '\n')


def assemble(module, blocks: list) -> tuple[str, dict]:
    """blocks: [(tag, defs, checks)] → (text, {tag: (defs_first, defs_last, block_last)}).
    `module`: the Translation or a deep module suffix (see `header`)."""
    lines = header(module).splitlines()
    spans = {}
    for tag, defs, checks in blocks:
        lines.append(f'-- {tag}')
        start = len(lines) + 1
        lines += defs.rstrip('\n').splitlines()
        end_defs = len(lines)
        lines += checks.rstrip('\n').splitlines() if checks else []
        spans[tag] = (start, end_defs, len(lines))
        lines.append('')
    return '\n'.join(lines) + '\n', spans


def errors_by_line(output: str, path: Path) -> list:
    out = []
    for m in re.finditer(r'^(.*?):(\d+):(\d+): error(?:\([^)]*\))?: (.*(?:\n(?!\S*:\d+:\d+: ).*)*)', output, re.M):
        if Path(m.group(1)).name == path.name:
            out.append((int(m.group(2)), m.group(4).strip()))
    return out


# --- runtime (CPython) -----------------------------------------------------------

RUNNER = r'''
import contextlib, importlib.util, io, json, os, signal, sys
path, name, root, per = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
points = json.loads(sys.stdin.read())
for d in (root, os.path.dirname(path)):
    if d and d not in sys.path:
        sys.path.insert(0, d)
try:
    sys.set_int_max_str_digits(0)
except AttributeError:
    pass
class _Deadline(BaseException):
    pass
def _alarm(*_):
    raise _Deadline()
signal.signal(signal.SIGALRM, _alarm)
sink = io.StringIO()
with contextlib.redirect_stdout(sink):
    spec = importlib.util.spec_from_file_location("autoform_subject", path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["autoform_subject"] = mod
    spec.loader.exec_module(mod)
f = getattr(mod, name)
out = []
for args in points:
    signal.alarm(per)
    try:
        with contextlib.redirect_stdout(sink):
            v = f(*args)
        signal.alarm(0)
        if v is None:
            out.append({"kind": "value", "type": "NoneType"})
        elif isinstance(v, (bool, int, str)) and type(v) in (bool, int, str):
            out.append({"kind": "value", "type": type(v).__name__, "value": v})
        else:
            out.append({"kind": "value", "type": type(v).__name__, "repr": repr(v)[:200]})
    except _Deadline:
        out.append({"kind": "timeout"})
    except BaseException as exc:
        signal.alarm(0)
        out.append({"kind": "exception", "type": type(exc).__name__})
    sink.seek(0); sink.truncate()
print("AUTOFORM_RUNTIME " + json.dumps(out))
'''


RECEIVER_KINDS = ('method', 'property', 'constructor')


def runtime_target(translation: dict, fn: dict | None):
    """(path, qualified name within the module) of a real Python function, method or
    constructor, or (None, reason)."""
    if (translation.get('language') or '').lower() != 'python':
        return None, f"runtime check supports Python only; language is {translation.get('language')!r}"
    if fn is None:
        return None, 'function not in the translation'
    qual = fn.get('name', '')
    local = qual.split('<module>.', 1)[-1] if '<module>.' in qual else fn.get('source_name', '')
    kind = fn.get('kind') or 'function'
    if not fn.get('source_name') or not str(fn.get('file', '')).endswith('.py') or \
            ('.' in local and kind not in RECEIVER_KINDS + ('static',)):
        return None, 'runtime check supports top-level Python functions and modelled methods only'
    path = Path(translation.get('source_root', '')) / fn['file']
    if not path.is_file():
        return None, f'source file {path} not found'
    return path, local


def python_point(plan: Plan, point):
    """The point as pyvalues tags, one per binder passed to the call, or None."""
    tags = []
    by_name = dict(zip(plan.names, zip(plan.kinds, point)))
    for b in plan.binders:
        val = (b.get('val') or '').strip()
        if not val:
            continue
        if val == b.get('name') and by_name.get(val, ('',))[0] == 'val':
            tags.append(by_name[val][1])
            continue
        m = VAL_RE.match(val)
        if not m or m.group(2) not in by_name:
            return None
        ctor, (kind, v) = m.group(1), by_name[m.group(2)]
        if {'int': ('int', 'nat'), 'bool': ('bool',), 'str': ('str',)}[ctor].count(kind) == 0:
            return None
        tags.append(pv.tag(v))
    return tags


def python_args(plan: Plan, point):
    """Positional Python arguments in the order the binders are passed, or None."""
    tags = python_point(plan, point)
    return None if tags is None else [pv.untag(t) for t in tags]


def run_runtime(translation: dict, fn: dict | None, plan: Plan, timeout=RUNTIME_TIMEOUT, work: Path | None = None):
    path, qual = runtime_target(translation, fn)
    if path is None:
        plan.runtime_note = qual
        return
    calls = [python_point(plan, p) for p in plan.points]
    if any(c is None for c in calls):
        plan.runtime_note = 'binder `val`s are not plain .int/.bool/.str of a binder (or a Val binder); runtime check skipped'
        return
    from . import model as M
    root = Path(translation.get('source_root', '')).resolve()
    import_root, dotted = M._package_info(root, path.resolve())
    classes = [fn['receiver']] if fn.get('receiver') else []
    cfg = M.runner_config(import_root, dotted, path.resolve(), qual, fn.get('kind') or 'function', classes)
    cfg['per'] = POINT_TIMEOUT
    with tempfile.TemporaryDirectory() as tmp:
        descs, err = M.run_points(cfg, calls, Path(work) if work else Path(tmp), f'rt_{plan.tag}',
                                  cwd=import_root, timeout=timeout)
    if err:
        plan.runtime_note = 'runtime runner failed: ' + err[-400:]
        return
    post = plan.st.get('entry') == 'post'
    out = []
    for i, d in enumerate(descs):
        if not post:
            d = {k: v for k, v in d.items() if k != 'post'}
        elif d.get('k') == 'ok' and 'post' not in d:
            d = {'k': 'no-post'}
        lit = pv.lean_outcome(d)
        out.append((i, d, lit[1:-1] if lit else None))
    plan.runtime = out


# --- per-function driver ---------------------------------------------------------------

def _marker(out, key, tag):
    m = re.search(rf'^AUTOFORM_{key} {re.escape(tag)} (.*)$', out, re.M)
    return m.group(1).strip() if m else None


def _idx(text):
    if text is None:
        return 'missing'
    m = re.search(r'some (\d+)', text)
    return int(m.group(1)) if m else None


def check_function(translation, fn, plans, work: Path, lean_root: Path, runtime: bool, stem: str) -> dict:
    """All statements of one function: one pass-1 Lean run, at most one pass-2 run."""
    module = translation   # header() derives the imports from the call_template
    started = time.time()
    if runtime:
        for p in plans:
            run_runtime(translation, fn, p, work=work / 'runtime')
    else:
        for p in plans:
            p.runtime_note = 'runtime check disabled'
    blocks = [(p.tag, *p.pass1()) for p in plans]
    text, spans = assemble(module, blocks)
    f1 = work / f'{stem}_check.lean'
    f1.write_text(text)
    code, out, secs = run_lean(lean_root, f1, LEAN_TIMEOUT)
    if code == 124 and len(plans) > 1:
        # one expensive statement must not sink its neighbours: retry them one by one
        res = {}
        for k, p in enumerate(plans):
            res.update(check_function(translation, fn, [p], work, lean_root, runtime, f'{stem}_{k}'))
        return res
    axioms = axioms_of(out)
    errs = errors_by_line(out, f1)
    results, pending = {}, {}
    for p in plans:
        r = schema.CheckResult(statement=p.id, status='ERROR', domain_size=len(p.points))
        results[p.id] = r
        notes = [f'lean file {f1}', f'{secs}s']
        a, b, _ = spans[p.tag]
        def_errs = [msg for line, msg in errs if a <= line <= b]
        if code == 124:
            r.detail = f'Lean exceeded {LEAN_TIMEOUT}s on {f1}'
            continue
        if def_errs:
            r.detail = 'statement does not elaborate in the check context: ' + def_errs[0][:600]
            continue
        ce = _idx(_marker(out, 'CE', p.tag))
        npre = _marker(out, 'PRE', p.tag)
        if ce == 'missing' or npre is None:
            r.detail = f'model search produced no result (Lean exit {code}): ' + out[-600:]
            continue
        bounded = certified(f'bounded_{p.tag}', axioms)
        nonvac = certified(f'nonvac_{p.tag}', axioms)
        r.kernel_bounded_proof = bounded and nonvac
        rt_ce = None
        if p.rt_rows():
            rt_ce_pos = _idx(_marker(out, 'RT', p.tag))
            rt_npre = _marker(out, 'RTPRE', p.tag)
            if rt_ce_pos == 'missing':
                p.runtime_note = 'runtime evaluation produced no result'
            else:
                rows = p.rt_rows()
                rt_ce = rows[rt_ce_pos][0] if isinstance(rt_ce_pos, int) else None
                if rt_ce is not None:
                    r.runtime_agrees = False
                elif rt_npre and int(rt_npre) > 0:
                    r.runtime_agrees = True
                else:
                    p.runtime_note = 'no encodable real execution satisfies the precondition'
        skipped = sum(1 for _, _, lit in (p.runtime or []) if lit is None)
        if p.runtime is not None:
            notes.append(f'runtime: {len(p.rt_rows())} real executions encoded, {skipped} skipped '
                         f'(no faithful EResult literal)')
        if p.runtime_note:
            notes.append('runtime: ' + p.runtime_note)
        notes.append(f'{npre}/{len(p.points)} domain points satisfy pre')
        r._notes, r._ce, r._rt_ce, r._bounded, r._nonvac = notes, ce, rt_ce, bounded, nonvac
        if ce is not None or rt_ce is not None:
            pending[p.id] = p
    out2, ax2, f2 = '', {}, None
    if pending:
        f2 = work / f'{stem}_refute.lean'
        text2, _ = assemble(module, [(p.tag, p.pass2(results[p.id]._ce, results[p.id]._rt_ce), '')
                                     for p in pending.values()])
        f2.write_text(text2)
        code2, out2, secs2 = run_lean(lean_root, f2, LEAN_TIMEOUT)
        ax2 = axioms_of(out2)
    for p in plans:
        r = results[p.id]
        if not hasattr(r, '_notes'):
            continue
        notes, ce, rt_ce = r._notes, r._ce, r._rt_ce
        if p.id in pending:
            notes.append(f'refutation file {f2}')
        model_ok = ce is not None and certified(f'refute_{p.tag}', ax2)
        rt_ok = rt_ce is not None and certified(f'rtrefute_{p.tag}', ax2)
        if model_ok or rt_ok:
            idx = ce if model_ok else rt_ce
            outcome = _json_marker(out2, 'model' if model_ok else 'runtime', p.tag)
            rt_desc = next((d for i, d, _ in (p.runtime or []) if i == idx), None)
            r.counterexample = dict(inputs=dict(zip(p.names, p.points[idx])), model=outcome,
                                    runtime=describe_outcome(rt_desc) if p.runtime is not None
                                    else 'not run: ' + (p.runtime_note or 'runtime check unavailable'))
            if model_ok and rt_ok and rt_ce != ce:
                r.counterexample['runtime_counterexample'] = dict(
                    inputs=dict(zip(p.names, p.points[rt_ce])),
                    model=_json_marker(out2, 'runtime', p.tag),
                    runtime=describe_outcome(next((d for i, d, _ in p.runtime if i == rt_ce), None)))
        if model_ok:
            r.status = 'REFUTED_MODEL'
            notes.insert(0, f'kernel-certified counterexample refute_{p.tag}')
            if r.runtime_agrees is False:
                notes.insert(1, 'the statement also fails on a real execution')
        elif ce is not None:
            r.status = 'ERROR'
            notes.insert(0, 'compiled search found a failing point the kernel does not confirm '
                            '(evaluator/kernel disagreement)')
        elif rt_ok:
            r.status = 'REFUTED_RUNTIME'
            notes.insert(0, f'the statement holds on the model over the domain but fails on a real '
                            f'CPython execution (certified rtrefute_{p.tag}): the model and the program '
                            f'disagree at this point')
        elif rt_ce is not None:
            r.status = 'ERROR'
            notes.insert(0, 'runtime search found a failing execution the kernel does not confirm')
        elif r._bounded and r._nonvac:
            r.status = 'BOUNDED_HOLDS'
            notes.insert(0, f'bounded_{p.tag} kernel-checked over {len(p.points)} points (standard axioms)')
        elif r._bounded:
            r.status = 'UNCHECKABLE'
            notes.insert(0, 'vacuous: no domain point satisfies the precondition')
        else:
            r.status = 'ERROR'
            notes.insert(0, 'no counterexample found but the bounded theorem was not accepted')
        r.detail = '; '.join(notes)
        for k in ('_notes', '_ce', '_rt_ce', '_bounded', '_nonvac'):
            delattr(r, k)
    elapsed = round(time.time() - started, 2)
    for r in results.values():
        r.detail = (r.detail + f'; function checked in {elapsed}s').lstrip('; ')
    return results


def _json_marker(out, which, tag):
    m = re.search(rf'^AUTOFORM_OUTCOME {which} {re.escape(tag)} (".*")$', out, re.M)
    try:
        return json.loads(m.group(1)) if m else ''
    except json.JSONDecodeError:
        return ''


def check(translation: dict, statements: list, out_dir: Path, *, domain_size=64, runtime=True,
          lean_root: Path | str | None = None) -> list:
    """Check every statement; write out_dir/checks.json; return [schema.CheckResult].

    `lean_root` defaults to translation['lean_root'] (the lake project holding the built
    model module)."""
    out_dir = Path(out_dir)
    work = out_dir / 'check'
    work.mkdir(parents=True, exist_ok=True)
    root = Path(lean_root or translation['lean_root'])
    fns = {f['name']: f for f in translation.get('functions', [])}
    statements = [s if isinstance(s, dict) else asdict(s) for s in statements]
    results: dict = {}
    groups: dict = {}
    for i, st in enumerate(statements):
        sid = st.get('id', f'#{i}')
        if not st.get('elaborates'):
            results[sid] = schema.CheckResult(sid, 'UNCHECKABLE', detail='statement did not elaborate')
            continue
        if st.get('function') not in fns:
            results[sid] = schema.CheckResult(sid, 'ERROR', detail=f"function {st.get('function')!r} "
                                                                  f"is not in the translation")
            continue
        try:
            plan = Plan(i, st, fns[st['function']], translation, domain_size)
        except (ValueError, KeyError) as exc:
            results[sid] = schema.CheckResult(sid, 'UNCHECKABLE', detail=f'not checkable: {exc}')
            continue
        groups.setdefault(st['function'], []).append(plan)

    def job(item):
        k, (fname, plans) = item
        stem = f'f{k}_' + re.sub(r'[^A-Za-z0-9_]', '_', fns[fname].get('source_name') or fname)[:40]
        try:
            return check_function(translation, fns[fname], plans, work, root, runtime, stem)
        except Exception as exc:          # noqa: BLE001 - one function's failure is reported, not fatal
            return {p.id: schema.CheckResult(p.id, 'ERROR', len(p.points), detail=f'checker error: {exc!r}')
                    for p in plans}

    with ThreadPoolExecutor(max_workers=MAX_PARALLEL) as pool:
        for res in pool.map(job, enumerate(groups.items())):
            results.update(res)
    ordered = [results[s.get('id', f'#{i}')] for i, s in enumerate(statements)]
    schema.dump(ordered, out_dir / schema.FILES['checks'])
    return ordered


def main(argv=None):
    import argparse
    ap = argparse.ArgumentParser(description='autoform nl check stage')
    ap.add_argument('run_dir', type=Path)
    ap.add_argument('--translation', type=Path)
    ap.add_argument('--statements', type=Path)
    ap.add_argument('--domain-size', type=int, default=64)
    ap.add_argument('--no-runtime', action='store_true')
    ap.add_argument('--lean-root', type=Path)
    a = ap.parse_args(argv)
    tr = schema.load(a.translation or a.run_dir / schema.FILES['translation'])
    sts = schema.load(a.statements or a.run_dir / schema.FILES['statements'])
    t0 = time.time()
    res = check(tr, sts, a.run_dir, domain_size=a.domain_size, runtime=not a.no_runtime, lean_root=a.lean_root)
    for r in res:
        print(f'{r.status:16} {r.statement}  runtime_agrees={r.runtime_agrees}')
    print(f'{len(res)} statements in {time.time() - t0:.1f}s -> {a.run_dir / schema.FILES["checks"]}')


if __name__ == '__main__':
    main()
