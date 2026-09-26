"""Canonical Program IR (CPIR) built from the Core AST (`ast-<Module>.json`).

The Core AST is already the verifier's input: `render_lean.py` prints it as the
`Autoform.Core.Program` term that `runFunc` interprets. CPIR does not replace it;
it indexes it. Every entity the rest of the harness may mention (function,
parameter, statement block, call site, global, external callee) receives a
deterministic identifier, so generated claims can only refer to things that exist.

Identifiers are assigned in a canonical order (functions sorted by qualified name,
parameters by position, blocks by pre-order traversal). The same AST therefore
always yields the same `F_0001`, `V_0003`, `B_0012`.
"""
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field, asdict
from pathlib import Path

STATEMENTS = {'assign', 'seq', 'ifte', 'loop', 'forIn', 'ret', 'raise', 'exprS', 'skip', 'brk',
              'cont', 'breakBlock', 'tryCatch', 'tryFinally', 'setGlobal', 'setField', 'setIndex',
              'setSlice', 'setDerefIref', 'del', 'delIndex', 'delSlice', 'declGlobal', 'holeS'}
WRITES = {'setGlobal': 'global', 'setField': 'field', 'setIndex': 'index', 'setSlice': 'slice',
          'setDerefIref': 'reference', 'del': 'binding', 'delIndex': 'index', 'delSlice': 'slice'}
COMPARISONS = {'==', '!=', '<', '<=', '>', '>='}
# Integer widths recorded by the C-family front ends, used to pick boundary witnesses.
WIDTHS = {'i8': 8, 'i16': 16, 'i32': 32, 'i64': 64, 'int8_t': 8, 'char': 8, 'signed char': 8, 'short': 16, 'int16_t': 16, 'int': 32,
          'int32_t': 32, 'long': 64, 'long long': 64, 'int64_t': 64, 'ssize_t': 64}
UWIDTHS = {'u8': 8, 'u16': 16, 'u32': 32, 'u64': 64, 'uint8_t': 8, 'unsigned char': 8, 'uint16_t': 16, 'unsigned short': 16,
           'unsigned': 32, 'unsigned int': 32, 'uint32_t': 32, 'size_t': 64,
           'unsigned long': 64, 'uint64_t': 64, 'unsigned long long': 64}


def sha256(value) -> str:
    data = value if isinstance(value, bytes) else json.dumps(value, sort_keys=True,
                                                               ensure_ascii=False).encode()
    return 'sha256:' + hashlib.sha256(data).hexdigest()


@dataclass
class Param:
    id: str
    name: str
    index: int
    sort: str            # int | bool | str | float | any
    integer_type: str = ''


@dataclass
class Block:
    id: str
    kind: str
    path: str            # structural path inside the function body, e.g. body.a.t
    hole: bool = False


@dataclass
class Branch:
    block: str
    condition: dict      # Core expression over locals/params
    params: list         # parameter names the condition mentions


@dataclass
class CallSite:
    block: str
    callee: str
    resolved: str | None     # F_ id when the callee is in the program
    order: int               # pre-order position, for ordering claims


@dataclass
class Function:
    id: str
    name: str
    source_name: str
    file: str
    params: list
    return_sort: str
    blocks: list = field(default_factory=list)
    branches: list = field(default_factory=list)
    calls: list = field(default_factory=list)
    writes: list = field(default_factory=list)
    reads_globals: list = field(default_factory=list)
    raises: list = field(default_factory=list)
    holes: list = field(default_factory=list)
    literals: dict = field(default_factory=dict)
    semantics_hash: str = ''
    synthetic: bool = False
    return_integer_type: str = ''
    arith: list = field(default_factory=list)   # binops over parameters: {op, a, b}

    def param(self, pid):
        return next((p for p in self.params if p.id == pid), None)


def integer_range(integer_type: str):
    if integer_type in WIDTHS:
        w = WIDTHS[integer_type]
        return -(2 ** (w - 1)), 2 ** (w - 1) - 1
    if integer_type in UWIDTHS:
        return 0, 2 ** UWIDTHS[integer_type] - 1
    return None


def _sort_of(type_name: str, integer_type: str) -> str:
    t = (type_name or '').lower()
    if integer_type or t in ('int', '__builtin.int', 'long', 'short') or t in WIDTHS or t in UWIDTHS:
        return 'int'
    if t in ('bool', '__builtin.bool', '_bool', 'boolean'):
        return 'bool'
    if t in ('str', '__builtin.str', 'string', 'java.lang.string'):
        return 'str'
    if t in ('float', 'double', '__builtin.float'):
        return 'float'
    return 'any'


def _base_op(op: str):
    """`num:c:i64:+` → ('+', 'i64'); plain operators carry no width."""
    if op.startswith('num:'):
        parts = op.split(':')
        return parts[-1], parts[2] if len(parts) >= 4 else ''
    return op, ''


def _names(expr) -> set:
    found = set()
    stack = [expr]
    while stack:
        node = stack.pop()
        if isinstance(node, dict):
            if node.get('k') == 'name' and isinstance(node.get('v'), str):
                found.add(node['v'])
            stack.extend(v for k, v in node.items() if k != 'k')
        elif isinstance(node, list):
            stack.extend(node)
    return found


class Program:
    """CPIR for one translated module."""

    def __init__(self, module: str, functions: list, ast_hash: str, source: str | None = None):
        self.module = module
        self.functions = functions
        self.ast_hash = ast_hash
        self.source = source
        self.by_id = {f.id: f for f in functions}
        self.by_name = {f.name: f for f in functions}
        self.entities = {}
        for f in functions:
            self.entities[f.id] = ('function', f)
            for p in f.params:
                self.entities[p.id] = ('param', p)
            for b in f.blocks:
                self.entities[b.id] = ('block', b)

    # --- graph queries ------------------------------------------------------
    def callers(self, fid: str) -> list:
        return sorted({f.id for f in self.functions for c in f.calls if c.resolved == fid})

    def callees(self, fid: str) -> list:
        return sorted({c.resolved for c in self.by_id[fid].calls if c.resolved})

    def closure(self, fid: str) -> list:
        seen, stack = set(), [fid]
        while stack:
            cur = stack.pop()
            if cur in seen:
                continue
            seen.add(cur)
            stack.extend(self.callees(cur))
        return sorted(seen)

    def externals(self, fid: str) -> list:
        return sorted({c.callee for c in self.by_id[fid].calls if not c.resolved})

    def coverage(self, fid: str, environment=None) -> dict:
        f = self.by_id[fid]
        externals = self.externals(fid)
        classes = {}
        for name in externals:
            summary = environment.summary(name) if environment else None
            cls = summary['semantics'] if summary else 'UNSUPPORTED'
            classes[cls] = classes.get(cls, 0) + 1
        total = len(f.blocks)
        modeled = total - len(f.holes)
        fully = classes.get('INLINE', 0) + classes.get('MODELED', 0)
        abstracted = classes.get('UNINTERPRETED', 0) + classes.get('NONDETERMINISTIC', 0)
        unknown = classes.get('UNSUPPORTED', 0)
        block_ratio = modeled / total if total else 1.0
        ext_ratio = (fully + 0.5 * abstracted) / len(externals) if externals else 1.0
        return dict(function=f.name, code_blocks_total=total, code_blocks_modeled=modeled,
                    external_calls_total=len(externals),
                    external_calls=dict(fully_modeled=fully, abstracted=abstracted, unknown=unknown),
                    concurrency=dict(modeled=False),
                    confidence=round(block_ratio * ext_ratio, 3))

    def entity_table(self) -> list:
        rows = []
        for f in self.functions:
            rows.append(dict(id=f.id, kind='function', name=f.name, file=f.file))
            rows += [dict(id=p.id, kind='param', name=p.name, function=f.id, sort=p.sort,
                          integer_type=p.integer_type) for p in f.params]
        return rows

    def to_json(self) -> dict:
        return dict(schema_version=1, module=self.module, ast_hash=self.ast_hash,
                    functions=[asdict(f) for f in self.functions])


class _Walker:
    def __init__(self, fn: Function, counter, names: dict):
        self.fn, self.counter, self.names = fn, counter, names
        self.order = 0

    def block(self, kind, path, hole=False):
        bid = 'B_%04d' % next(self.counter)
        self.fn.blocks.append(Block(bid, kind, path, hole))
        if hole:
            self.fn.holes.append(bid)
        return bid

    def expr(self, node, path, owner):
        stack = [(node, path)]
        while stack:
            cur, where = stack.pop()
            if isinstance(cur, list):
                stack.extend((v, f'{where}[{i}]') for i, v in reversed(list(enumerate(cur))))
                continue
            if not isinstance(cur, dict):
                continue
            k = cur.get('k')
            if k in ('call', 'callV', 'mcall'):
                callee = cur.get('f') if k == 'call' else (
                    '.' + cur.get('m', '?') if k == 'mcall' else '<dynamic>')
                if not isinstance(callee, str):
                    callee = '<dynamic>'
                self.order += 1
                target = self.names.get(callee)
                self.fn.calls.append(CallSite(owner, callee, target, self.order))
            elif k == 'name' and cur.get('v') not in {p.name for p in self.fn.params}:
                if isinstance(cur.get('v'), str) and cur['v'] not in self.fn.reads_globals:
                    self.fn.reads_globals.append(cur['v'])
            elif k == 'hole':
                self.fn.holes.append(owner)
            elif k == 'binop' and isinstance(cur.get('op'), str) and \
                    _base_op(cur['op'])[0] in ('+', '-', '*', '<<', '>>', '>>>', '/', '//', '%'):
                params = {p.name for p in self.fn.params}
                sides = []
                for side in (cur.get('a'), cur.get('b')):
                    if isinstance(side, dict) and side.get('k') == 'name' and side.get('v') in params:
                        sides.append(side['v'])
                    elif isinstance(side, dict) and side.get('k') == 'int' and type(side.get('v')) is int:
                        sides.append(side['v'])
                if len(sides) == 2 and any(isinstance(x, str) for x in sides):
                    base, itype = _base_op(cur['op'])
                    entry = dict(op=base, a=sides[0], b=sides[1], type=itype)
                    if entry not in self.fn.arith:
                        self.fn.arith.append(entry)
            elif k in ('int', 'str', 'bool') and 'v' in cur:
                self.fn.literals.setdefault(k, [])
                if cur['v'] not in self.fn.literals[k]:
                    self.fn.literals[k].append(cur['v'])
            stack.extend((v, f'{where}.{key}') for key, v in cur.items() if key != 'k')

    def stmt(self, node, path='body'):
        stack = [(node, path)]
        while stack:
            cur, where = stack.pop()
            if not isinstance(cur, dict):
                continue
            k = cur.get('k')
            if k == 'seq':
                stack.append((cur.get('b'), where + '.b'))
                stack.append((cur.get('a'), where + '.a'))
                continue
            bid = self.block(k, where, hole=k == 'holeS')
            if k in WRITES:
                target = cur.get('x') if k in ('setGlobal', 'del') else cur.get('f', k)
                self.fn.writes.append(dict(block=bid, kind=WRITES[k], target=str(target)))
            if k == 'raise':
                self.fn.raises.append(bid)
            if k in ('ifte', 'loop'):
                params = sorted(_names(cur.get('c')) & {p.name for p in self.fn.params})
                self.fn.branches.append(Branch(bid, cur.get('c'), params))
            for key, value in cur.items():
                if key == 'k':
                    continue
                if key in ('t', 'e', 'body', 'handler', 'fin') and isinstance(value, dict) \
                        and value.get('k') in STATEMENTS:
                    stack.append((value, f'{where}.{key}'))
                else:
                    self.expr(value, f'{where}.{key}', bid)


def build(ast_path: Path | str, module: str, source: str | None = None) -> Program:
    raw = Path(ast_path).read_bytes()
    data = json.loads(raw)
    if not isinstance(data, list):
        raise ValueError('Core AST must be a list of functions')
    entries = sorted((f for f in data if isinstance(f, dict) and isinstance(f.get('name'), str)),
                     key=lambda f: f['name'])
    ids = {f['name']: 'F_%04d' % (i + 1) for i, f in enumerate(entries)}
    # Calls name functions by qualified name or by source name inside a module.
    names = dict(ids)
    for f in entries:
        if f.get('sourceName') and f['sourceName'] not in names:
            names[f['sourceName']] = ids[f['name']]
    vcount = iter(range(1, 10 ** 9))
    bcount = iter(range(1, 10 ** 9))
    functions = []
    for f in entries:
        types = f.get('paramTypes') or []
        itypes = f.get('paramIntegerTypes') or []
        params = [Param('V_%04d' % next(vcount), name, i,
                        _sort_of(types[i] if i < len(types) else '', itypes[i] if i < len(itypes) else ''),
                        itypes[i] if i < len(itypes) else '')
                  for i, name in enumerate(f.get('params') or [])]
        source_name = f.get('sourceName') or f['name'].rsplit('.', 1)[-1].rsplit(':', 1)[-1]
        fn = Function(ids[f['name']], f['name'], source_name, f.get('file', ''), params,
                      _sort_of(f.get('returnType', ''), f.get('returnIntegerType', '')),
                      synthetic=f['name'].startswith('<') or source_name.startswith('<'),
                      return_integer_type=f.get('returnIntegerType') or '')
        fn.semantics_hash = sha256(f.get('body'))
        _Walker(fn, bcount, names).stmt(f.get('body'))
        functions.append(fn)
    return Program(module, functions, sha256(raw), source)
