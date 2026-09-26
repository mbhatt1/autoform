"""Model stage: an AI-written plain Lean model of each function, validated against the real code.

    discover(source_root)                 -> [FunctionInfo]      (Python `ast`, no Joern)
    model(source_root, out_dir, lean_root) -> Translation        (+ models.json, Lean module)

This is the main path of the natural-language autoformalizer. Instead of interpreting a
Joern AST in Lean, a language model translates each function into an ordinary Lean `def`
(`Int` for Python int, `Except String τ` for raising code, ...). Nothing it writes is
trusted:

  1. Translation A (via English): the model first states precisely what the function
     computes, then writes the Lean `def` (callees are translated first and offered to it).
  2. Dispatcher: this module — not the model — generates the glue
         call : String → List Val → EResult
     that decodes the `Val` arguments into the def's parameter types (a value of the wrong
     shape is `.hole "nl:arg-type"`, never coerced), runs the def and encodes the result
     (`.error "E"` becomes `.exn (.str "E")`). Everything is structurally recursive, so the
     kernel evaluates `call` on concrete arguments (`decide +kernel`), which the check
     stage relies on; a few kernel evaluations per function are checked here.
  3. Differential validation: the inputs are the argument tuples observed while the
     repository's own tests run under a tracer, plus typed boundary values for the Lean
     parameter types. The REAL function runs on them in CPython (subprocess, timeouts) and
     the Lean model runs on them with one batched `#eval`; outcomes are compared exactly
     (ints, bools, strs, None, floats by bits, tuples/lists/dicts, exception class names).
     Points whose inputs or outputs have no faithful encoding are skipped and counted.
     Disagreements are shown to the model as concrete counterexamples, up to `repairs`
     rounds.
  4. Translation B: an independent translation straight from the code (different prompt,
     no English step) is run on the same inputs and compared with A.

The result is a normal `Translation` whose call_template is
`Autoform.NLModel.<M>.call {name} {args}`, so describe/formalize/check/prove run on it
unchanged: they import the modules `schema.lean_imports` derives from the call_template
(`Autoform.NLModel.<M>`; there is no `Autoform.Generated.<M>` for a model, so a deep
translation of the same repository can coexist under the same module name). The module is
written to `Autoform/NLModel/<M>.lean` under the Lean root (a per-run build product, not
tracked) and built with `lake build Autoform.NLModel.<M>`; every recorded input is then
re-run through the built module as a final consistency check.

Trust: a VALIDATED model agreed with CPython on every one of `tests_run` inputs; `level`
L0 additionally requires that translation B did not disagree. Proofs downstream are about
the model, and the model is only as good as that evidence.

    python -m autoform.nl.model <source> --out DIR [--function f ...] [--tests DIR]
"""
from __future__ import annotations

import ast
import json
import os
import re
import subprocess
import sys
import textwrap
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass, field
from pathlib import Path

from . import fuzz, llm, pyvalues as pv, schema
from .formalize import LEAN_SLOTS, lake

HERE = Path(__file__).resolve()
PYVALUES = HERE.with_name('pyvalues.py')
LEAN_TIMEOUT = 600
BUILD_TIMEOUT = 1800
TRACE_TIMEOUT = 900
RUNTIME_TIMEOUT = 300          # one CPython batch
POINT_TIMEOUT = 2.0            # one real call, seconds
TRACE_LIMIT = 120              # distinct traced argument tuples kept per function
MAX_POINTS = 240               # inputs per function (traced first, then boundary values)
BOUNDARY_CAP = 120
KERNEL_POINTS = 3              # `decide +kernel` evaluations checked per function
MAX_SHOWN = 8                  # counterexamples shown to the model in a repair round
SKIP_DIRS = {'.git', '.hg', '.svn', '__pycache__', '.lake', 'node_modules', '.venv', 'venv', '.tox',
             'build', 'dist', 'tests', 'test', 'docs', 'doc', '.eggs', 'site-packages'}

# ---------------------------------------------------------------- static purity screen

IMPURE_CALLS = {
    'open': 'file access', 'print': 'I/O (print)', 'input': 'I/O (input)', 'exec': 'dynamic code',
    'eval': 'dynamic code', 'compile': 'dynamic code', 'globals': 'reflection on globals',
    'locals': 'reflection', 'vars': 'reflection', 'setattr': 'attribute mutation',
    'delattr': 'attribute mutation', '__import__': 'dynamic import', 'id': 'object identity (id)',
    'hash': 'process-dependent hash()', 'breakpoint': 'debugger', 'exit': 'process exit',
    'quit': 'process exit', 'help': 'I/O', 'memoryview': 'buffer access',
}
IMPURE_MODULES = {
    'os': 'OS/file access', 'sys': 'interpreter state', 'time': 'time', 'random': 'randomness',
    'subprocess': 'subprocess', 'socket': 'network', 'shutil': 'file access', 'pathlib': 'file access',
    'datetime': 'time', 'uuid': 'randomness', 'secrets': 'randomness', 'threading': 'threads',
    'asyncio': 'async I/O', 'requests': 'network', 'urllib': 'network', 'http': 'network',
    'logging': 'logging I/O', 'io': 'I/O', 'tempfile': 'file access', 'glob': 'file access',
    'signal': 'signals', 'multiprocessing': 'processes', 'sqlite3': 'database', 'ctypes': 'native code',
    'select': 'I/O', 'fcntl': 'file access', 'platform': 'environment', 'getpass': 'environment',
    'webbrowser': 'I/O', 'smtplib': 'network', 'ftplib': 'network', 'warnings': 'warnings I/O',
    'atexit': 'process state', 'gc': 'interpreter state', 'importlib': 'dynamic import',
    'concurrent': 'threads', 'queue': 'threads', 'mmap': 'file access', 'resource': 'process state',
    'shelve': 'file access', 'dbm': 'file access', 'zipfile': 'file access', 'tarfile': 'file access',
    'gzip': 'file access', 'bz2': 'file access', 'lzma': 'file access', 'fileinput': 'file access',
    'weakref': 'object lifetime', 'inspect': 'reflection',
}
MUTATING_METHODS = {'append', 'extend', 'insert', 'pop', 'remove', 'clear', 'update', 'add', 'discard',
                    'setdefault', 'popitem', 'sort', 'reverse', 'write', '__setitem__', '__delitem__'}
PURE_DECORATORS = {'staticmethod', 'functools.lru_cache', 'lru_cache', 'functools.cache', 'cache'}


@dataclass
class _Module:
    rel: str
    path: Path
    text: str
    tree: ast.Module
    dotted: str | None                  # importable dotted name (None: load by path)
    import_root: Path
    imports: dict = field(default_factory=dict)   # alias -> ('module', dotted) | ('name', dotted, name)
    top_funcs: dict = field(default_factory=dict)  # name -> qualified function name
    globals: set = field(default_factory=set)     # module-level assigned names


@dataclass
class _Fn:
    info: schema.FunctionInfo
    node: ast.AST
    mod: _Module
    qual: str                           # "Class.meth" / "f"
    first_lines: list                   # def line and decorator lines (co_firstlineno candidates)
    reason: str | None = None           # why it is not attempted
    callees: list = field(default_factory=list)


def _mangle(name: str, cls: str | None) -> str:
    if cls is None or not name.startswith('__') or name.endswith('__'):
        return name
    return '_' + cls.lstrip('_') + name


def _package_info(root: Path, path: Path):
    """(import_root, dotted) for a file inside packages, else (dir, None)."""
    parts = [path.stem] if path.stem != '__init__' else []
    d = path.parent
    if not (d / '__init__.py').is_file():
        return d, None
    while (d / '__init__.py').is_file() and d != d.parent:
        parts.insert(0, d.name)
        d = d.parent
    return d, '.'.join(parts)


def _is_test_file(p: Path) -> bool:
    return p.name.startswith('test_') or p.name.endswith('_test.py') or p.name in ('conftest.py', 'setup.py')


def _source_files(root: Path) -> list:
    out = []
    for dirpath, dirs, files in os.walk(root):
        dirs[:] = sorted(d for d in dirs if d not in SKIP_DIRS and not d.startswith('.'))
        for f in sorted(files):
            p = Path(dirpath) / f
            if f.endswith('.py') and not _is_test_file(p):
                out.append(p)
    return out


def _dotted(node) -> str | None:
    parts = []
    while isinstance(node, ast.Attribute):
        parts.insert(0, node.attr)
        node = node.value
    if isinstance(node, ast.Name):
        return '.'.join([node.id] + parts)
    return None


def _resolve_relative(mod: _Module, level: int, name: str | None) -> str | None:
    if level == 0:
        return name
    if mod.dotted is None:
        return name
    pkg = mod.dotted.split('.')
    if not mod.path.name == '__init__.py':
        pkg = pkg[:-1]
    if level > 1:
        pkg = pkg[:len(pkg) - (level - 1)]
    return '.'.join(pkg + ([name] if name else []))


def _collect_imports(mod: _Module):
    for node in mod.tree.body:
        if isinstance(node, ast.Import):
            for a in node.names:
                if a.asname:
                    mod.imports[a.asname] = ('module', a.name)
                else:
                    mod.imports[a.name.split('.')[0]] = ('module', a.name.split('.')[0])
        elif isinstance(node, ast.ImportFrom):
            base = _resolve_relative(mod, node.level, node.module)
            for a in node.names:
                if a.name == '*':
                    continue
                mod.imports[a.asname or a.name] = ('name', base or '', a.name)
        elif isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            for t in targets:
                for n in ast.walk(t):
                    if isinstance(n, ast.Name):
                        mod.globals.add(n.id)


def _annotation_sort(ann) -> str:
    name = _dotted(ann) if ann is not None else None
    if isinstance(ann, ast.Constant) and isinstance(ann.value, str):
        name = ann.value
    return {'int': 'int', 'bool': 'bool', 'str': 'str', 'float': 'float'}.get(name or '', 'any')


def _params(node) -> list:
    a = node.args
    out = [schema.Param(x.arg, _annotation_sort(x.annotation)) for x in a.posonlyargs + a.args]
    if a.vararg:
        out.append(schema.Param(a.vararg.arg, 'any'))
    return out


def _segment(lines: list, node) -> str:
    start = min([node.lineno] + [d.lineno for d in node.decorator_list])
    return textwrap.dedent(''.join(lines[start - 1:node.end_lineno]))


def _parse_modules(root: Path) -> dict:
    mods = {}
    for p in _source_files(root):
        try:
            text = p.read_text(encoding='utf-8')
            tree = ast.parse(text, str(p))
        except (SyntaxError, UnicodeDecodeError, OSError, ValueError):
            continue
        rel = p.relative_to(root).as_posix()
        import_root, dotted = _package_info(root, p)
        mod = _Module(rel, p, text, tree, dotted, import_root)
        _collect_imports(mod)
        mods[rel] = mod
    return mods


def _walk_defs(mod: _Module):
    """Yield (node, qual, cls) for top-level functions and methods (recursively in classes)."""
    def visit(body, prefix, cls):
        for n in body:
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
                yield n, prefix + _mangle(n.name, cls), cls
            elif isinstance(n, ast.ClassDef):
                yield from visit(n.body, prefix + n.name + '.', n.name)
    yield from visit(mod.tree.body, '', None)


def _decorator_names(node) -> list:
    out = []
    for d in node.decorator_list:
        target = d.func if isinstance(d, ast.Call) else d
        out.append(_dotted(target) or ast.unparse(d))
    return out


def _local_names(node) -> set:
    names = {a.arg for a in node.args.posonlyargs + node.args.args + node.args.kwonlyargs}
    for a in (node.args.vararg, node.args.kwarg):
        if a:
            names.add(a.arg)
    for n in ast.walk(node):
        if isinstance(n, ast.Name) and isinstance(n.ctx, (ast.Store, ast.Del)):
            names.add(n.id)
        elif isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and n is not node:
            names.add(n.name)
        elif isinstance(n, ast.arg):
            names.add(n.arg)
        elif isinstance(n, ast.ExceptHandler) and n.name:
            names.add(n.name)
    return names


def _impure_module(mod: _Module, name: str) -> str | None:
    """The impure module a bare name refers to, if any."""
    imp = mod.imports.get(name)
    if not imp:
        return None
    target = imp[1]
    top = target.split('.')[0] if target else ''
    if top in IMPURE_MODULES:
        return top
    return None


def screen(node, mod: _Module, cls: str | None) -> str | None:
    """Why the function is not pure enough to model as a plain Lean def (None: attempt it)."""
    if isinstance(node, ast.AsyncFunctionDef):
        return 'async function (coroutine)'
    decos = _decorator_names(node)
    if cls is not None and 'staticmethod' not in decos:
        return 'method: the receiver object\'s state is not modelled'
    other = [d for d in decos if d not in PURE_DECORATORS]
    if other:
        return 'decorated by ' + ', '.join(other) + ' (the decorator changes its behaviour)'
    a = node.args
    if any(d is None for d in a.kw_defaults):
        return 'keyword-only parameters without defaults (cannot be called positionally)'
    local = _local_names(node)
    defaults = a.defaults + [d for d in a.kw_defaults if d is not None]
    for sub in [node.body] + [defaults]:
        for top in sub:
            for n in ast.walk(top):
                if isinstance(n, (ast.Yield, ast.YieldFrom)):
                    return 'generator (yield)'
                if isinstance(n, ast.Await):
                    return 'coroutine (await)'
                if isinstance(n, (ast.Global, ast.Nonlocal)):
                    return 'global/nonlocal mutation'
                if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    return 'defines a nested function (closure)'
                if isinstance(n, ast.ClassDef):
                    return 'defines a class'
                if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load) and n.id not in local:
                    bad = _impure_module(mod, n.id)
                    if bad:
                        return f'uses {bad} ({IMPURE_MODULES[bad]})'
                if isinstance(n, ast.Call):
                    f = n.func
                    if isinstance(f, ast.Name) and f.id in IMPURE_CALLS and f.id not in local \
                            and f.id not in mod.top_funcs and f.id not in mod.imports:
                        return f'calls {f.id}() ({IMPURE_CALLS[f.id]})'
                    if isinstance(f, ast.Attribute) and f.attr in MUTATING_METHODS \
                            and isinstance(f.value, ast.Name) and f.value.id not in local \
                            and (f.value.id in mod.globals or f.value.id in mod.imports):
                        return f'mutates module-level state ({f.value.id}.{f.attr})'
                if isinstance(n, (ast.Assign, ast.AugAssign, ast.AnnAssign, ast.Delete)):
                    targets = (n.targets if isinstance(n, (ast.Assign, ast.Delete)) else [n.target])
                    for t in targets:
                        if isinstance(t, (ast.Attribute, ast.Subscript)):
                            base = t.value
                            while isinstance(base, (ast.Attribute, ast.Subscript)):
                                base = base.value
                            if isinstance(base, ast.Name) and base.id not in local:
                                return f'mutates module-level state ({base.id})'
    return None


def _callees(node, mod: _Module, mods_by_dotted: dict, local: set) -> list:
    out = []
    for n in ast.walk(node):
        if not isinstance(n, ast.Call):
            continue
        target = None
        f = n.func
        if isinstance(f, ast.Name) and f.id not in local:
            if f.id in mod.top_funcs:
                target = mod.top_funcs[f.id]
            elif mod.imports.get(f.id, ('',))[0] == 'name':
                _, m, name = mod.imports[f.id]
                other = mods_by_dotted.get(m)
                if other is not None:
                    target = other.top_funcs.get(name)
        elif isinstance(f, ast.Attribute):
            dotted = _dotted(f)
            if dotted and dotted.split('.')[0] not in local:
                head, *rest = dotted.split('.')
                imp = mod.imports.get(head)
                if imp:
                    full = '.'.join(([imp[1]] if imp[0] == 'module' else [imp[1], imp[2]]) + rest)
                    mname, _, fname = full.rpartition('.')
                    other = mods_by_dotted.get(mname)
                    if other is not None:
                        target = other.top_funcs.get(fname)
        if target and target not in out:
            out.append(target)
    return out


def _test_dirs(root: Path, extra=()) -> list:
    dirs = [root / d for d in ('tests', 'test') if (root / d).is_dir()]
    dirs += [Path(d).resolve() for d in extra or () if Path(d).is_dir()]
    seen, out = set(), []
    for d in dirs:
        if d.resolve() not in seen:
            seen.add(d.resolve())
            out.append(d)
    return out


def _test_lines(test_dirs: list) -> list:
    """[(location, line text, file text)] of every test file line."""
    out = []
    for d in test_dirs:
        for p in sorted(Path(d).rglob('*.py')):
            try:
                text = p.read_text(encoding='utf-8')
            except (OSError, UnicodeDecodeError):
                continue
            loc_base = f'{Path(d).name}/{p.relative_to(d).as_posix()}'
            for i, line in enumerate(text.splitlines(), 1):
                out.append((f'{loc_base}:{i}', line, text))
    return out


def _tests_for(fn: _Fn, lines: list, limit: int = 12) -> list:
    name = fn.info.source_name
    stem = fn.mod.path.stem if fn.mod.path.stem != '__init__' else fn.mod.path.parent.name
    method = '.' in fn.qual
    call = re.compile((r'\.' if method else r'(?<![\w])') + re.escape(name) + r'\s*\(')
    ref = re.compile(r'(?<![\w])' + re.escape(stem) + r'\.' + re.escape(name) + r'\b')
    cls = fn.qual.split('.')[-2] if method else None
    if method and name.startswith('__') and name.endswith('__'):
        return []      # dunder methods are called through syntax, never by name
    out = []
    for loc, line, text in lines:
        if not (call.search(line) or ref.search(line)):
            continue
        if cls and not re.search(r'\b' + re.escape(cls) + r'\b', text):
            continue
        if re.match(r'\s*def\s', line):
            continue
        # precise: the test file must import the defining module (or the name itself)
        if not (re.search(r'\b' + re.escape(stem) + r'\b', text) and
                (re.search(r'\bimport\b.*\b' + re.escape(name) + r'\b', text) or ref.search(text)
                 or re.search(r'\bimport\b.*\b' + re.escape(stem) + r'\b', text))):
            continue
        out.append({'location': loc, 'text': line.strip()[:240]})
        if len(out) >= limit:
            break
    return out


def _discover(source_root: Path, functions=None, tests=()):
    root = Path(source_root).resolve()
    mods = _parse_modules(root)
    for mod in mods.values():
        for node, qual, cls in _walk_defs(mod):
            if cls is None:
                mod.top_funcs[node.name] = f'{mod.rel}:<module>.{qual}'
    by_dotted = {m.dotted: m for m in mods.values() if m.dotted}
    fns = []
    for mod in mods.values():
        lines = mod.text.splitlines(keepends=True)
        for node, qual, cls in _walk_defs(mod):
            name = f'{mod.rel}:<module>.{qual}'
            params = _params(node)
            if cls is not None and 'staticmethod' not in _decorator_names(node) and params:
                pass   # keep `self` as written: methods are listed, not attempted
            info = schema.FunctionInfo(
                name=name, source_name=node.name, file=mod.rel, line=node.lineno, params=params,
                returns=_annotation_sort(node.returns), hole_free=False, holes=[], call_closed=False,
                needs_init=False, source=_segment(lines, node), doc=ast.get_docstring(node) or '')
            fn = _Fn(info, node, mod, qual, [node.lineno] + [d.lineno for d in node.decorator_list])
            fn.reason = screen(node, mod, cls)
            fn.callees = _callees(node, mod, by_dotted, _local_names(node))
            fns.append(fn)
    by_name = {f.info.name: f for f in fns}
    for f in fns:
        for c in f.callees:
            if c in by_name and f.info.name not in by_name[c].info.callers:
                by_name[c].info.callers.append(f.info.name)
    # impurity is transitive through repository callees
    changed = True
    while changed:
        changed = False
        for f in fns:
            if f.reason:
                continue
            for c in f.callees:
                g = by_name.get(c)
                if g is not None and g.reason and not g.reason.startswith(('method', 'decorated')):
                    f.reason = f'calls {g.info.source_name}, which is not pure ({g.reason})'
                    changed = True
                    break
    lines = _test_lines(_test_dirs(root, tests))
    for f in fns:
        f.info.tests = _tests_for(f, lines)
    if functions:
        wanted = set(functions)
        fns = [f for f in fns if f.info.name in wanted or f.info.source_name in wanted or f.qual in wanted
               or f.info.file in wanted]
    for f in fns:
        f.info.hole_free = f.info.call_closed = f.reason is None
    return fns, mods


def discover(source_root: Path, *, functions=None, tests=()) -> list:
    """Every top-level function and method of a Python tree, as FunctionInfo.

    Functions the static screen accepts (no I/O, time, randomness, subprocess, network,
    file access, global mutation, generators, closures, receivers) get hole_free =
    call_closed = True; the others False (see `screen` for the reasons)."""
    return [f.info for f in _discover(source_root, functions, tests)[0]]


# ---------------------------------------------------------------- Lean types and dispatcher

SCALARS = {'Int': ('dInt', 'Val.int'), 'Bool': ('dBool', 'Val.bool'), 'String': ('dStr', 'Val.str'),
           'Unit': ('dUnit', 'eUnit'), 'Val': ('dVal', 'id'), 'Fl': ('dFl', 'Val.float')}
SORT_OF = {'Int': 'int', 'Bool': 'bool', 'String': 'str', 'Fl': 'float'}
TYPE_TOKEN = re.compile(r'\s*(×|\(|\)|[A-Za-z_][A-Za-z0-9_.]*)')


class TypeError_(ValueError):
    pass


def parse_type(text: str):
    """'List (Option Int) × String' → ('Prod', [('List', ('Option', 'Int')), 'String'])."""
    toks, pos, text = [], 0, text.strip()
    while pos < len(text):
        m = TYPE_TOKEN.match(text, pos)
        if not m or m.end() == pos:
            raise TypeError_(f'cannot parse type {text!r}')
        toks.append(m.group(1))
        pos = m.end()
    i = 0

    def prod():
        nonlocal i
        items = [app()]
        while i < len(toks) and toks[i] == '×':
            i += 1
            items.append(app())
        return items[0] if len(items) == 1 else ('Prod', items)

    def app():
        nonlocal i
        if i < len(toks) and toks[i] in ('Option', 'List'):
            head = toks[i]
            i += 1
            return (head, atom())
        if i < len(toks) and toks[i] == 'Except':
            if i + 1 < len(toks) and toks[i + 1] == 'String':
                i += 2
                return ('Except', atom())
            raise TypeError_('only `Except String τ` is supported')
        return atom()

    def atom():
        nonlocal i
        if i >= len(toks):
            raise TypeError_(f'truncated type {text!r}')
        t = toks[i]
        i += 1
        if t == '(':
            inner = prod()
            if i >= len(toks) or toks[i] != ')':
                raise TypeError_(f'unbalanced parentheses in {text!r}')
            i += 1
            return inner
        t = t.split('.')[-1] if t.startswith(('Autoform.Core.', 'Core.')) else t
        if t in SCALARS:
            return t
        hint = ' (use Int for Python int)' if t == 'Nat' else ' (use Fl, never Float)' if t == 'Float' else ''
        raise TypeError_(f'unsupported type {t!r}{hint}; use Int, Bool, String, Unit, Val, Fl, '
                         'Option τ, List τ, τ × σ, Except String τ')

    out = prod()
    if i != len(toks):
        raise TypeError_(f'trailing tokens in type {text!r}')
    if isinstance(out, tuple) and out[0] == 'Prod' and len(out[1]) > 4:
        raise TypeError_('tuples of more than 4 components are not supported')
    return out


def _has_except(t) -> bool:
    if isinstance(t, str):
        return False
    if t[0] == 'Except':
        return True
    if t[0] == 'Prod':
        return any(_has_except(x) for x in t[1])
    return _has_except(t[1])


def decoder(t) -> str:
    if isinstance(t, str):
        return SCALARS[t][0]
    if t[0] == 'Option':
        return f'(dOpt {decoder(t[1])})'
    if t[0] == 'List':
        return f'(dList {decoder(t[1])})'
    if t[0] == 'Prod':
        return f'(dTup{len(t[1])} ' + ' '.join(decoder(x) for x in t[1]) + ')'
    raise TypeError_('Except is only allowed as the outermost return type')


def encoder(t) -> str:
    if isinstance(t, str):
        return SCALARS[t][1]
    if t[0] == 'Option':
        return f'(eOpt {encoder(t[1])})'
    if t[0] == 'List':
        return f'(eList {encoder(t[1])})'
    if t[0] == 'Prod':
        return f'(eTup{len(t[1])} ' + ' '.join(encoder(x) for x in t[1]) + ')'
    raise TypeError_('Except is only allowed as the outermost return type')


def sort_of(t) -> str:
    if isinstance(t, tuple) and t[0] == 'Except':
        t = t[1]
    return SORT_OF.get(t, 'any') if isinstance(t, str) else 'any'


@dataclass
class Sig:
    params: list        # [{'name', 'type': parsed, 'kind', 'default'}]
    returns: object     # parsed return type (may be ('Except', τ))

    @property
    def raises(self) -> bool:
        return isinstance(self.returns, tuple) and self.returns[0] == 'Except'


def parse_sig(params: list, returns: str) -> Sig:
    out, seen_default, var = [], False, 0
    for i, p in enumerate(params or []):
        if not isinstance(p, dict):
            raise TypeError_(f'parameter #{i + 1} is not an object')
        kind = str(p.get('kind') or 'positional')
        if kind not in ('positional', 'varargs'):
            raise TypeError_(f'parameter kind {kind!r} must be positional or varargs')
        t = parse_type(str(p.get('type', '')))
        if _has_except(t):
            raise TypeError_('parameters cannot have an Except type')
        default = p.get('default')
        default = None if default in (None, '', 'null') else str(default)
        if kind == 'varargs':
            var += 1
            if not (isinstance(t, tuple) and t[0] == 'List'):
                raise TypeError_('a varargs parameter must have type `List τ`')
            if i != len(params) - 1:
                raise TypeError_('the varargs parameter must be last')
        elif default is not None:
            seen_default = True
        elif seen_default:
            raise TypeError_('a parameter without default follows one with a default')
        out.append({'name': str(p.get('name', f'p{i}')), 'type': t, 'kind': kind, 'default': default})
    if var > 1:
        raise TypeError_('at most one varargs parameter')
    r = parse_type(str(returns or ''))
    inner = r[1] if isinstance(r, tuple) and r[0] == 'Except' else r
    if _has_except(inner):
        raise TypeError_('Except must be the outermost return type')
    return Sig(out, r)


def wrapper(lean_name: str, sig: Sig) -> str:
    """`call_<lean_name> : List Val → EResult`: decode, run, encode. Generated, never model-written."""
    fixed = [p for p in sig.params if p['kind'] == 'positional']
    var = next((p for p in sig.params if p['kind'] == 'varargs'), None)
    inner = sig.returns[1] if sig.raises else sig.returns
    res = f'resE {encoder(inner)}' if sig.raises else f'resV {encoder(inner)}'
    required = sum(1 for p in fixed if p['default'] is None)
    arities = [len(fixed)] if var else list(range(len(fixed), required - 1, -1))
    lines = [f'def call_{lean_name} : List Val → EResult']
    for k in arities:
        pats = [f'a{i}' for i in range(k)]
        if var:
            pattern = ' :: '.join(pats + ['rest'])
        else:
            pattern = '[' + ', '.join(pats) + ']'
        discr = [f'{decoder(fixed[i]["type"])} a{i}' for i in range(k)]
        binds = [f'some x{i}' for i in range(k)]
        args = [f'x{i}' for i in range(k)] + [f'({fixed[i]["default"]})' for i in range(k, len(fixed))]
        if var:
            discr.append(f'dListAux {decoder(var["type"][1])} rest')
            binds.append('some xs')
            args.append('xs')
        app = f'({lean_name} {" ".join(args)})' if args else lean_name
        if discr:
            body = (f'\n    match {", ".join(discr)} with\n    | {", ".join(binds)} => {res} {app}\n'
                    f'    | {", ".join("_" for _ in discr)} => .hole "nl:arg-type"')
        else:
            body = f' {res} {app}'
        lines.append(f'  | {pattern} =>{body}')
    if not (var and not fixed):
        lines.append('  | _ => .hole "nl:arg-count"')
    return '\n'.join(lines) + '\n'


def dispatcher(entries: list) -> str:
    """entries: [(qualified name, lean_name)] → the `call` function."""
    lines = ['def call (name : String) (args : List Val) : EResult :=', '  match name with']
    for qual, lean_name in entries:
        lines.append(f'  | {pv.lean_str(qual)} => call_{lean_name} args')
    lines.append('  | _ => .hole "nl:unknown-function"')
    return '\n'.join(lines) + '\n'


PRELUDE = r'''
/-! Argument decoding and result encoding shared by every model in this module.
Generated by autoform.nl.model; all definitions are structurally recursive, so the kernel
evaluates `call` on concrete arguments. -/
def dInt : Val → Option Int | .int n => some n | _ => none
def dBool : Val → Option Bool | .bool b => some b | _ => none
def dStr : Val → Option String | .str s => some s | _ => none
def dUnit : Val → Option Unit | .unit => some () | _ => none
def dVal : Val → Option Val := some
def dFl : Val → Option Fl | .float x => some x | _ => none
def dListAux {α : Type} (d : Val → Option α) : List Val → Option (List α)
  | [] => some []
  | v :: vs => match d v, dListAux d vs with
    | some a, some as => some (a :: as)
    | _, _ => none
def dList {α : Type} (d : Val → Option α) : Val → Option (List α)
  | .list vs => dListAux d vs
  | _ => none
def dOpt {α : Type} (d : Val → Option α) : Val → Option (Option α)
  | .unit => some none
  | v => (d v).map some
def dTup2 {α β : Type} (da : Val → Option α) (db : Val → Option β) : Val → Option (α × β)
  | .tuple [a, b] => match da a, db b with
    | some x, some y => some (x, y)
    | _, _ => none
  | _ => none
def dTup3 {α β γ : Type} (da : Val → Option α) (db : Val → Option β) (dc : Val → Option γ) :
    Val → Option (α × β × γ)
  | .tuple [a, b, c] => match da a, db b, dc c with
    | some x, some y, some z => some (x, y, z)
    | _, _, _ => none
  | _ => none
def dTup4 {α β γ δ : Type} (da : Val → Option α) (db : Val → Option β) (dc : Val → Option γ)
    (dd : Val → Option δ) : Val → Option (α × β × γ × δ)
  | .tuple [a, b, c, d] => match da a, db b, dc c, dd d with
    | some x, some y, some z, some w => some (x, y, z, w)
    | _, _, _, _ => none
  | _ => none
def eUnit (_ : Unit) : Val := .unit
def eOpt {α : Type} (e : α → Val) : Option α → Val
  | none => .unit
  | some a => e a
def eList {α : Type} (e : α → Val) (xs : List α) : Val := .list (xs.map e)
def eTup2 {α β : Type} (ea : α → Val) (eb : β → Val) : α × β → Val
  | (a, b) => .tuple [ea a, eb b]
def eTup3 {α β γ : Type} (ea : α → Val) (eb : β → Val) (ec : γ → Val) : α × β × γ → Val
  | (a, b, c) => .tuple [ea a, eb b, ec c]
def eTup4 {α β γ δ : Type} (ea : α → Val) (eb : β → Val) (ec : γ → Val) (ed : δ → Val) :
    α × β × γ × δ → Val
  | (a, b, c, d) => .tuple [ea a, eb b, ec c, ed d]
def resV {α : Type} (e : α → Val) (a : α) : EResult := .val (e a)
def resE {α : Type} (e : α → Val) : Except String α → EResult
  | .ok a => .val (e a)
  | .error n => .exn (.str n)
'''

RENDER = r'''
mutual
def rv : Val → String
  | .int n => "i:" ++ toString n
  | .bool b => "b:" ++ toString b
  | .str s => "s:" ++ toString (s.toList.map Char.toNat)
  | .unit => "none"
  | .float x => if x.isNaN then "f:nan" else "f:" ++ toString x.bits
  | .list vs => "L(" ++ rl vs ++ ")"
  | .tuple vs => "T(" ++ rl vs ++ ")"
  | .dict kvs => "D(" ++ rd kvs ++ ")"
  | .fn n => "F:" ++ n
  | _ => "?"
def rl : List Val → String
  | [] => ""
  | v :: vs => rv v ++ "," ++ rl vs
def rd : List (Val × Val) → String
  | [] => ""
  | (k, v) :: kvs => rv k ++ "=" ++ rv v ++ ";" ++ rd kvs
end
def rr : EResult → String
  | .val v => "ok " ++ rv v
  | .exn (.str n) => "exn " ++ n
  | .exn v => "exn? " ++ rv v
  | .hole l => "hole " ++ l
  | .outOfFuel => "fuel"
def sameR : EResult → EResult → Bool
  | .val a, .val b => Val.beq a b
  | .exn a, .exn b => Val.beq a b
  | _, _ => false
'''

HEADER = ('import Autoform.Lang.Core.Syntax\nset_option autoImplicit false\nset_option maxRecDepth 100000\n'
          'set_option maxHeartbeats 4000000\nset_option linter.all false\n')

FORBIDDEN = re.compile(r'\b(sorry|admit|partial|unsafe|native_decide|axiom|implemented_by|extern|opaque|'
                       r'import|namespace|section|macro|syntax|elab|initialize|IO|unsafeCast|Float|'
                       r'set_option|decide\s*\+native|ofReduceBool|Lean\.)\b')


def lean_ident(fn_name: str, taken: set) -> str:
    qual = fn_name.split(':<module>.', 1)[-1]
    base = 'py_' + re.sub(r'_+', '_', re.sub(r'[^A-Za-z0-9_]', '_', qual)).strip('_')
    if base in taken:
        stem = re.sub(r'[^A-Za-z0-9_]', '_', fn_name.split(':')[0].rsplit('.', 1)[0])
        base = f'py_{stem}_' + base[3:]
    name, k = base, 2
    while name in taken:
        name, k = f'{base}_{k}', k + 1
    taken.add(name)
    return name


def lean_problems(text: str, lean_name: str) -> list:
    """Reasons a model-written Lean text cannot go into the module (before Lean runs)."""
    problems = []
    body = re.sub(r'"(?:[^"\\]|\\.)*"', '""', text or '')
    body = re.sub(r'--.*', '', body)
    body = re.sub(r'/-.*?-/', '', body, flags=re.S)
    if not body.strip():
        return ['empty Lean text']
    m = FORBIDDEN.search(body)
    if m:
        problems.append(f'forbidden construct `{m.group(1)}` (definitions must be plain, total and pure; '
                        'no Float: use Fl)')
    names = re.findall(r'(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)?'
                       r'(?:def|abbrev|theorem|lemma|instance|structure|inductive|class)\s+([^\s:({\[]+)', body)
    kinds = re.findall(r'(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)?'
                       r'(def|abbrev|theorem|lemma|instance|structure|inductive|class)\b', body)
    if any(k not in ('def', 'abbrev') for k in kinds):
        problems.append('only `def`s are allowed (no theorem/instance/structure/inductive)')
    if lean_name not in names:
        problems.append(f'the main definition must be named exactly `{lean_name}`')
    for n in names:
        if n != lean_name and not n.startswith(lean_name + '_'):
            problems.append(f'helper `{n}` must be named `{lean_name}_<suffix>`')
    if re.search(r'(?m)^\s*(open|end|variable|universe|#)', re.sub(r'(?ms)^\s*mutual\b.*?^\s*end\b', '', body)):
        problems.append('no commands other than `def` (and a `mutual ... end` block)')
    return problems


# ---------------------------------------------------------------- subprocess scripts

TRACER = r'''
import contextlib, importlib.util, io, json, os, sys, threading
cfg = json.load(open(sys.argv[1]))
spec = importlib.util.spec_from_file_location('_af_pyvalues', cfg['pyvalues'])
pv = importlib.util.module_from_spec(spec); spec.loader.exec_module(pv)
for d in reversed(cfg['sys_path']):
    if d not in sys.path:
        sys.path.insert(0, d)
try:
    sys.set_int_max_str_digits(0)
except AttributeError:
    pass
wanted = {}
for f, lines, key in cfg['wanted']:
    for ln in lines:
        wanted[(os.path.realpath(f), ln)] = key
limit = cfg['limit']
records, stats, known = {}, {'calls': 0, 'kwargs': 0, 'unencodable': 0}, {}
def tracer(frame, event, arg):
    if event != 'call':
        return None
    code = frame.f_code
    key = known.get(code, 0)
    if key == 0:
        key = known[code] = wanted.get((os.path.realpath(code.co_filename), code.co_firstlineno))
    if key is None:
        return None
    if code.co_flags & 0x3a0:        # generator / coroutine / async generator
        return None
    stats['calls'] += 1
    loc = frame.f_locals
    n, k = code.co_argcount, code.co_kwonlyargcount
    try:
        args = [loc[x] for x in code.co_varnames[:n]]
        i = n + k
        if code.co_flags & 0x04:
            args += list(loc[code.co_varnames[i]]); i += 1
        if code.co_flags & 0x08 and loc[code.co_varnames[i]]:
            stats['kwargs'] += 1
            return None
        tagged = json.dumps([pv.tag(a) for a in args])
    except (pv.Unencodable, KeyError, ValueError, TypeError, RecursionError):
        stats['unencodable'] += 1
        return None
    bucket = records.setdefault(key, {})
    if len(bucket) < limit:
        bucket[tagged] = None
    return None
buf = io.StringIO()
ran = []
sys.settrace(tracer); threading.settrace(tracer)
try:
    for d in cfg['tests']:
        os.chdir(os.path.dirname(d))
        try:
            with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
                try:
                    import pytest
                    rc = int(pytest.main([d, '-q', '-p', 'no:cacheprovider', '--no-header']))
                except ImportError:
                    import unittest
                    suite = unittest.TestLoader().discover(d, top_level_dir=os.path.dirname(d))
                    rc = 0 if unittest.TextTestRunner(stream=buf, verbosity=0).run(suite).wasSuccessful() else 1
            ran.append({'dir': d, 'rc': rc})
        except BaseException as e:
            ran.append({'dir': d, 'error': repr(e)[:300]})
finally:
    sys.settrace(None); threading.settrace(None)
json.dump({'records': {k: [json.loads(t) for t in v] for k, v in records.items()}, 'stats': stats,
           'runs': ran, 'log_tail': buf.getvalue()[-1500:]}, open(cfg['out'], 'w'))
'''

RUNNER = r'''
import contextlib, importlib, importlib.util, io, json, os, signal, sys
cfg = json.load(open(sys.argv[1]))
spec = importlib.util.spec_from_file_location('_af_pyvalues', cfg['pyvalues'])
pv = importlib.util.module_from_spec(spec); spec.loader.exec_module(pv)
for d in reversed(cfg['sys_path']):
    if d not in sys.path:
        sys.path.insert(0, d)
try:
    sys.set_int_max_str_digits(0)
except AttributeError:
    pass
sys.setrecursionlimit(5000)
class _Deadline(BaseException):
    pass
def _alarm(*_):
    raise _Deadline()
signal.signal(signal.SIGALRM, _alarm)
sink = io.StringIO()
with contextlib.redirect_stdout(sink), contextlib.redirect_stderr(sink):
    if cfg['dotted']:
        mod = importlib.import_module(cfg['dotted'])
    else:
        s = importlib.util.spec_from_file_location('autoform_subject', cfg['path'])
        mod = importlib.util.module_from_spec(s); sys.modules['autoform_subject'] = mod
        s.loader.exec_module(mod)
obj = mod
for part in cfg['qual'].split('.'):
    obj = getattr(obj, part)
out = []
for point in cfg['points']:
    try:
        args = [pv.untag(t) for t in point]
    except Exception as e:
        out.append({'k': 'bad-input', 'why': repr(e)[:200]}); continue
    signal.setitimer(signal.ITIMER_REAL, cfg['per'])
    try:
        with contextlib.redirect_stdout(sink), contextlib.redirect_stderr(sink):
            v = obj(*args)
        signal.setitimer(signal.ITIMER_REAL, 0)
        try:
            out.append({'k': 'ok', 'v': pv.tag(v)})
        except pv.Unencodable as e:
            out.append({'k': 'unencodable', 'why': str(e)[:200]})
    except _Deadline:
        out.append({'k': 'timeout'})
    except BaseException as exc:
        signal.setitimer(signal.ITIMER_REAL, 0)
        out.append({'k': 'exn', 't': type(exc).__name__})
    sink.seek(0); sink.truncate()
json.dump(out, open(cfg['out'], 'w'))
'''


def _run_script(script: str, cfg: dict, work: Path, stem: str, timeout: int, cwd=None):
    work = Path(work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    cfg_path, out_path = work / f'{stem}.cfg.json', work / f'{stem}.out.json'
    cfg = dict(cfg, out=str(out_path), pyvalues=str(PYVALUES))
    cfg_path.write_text(json.dumps(cfg))
    if out_path.exists():
        out_path.unlink()
    env = {k: v for k, v in os.environ.items() if k not in ('PYTHONPATH',)}
    env['PYTHONHASHSEED'] = '0'
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    try:
        proc = subprocess.run([sys.executable, '-c', script, str(cfg_path)], cwd=str(cwd or work), env=env,
                              capture_output=True, text=True, timeout=timeout, start_new_session=True)
    except subprocess.TimeoutExpired:
        return None, f'timed out after {timeout}s'
    if not out_path.is_file():
        return None, (proc.stderr or proc.stdout)[-1500:]
    return json.loads(out_path.read_text()), ''


def trace_tests(fns: list, source_root: Path, test_dirs: list, work: Path) -> tuple:
    """Run the repository's tests under a tracer; {qualified name: [point]} and stats."""
    if not fns or not test_dirs:
        return {}, {'note': 'no tests to trace'}
    roots = []
    for f in fns:
        r = str(f.mod.import_root)
        if r not in roots:
            roots.append(r)
    sys_path = roots + [str(Path(d).resolve().parent) for d in test_dirs]
    cfg = {'sys_path': sys_path, 'tests': [str(Path(d).resolve()) for d in test_dirs], 'limit': TRACE_LIMIT,
           'wanted': [[str(f.mod.path), f.first_lines, f.info.name] for f in fns]}
    data, err = _run_script(TRACER, cfg, work, 'trace', TRACE_TIMEOUT)
    if data is None:
        return {}, {'error': err}
    stats = dict(data['stats'], runs=data['runs'],
                 traced={k: len(v) for k, v in data['records'].items()})
    return data['records'], stats


class Runtime:
    """CPython outcomes of one function, cached by input point."""

    def __init__(self, fn: _Fn, work: Path):
        self.fn, self.work, self.cache, self.error = fn, work, {}, ''
        self.calls = 0

    def run(self, points: list) -> list:
        todo = []
        for p in points:
            k = json.dumps(p)
            if k not in self.cache and k not in todo:
                todo.append(k)
        if todo:
            self.calls += 1
            mod = self.fn.mod
            cfg = {'sys_path': [str(mod.import_root)], 'dotted': mod.dotted, 'path': str(mod.path),
                   'qual': self.fn.qual, 'per': POINT_TIMEOUT, 'points': [json.loads(k) for k in todo]}
            data, err = _run_script(RUNNER, cfg, self.work, f'runtime{self.calls}', RUNTIME_TIMEOUT,
                                    cwd=mod.import_root)
            if data is None or len(data) != len(todo):
                self.error = err or 'runner returned a wrong number of results'
                data = [{'k': 'runner-failed'}] * len(todo)
            for k, r in zip(todo, data):
                self.cache[k] = r
        return [self.cache[json.dumps(p)] for p in points]


# ---------------------------------------------------------------- input generation

INT_VALUES = [0, 1, -1, 2, -2, 2 ** 63 + 1, -2 ** 63 - 1, 3, -3, 7, -7, 10, -10, 2 ** 31 - 1, -2 ** 31, 5,
              100, -100, 255, 256, 2 ** 53 + 1, 12345678901234567891]
STR_VALUES = ['', 'a', 'b', 'ab', 'abc', 'A', ' ', 'a b', '0', '-1', 'é', 'hello world']
FLOAT_VALUES = [0.0, 1.0, -1.0, 0.5, -2.5, 1e300, float('inf'), float('nan')]
VAL_VALUES = [0, 1, -1, 'a', '', None, True, False, 2.5, (1, 2), [1], {}, ('a',)]


def _literals(source: str):
    ints, strs = [], []
    for m in re.finditer(r'(?<![\w.])(\d+)(?![\w.])', source or ''):
        v = int(m.group(1))
        for x in (v, v - 1, v + 1, -v):
            if x not in ints:
                ints.append(x)
    text = re.sub(r'("""|\'\'\')[\s\S]*?\1', '', source or '')
    for m in re.finditer(r'"((?:[^"\\\n]|\\.){0,30})"|\'((?:[^\'\\\n]|\\.){0,30})\'', text):
        s = m.group(1) if m.group(1) is not None else m.group(2)
        if '\\' not in s and s not in strs:
            strs.append(s)
    return ints[:12], strs[:8]


def values_for(t, ints=(), strs=(), depth=0) -> list:
    """Python values of Lean type `t`, most informative first."""
    if isinstance(t, str):
        if t == 'Int':
            return list(dict.fromkeys([0, 1, -1] + list(ints)[:6] + INT_VALUES))
        if t == 'Bool':
            return [False, True]
        if t == 'String':
            return list(dict.fromkeys(list(strs) + STR_VALUES))
        if t == 'Unit':
            return [None]
        if t == 'Fl':
            return FLOAT_VALUES
        return VAL_VALUES
    if depth > 2:
        return []
    if t[0] == 'Option':
        return [None] + values_for(t[1], ints, strs, depth + 1)[:8]
    if t[0] == 'List':
        e = values_for(t[1], ints, strs, depth + 1)[:6]
        out = [[]]
        if e:
            out += [[e[0]], e[:2], e[:3], list(reversed(e[:4])), [e[-1], e[0], e[-1]]]
            if len(e) > 3:
                out.append(e[1:5])
        return out
    if t[0] == 'Prod':
        per = [values_for(x, ints, strs, depth + 1)[:4] for x in t[1]]
        return [tuple(c) for c in _product(per, 12)]
    return []


def _product(per: list, cap: int) -> list:
    import itertools
    per = [list(p) for p in per]
    while per and _count(per) > cap and max(len(p) for p in per) > 1:
        i = max(range(len(per)), key=lambda k: len(per[k]))
        per[i] = per[i][:-1]
    return [list(c) for c in itertools.product(*per)] if per else [[]]


def _count(per) -> int:
    n = 1
    for p in per:
        n *= len(p)
    return n


def boundary_points(sig: Sig, source: str, cap: int = BOUNDARY_CAP) -> list:
    ints, strs = _literals(source)
    per = []
    for p in sig.params:
        if p['kind'] == 'varargs':
            elems = values_for(p['type'][1], ints, strs)[:5]
            per.append([('*', e) for e in [[], elems[:1], elems[:2], elems[1:4], elems[:3]]])
        else:
            per.append(values_for(p['type'], ints, strs))
    out = []
    for combo in _product(per, cap):
        args = []
        for v in combo:
            if isinstance(v, tuple) and len(v) == 2 and v[:1] == ('*',):
                args += list(v[1])
            else:
                args.append(v)
        try:
            out.append([pv.tag(a) for a in args])
        except pv.Unencodable:
            continue
    return out


# ---------------------------------------------------------------- prompts

CONVENTIONS = r'''
Lean conventions (Lean 4 core, no Mathlib; the namespace `Autoform.Core` is open):
- Types. Python int → `Int` (unbounded; never `Nat` for a Python int), bool → `Bool`,
  str → `String`, a value that may be None → `Option τ` (None is `none`), list → `List τ`,
  fixed-length tuple → `τ × σ` (up to 4 components), returning None → `Unit`. A Python tuple
  of variable length (or of a tuple subclass) is a `Val` built with `.tuple vs`: `List τ` is a
  Python *list*, and a list never equals a tuple.
  Python float → `Fl` only if unavoidable (IEEE binary64 bit patterns; never Lean `Float`). API:
  `FConfig.python.ofInt (n : Int) : FResult` and `FConfig.python.add/sub/mul/div (x y : Fl) : FResult`
  (`inductive FResult | ok (x : Fl) | exn (name : String) | ub (s : String) | unmodelled (s : String)`),
  `Format.round Format.binary64 (neg : Bool) (num den : Nat) : Fl` = the correctly rounded value of
  ±num/den (may be infinite), `Fl.isInf`, `Fl.isNaN`, `Fl.isZero`, `FConfig.python.eq/lt/le x y : Bool`.
  A parameter or result that really mixes Python types (e.g. `*args` of a key function) uses
  the universal type `Val`: `.int n`, `.bool b`, `.str s`, `.float x`, `.unit` (None),
  `.list vs`, `.tuple vs`, `.dict (kvs : List (Val × Val))`, `.fn "int"` (a builtin type
  object such as `type(3)`: `.fn "int"`, `.fn "str"`, `.fn "bool"`, `.fn "float"`,
  `.fn "NoneType"`, `.fn "tuple"`, `.fn "list"`, `.fn "dict"`).
  Python `True == 1`, but `.bool true` and `.int 1` are different `Val`s: keep the Python type.
- Exceptions. If the function can raise on its domain, the return type is `Except String τ`
  and raising is `.error "<ExactPythonExceptionClassName>"`, e.g. `.error "ZeroDivisionError"`,
  `.error "ValueError"`, `.error "IndexError"`, `.error "KeyError"`, `.error "TypeError"`.
  Model every exception the Python code raises, including implicit ones (division or modulo
  by zero, index out of range, missing dict key, int() of a bad string, ...).
- Arithmetic. Python `a // b` is `Int.fdiv a b` and `a % b` is `Int.fmod a b` (Lean's `/`
  and `%` on Int differ for negative operands: never use them for Python // and %).
  `abs a` is `(Int.natAbs a : Int)`; `a ** n` with n ≥ 0 is `a ^ n.toNat`.
- Strings and lists behave exactly as in Python: `len(s)` is `s.length` (code points), negative
  indices count from the end, slices clamp, `in`, `split`, `strip`, `lower`, `sorted`, ...
  Implement them exactly (e.g. over `s.toList`), not approximately.
- Totality. Definitions must be total and evaluable by the Lean kernel (`decide +kernel`):
  structural recursion on a list or on a `Nat` fuel bounded by the input size, `List.foldl`,
  `List.map`, `List.range`, `List.filter`, `match`, `if`. No `partial`, `unsafe`,
  `native_decide`, `sorry`, `axiom`, `IO`, `Float`, no well-founded recursion (`termination_by`).
- Parameters. List the Python parameters in order. `*args` is ONE parameter with
  "kind": "varargs" and type `List τ` (usually `List Val`). `**kwargs` is always empty: drop it.
  A parameter with a Python default keeps its type and gives "default": a Lean term for the
  default value (else null). Keyword-only parameters take their defaults: inline them.
- Naming. The main definition is named exactly NAME (given below); helpers are named
  `NAME_<suffix>` and come before it. Write only `def`s (a `mutual ... end` block is allowed):
  no `namespace`, `open`, `import`, `theorem`, `instance`, `structure`, `#eval`.
'''

KEYS_A = ['english', 'params', 'returns', 'lean']
KEYS_B = ['params', 'returns', 'lean']


def _function_block(fn: _Fn, lean_name: str, callees: list, context: str) -> str:
    info = fn.info
    lines = [f'NAME: {lean_name}',
             f'Python function: {info.name}  ({info.file}:{info.line})',
             'Source:', '```python', info.source.rstrip(), '```']
    if info.doc:
        lines.append('Docstring: ' + info.doc[:1500])
    if info.tests:
        lines.append('Lines of the project\'s tests that use it:')
        lines += [f"  {t['location']}: {t['text']}" for t in info.tests[:10]]
    if info.callers:
        lines.append('Called by: ' + ', '.join(info.callers[:6]))
    if callees:
        lines.append('Functions it calls that are already translated (call their Lean defs; they are '
                     'validated against Python):')
        for qual, lname, src in callees:
            lines.append(f'  {qual} is `{lname}`:\n```lean\n{src.strip()[:1500]}\n```')
    if context:
        lines += ['Module context (imports, constants, classes it may use):', '```python', context, '```']
    return '\n'.join(lines)


def prompt_a(block: str) -> str:
    return ('You translate one Python function into a plain Lean 4 definition. The definition will be '
            'run on many inputs next to the real Python function and the results compared exactly, so it '
            'must be faithful to Python semantics on the domain the function is used with, including '
            'exceptions and edge cases.\n\n'
            'Work in two steps. First write "english": a precise description of what the function '
            'computes: its input domain (as its tests and callers use it), its result for every input, and '
            'exactly which inputs raise which exception class. Then write "lean": Lean 4 definitions that '
            'implement exactly that description.\n' + CONVENTIONS + '\n' + block +
            '\n\nReply with JSON keys: "english" (the description), "params" (a list of {"name", "type", '
            '"kind": "positional"|"varargs", "default": null or a Lean term}, in Python parameter order), '
            '"returns" (the Lean return type of NAME exactly as in the def, e.g. "Int" or '
            '"Except String Int"), "lean" (the Lean source of the definitions).')


def prompt_b(block: str) -> str:
    return ('Independent re-implementation check. Read the Python code below and write a Lean 4 function '
            'that returns exactly what the Python code returns (or raises exactly what it raises) for '
            'every argument tuple of the types you choose. Work directly from the code: do not describe '
            'it first, just translate each statement faithfully.\n' + CONVENTIONS + '\n' + block +
            '\n\nReply with JSON keys: "params" ([{"name", "type", "kind", "default"}] in Python order), '
            '"returns" (the Lean return type of NAME), "lean" (the Lean definitions).')


def repair_prompt(base: str, cand: dict, problem: str) -> str:
    prev = {k: cand.get(k) for k in ('params', 'returns', 'lean') if k in cand}
    return (base + '\n\n## Your previous answer was rejected\n```json\n' + json.dumps(prev, indent=1,
                                                                                     ensure_ascii=False)
            + '\n```\n' + problem.strip() +
            '\n\nReply with the complete corrected answer (all keys). Fix the translation so it matches '
            'Python on these inputs and on all others; do not special-case the listed inputs.')


def _module_context(fn: _Fn, limit: int = 5000) -> str:
    text = fn.mod.text
    if len(text) <= limit:
        return text.strip()
    parts = []
    for node in fn.mod.tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        seg = ast.get_source_segment(text, node) or ''
        if isinstance(node, ast.ClassDef) and len(seg) > 1500:
            seg = seg[:1500] + '\n    ...'
        parts.append(seg)
    return '\n'.join(parts)[:limit]


# ---------------------------------------------------------------- one Lean run

@dataclass
class Candidate:
    data: dict
    sig: Sig | None = None
    problems: list = field(default_factory=list)


def _candidate(data: dict, lean_name: str) -> Candidate:
    c = Candidate(data)
    try:
        c.sig = parse_sig(data.get('params') or [], data.get('returns') or '')
    except (TypeError_, ValueError) as exc:
        c.problems.append(f'signature: {exc}')
    lean = data.get('lean')
    if not isinstance(lean, str):
        c.problems.append('"lean" must be a string of Lean source')
    else:
        c.problems += lean_problems(lean, lean_name)
    return c


def scratch_file(module: str, callee_src: str, cand_src: str, wrap: str, qual: str, lean_name: str,
                 points: list, kernel: list) -> tuple:
    """(text, spans); spans['check'] is the first line of the evaluation section."""
    ns = f'Autoform.NLModel.{module}'
    parts = [HEADER, f'namespace {ns}', 'open Autoform.Core', PRELUDE, callee_src, '-- candidate']
    text = '\n'.join(parts) + '\n'
    spans = {'candidate': text.count('\n') + 1}
    text += cand_src.rstrip() + '\n\n'
    spans['wrapper'] = text.count('\n') + 1
    text += wrap + '\n' + dispatcher([(qual, lean_name)]) + f'end {ns}\n\n'
    spans['check'] = text.count('\n') + 1
    text += 'namespace AutoformNLCheck\nopen Autoform.Core\n' + RENDER
    text += 'def pts : List (List Val) := [\n  ' + ',\n  '.join(
        '[' + ', '.join(pv.lean_lit(t) for t in p) + ']' for p in points) + ']\n'
    text += (f'#eval (pts.zipIdx.forM fun (p, i) => IO.println ("AFR " ++ toString i ++ " " ++ '
             f'rr ({ns}.call {pv.lean_str(qual)} p)))\n')
    spans['kernel'] = {}
    for i, lit in kernel:
        spans['kernel'][text.count('\n') + 1] = i
        args = '[' + ', '.join(pv.lean_lit(t) for t in points[i]) + ']'
        text += (f'theorem kchk_{i} : sameR ({ns}.call {pv.lean_str(qual)} {args}) {lit} = true := by\n'
                 f'  decide +kernel\n')
    text += 'end AutoformNLCheck\n'
    return text, spans


def run_lean(lean_root: Path, path: Path, timeout: int = LEAN_TIMEOUT) -> tuple:
    env = dict(os.environ)
    env['PATH'] = str(Path.home() / '.elan/bin') + os.pathsep + env.get('PATH', '')
    t0 = time.time()
    with LEAN_SLOTS:
        try:
            proc = subprocess.run([lake(), 'env', 'lean', str(path)], cwd=str(lean_root), env=env,
                                  capture_output=True, text=True, timeout=timeout)
            code, log = proc.returncode, proc.stdout + proc.stderr
        except subprocess.TimeoutExpired:
            code, log = 124, f'lean timed out after {timeout}s'
    log = '\n'.join(ln for ln in log.splitlines() if 'has local changes' not in ln)
    return code, log, round(time.time() - t0, 1)


ERR_RE = re.compile(r'^(.*?):(\d+):(\d+): error(?:\([^)]*\))?: (.*(?:\n(?!\S*:\d+:\d+: |AFR ).*)*)', re.M)


def lean_errors(log: str, path: Path) -> list:
    return [(int(m.group(2)), m.group(4).strip()) for m in ERR_RE.finditer(log)
            if Path(m.group(1)).name == path.name]


@dataclass
class Evaluation:
    elaborates: bool = False
    errors: str = ''
    outputs: list = field(default_factory=list)   # canonical strings (None if missing)
    compared: int = 0
    skipped: int = 0
    disagreements: list = field(default_factory=list)
    kernel_failures: list = field(default_factory=list)
    kernel_checked: int = 0
    seconds: float = 0.0


def evaluate(module: str, lean_root: Path, work: Path, stem: str, callee_src: str, cand: Candidate,
             lean_name: str, qual: str, points: list, runtime: list | None, kernel_points: int = KERNEL_POINTS
             ) -> Evaluation:
    ev = Evaluation()
    wrap = wrapper(lean_name, cand.sig)
    kernel = []
    if runtime is not None and kernel_points:
        # one point per outcome kind first (a return and a raise, when both occur), then fill
        lits = [(i, pv.lean_outcome(r), r.get('k')) for i, r in enumerate(runtime)]
        lits = [x for x in lits if x[1] is not None]
        for kind in ('ok', 'exn'):
            first = next((x for x in lits if x[2] == kind), None)
            if first:
                kernel.append(first[:2])
        for x in lits:
            if len(kernel) >= kernel_points:
                break
            if x[0] not in [j for j, _ in kernel]:
                kernel.append(x[:2])
        kernel = kernel[:kernel_points]
    text, spans = scratch_file(module, callee_src, cand.data['lean'], wrap, qual, lean_name, points, kernel)
    path = work / f'{stem}.lean'
    path.write_text(text)
    code, log, ev.seconds = run_lean(lean_root, path)
    if code == 124:
        ev.errors = log
        return ev
    errs = lean_errors(log, path)
    cand_start, check = spans['candidate'], spans['check']
    early = [(ln, msg) for ln, msg in errs if ln < check]
    if early or (code != 0 and not errs):
        numbered = '\n'.join(f'{i + cand_start:5d}  {line}' for i, line in enumerate(cand.data['lean'].splitlines()))
        where = []
        for ln, msg in early[:8]:
            part = 'your definitions' if cand_start <= ln < spans['wrapper'] else \
                'the generated dispatcher (does the def match the declared "params"/"returns"?)' \
                if ln >= spans['wrapper'] else 'the prelude'
            where.append(f'line {ln} ({part}): {msg[:1200]}')
        ev.errors = ('Lean rejected the definitions:\n' + '\n'.join(where) +
                     f'\n\nYour definitions as numbered in the checked file:\n{numbered}') if early else log[-3000:]
        wrapper_numbered = '\n'.join(f'{i + spans["wrapper"]:5d}  {line}' for i, line in enumerate(wrap.splitlines()))
        if any(ln >= spans['wrapper'] for ln, _ in early):
            ev.errors += '\n\nThe generated dispatcher:\n' + wrapper_numbered
        return ev
    ev.elaborates = True
    outs = {}
    for m in re.finditer(r'^AFR (\d+) (.*)$', log, re.M):
        outs[int(m.group(1))] = m.group(2)
    ev.outputs = [outs.get(i) for i in range(len(points))]
    if any(o is None for o in ev.outputs):
        ev.elaborates = False
        ev.errors = 'the batched #eval produced no output:\n' + '\n'.join(msg for _, msg in errs)[:3000]
        return ev
    for ln, msg in errs:
        i = spans['kernel'].get(ln, spans['kernel'].get(ln - 1))
        if i is not None:
            ev.kernel_failures.append({'point': i, 'error': msg[:500]})
    ev.kernel_checked = len(kernel)
    if runtime is not None:
        for i, (p, r) in enumerate(zip(points, runtime)):
            rt = pv.canon_outcome(r)
            if rt is None:
                ev.skipped += 1
                continue
            ev.compared += 1
            if ev.outputs[i] != rt:
                ev.disagreements.append({'point': i, 'inputs': pv.show_args(p), 'model': pv.display(ev.outputs[i]),
                                         'runtime': pv.display(rt), 'model_raw': ev.outputs[i], 'runtime_raw': rt})
    return ev


def counterexample_text(ev: Evaluation, name: str) -> str:
    lines = [f'Differential test: {len(ev.disagreements)} of {ev.compared} inputs disagree with the real Python '
             f'function. Examples (Python arguments → real Python outcome vs. your Lean model):']
    for d in ev.disagreements[:MAX_SHOWN]:
        lines.append(f'  {name}{d["inputs"]}: Python {d["runtime"]}; Lean model {d["model"]}')
    if ev.kernel_failures and not ev.disagreements:
        lines = ['The model agrees with Python, but the Lean kernel could not evaluate it (`decide +kernel` '
                 'failed); use plain structural recursion, no well-founded recursion:']
        lines += [f'  point {k["point"]}: {k["error"][:600]}' for k in ev.kernel_failures[:3]]
    return '\n'.join(lines)


# ---------------------------------------------------------------- one function

@dataclass
class _Result:
    fn: _Fn
    lean_name: str
    lean_src: str = ''
    sig: Sig | None = None
    data: dict | None = None
    record: schema.LeanModel | None = None
    points: list = field(default_factory=list)
    outputs: list = field(default_factory=list)
    cost: float = 0.0
    seconds: float = 0.0
    log: list = field(default_factory=list)


def _ask(prompt: str, keys: list, work: Path, ask) -> tuple:
    try:
        return (ask or llm.ask_json)(prompt, keys, cwd=str(work))
    except llm.LLMError as exc:
        return None, str(exc)


def model_function(fn: _Fn, lean_name: str, module: str, lean_root: Path, work: Path, traced: list,
                   done: dict, *, repairs: int = 3, second: bool = True, ask=None) -> _Result:
    t0 = time.time()
    work.mkdir(parents=True, exist_ok=True)
    res = _Result(fn, lean_name)
    callees = [done[c] for c in fn.callees if c in done and done[c].lean_src]
    # transitive callee sources, in dependency order
    order, seen = [], set()

    def add(r):
        if r.fn.info.name in seen:
            return
        seen.add(r.fn.info.name)
        for c in r.fn.callees:
            if c in done and done[c].lean_src:
                add(done[c])
        order.append(r)
    for r in callees:
        add(r)
    callee_src = '\n'.join(r.lean_src.rstrip() + '\n' for r in order)
    block = _function_block(fn, lean_name, [(r.fn.info.name, r.lean_name, r.lean_src) for r in callees],
                            _module_context(fn))
    runtime = Runtime(fn, work)
    base = prompt_a(block)
    prompt = base
    best = None          # (score, round, cand, ev, points, rt)
    rounds = 0
    for rnd in range(repairs + 1):
        rounds = rnd
        data, c = _ask(prompt, KEYS_A, work, ask)
        if data is None:
            res.log.append(f'round {rnd}: model error: {c}')
            break
        res.cost += c
        cand = _candidate(data, lean_name)
        if cand.problems:
            problem = 'It was rejected before Lean ran:\n' + '\n'.join('- ' + p for p in cand.problems)
            res.log.append(f'round {rnd}: ' + '; '.join(cand.problems))
            prompt = repair_prompt(base, data, problem)
            continue
        points = list(traced[:MAX_POINTS])
        for p in boundary_points(cand.sig, fn.info.source):
            if len(points) >= MAX_POINTS:
                break
            if p not in points:
                points.append(p)
        rt = runtime.run(points) if points else []
        ev = evaluate(module, lean_root, work, f'a{rnd}', callee_src, cand, lean_name, fn.info.name, points, rt)
        # fuzz.py: once the model agrees on traced + boundary inputs, search for more (coverage-guided,
        # shrunk); minimal counterexamples land in ev.disagreements and feed the repair below.
        fuzz.extend(ev, fn=fn, cand=cand, lean_name=lean_name, module=module, lean_root=lean_root, work=work,
                    stem=f'z{rnd}', callee_src=callee_src, points=points, rt=rt, runtime=runtime, traced=traced)
        if not ev.elaborates:
            res.log.append(f'round {rnd}: does not elaborate')
            if best is None:
                best = ((3, 0), rnd, cand, ev, points, rt)
            prompt = repair_prompt(base, data, ev.errors)
            continue
        score = (0 if not ev.disagreements and not ev.kernel_failures else 1,
                 len(ev.disagreements) + len(ev.kernel_failures))
        res.log.append(f'round {rnd}: {ev.compared} compared, {len(ev.disagreements)} disagree, '
                       f'{len(ev.kernel_failures)} kernel failures, {ev.skipped} skipped')
        if best is None or score <= best[0]:
            best = (score, rnd, cand, ev, points, rt)
        if score[0] == 0:
            break
        prompt = repair_prompt(base, data, counterexample_text(ev, fn.info.source_name))
    status, notes = 'FAILED', []
    rec = schema.LeanModel(function=fn.info.name, lean_name=f'Autoform.NLModel.{module}.{lean_name}',
                           lean_source='', signature='', status='FAILED', repairs=rounds)
    if best is None or not best[3].elaborates:
        rec.notes = 'no elaborating translation: ' + ('; '.join(res.log[-3:]) or 'model unavailable')
        if best is not None:
            rec.notes += '\nlast Lean errors:\n' + best[3].errors[:1500]
        res.record = rec
        res.seconds = round(time.time() - t0, 1)
        return res
    _, _, cand, ev, points, rt = best
    res.lean_src = cand.data['lean'].rstrip() + '\n\n' + wrapper(lean_name, cand.sig)
    res.sig, res.data, res.points, res.outputs = cand.sig, cand.data, points, ev.outputs
    rec.lean_source = cand.data['lean'].rstrip() + '\n'
    params = ' '.join(f"({p['name']} : {cand.data['params'][i].get('type')})"
                      for i, p in enumerate(cand.sig.params))
    rec.signature = f'{params} : {cand.data.get("returns")}'.strip()
    rec.tests_run = ev.compared
    rec.disagreements = [{k: d[k] for k in ('inputs', 'model', 'runtime')} for d in ev.disagreements[:20]]
    if ev.disagreements:
        status = 'DISAGREES'
    elif ev.kernel_failures:
        status = 'FAILED'
        notes.append(f'agrees with CPython but the kernel could not evaluate {len(ev.kernel_failures)} of '
                     f'{ev.kernel_checked} checked points')
    elif ev.compared == 0:
        status = 'UNTESTABLE'
    else:
        status = 'VALIDATED'
    traced_n = sum(1 for p in points[:len(traced)] if p in traced)
    notes.append(f'{ev.compared} inputs compared ({traced_n} traced from tests, {len(points) - traced_n} '
                 f'boundary), {ev.skipped} skipped (no faithful encoding or timeout), '
                 f'kernel-evaluated {ev.kernel_checked - len(ev.kernel_failures)}/{ev.kernel_checked}')
    if runtime.error:
        notes.append('runtime: ' + runtime.error[:300])
    if cand.data.get('english'):
        notes.append('english: ' + ' '.join(str(cand.data['english']).split())[:1200])
    rec.status = status
    rec.repairs = best[1]
    # --- translation B
    if second and ev.elaborates:
        rec.second_translation, bnote, bcost = second_translation(
            fn, lean_name, module, lean_root, work, block, callee_src, points, rt, ev, ask)
        res.cost += bcost
        notes.append(bnote)
    rec.level = 'L0' if status == 'VALIDATED' and rec.second_translation != 'disagrees' else 'none'
    rec.notes = '\n'.join(notes)
    res.record = rec
    res.seconds = round(time.time() - t0, 1)
    res.log.append(f'cost ${res.cost:.4f}, {res.seconds}s')
    return res


def second_translation(fn, lean_name, module, lean_root, work, block, callee_src, points, rt, ev_a, ask):
    """('agrees'|'disagrees'|'not_run', note, cost). One Lean-error repair; no semantic feedback."""
    base = prompt_b(block)
    prompt, cost = base, 0.0
    for attempt in range(2):
        data, c = _ask(prompt, KEYS_B, work, ask)
        if data is None:
            return 'not_run', f'translation B: model error: {c}', cost
        cost += c
        cand = _candidate(data, lean_name)
        if cand.problems:
            prompt = repair_prompt(base, data, 'Rejected before Lean ran:\n' + '\n'.join(cand.problems))
            continue
        ev = evaluate(module, lean_root, work, f'b{attempt}', callee_src, cand, lean_name, fn.info.name,
                      points, None, kernel_points=0)
        if not ev.elaborates:
            prompt = repair_prompt(base, data, ev.errors)
            continue
        diff, vs_python = [], 0
        compared = 0
        for i, (a, b) in enumerate(zip(ev_a.outputs, ev.outputs)):
            if 'nl:arg-type' in (a or '') or 'nl:arg-type' in (b or ''):
                continue
            compared += 1
            if a != b:
                diff.append(i)
                if pv.canon_outcome(rt[i]) not in (None, b):
                    vs_python += 1
        if compared == 0:
            return 'not_run', 'translation B: no input decodes for both translations', cost
        if not diff:
            return 'agrees', f'translation B (independent, from code) agrees with A on {compared} inputs', cost
        ex = diff[0]
        return ('disagrees', f'translation B differs from A on {len(diff)} of {compared} inputs '
                f'({vs_python} of those are points where B also disagrees with CPython); e.g. '
                f'{fn.info.source_name}{pv.show_args(points[ex])}: A {pv.display(ev_a.outputs[ex])}, '
                f'B {pv.display(ev.outputs[ex])}', cost)
    return 'not_run', 'translation B did not elaborate', cost


# ---------------------------------------------------------------- module, build, driver

MODULE_MARK = '-- Generated by autoform.nl.model'


def module_text(module: str, results: list) -> str:
    ns = f'Autoform.NLModel.{module}'
    body = [MODULE_MARK + ' (per-run build product; not tracked).', HEADER.rstrip(), '',
            '/-! Plain Lean models of Python functions, written by a language model and validated',
            'against CPython by differential testing (autoform.nl.model). See models.json for the',
            'evidence behind each definition; nothing here is trusted beyond it. -/', '',
            f'namespace {ns}', 'open Autoform.Core', PRELUDE]
    for r in results:
        body.append(f'-- model of {r.fn.info.name}: {r.record.status}'
                    + (f' ({r.record.level})' if r.record.level != 'none' else ''))
        body.append(r.lean_src.rstrip())
        body.append(f'-- end model of {r.fn.info.name}\n')
    body.append(dispatcher([(r.fn.info.name, r.lean_name) for r in results]))
    body.append(f'end {ns}\n')
    return '\n'.join(body)


def write_module(lean_root: Path, module: str, text: str) -> Path:
    """Write Autoform/NLModel/<module>.lean; never over a file this stage did not write."""
    nl_dir = lean_root / 'Autoform' / 'NLModel'
    nl_dir.mkdir(parents=True, exist_ok=True)
    path = nl_dir / f'{module}.lean'
    if path.exists() and not path.read_text(errors='replace').startswith(MODULE_MARK):
        raise RuntimeError(f'{path} exists and was not written by the model stage; choose another module name')
    path.write_text(text)
    return path


def build(lean_root: Path, module: str) -> tuple:
    env = dict(os.environ)
    env['PATH'] = str(Path.home() / '.elan/bin') + os.pathsep + env.get('PATH', '')
    t0 = time.time()
    with LEAN_SLOTS:
        try:
            proc = subprocess.run([lake(), 'build', f'Autoform.NLModel.{module}'], cwd=str(lean_root),
                                  env=env, capture_output=True, text=True, timeout=BUILD_TIMEOUT)
            ok, log = proc.returncode == 0, proc.stdout + proc.stderr
        except subprocess.TimeoutExpired:
            ok, log = False, f'lake build timed out after {BUILD_TIMEOUT}s'
    return ok, log[-4000:], round(time.time() - t0, 1)


def smoke(lean_root: Path, module: str, results: list, work: Path) -> list:
    """Re-run every recorded point through the BUILT module; return mismatches."""
    ns = f'Autoform.NLModel.{module}'
    rows, expect = [], []
    for r in results:
        for p, o in zip(r.points, r.outputs):
            rows.append(f'({pv.lean_str(r.fn.info.name)}, [' + ', '.join(pv.lean_lit(t) for t in p) + '])')
            expect.append((r.fn.info.name, o))
    if not rows:
        return []
    text = (f'import Autoform.NLModel.{module}\n' + HEADER.split('\n', 1)[1] +
            'namespace AutoformNLSmoke\nopen Autoform.Core\n' + RENDER +
            'def pts : List (String × List Val) := [\n  ' + ',\n  '.join(rows) + ']\n'
            f'#eval (pts.zipIdx.forM fun (p, i) => IO.println ("AFR " ++ toString i ++ " " ++ '
            f'rr ({ns}.call p.1 p.2)))\nend AutoformNLSmoke\n')
    path = work / 'smoke.lean'
    path.write_text(text)
    code, log, _ = run_lean(lean_root, path)
    outs = {int(m.group(1)): m.group(2) for m in re.finditer(r'^AFR (\d+) (.*)$', log, re.M)}
    bad = []
    for i, (name, o) in enumerate(expect):
        if outs.get(i) != o:
            bad.append({'function': name, 'point': i, 'expected': o, 'got': outs.get(i)})
    if code != 0 and not bad:
        bad.append({'error': log[-1500:]})
    return bad


def _levels(fns: list) -> list:
    """Topological levels over repository call edges (callees first); cycles share a level."""
    names = {f.info.name for f in fns}
    deps = {f.info.name: {c for c in f.callees if c in names and c != f.info.name} for f in fns}
    levels, placed = [], set()
    by_name = {f.info.name: f for f in fns}
    while len(placed) < len(fns):
        ready = [n for n in deps if n not in placed and deps[n] <= placed]
        if not ready:   # a cycle: take everything left whose deps are placed or in the cycle
            ready = [n for n in deps if n not in placed]
        levels.append([by_name[n] for n in sorted(ready)])
        placed |= set(ready)
    return levels


def source_revision(source_root: Path) -> str:
    import importlib.util
    try:
        spec = importlib.util.spec_from_file_location(
            '_autoform_provenance', HERE.parents[3] / 'scripts' / 'provenance.py')
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return mod.source_revision(Path(source_root))
    except Exception as exc:   # noqa: BLE001
        return f'unavailable: {type(exc).__name__}'


def default_module(source_root) -> str:
    from .pipeline import default_module as dm
    return dm(str(source_root))


def model(source_root, out_dir, lean_root, *, module=None, functions=None, parallel=3, repairs=3,
          second=True, tests=(), ask=None, do_build=True) -> schema.Translation:
    """Model every pure-enough function; write translation.json, models.json and the module."""
    t0 = time.time()
    source_root, out_dir, lean_root = Path(source_root).resolve(), Path(out_dir), Path(lean_root).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    module = module or default_module(source_root)
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*', module):
        raise ValueError(f'module name {module!r} must be a capitalized Lean identifier')
    work = out_dir / 'model-work'
    fns, _ = _discover(source_root, functions, tests)
    attempt = [f for f in fns if f.reason is None]
    skipped = [f for f in fns if f.reason is not None]
    notes = [f'skipped {f.info.name}: {f.reason}' for f in skipped]
    if functions:
        found = {f.info.name for f in fns} | {f.info.source_name for f in fns} | {f.qual for f in fns}
        notes += [f'requested function {w!r} not found' for w in functions if w not in found]
    t_trace = time.time()
    traced, trace_stats = trace_tests(attempt, source_root, _test_dirs(source_root, tests), work / 'trace')
    trace_secs = round(time.time() - t_trace, 1)
    taken: set = set()
    names = {f.info.name: lean_ident(f.info.name, taken) for f in attempt}
    done: dict = {}
    order = []
    for level in _levels(attempt):
        def job(f):
            stem = re.sub(r'[^A-Za-z0-9_]', '_', names[f.info.name])
            return model_function(f, names[f.info.name], module, lean_root, work / stem,
                                  traced.get(f.info.name, []), dict(done), repairs=repairs, second=second, ask=ask)
        with ThreadPoolExecutor(max_workers=max(1, parallel)) as pool:
            for r in pool.map(job, level):
                done[r.fn.info.name] = r
                order.append(r)
    modelled = [r for r in order if r.lean_src]
    build_info = {}
    if modelled:
        text = module_text(module, modelled)
        path = write_module(lean_root, module, text)
        build_info['module_file'] = str(path)
        if do_build:
            ok, log, secs = build(lean_root, module)
            build_info.update(ok=ok, seconds=secs)
            if not ok:
                build_info['log'] = log
                notes.append('lake build of the model module FAILED: ' + log[-600:])
            else:
                mism = smoke(lean_root, module, modelled, work)
                build_info['smoke_mismatches'] = mism[:20]
                if mism:
                    notes.append(f'built module disagrees with the per-function runs at {len(mism)} points')
    infos = []
    for r in order:
        rec = r.record
        if not r.lean_src:
            notes.append(f'FAILED {r.fn.info.name}: {rec.notes[:300]}')
            continue
        info = r.fn.info
        info.needs_init = False
        if r.sig is not None:
            for p, sp in zip(info.params, r.sig.params):
                p.sort = sort_of(sp['type']) if sp['kind'] == 'positional' else 'any'
            info.returns = sort_of(r.sig.returns)
        ok = rec.status in ('VALIDATED', 'UNTESTABLE')
        info.hole_free = info.call_closed = ok
        info.holes = [] if ok else [f'nl:model-{rec.status.lower()}']
        infos.append(info)
        if rec.second_translation == 'disagrees':
            notes.append(f'{info.name}: translation B disagrees with A ({rec.status}); level none')
    tr = schema.Translation(
        module=module, language='python', lean_root=str(lean_root), source_root=str(source_root),
        source_revision=source_revision(source_root), ast='', program_const='', init_const=None,
        call_template=f'Autoform.NLModel.{module}.call {{name}} {{args}}', fuel=0, functions=infos, notes=notes)
    schema.dump(tr, out_dir / schema.FILES['translation'])
    schema.dump([r.record for r in order], out_dir / schema.FILES['models'])
    meta = {
        'module': module, 'discovered': len(fns), 'attempted': len(attempt), 'skipped': len(skipped),
        'statuses': {s: sum(1 for r in order if r.record.status == s)
                     for s in ('VALIDATED', 'DISAGREES', 'UNTESTABLE', 'FAILED')},
        'L0': sum(1 for r in order if r.record.level == 'L0'),
        'cost_usd': round(sum(r.cost for r in order), 4), 'seconds': round(time.time() - t0, 1),
        'trace_seconds': trace_secs, 'trace': trace_stats, 'build': build_info,
        'functions': [{'function': r.fn.info.name, 'lean_name': r.lean_name, 'status': r.record.status,
                       'tests_run': r.record.tests_run, 'repairs': r.record.repairs,
                       'second_translation': r.record.second_translation, 'level': r.record.level,
                       'cost_usd': round(r.cost, 4), 'seconds': r.seconds, 'log': r.log} for r in order],
    }
    (out_dir / 'model.meta.json').write_text(json.dumps(meta, indent=1, default=str))
    return tr


def main(argv=None) -> int:
    import argparse
    ap = argparse.ArgumentParser(prog='python -m autoform.nl.model',
                                 description='AI-written Lean models of Python functions, validated by '
                                             'differential testing against CPython.')
    ap.add_argument('source', type=Path)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--module', help='Lean module suffix (Autoform.NLModel.<Module>)')
    ap.add_argument('--function', action='append', help='only these (source, qualified or file names)')
    ap.add_argument('--lean-root', type=Path, help='lake root (default: this checkout)')
    ap.add_argument('--tests', action='append', default=[], help='extra test directory (named tests)')
    ap.add_argument('--parallel', type=int, default=3)
    ap.add_argument('--repairs', type=int, default=3)
    ap.add_argument('--no-second', action='store_true', help='skip the independent translation B')
    ap.add_argument('--no-build', action='store_true')
    fuzz.add_arguments(ap)
    a = ap.parse_args(argv)
    fuzz.configure(a)
    from .pipeline import default_lean_root
    tr = model(a.source, a.out, a.lean_root or default_lean_root(), module=a.module, functions=a.function,
               parallel=a.parallel, repairs=a.repairs, second=not a.no_second, tests=a.tests,
               do_build=not a.no_build)
    meta = json.loads((a.out / 'model.meta.json').read_text())
    for f in meta['functions']:
        print(f"{f['status']:10s} {f['level']:4s} tests={f['tests_run']:<4d} repairs={f['repairs']} "
              f"B={f['second_translation']:9s} ${f['cost_usd']:<7} {f['function']}")
    print(f"module Autoform.NLModel.{tr.module}: {meta['statuses']}, L0 {meta['L0']}, "
          f"skipped {meta['skipped']}, ${meta['cost_usd']}, {meta['seconds']}s -> {a.out}")
    return 0 if meta['statuses'].get('VALIDATED') else 1


if __name__ == '__main__':
    sys.exit(main())
