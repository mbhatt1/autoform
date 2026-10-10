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
from dataclasses import dataclass, field
from pathlib import Path

from . import fuzz, llm, pyvalues as pv, schema
from .formalize import LEAN_SLOTS, lake

HERE = Path(__file__).resolve()
PYVALUES = HERE.with_name('pyvalues.py')
LEAN_TIMEOUT = 600
BUILD_TIMEOUT = 1800
TRACE_TIMEOUT = 900
# The interpreter that runs the code under test (tracer, differential runner, check stage).
SUBJECT_PYTHON = os.environ.get('AUTOFORM_PYTHON') or sys.executable
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
    'weakref': 'object lifetime', 'inspect': 'reflection', 'urllib3': 'network', 'ssl': 'network',
    'email': 'I/O', 'mimetypes': 'environment', 'netrc': 'file access',
}
MUTATING_METHODS = {'append', 'extend', 'insert', 'pop', 'remove', 'clear', 'update', 'add', 'discard',
                    'setdefault', 'popitem', 'sort', 'reverse', 'write', '__setitem__', '__delitem__'}
PURE_DECORATORS = {'staticmethod', 'functools.lru_cache', 'lru_cache', 'functools.cache', 'cache', 'property'}
# Bases whose instances carry a builtin payload (not attributes): not modelled as structures.
BUILTIN_BASES = {'dict', 'list', 'set', 'frozenset', 'tuple', 'str', 'bytes', 'bytearray', 'int', 'float',
                 'complex', 'bool', 'collections.OrderedDict', 'collections.defaultdict', 'collections.deque',
                 'collections.Counter', 'OrderedDict', 'defaultdict', 'deque', 'Counter'}
EXCEPTION_BASES = re.compile(r'(^|\.)(BaseException|Exception|\w+Error|\w+Warning)$')
# Receiver syntax that calls a dunder method of the receiver's class.
SYNTAX_DUNDERS = {'getitem': '__getitem__', 'setitem': '__setitem__', 'delitem': '__delitem__',
                  'contains': '__contains__', 'len': '__len__', 'iter': '__iter__'}


@dataclass
class _Class:
    """A class defined in the repository (the unit a Lean structure is generated for)."""
    name: str                           # Python name
    qual: str                           # qualified within its module ("Outer.Inner")
    mod: '_Module'
    node: ast.ClassDef
    bases: list = field(default_factory=list)     # [('repo', _Class) | ('builtin', dotted) | ('external', dotted)]
    methods: dict = field(default_factory=dict)   # mangled name -> FunctionDef
    reason: str | None = None                     # why its methods are not modelled

    @property
    def dotted(self) -> str:
        """`type(obj).__module__ + '.' + __qualname__` of its instances (pyvalues.class_name)."""
        return f'{self.mod.dotted or self.mod.path.stem}.{self.qual}'

    def mro(self) -> list:
        """Repository classes in method-resolution order (left-to-right depth-first, deduplicated
        keeping the last occurrence, which agrees with C3 for the hierarchies found in practice)."""
        seq = []

        def visit(c):
            seq.append(c)
            for kind, b in c.bases:
                if kind == 'repo':
                    visit(b)
        visit(self)
        out = []
        for i, c in enumerate(seq):
            if c not in seq[i + 1:]:
                out.append(c)
        return out

    def external_bases(self) -> list:
        out = []
        for c in self.mro():
            out += [b for k, b in c.bases if k == 'external' and b not in out]
        return out

    def lookup(self, attr: str):
        """(defining _Class, FunctionDef) of a method along the repository MRO, or None."""
        for c in self.mro():
            if attr in c.methods:
                return c, c.methods[attr]
        return None


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
    classes: dict = field(default_factory=dict)   # qualified class name -> _Class
    repo_tops: set = field(default_factory=set)   # top-level packages of the repository itself


@dataclass
class _Fn:
    info: schema.FunctionInfo
    node: ast.AST
    mod: _Module
    qual: str                           # "Class.meth" / "f"
    first_lines: list                   # def line and decorator lines (co_firstlineno candidates)
    reason: str | None = None           # why it is not attempted
    callees: list = field(default_factory=list)
    kind: str = 'function'              # function | static | method | property | constructor
    cls: _Class | None = None           # the receiver's class (methods, properties, constructors)
    unmodelled: list = field(default_factory=list)   # receiver calls that leave the model

    @property
    def attr(self) -> str:
        return self.qual.rsplit('.', 1)[-1]

    @property
    def has_receiver(self) -> bool:
        return self.kind in ('method', 'property')


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


def _collect_classes(mod: _Module):
    def visit(body, prefix):
        for n in body:
            if isinstance(n, ast.ClassDef):
                c = _Class(n.name, prefix + n.name, mod, n)
                for m in n.body:
                    if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        c.methods[_mangle(m.name, n.name)] = m
                mod.classes[c.qual] = c
                visit(n.body, prefix + n.name + '.')
    visit(mod.tree.body, '')


def _resolve_class(mod: _Module, expr, by_dotted: dict):
    """A base-class expression → ('repo', _Class) | ('builtin', name) | ('external', dotted)."""
    dotted = _dotted(expr) or ast.unparse(expr)
    head, _, rest = dotted.partition('.')
    if dotted in mod.classes:
        return 'repo', mod.classes[dotted]
    imp = mod.imports.get(head)
    full = dotted
    if imp:
        full = '.'.join(([imp[1]] if imp[0] == 'module' else [x for x in (imp[1], imp[2]) if x])
                        + ([rest] if rest else []))
        for i in range(full.count('.'), 0, -1):
            mname, cq = full.rsplit('.', i)[0], '.'.join(full.split('.')[-i:])
            other = by_dotted.get(mname)
            if other is not None and cq in other.classes:
                return 'repo', other.classes[cq]
        # re-exported through a repository module (`from .compat import MutableMapping`)
        mname, _, name = full.rpartition('.')
        other = by_dotted.get(mname)
        if other is not None and name in other.imports:
            inner = other.imports[name]
            full = '.'.join([inner[1]] if inner[0] == 'module' else [x for x in (inner[1], inner[2]) if x])
    if dotted in BUILTIN_BASES or full in BUILTIN_BASES or full.startswith('builtins.'):
        return 'builtin', full
    return 'external', full


def _link_classes(mods: dict):
    by_dotted = {m.dotted: m for m in mods.values() if m.dotted}
    for mod in mods.values():
        for c in mod.classes.values():
            c.bases = [_resolve_class(mod, b, by_dotted) for b in c.node.bases]
    for mod in mods.values():
        for c in mod.classes.values():
            for k in c.mro():
                bad = [b for kind, b in k.bases if kind == 'builtin']
                if bad:
                    c.reason = (f'class with a builtin base ({bad[0]}): its instances carry a builtin '
                                'payload, not attributes')
                    break
                exc = [b for kind, b in k.bases if kind == 'external' and EXCEPTION_BASES.search(b)]
                if exc:
                    c.reason = f'exception class (base {exc[0]})'
                    break
            if c.reason is None and any(isinstance(d, ast.Call) or _dotted(d) not in (None, 'dataclass')
                                        for d in c.node.decorator_list):
                c.reason = 'decorated class (the decorator may change its instances)'
            if c.reason is None and any(k.node.keywords for k in c.mro()):
                c.reason = 'class with keywords in its bases (metaclass)'


def method_kind(node, cls) -> str:
    if cls is None:
        return 'function'
    decos = _decorator_names(node)
    if 'staticmethod' in decos:
        return 'static'
    if 'property' in decos:
        return 'property'
    if node.name == '__init__':
        return 'constructor'
    return 'method'


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
    if top in mod.repo_tops:        # the repository's own package (e.g. `requests` inside requests)
        return None
    if top in IMPURE_MODULES:
        return top
    return None


def screen(node, mod: _Module, cls=None) -> str | None:
    """Why the function is not pure enough to model as a plain Lean def (None: attempt it).

    Methods are attempted: the receiver becomes a Lean structure and a method that mutates
    it returns the new structure (see `method_kind`). What stays out: real I/O, time,
    randomness, network, subprocesses, module-level mutable state, generators, closures,
    classmethods (class-level state), property setters, and classes whose instances carry a
    builtin payload (dict/list/... bases) or are exceptions."""
    if isinstance(node, ast.AsyncFunctionDef):
        return 'async function (coroutine)'
    decos = _decorator_names(node)
    if cls is not None and 'staticmethod' not in decos:
        if isinstance(cls, _Class) and cls.reason:
            return cls.reason
        if 'classmethod' in decos:
            return 'classmethod (class-level state is not modelled)'
        if any(d.endswith(('.setter', '.deleter')) for d in decos):
            return 'property setter/deleter (called through attribute assignment)'
        a = node.args
        if not (a.posonlyargs + a.args):
            return 'method without a receiver parameter'
    elif 'classmethod' in decos:
        return 'classmethod (class-level state is not modelled)'
    other = [d for d in decos if d not in PURE_DECORATORS and not (d == 'property' and cls is not None)]
    if cls is None and 'property' in decos:
        other.append('property')
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


EFFECT_WORDS = tuple(sorted(set(IMPURE_MODULES.values()) | set(IMPURE_CALLS.values()) | {'module-level state'}))


def _effectful(f) -> bool:
    """Is `f` excluded because it has an external effect (I/O, time, randomness, network,
    module state...), as opposed to a modelling limitation (generator, closure, ...)?"""
    return f is not None and bool(f.reason) and any(w in f.reason for w in EFFECT_WORDS)


def _instantiated(node, mod: '_Module', by_dotted: dict) -> list:
    """Repository classes the body calls (instantiates): `C(...)`, `mod.C(...)`."""
    out = []
    local = _local_names(node)
    for n in ast.walk(node):
        if not isinstance(n, ast.Call):
            continue
        dotted = _dotted(n.func)
        if not dotted or dotted.split('.')[0] in local:
            continue
        try:
            kind, target = _resolve_class(mod, n.func, by_dotted)
        except (KeyError, ValueError):
            continue
        if kind == 'repo' and target not in out:
            out.append(target)
    return out


def _fn_name(c: _Class, attr: str) -> str:
    return f'{c.mod.rel}:<module>.{c.qual}.{attr}'


def _receiver_uses(node, recv: str) -> list:
    """Methods of the receiver `recv` the body uses: explicit calls `recv.m(...)`, attribute
    reads `recv.m` that may be properties, and syntax (`recv[k]`, `k in recv`, `len(recv)`,
    `del recv[k]`, `iter(recv)`, `for x in recv`)."""
    out = []

    def add(a):
        if a not in out:
            out.append(a)
    for n in ast.walk(node):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and isinstance(n.func.value, ast.Name) \
                and n.func.value.id == recv:
            add(n.func.attr)
        elif isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name) and n.value.id == recv:
            add(n.attr)
        elif isinstance(n, ast.Subscript) and isinstance(n.value, ast.Name) and n.value.id == recv:
            add({ast.Load: '__getitem__', ast.Store: '__setitem__', ast.Del: '__delitem__'}[type(n.ctx)])
        elif isinstance(n, ast.Compare) and any(isinstance(o, (ast.In, ast.NotIn)) for o in n.ops) \
                and any(isinstance(c, ast.Name) and c.id == recv for c in n.comparators):
            add('__contains__')
        elif isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in ('len', 'iter') \
                and n.args and isinstance(n.args[0], ast.Name) and n.args[0].id == recv:
            add('__len__' if n.func.id == 'len' else '__iter__')
        elif isinstance(n, (ast.For, ast.comprehension)) and isinstance(n.iter, ast.Name) and n.iter.id == recv:
            add('__iter__')
    return out


def _method_links(fn: '_Fn', mods_by_dotted: dict):
    """Callees and unmodelled receiver calls of a method (fills fn.callees / fn.unmodelled)."""
    node, cls = fn.node, fn.cls
    a = node.args
    recv = (a.posonlyargs + a.args)[0].arg if fn.kind in ('method', 'property', 'constructor') and \
        (a.posonlyargs + a.args) else None
    if recv:
        for attr in _receiver_uses(node, recv):
            mangled = _mangle(attr, cls.name) if attr.startswith('__') and not attr.endswith('__') else attr
            hit = cls.lookup(mangled)
            if hit is not None:
                name = _fn_name(hit[0], mangled)
                if name != fn.info.name and name not in fn.callees:
                    fn.callees.append(name)
            elif cls.external_bases() and not any(t.attr == attr for t in _stored_attrs(cls)) \
                    and mangled not in _class_data(cls):
                ext = ', '.join(cls.external_bases())
                note = (f'{recv}.{attr}: inherited from an external base ({ext}); not modelled')
                if attr.startswith('__') and attr.endswith('__') and attr not in SYNTAX_DUNDERS.values():
                    continue      # object protocol (e.g. __class__), not a mixin method
                if note not in fn.unmodelled:
                    fn.unmodelled.append(note)
    # `Base.meth(self, ...)` and default-argument aliases `f=Base.meth` on repository classes
    exprs = [n.func for n in ast.walk(node) if isinstance(n, ast.Call)] + list(a.defaults)
    for e in exprs:
        dotted = _dotted(e) if isinstance(e, ast.Attribute) else None
        if not dotted:
            continue
        head, _, attr = dotted.rpartition('.')
        kind, target = _resolve_class(fn.mod, ast.parse(head, mode='eval').body, mods_by_dotted) \
            if head else (None, None)
        if kind == 'repo':
            mangled = _mangle(attr, target.name)
            hit = target.lookup(mangled)
            if hit is not None:
                name = _fn_name(hit[0], mangled)
                if name != fn.info.name and name not in fn.callees:
                    fn.callees.append(name)


def _class_data(cls: _Class) -> set:
    """Names assigned in the class bodies along the repository MRO (class attributes)."""
    out = set()
    for c in cls.mro():
        for n in c.node.body:
            targets = n.targets if isinstance(n, ast.Assign) else [n.target] if isinstance(n, ast.AnnAssign) else []
            for t in targets:
                if isinstance(t, ast.Name):
                    out.add(_mangle(t.id, c.name))
    return out


def _stored_attrs(cls: _Class) -> list:
    """`self.x = ...` targets anywhere in the class's repository MRO (instance attributes)."""
    out = []
    for c in cls.mro():
        for m in c.methods.values():
            args = m.args.posonlyargs + m.args.args
            if not args:
                continue
            recv = args[0].arg
            for n in ast.walk(m):
                if isinstance(n, ast.Attribute) and isinstance(n.ctx, ast.Store) and \
                        isinstance(n.value, ast.Name) and n.value.id == recv:
                    out.append(n)
    return out


def static_fields(cls: _Class) -> list:
    """Instance attribute names from `__slots__` and `self.x = ...` along the repository MRO
    (private names mangled by their defining class)."""
    out = []
    for c in cls.mro():
        for n in c.node.body:
            if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == '__slots__' for t in n.targets):
                try:
                    slots = ast.literal_eval(n.value)
                except ValueError:
                    slots = ()
                for s in ([slots] if isinstance(slots, str) else slots):
                    s = _mangle(s, c.name)
                    if s not in out:
                        out.append(s)
        for m in c.methods.values():
            args = m.args.posonlyargs + m.args.args
            if not args:
                continue
            for n in ast.walk(m):
                if isinstance(n, ast.Attribute) and isinstance(n.ctx, ast.Store) and \
                        isinstance(n.value, ast.Name) and n.value.id == args[0].arg:
                    s = _mangle(n.attr, c.name)
                    if s not in out:
                        out.append(s)
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
    tops = {m.dotted.split('.')[0] for m in mods.values() if m.dotted}
    for mod in mods.values():
        mod.repo_tops = tops
        _collect_classes(mod)
        for node, qual, cls in _walk_defs(mod):
            if cls is None:
                mod.top_funcs[node.name] = f'{mod.rel}:<module>.{qual}'
    _link_classes(mods)
    by_dotted = {m.dotted: m for m in mods.values() if m.dotted}
    fns = []
    for mod in mods.values():
        lines = mod.text.splitlines(keepends=True)
        for node, qual, cls in _walk_defs(mod):
            name = f'{mod.rel}:<module>.{qual}'
            params = _params(node)
            klass = mod.classes.get(qual.rsplit('.', 1)[0]) if cls is not None else None
            kind = method_kind(node, klass)
            if kind in ('method', 'property') and params:
                params[0].sort = 'object'
            elif kind == 'constructor' and params:
                params = params[1:]       # `Cls(args)`: the receiver is created, not passed
            info = schema.FunctionInfo(
                name=name, source_name=node.name, file=mod.rel, line=node.lineno, params=params,
                returns='object' if kind == 'constructor' else _annotation_sort(node.returns), hole_free=False,
                holes=[], call_closed=False, needs_init=False, source=_segment(lines, node),
                doc=ast.get_docstring(node) or '', kind=kind, receiver=klass.dotted if klass else '')
            fn = _Fn(info, node, mod, qual, [node.lineno] + [d.lineno for d in node.decorator_list],
                     kind=kind, cls=klass)
            fn.reason = screen(node, mod, klass)
            fn.callees = _callees(node, mod, by_dotted, _local_names(node))
            if klass is not None and kind != 'static':
                _method_links(fn, by_dotted)
            fns.append(fn)
    by_name = {f.info.name: f for f in fns}
    for f in fns:
        for c in f.callees:
            if c in by_name and f.info.name not in by_name[c].info.callers:
                by_name[c].info.callers.append(f.info.name)
    # impurity is transitive through repository callees, and through the repository classes a
    # function instantiates: an object whose methods do I/O, time, randomness, ... (e.g. a
    # session that sends requests) makes its creator impure, since the calls on it are not tracked
    made = {id(f): _instantiated(f.node, f.mod, by_dotted) for f in fns}
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
            if f.reason:
                continue
            for cls in made[id(f)]:
                bad = next(((c, m) for c in cls.mro() for m in c.methods
                            if _effectful(by_name.get(_fn_name(c, m)))), None)
                if bad is not None:
                    g = by_name[_fn_name(*bad)]
                    f.reason = f'creates a {cls.name}, whose method {g.qual} is not pure ({g.reason})'
                    changed = True
                    break
    # a method's receiver is built by its class's __init__: if that is not modelled because it
    # uses time, randomness, I/O, ... (e.g. a `timer=time.monotonic` default), neither is the method
    for f in fns:
        if f.reason is None and f.cls is not None and f.kind in ('method', 'property'):
            hit = f.cls.lookup('__init__')
            init = by_name.get(_fn_name(hit[0], '__init__')) if hit else None
            if init is not None and init.reason and not init.reason.startswith('its receiver'):
                f.reason = f'its receiver is built by {init.qual}, which is not modelled ({init.reason})'
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
           'Unit': ('dUnit', 'eUnit'), 'Val': ('dVal', 'id'), 'Fl': ('dFl', 'Val.float'),
           'Bytes': ('dBytes', 'eBytes')}
UNARY = {'Option': ('dOpt', 'eOpt'), 'List': ('dList', 'eList'), 'Tuple': ('dTuple', 'eTuple'),
         'PySet': ('dSet', 'eSet'), 'FrozenSet': ('dFrozenSet', 'eFrozenSet')}
SORT_OF = {'Int': 'int', 'Bool': 'bool', 'String': 'str', 'Fl': 'float'}
TYPE_TOKEN = re.compile(r'\s*(×|\(|\)|[A-Za-z_][A-Za-z0-9_.]*)')
TYPE_HELP = ('use Int, Bool, String, Unit, Val, Fl, Bytes, Option τ, List τ, Tuple τ, PySet τ, FrozenSet τ, '
             'Dict κ ν, τ × σ, Except String τ, or the receiver structure')


class TypeError_(ValueError):
    pass


def parse_type(text: str, structs=()):
    """'List (Option Int) × String' → ('Prod', [('List', ('Option', 'Int')), 'String']).

    Atoms are the SCALARS and the names in `structs` (generated receiver structures, parsed
    as ('Struct', name)); `Dict κ ν` is ('Dict', κ, ν)."""
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
        if i < len(toks) and toks[i] in UNARY:
            head = toks[i]
            i += 1
            return (head, atom())
        if i < len(toks) and toks[i] == 'Dict':
            i += 1
            k = atom()
            return ('Dict', k, atom())
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
        if t in structs:
            return ('Struct', t)
        hint = ' (use Int for Python int)' if t == 'Nat' else ' (use Fl, never Float)' if t == 'Float' else \
            ' (a Python set is PySet τ)' if t in ('Set', 'Finset', 'HashSet') else \
            ' (a Python dict is Dict κ ν)' if t in ('HashMap', 'RBMap', 'Std.HashMap', 'AssocList') else ''
        raise TypeError_(f'unsupported type {t!r}{hint}; {TYPE_HELP}')

    out = prod()
    if i != len(toks):
        raise TypeError_(f'trailing tokens in type {text!r}')
    if isinstance(out, tuple) and out[0] == 'Prod' and len(out[1]) > 4:
        raise TypeError_('tuples of more than 4 components are not supported (use Tuple Val)')
    return out


def _children(t) -> list:
    if isinstance(t, str):
        return []
    if t[0] == 'Prod':
        return list(t[1])
    if t[0] == 'Dict':
        return [t[1], t[2]]
    if t[0] == 'Struct':
        return []
    return [t[1]]


def _has_except(t) -> bool:
    if isinstance(t, str):
        return False
    return t[0] == 'Except' or any(_has_except(x) for x in _children(t))


def decoder(t) -> str:
    if isinstance(t, str):
        return SCALARS[t][0]
    if t[0] == 'Struct':
        return f'dObj_{t[1]}'
    if t[0] in UNARY:
        return f'({UNARY[t[0]][0]} {decoder(t[1])})'
    if t[0] == 'Dict':
        return f'(dDict {decoder(t[1])} {decoder(t[2])})'
    if t[0] == 'Prod':
        return f'(dTup{len(t[1])} ' + ' '.join(decoder(x) for x in t[1]) + ')'
    raise TypeError_('Except is only allowed as the outermost return type')


def encoder(t) -> str:
    if isinstance(t, str):
        return SCALARS[t][1]
    if t[0] == 'Struct':
        return f'eObj_{t[1]}'
    if t[0] in UNARY:
        return f'({UNARY[t[0]][1]} {encoder(t[1])})'
    if t[0] == 'Dict':
        return f'(eDict {encoder(t[1])} {encoder(t[2])})'
    if t[0] == 'Prod':
        return f'(eTup{len(t[1])} ' + ' '.join(encoder(x) for x in t[1]) + ')'
    raise TypeError_('Except is only allowed as the outermost return type')


def show_type(t) -> str:
    """Lean text of a parsed type (for prompts and records)."""
    if isinstance(t, str):
        return t
    if t[0] == 'Struct':
        return t[1]
    if t[0] == 'Prod':
        return ' × '.join(f'({show_type(x)})' if isinstance(x, tuple) and x[0] == 'Prod' else show_type(x)
                          for x in t[1])
    args = _children(t)
    return t[0] + ' ' + ' '.join(show_type(x) if isinstance(x, str) or x[0] == 'Struct' else f'({show_type(x)})'
                                 for x in args) if t[0] != 'Except' else f'Except String ({show_type(t[1])})'


def sort_of(t) -> str:
    if isinstance(t, tuple) and t[0] == 'Except':
        t = t[1]
    if isinstance(t, tuple) and t[0] == 'Struct':
        return 'object'
    return SORT_OF.get(t, 'any') if isinstance(t, str) else 'any'


@dataclass
class Sig:
    params: list        # [{'name', 'type': parsed, 'kind', 'default'}]
    returns: object     # parsed return type (may be ('Except', τ))
    kind: str = 'function'      # function | static | method | property | constructor
    struct: str | None = None   # the receiver structure (methods) / the constructed one
    mutates: bool = False       # returns (result, receiver') — a method that changes its receiver

    @property
    def raises(self) -> bool:
        return isinstance(self.returns, tuple) and self.returns[0] == 'Except'

    @property
    def inner(self):
        return self.returns[1] if self.raises else self.returns

    @property
    def result(self):
        """The Python-visible result type (the first component for a mutating method)."""
        return self.inner[1][0] if self.mutates else self.inner


def parse_sig(params: list, returns: str, *, structs=(), kind: str = 'function', struct: str | None = None,
              mutates=False) -> Sig:
    out, seen_default, var = [], False, 0
    for i, p in enumerate(params or []):
        if not isinstance(p, dict):
            raise TypeError_(f'parameter #{i + 1} is not an object')
        pkind = str(p.get('kind') or 'positional')
        if pkind not in ('positional', 'varargs'):
            raise TypeError_(f'parameter kind {pkind!r} must be positional or varargs')
        t = parse_type(str(p.get('type', '')), structs)
        if _has_except(t):
            raise TypeError_('parameters cannot have an Except type')
        default = p.get('default')
        default = None if default in (None, '', 'null') else str(default)
        if pkind == 'varargs':
            var += 1
            if not (isinstance(t, tuple) and t[0] == 'List'):
                raise TypeError_('a varargs parameter must have type `List τ`')
            if i != len(params) - 1:
                raise TypeError_('the varargs parameter must be last')
        elif default is not None:
            seen_default = True
        elif seen_default:
            raise TypeError_('a parameter without default follows one with a default')
        out.append({'name': str(p.get('name', f'p{i}')), 'type': t, 'kind': pkind, 'default': default})
    if var > 1:
        raise TypeError_('at most one varargs parameter')
    r = parse_type(str(returns or ''), structs)
    inner = r[1] if isinstance(r, tuple) and r[0] == 'Except' else r
    if _has_except(inner):
        raise TypeError_('Except must be the outermost return type')
    mutates = bool(mutates) and mutates not in ('false', 'False', 0)
    if kind in ('method', 'property'):
        if not out or out[0]['type'] != ('Struct', struct) or out[0]['kind'] != 'positional' \
                or out[0]['default'] is not None:
            raise TypeError_(f'the first parameter must be the receiver `self` of type {struct} (no default)')
        if mutates:
            if not (isinstance(inner, tuple) and inner[0] == 'Prod' and len(inner[1]) == 2
                    and inner[1][1] == ('Struct', struct)):
                raise TypeError_(f'a mutating method ("mutates": true) returns `τ × {struct}` (or '
                                 f'`Except String (τ × {struct})`): the Python result and the receiver after '
                                 f'the call; write a product result type in parentheses: `(A × B) × {struct}`')
    elif mutates:
        raise TypeError_('"mutates" is only for methods')
    if kind == 'constructor':
        if inner != ('Struct', struct):
            raise TypeError_(f'the constructor (__init__) returns the new object: `{struct}` or '
                             f'`Except String {struct}`; do not list `self` as a parameter')
        if any(p['type'] == ('Struct', struct) and p['name'] == 'self' for p in out):
            raise TypeError_('the constructor does not take `self`: list only the arguments after it')
    return Sig(out, r, kind, struct, mutates)


def _alternatives(sig: Sig) -> list:
    """[(pattern, [decoder exprs], [bind patterns], [lean call args])] for each accepted arity."""
    fixed = [p for p in sig.params if p['kind'] == 'positional']
    var = next((p for p in sig.params if p['kind'] == 'varargs'), None)
    required = sum(1 for p in fixed if p['default'] is None)
    arities = [len(fixed)] if var else list(range(len(fixed), required - 1, -1))
    out = []
    for k in arities:
        pats = [f'a{i}' for i in range(k)]
        pattern = ' :: '.join(pats + ['rest']) if var else '[' + ', '.join(pats) + ']'
        discr = [f'{decoder(fixed[i]["type"])} a{i}' for i in range(k)]
        binds = [f'some x{i}' for i in range(k)]
        args = [f'x{i}' for i in range(k)] + [f'({fixed[i]["default"]})' for i in range(k, len(fixed))]
        if var:
            discr.append(f'dListAux {decoder(var["type"][1])} rest')
            binds.append('some xs')
            args.append('xs')
        out.append((pattern, discr, binds, args))
    return out


def _one_wrapper(name: str, lean_name: str, sig: Sig, enc_of) -> str:
    """`def name : List Val → EResult` over every arity; `enc_of(args)` is the result encoder."""
    res = 'resE' if sig.raises else 'resV'
    lines = [f'def {name} : List Val → EResult']
    for pattern, discr, binds, args in _alternatives(sig):
        app = f'({lean_name} {" ".join(args)})' if args else lean_name
        call = f'{res} {enc_of(args)} {app}'
        if discr:
            body = (f'\n    match {", ".join(discr)} with\n    | {", ".join(binds)} => {call}\n'
                    f'    | {", ".join("_" for _ in discr)} => .hole "nl:arg-type"')
        else:
            body = f' {call}'
        lines.append(f'  | {pattern} =>{body}')
    var = any(p['kind'] == 'varargs' for p in sig.params)
    fixed = [p for p in sig.params if p['kind'] == 'positional']
    if not (var and not fixed):
        lines.append('  | _ => .hole "nl:arg-count"')
    return '\n'.join(lines) + '\n'


def wrapper(lean_name: str, sig: Sig) -> str:
    """The generated (never model-written) glue for one def: `call_<lean_name> : List Val →
    EResult` decodes, runs and encodes the Python-visible result. A method also gets
    `call_<lean_name>_post`, whose value is `.tuple [result, receiver after the call]` (a
    method that does not mutate returns its receiver unchanged)."""
    if sig.kind not in ('method', 'property'):
        return _one_wrapper(f'call_{lean_name}', lean_name, sig, lambda args: encoder(sig.inner))
    enc = encoder(sig.result)
    obj = encoder(('Struct', sig.struct))
    if sig.mutates:
        result = _one_wrapper(f'call_{lean_name}', lean_name, sig, lambda args: f'(eFst {enc})')
        post = _one_wrapper(f'call_{lean_name}_post', lean_name, sig, lambda args: f'(eTup2 {enc} {obj})')
    else:
        result = _one_wrapper(f'call_{lean_name}', lean_name, sig, lambda args: enc)
        post = _one_wrapper(f'call_{lean_name}_post', lean_name, sig, lambda args: f'(ePure {enc} {obj} {args[0]})')
    return result + '\n' + post


def dispatcher(entries: list) -> str:
    """entries: [(qualified name, lean_name[, kind])] → the `call` function. A method has a
    second entry `<qualified name>#post` (see `wrapper`)."""
    lines = ['def call (name : String) (args : List Val) : EResult :=', '  match name with']
    for e in entries:
        qual, lean_name = e[0], e[1]
        lines.append(f'  | {pv.lean_str(qual)} => call_{lean_name} args')
        if len(e) > 2 and e[2] in ('method', 'property'):
            lines.append(f'  | {pv.lean_str(qual + "#post")} => call_{lean_name}_post args')
    lines.append('  | _ => .hole "nl:unknown-function"')
    return '\n'.join(lines) + '\n'


CANON = r'''
mutual
def {v} : Val → String
  | .int n => "i:" ++ toString n
  | .bool b => "b:" ++ toString b
  | .str s => "s:" ++ toString (s.toList.map Char.toNat)
  | .unit => "none"
  | .float x => if x.isNaN then "f:nan" else "f:" ++ toString x.bits
  | .list vs => "L(" ++ {l} vs ++ ")"
  | .tuple vs => "T(" ++ {l} vs ++ ")"
  | .dict kvs => "D(" ++ {d} kvs ++ ")"
  | .fn n => "F:" ++ n
  | .bobj n v => "X:" ++ n ++ "(" ++ {v} v ++ ")"
  | _ => "?"
def {l} : List Val → String
  | [] => ""
  | v :: vs => {v} v ++ "," ++ {l} vs
def {d} : List (Val × Val) → String
  | [] => ""
  | (k, v) :: kvs => {v} k ++ "=" ++ {v} v ++ ";" ++ {d} kvs
end
'''

PRELUDE = r'''
/-! Argument decoding and result encoding shared by every model in this module.
Generated by autoform.nl.model; all definitions are structurally recursive, so the kernel
evaluates `call` on concrete arguments.

Python data in `Val` (see autoform/nl/pyvalues.py): tuples are `.tuple`, lists `.list`,
dicts `.dict` (association list in insertion order), bytes `.bobj "bytes" (.list [.int b..])`,
sets `.bobj "set" (.list elems)` with the elements sorted by their canonical string
(`canonV`) and deduplicated (the encoders below normalize, so a model may keep any order),
objects of modelled classes `.bobj "obj:<module>.<Class>" (.dict [(.str attr, v), ...])`
with the attributes sorted by name. -/
''' + CANON.replace('{v}', 'canonV').replace('{l}', 'canonL').replace('{d}', 'canonD') + r'''
abbrev Tuple (α : Type) := List α
abbrev Bytes := List Nat
abbrev PySet (α : Type) := List α
abbrev FrozenSet (α : Type) := List α
abbrev Dict (κ ν : Type) := List (κ × ν)
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
def dTuple {α : Type} (d : Val → Option α) : Val → Option (List α)
  | .tuple vs => dListAux d vs
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
def dByte : Val → Option Nat
  | .int n => if 0 ≤ n ∧ n < 256 then some n.toNat else none
  | _ => none
def dBytes : Val → Option (List Nat)
  | .bobj n (.list vs) => if n == "bytes" then dListAux dByte vs else none
  | _ => none
def dSet {α : Type} (d : Val → Option α) : Val → Option (List α)
  | .bobj n (.list vs) => if n == "set" then dListAux d vs else none
  | _ => none
def dFrozenSet {α : Type} (d : Val → Option α) : Val → Option (List α)
  | .bobj n (.list vs) => if n == "frozenset" then dListAux d vs else none
  | _ => none
def dPairs {κ ν : Type} (dk : Val → Option κ) (dv : Val → Option ν) :
    List (Val × Val) → Option (List (κ × ν))
  | [] => some []
  | (k, v) :: kvs => match dk k, dv v, dPairs dk dv kvs with
    | some a, some b, some r => some ((a, b) :: r)
    | _, _, _ => none
def dDict {κ ν : Type} (dk : Val → Option κ) (dv : Val → Option ν) : Val → Option (List (κ × ν))
  | .dict kvs => dPairs dk dv kvs
  | _ => none
def dField (k : String) : List (Val × Val) → Option Val
  | [] => none
  | (.str k', v) :: kvs => if k == k' then some v else dField k kvs
  | _ :: kvs => dField k kvs
def insKey (x : Val) : List Val → List Val
  | [] => [x]
  | y :: ys => if canonV x == canonV y then y :: ys
    else if decide (canonV x < canonV y) then x :: y :: ys else y :: insKey x ys
def sortKey : List Val → List Val
  | [] => []
  | x :: xs => insKey x (sortKey xs)
def eUnit (_ : Unit) : Val := .unit
def eOpt {α : Type} (e : α → Val) : Option α → Val
  | none => .unit
  | some a => e a
def eList {α : Type} (e : α → Val) (xs : List α) : Val := .list (xs.map e)
def eTuple {α : Type} (e : α → Val) (xs : List α) : Val := .tuple (xs.map e)
def eBytes (xs : List Nat) : Val := .bobj "bytes" (.list (xs.map fun n => .int n))
def eSet {α : Type} (e : α → Val) (xs : List α) : Val := .bobj "set" (.list (sortKey (xs.map e)))
def eFrozenSet {α : Type} (e : α → Val) (xs : List α) : Val := .bobj "frozenset" (.list (sortKey (xs.map e)))
def eDict {κ ν : Type} (ek : κ → Val) (ev : ν → Val) (kvs : List (κ × ν)) : Val :=
  .dict (kvs.map fun p => (ek p.1, ev p.2))
def eTup2 {α β : Type} (ea : α → Val) (eb : β → Val) : α × β → Val
  | (a, b) => .tuple [ea a, eb b]
def eTup3 {α β γ : Type} (ea : α → Val) (eb : β → Val) (ec : γ → Val) : α × β × γ → Val
  | (a, b, c) => .tuple [ea a, eb b, ec c]
def eTup4 {α β γ δ : Type} (ea : α → Val) (eb : β → Val) (ec : γ → Val) (ed : δ → Val) :
    α × β × γ × δ → Val
  | (a, b, c, d) => .tuple [ea a, eb b, ec c, ed d]
def eFst {α β : Type} (ea : α → Val) : α × β → Val
  | (a, _) => ea a
def ePure {α β : Type} (ea : α → Val) (eb : β → Val) (b : β) (a : α) : Val := .tuple [ea a, eb b]
def resV {α : Type} (e : α → Val) (a : α) : EResult := .val (e a)
/-- `.error "nl:unmodelled"` marks a path the model leaves out (e.g. a call to a mixin
method inherited from an external base): it is a hole, never a Python exception. -/
def resE {α : Type} (e : α → Val) : Except String α → EResult
  | .ok a => .val (e a)
  | .error n => if n == "nl:unmodelled" then .hole n else .exn (.str n)

/-! Helpers for statements about Python data (exported to statement files by
`schema.lean_opens`). All are total and kernel-evaluable. -/
/-- The attribute `attr` of an encoded object (`.unit` when absent or not an object). -/
def vField (o : Val) (attr : String) : Val :=
  match o with
  | .bobj _ (.dict kvs) => (dField attr kvs).getD .unit
  | _ => .unit
def vLookup (k : Val) : List (Val × Val) → Option Val
  | [] => none
  | (k', v) :: kvs => if Val.beq k k' then some v else vLookup k kvs
/-- `d[k]` for a dict (or a dict-valued attribute), by Python equality. -/
def vGet (d : Val) (k : Val) : Option Val :=
  match d with
  | .dict kvs => vLookup k kvs
  | _ => none
def vElems : Val → List Val
  | .list vs => vs
  | .tuple vs => vs
  | .dict kvs => kvs.map Prod.fst
  | .bobj _ (.list vs) => vs
  | .str s => s.toList.map fun c => .str (String.singleton c)
  | _ => []
/-- The keys of a dict in insertion order (elements of a list/tuple/set). -/
def vKeys (d : Val) : List Val := vElems d
/-- `k in d` for a dict (keys), list, tuple or set, by Python equality. -/
def vHas (d : Val) (k : Val) : Bool := (vElems d).any (Val.beq k)
/-- `len(d)` of a str, list, tuple, dict, set or bytes. -/
def vLen : Val → Int
  | .str s => s.length
  | v => (vElems v).length
'''

RENDER = CANON.replace('{v}', 'rv').replace('{l}', 'rl').replace('{d}', 'rd') + r'''
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


# ---------------------------------------------------------------- receiver structures

@dataclass
class Structure:
    """The Lean structure generated for a repository class: one field per instance
    attribute (all attributes along the repository MRO that its instances carry), types
    inferred from the attribute values observed while the tests ran."""
    cls: str                    # pyvalues.class_name of the instances
    lean: str                   # structure name, e.g. S_Cache
    fields: list                # [(python attr, lean field, parsed type)] sorted by attr
    observed: int = 0           # receiver states observed
    decodable: int = 0          # observed states whose attribute set and values fit the structure
    source: str = 'observed'    # observed | static (no instance seen: static attributes typed Val)

    def text(self) -> str:
        tag = pv.lean_str('obj:' + self.cls)
        n = len(self.fields)
        lines = [f'/-- Python class `{self.cls}` (instance attributes, sorted). -/',
                 f'structure {self.lean} where']
        lines += [f'  {lf} : {show_type(t)}' for _, lf, t in self.fields]
        if not self.fields:
            lines[-1] += '\n  mk ::'
        lines.append(f'def dObj_{self.lean} : Val → Option {self.lean}')
        if self.fields:
            discr = ', '.join(f'(dField {pv.lean_str(a)} kvs).bind {decoder(t)}' for a, _, t in self.fields)
            binds = ', '.join(f'some x{i}' for i in range(n))
            build = '{ ' + ', '.join(f'{lf} := x{i}' for i, (_, lf, _) in enumerate(self.fields)) + ' }'
            lines += ['  | .bobj n (.dict kvs) =>',
                      f'    if n == {tag} && kvs.length == {n} then',
                      f'      match {discr} with',
                      f'      | {binds} => some {build}',
                      f'      | {", ".join("_" for _ in range(n))} => none',
                      '    else none']
        else:
            lines += [f'  | .bobj n (.dict kvs) => if n == {tag} && kvs.length == 0 then some {{}} else none']
        lines.append('  | _ => none')
        items = ', '.join(f'(.str {pv.lean_str(a)}, {encoder(t)} s.{lf})' for a, lf, t in self.fields)
        lines.append(f'def eObj_{self.lean} (s : {self.lean}) : Val := .bobj {tag} (.dict [{items}])')
        return '\n'.join(lines) + '\n'

    def describe(self) -> str:
        rows = [f'  {lf} : {show_type(t)}    -- Python attribute `{a}`' for a, lf, t in self.fields]
        return (f'structure {self.lean} where    -- instances of {self.cls}\n' + '\n'.join(rows)
                + ('\n  (no attributes)' if not rows else ''))


def field_ident(attr: str, taken: set) -> str:
    base = 'f_' + re.sub(r'[^A-Za-z0-9_]', '_', attr)
    name, k = base, 2
    while name in taken:
        name, k = f'{base}_{k}', k + 1
    taken.add(name)
    return name


def _join(a, b):
    """Least upper bound of two inferred types (None = no information yet, 'NoneT' = only None)."""
    if a is None:
        return b
    if b is None or a == b:
        return a
    if a == 'NoneT':
        return b if isinstance(b, tuple) and b[0] == 'Option' else ('Option', b)
    if b == 'NoneT':
        return _join(b, a)
    if isinstance(a, tuple) and a[0] == 'Option':
        inner = _join(a[1], b[1] if isinstance(b, tuple) and b[0] == 'Option' else b)
        return 'Val' if inner == 'Val' else ('Option', inner)
    if isinstance(b, tuple) and b[0] == 'Option':
        return _join(b, a)
    if isinstance(a, tuple) and isinstance(b, tuple) and a[0] == b[0] and len(a) == len(b):
        if a[0] == 'Prod':
            if len(a[1]) != len(b[1]):
                return ('Tuple', _fin(_join_all(a[1] + b[1])))
            return ('Prod', [_join(x, y) for x, y in zip(a[1], b[1])])
        return (a[0],) + tuple(_join(x, y) for x, y in zip(a[1:], b[1:]))
    if isinstance(a, tuple) and isinstance(b, tuple) and {a[0], b[0]} == {'Prod', 'Tuple'}:
        p, t = (a, b) if a[0] == 'Prod' else (b, a)
        return ('Tuple', _join(t[1], _join_all(p[1])))
    return 'Val'


def _join_all(ts):
    out = None
    for t in ts:
        out = _join(out, t)
    return out


def _fin(t):
    """Close an inferred type: unknown element types become Val; nested None-only → Val."""
    if t is None or t == 'NoneT':
        return 'Val'
    if isinstance(t, str):
        return t
    if t[0] == 'Prod':
        return ('Prod', [_fin(x) for x in t[1]])
    if t[0] == 'Option':
        inner = _fin(t[1])
        return 'Val' if inner == 'Val' else ('Option', inner)
    return (t[0],) + tuple(_fin(x) for x in t[1:])


def infer_type(t):
    """Inferred Lean type of one tagged value (None = no information: an empty container's element)."""
    k = t[0]
    if k == 'n':
        return 'NoneT'
    simple = {'i': 'Int', 'b': 'Bool', 's': 'String', 'f': 'Fl', 'y': 'Bytes'}
    if k in simple:
        return simple[k]
    if k == 'l':
        return ('List', _join_all(infer_type(x) for x in t[1]))
    if k == 't':
        if 2 <= len(t[1]) <= 4:
            return ('Prod', [infer_type(x) for x in t[1]])
        return ('Tuple', _join_all(infer_type(x) for x in t[1]))
    if k == 'd':
        return ('Dict', _join_all(infer_type(a) for a, _ in t[1]), _join_all(infer_type(b) for _, b in t[1]))
    if k == 'S':
        return ('FrozenSet' if t[2] == 'frozenset' else 'PySet', _join_all(infer_type(x) for x in t[1]))
    return 'Val'


def _fits(t, typ) -> bool:
    """Does the tagged value decode at the inferred type (mirrors the Lean decoders)?"""
    k = t[0]
    if typ == 'Val':
        return True
    if isinstance(typ, tuple) and typ[0] == 'Option':
        return k == 'n' or _fits(t, typ[1])
    table = {'Int': 'i', 'Bool': 'b', 'String': 's', 'Fl': 'f', 'Bytes': 'y', 'Unit': 'n'}
    if isinstance(typ, str):
        return table.get(typ) == k
    head = typ[0]
    if head in ('List', 'Tuple'):
        return k == ('l' if head == 'List' else 't') and all(_fits(x, typ[1]) for x in t[1])
    if head in ('PySet', 'FrozenSet'):
        return k == 'S' and t[2] == ('set' if head == 'PySet' else 'frozenset') and all(_fits(x, typ[1]) for x in t[1])
    if head == 'Dict':
        return k == 'd' and all(_fits(a, typ[1]) and _fits(b, typ[2]) for a, b in t[1])
    if head == 'Prod':
        return k == 't' and len(t[1]) == len(typ[1]) and all(_fits(x, y) for x, y in zip(t[1], typ[1]))
    return False


def infer_structure(cls: _Class, states: list, lean: str) -> Structure:
    """The structure for `cls` from the receiver states observed for it (pyvalues 'O' tags).

    The attribute set is the most common one among the observations (an instance with other
    attributes does not decode, and such inputs are skipped and counted); each attribute's
    type is the join of its observed values' types (mixed types → Val). With no
    observations, the attributes assigned in the class's code are used, typed Val."""
    sets = {}
    for s in states:
        key = tuple(a for a, _ in s[2])
        sets[key] = sets.get(key, 0) + 1
    taken: set = set()
    if sets:
        attrs = max(sets.items(), key=lambda kv: (kv[1], -len(kv[0])))[0]
        types = {a: None for a in attrs}
        for s in states:
            if tuple(a for a, _ in s[2]) == attrs:
                for a, v in s[2]:
                    types[a] = _join(types[a], infer_type(v))
        fields = [(a, field_ident(a, taken), _fin(types[a])) for a in sorted(attrs)]
        st = Structure(cls.dotted, lean, fields, observed=len(states))
        st.decodable = sum(1 for s in states if st.fits(s))
        return st
    fields = [(a, field_ident(a, taken), 'Val') for a in sorted(static_fields(cls))]
    return Structure(cls.dotted, lean, fields, source='static')


def _structure_fits(self: Structure, state) -> bool:
    if state[0] != 'O' or state[1] != self.cls or [a for a, _ in state[2]] != [a for a, _, _ in self.fields]:
        return False
    return all(_fits(v, t) for (_, v), (_, _, t) in zip(state[2], self.fields))


Structure.fits = _structure_fits


PRELUDE_TAIL = ''   # structures are appended per module (see structures_text)


def structures_text(structs: list) -> str:
    return '\n'.join(s.text() for s in structs)


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
    # char literals first ('"' would otherwise open a string), then strings, then comments
    body = re.sub(r"(?<![\w'])'(?:[^'\\\n]|\\.)'", "' '", text or '')
    body = re.sub(r'"(?:[^"\\]|\\.)*"', '""', body)
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
for f, lines, key, kind, cls, qual, modname in cfg['wanted']:
    for ln in lines:
        wanted.setdefault((os.path.realpath(f), ln), []).append((key, kind, cls, qual, modname))
classes = set(cfg.get('classes') or [])
limit = cfg['limit']
records, states, known, funcs, nested_pts = {}, {}, {}, {}, {}
stats = {'calls': 0, 'kwargs': 0, 'unencodable': 0, 'other_receiver': 0, 'defaults_dropped': 0, 'nested': 0}
def is_nested(frame, obj):
    # a call on `obj` made from inside another method running on the same object: its state
    # may be mid-update (not reachable from outside), e.g. popitem() inside __setitem__
    f, depth = frame.f_back, 0
    while f is not None and depth < 12:
        c = f.f_code
        if c.co_argcount and f.f_locals.get(c.co_varnames[0]) is obj:
            return True
        f, depth = f.f_back, depth + 1
    return False
def defaults_of(key, qual, modname):
    if key not in funcs:
        d = ()
        try:
            obj = sys.modules[modname]
            for part in qual.split('.'):
                obj = getattr(obj, part)
            obj = getattr(obj, 'fget', obj)
            d = tuple(getattr(obj, '__defaults__', None) or ())
        except (KeyError, AttributeError):
            pass
        funcs[key] = d
    return funcs[key]
def snapshot(cls, obj):
    try:
        t = json.dumps(pv.tag(obj, 0, classes))
    except (pv.Unencodable, ValueError, TypeError, RecursionError):
        return
    bucket = states.setdefault(cls, {})
    if len(bucket) < 4 * limit:
        bucket[t] = None
def tracer(frame, event, arg):
    if event != 'call':
        return None
    code = frame.f_code
    entries = known.get(code, 0)
    if entries == 0:
        entries = known[code] = wanted.get((os.path.realpath(code.co_filename), code.co_firstlineno))
    if entries is None or code.co_name == '<module>':   # a module body starting on a def's line
        return None
    if code.co_flags & 0x3a0:        # generator / coroutine / async generator
        return None
    loc = frame.f_locals
    n, k = code.co_argcount, code.co_kwonlyargcount
    entry = entries[0]
    if entry[1] in ('method', 'property', 'constructor'):
        if n == 0:
            return None
        recv_cls = pv.class_name(type(loc.get(code.co_varnames[0])))
        entry = next((e for e in entries if e[2] == recv_cls), None)
        if entry is None:
            stats['other_receiver'] += 1
            return None
    key, kind, cls, qual, modname = entry
    stats['calls'] += 1
    try:
        args = [loc[x] for x in code.co_varnames[:n]]
        i = n + k
        extra = []
        if code.co_flags & 0x04:
            extra = list(loc[code.co_varnames[i]]); i += 1
        if code.co_flags & 0x08 and loc[code.co_varnames[i]]:
            stats['kwargs'] += 1
            return None
    except (KeyError, IndexError):
        stats['unencodable'] += 1
        return None
    defaults = defaults_of(key, qual, modname)
    cut = n
    while defaults and cut > n - len(defaults) and args[cut - 1] is defaults[cut - 1 - (n - len(defaults))]:
        cut -= 1
    first = 1 if kind == 'constructor' else 0
    tags = []
    try:
        for j, a in enumerate(args):
            if j < first:
                continue
            try:
                tags.append(pv.tag(a, 0, classes))
            except pv.Unencodable:
                if j >= cut and not extra and j > 0:
                    stats['defaults_dropped'] += 1
                    break              # this and every later argument is the unencodable default
                raise
        else:
            tags += [pv.tag(a, 0, classes) for a in extra]
        tagged = json.dumps(tags)
    except (pv.Unencodable, ValueError, TypeError, RecursionError):
        stats['unencodable'] += 1
        tagged = None
    nested = kind in ('method', 'property') and is_nested(frame, args[0])
    if nested:
        stats['nested'] += 1
    elif kind in ('method', 'property'):
        snapshot(cls, args[0])
    if tagged is not None:
        bucket = records.setdefault(key, {})
        if len(bucket) < limit:
            bucket[tagged] = None
            if nested:
                nested_pts.setdefault(key, {})[tagged] = None
    if kind == 'constructor':
        self_name = code.co_varnames[0]
        def local(fr, ev, a):
            if ev == 'return':
                snapshot(cls, fr.f_locals.get(self_name))
            return local
        return local
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
                except ImportError:
                    pytest = None
                if pytest is not None:
                    rc = int(pytest.main([d, '-q', '-p', 'no:cacheprovider', '--no-header']))
                else:
                    import unittest
                    suite = unittest.TestLoader().discover(d, top_level_dir=os.path.dirname(d))
                    rc = 0 if unittest.TextTestRunner(stream=buf, verbosity=0).run(suite).wasSuccessful() else 1
            ran.append({'dir': d, 'rc': rc})
        except BaseException as e:
            ran.append({'dir': d, 'error': repr(e)[:300]})
finally:
    sys.settrace(None); threading.settrace(None)
json.dump({'records': {k: [json.loads(t) for t in v] for k, v in records.items()}, 'stats': stats,
           'states': {c: [json.loads(t) for t in v] for c, v in states.items()},
           'nested': {k: [json.loads(t) for t in v] for k, v in nested_pts.items()},
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
        name = os.path.splitext(os.path.basename(cfg['path']))[0]
        s = importlib.util.spec_from_file_location(name, cfg['path'])
        mod = importlib.util.module_from_spec(s); sys.modules[name] = mod
        s.loader.exec_module(mod)
kind = cfg.get('kind') or 'function'
classes = set(cfg.get('classes') or [])
parts = cfg['qual'].split('.')
owner = mod
for part in parts[:-1]:
    owner = getattr(owner, part)
if kind == 'constructor':
    target = owner
elif kind == 'property':
    target = None
    for c in owner.__mro__:
        if parts[-1] in c.__dict__:
            target = c.__dict__[parts[-1]].fget
            break
else:
    target = getattr(owner, parts[-1])
out = []
for point in cfg['points']:
    try:
        args = [pv.untag(t) for t in point]
        if kind in ('method', 'property') and (not args or type(args[0]) is not owner):
            raise ValueError('the receiver is not an instance of ' + pv.class_name(owner))
    except Exception as e:
        out.append({'k': 'bad-input', 'why': repr(e)[:200]}); continue
    signal.setitimer(signal.ITIMER_REAL, cfg['per'])
    try:
        with contextlib.redirect_stdout(sink), contextlib.redirect_stderr(sink):
            v = target(*args)
        signal.setitimer(signal.ITIMER_REAL, 0)
        try:
            r = {'k': 'ok', 'v': pv.tag(v, 0, classes)}
            if kind in ('method', 'property'):
                r['post'] = pv.tag(args[0], 0, classes)
            out.append(r)
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
        proc = subprocess.run([SUBJECT_PYTHON, '-c', script, str(cfg_path)], cwd=str(cwd or work), env=env,
                              capture_output=True, text=True, timeout=timeout, start_new_session=True)
    except subprocess.TimeoutExpired:
        return None, f'timed out after {timeout}s'
    if not out_path.is_file():
        return None, (proc.stderr or proc.stdout)[-1500:]
    return json.loads(out_path.read_text()), ''


def _modname(mod: _Module) -> str:
    return mod.dotted or mod.path.stem


def trace_tests(fns: list, source_root: Path, test_dirs: list, work: Path, classes=(), limit: int = TRACE_LIMIT) -> tuple:
    """Run the repository's tests under a tracer.

    Returns ({qualified name: [point]}, stats); stats['states'] maps each class in `classes`
    to the receiver states observed (pyvalues 'O' tags: before every outermost call of one
    of its traced methods, and after every traced constructor). A call made from inside
    another method running on the same object is *nested*: its receiver may be mid-update,
    so it is recorded as an input (stats['nested']) but its state does not join the pool of
    receivers and it is not used as a check-stage sample. A method's point starts with its
    receiver's state; a constructor's point omits the receiver. A trailing argument that
    is the parameter's own (unencodable) default object, e.g. a sentinel or a function
    alias, is dropped, so the call is replayed with the default. `limit`: distinct argument
    tuples kept per function (TRACE_LIMIT; the emit stage asks for all of them)."""
    if not fns or not test_dirs:
        return {}, {'note': 'no tests to trace', 'states': {}}
    roots = []
    for f in fns:
        r = str(f.mod.import_root)
        if r not in roots:
            roots.append(r)
    sys_path = roots + [str(Path(d).resolve().parent) for d in test_dirs]
    classes = sorted(set(classes) | {f.cls.dotted for f in fns if f.cls is not None and f.kind != 'static'})
    cfg = {'sys_path': sys_path, 'tests': [str(Path(d).resolve()) for d in test_dirs], 'limit': limit,
           'classes': classes,
           'wanted': [[str(f.mod.path), f.first_lines, f.info.name, f.kind,
                       f.cls.dotted if f.cls is not None else '', f.qual, _modname(f.mod)] for f in fns]}
    data, err = _run_script(TRACER, cfg, work, 'trace', TRACE_TIMEOUT)
    if data is None:
        return {}, {'error': err, 'states': {}}
    stats = dict(data['stats'], runs=data['runs'], states=data.get('states', {}), nested=data.get('nested', {}),
                 traced={k: len(v) for k, v in data['records'].items()})
    return data['records'], stats


def runner_config(import_root, dotted, path, qual: str, kind: str = 'function', classes=()) -> dict:
    return {'sys_path': [str(import_root)], 'dotted': dotted, 'path': str(path), 'qual': qual,
            'kind': kind, 'classes': sorted(classes), 'per': POINT_TIMEOUT}


def run_points(cfg: dict, points: list, work: Path, stem: str, cwd=None, timeout=RUNTIME_TIMEOUT) -> tuple:
    """Run the real function on tagged points in CPython: ([outcome dict], error text)."""
    data, err = _run_script(RUNNER, dict(cfg, points=points), work, stem, timeout, cwd=cwd)
    if data is None or len(data) != len(points):
        return [{'k': 'runner-failed'}] * len(points), err or 'runner returned a wrong number of results'
    return data, ''


class Runtime:
    """CPython outcomes of one function, cached by input point."""

    def __init__(self, fn: _Fn, work: Path, classes=()):
        self.fn, self.work, self.cache, self.error = fn, work, {}, ''
        self.calls = 0
        mod = fn.mod
        cls = {fn.cls.dotted} if fn.cls is not None else set()
        self.cfg = runner_config(mod.import_root, mod.dotted, mod.path, fn.qual, fn.kind, cls | set(classes))

    def run(self, points: list) -> list:
        todo = []
        for p in points:
            k = json.dumps(p)
            if k not in self.cache and k not in todo:
                todo.append(k)
        if todo:
            self.calls += 1
            data, err = run_points(self.cfg, [json.loads(k) for k in todo], self.work, f'runtime{self.calls}',
                                   cwd=self.fn.mod.import_root)
            if err:
                self.error = err
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


class _Tagged:
    """An already-tagged value (a receiver state) inside a boundary combination."""

    def __init__(self, t):
        self.t = t


def _hashable(xs) -> list:
    out = []
    for x in xs:
        try:
            hash(x)
        except TypeError:
            continue
        if x not in out and not any(type(x) is not type(y) and x == y for y in out):
            out.append(x)
    return out


def values_for(t, ints=(), strs=(), depth=0, receivers=()) -> list:
    """Python values of Lean type `t`, most informative first (`receivers`: tagged states of
    the receiver structure, used for a parameter of structure type)."""
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
        if t == 'Bytes':
            return [b'', b'a', b'\x00', b'ab', b'\xff\x00', (strs[0].encode() if strs else b'hello')]
        return VAL_VALUES
    if t[0] == 'Struct':
        return [_Tagged(r) for r in receivers]
    if depth > 2:
        return []
    if t[0] == 'Option':
        return [None] + values_for(t[1], ints, strs, depth + 1, receivers)[:8]
    if t[0] in ('List', 'Tuple'):
        e = values_for(t[1], ints, strs, depth + 1, receivers)[:6]
        out = [[]]
        if e:
            out += [[e[0]], e[:2], e[:3], list(reversed(e[:4])), [e[-1], e[0], e[-1]]]
            if len(e) > 3:
                out.append(e[1:5])
        return out if t[0] == 'List' else [tuple(x) for x in out]
    if t[0] in ('PySet', 'FrozenSet'):
        e = _hashable(values_for(t[1], ints, strs, depth + 1, receivers))[:6]
        make = set if t[0] == 'PySet' else frozenset
        return [make(x) for x in ([], e[:1], e[:2], e[1:4], e[:5])]
    if t[0] == 'Dict':
        ks = _hashable(values_for(t[1], ints, strs, depth + 1, receivers))[:5]
        vs = values_for(t[2], ints, strs, depth + 1, receivers)[:5] or [None]
        out = [{}]
        for n in (1, 2, 3):
            if len(ks) >= n:
                out.append({k: vs[i % len(vs)] for i, k in enumerate(ks[:n])})
        if len(ks) >= 2:
            out.append({ks[1]: vs[0], ks[0]: vs[-1]})
        return out
    if t[0] == 'Prod':
        per = [values_for(x, ints, strs, depth + 1, receivers)[:4] for x in t[1]]
        return [tuple(c) for c in _product(per, 12)]
    return []


def _tag_value(v):
    if isinstance(v, _Tagged):
        return v.t
    if isinstance(v, (tuple, list)) and any(isinstance(x, _Tagged) for x in v):
        return ['t' if isinstance(v, tuple) else 'l', [_tag_value(x) for x in v]]
    return pv.tag(v)


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


def boundary_points(sig: Sig, source: str, cap: int = BOUNDARY_CAP, receivers=()) -> list:
    """Typed boundary inputs. For a method, the receiver ranges over `receivers` (tagged
    states observed in the tests), and the other parameters over their types' values."""
    ints, strs = _literals(source)
    per = []
    for p in sig.params:
        if p['kind'] == 'varargs':
            elems = values_for(p['type'][1], ints, strs, receivers=receivers)[:5]
            per.append([('*', e) for e in [[], elems[:1], elems[:2], elems[1:4], elems[:3]]])
        else:
            per.append(values_for(p['type'], ints, strs, receivers=receivers))
    if any(not p for p in per):
        return []
    out = []
    for combo in _product(per, cap):
        args = []
        for v in combo:
            if isinstance(v, tuple) and len(v) == 2 and v[:1] == ('*',):
                args += list(v[1])
            else:
                args.append(v)
        try:
            out.append([_tag_value(a) for a in args])
        except pv.Unencodable:
            continue
    return out


# ---------------------------------------------------------------- prompts

CONVENTIONS = r'''
Lean conventions (Lean 4 core, no Mathlib; the namespace `Autoform.Core` is open):
- Types. Python int → `Int` (unbounded; never `Nat` for a Python int), bool → `Bool`,
  str → `String`, a value that may be None → `Option τ` (None is `none`), list → `List τ`,
  fixed-length tuple → `τ × σ` (up to 4 components), variable-length tuple → `Tuple τ`
  (an abbreviation of `List τ` that the dispatcher encodes as a Python tuple: a list never
  equals a tuple), dict → `Dict κ ν` (= `List (κ × ν)`, an association list in Python's
  insertion order: assigning an existing key keeps its position, a new key goes last,
  deleting removes it), set → `PySet τ` and frozenset → `FrozenSet τ` (= `List τ`; order and
  duplicates are irrelevant: the dispatcher sorts and deduplicates when encoding), bytes →
  `Bytes` (= `List Nat`, each 0..255), returning None → `Unit`.
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

METHOD_CONVENTIONS = r'''
Methods and objects (this function is {what} of class `{cls}`):
- The receiver's state is the generated Lean structure below; its fields are the instance
  attributes (private names as CPython mangles them), typed from the values seen while the
  project's tests ran. Read a field as `self.f_x`; build a changed state with
  `{{ self with f_x := v }}`. Class-level attributes and the class's own source are shown
  in the module context; a class attribute that is never assigned per instance is a constant.
{structure}
- A method is a Lean function whose FIRST parameter is the receiver, named `self`, of type
  `{S}` (list it first in "params"; no default). The other parameters follow in Python order.
- If the method can change any attribute of the receiver (assignment, `del`, or a mutating
  call on an attribute such as `self.d[k] = v`, `self.d.pop(k)`, `self.xs.append(x)`), set
  "mutates": true and return the Python result together with the receiver AFTER the call:
  `τ × {S}` (or `Except String (τ × {S})`). A result that is a product is parenthesized:
  `(A × B) × {S}`. A method returning None has result `Unit`. Otherwise "mutates": false and
  return just the result. The receiver's state after a raised exception is not compared.
- A constructor (`__init__`) does not take `self`: its parameters are the arguments after it,
  and it returns the new object `{S}` (or `Except String {S}`), with every field set exactly as
  `__init__` leaves it (including attributes set by base-class `__init__`s it calls).
- Calls to other methods of the receiver (`self.m(...)`, `self[k]`, `k in self`, `len(self)`)
  run THOSE methods (for this class, following Python's method resolution); implement their
  effect on the structure (you may reuse translated callees below if their receiver type is
  `{S}`, else write helpers).
{unmodelled}'''

KEYS_A = ['english', 'params', 'returns', 'lean']
KEYS_B = ['params', 'returns', 'lean']


def _keys(keys: list, fn: _Fn) -> list:
    return keys[:-1] + ['mutates', keys[-1]] if fn.has_receiver else keys


def _method_block(fn: _Fn, struct) -> str:
    if fn.cls is None or fn.kind == 'static' or struct is None:
        return ''
    what = {'method': 'a method', 'property': 'a property getter (called as `obj.name`)',
            'constructor': 'the constructor'}[fn.kind]
    unmod = ''
    if fn.unmodelled:
        unmod = ('- NOT MODELLED (inherited from a base class outside the repository): '
                 + '; '.join(fn.unmodelled) + '. Any path that reaches such a call must return '
                 '`.error "nl:unmodelled"` (so the result type is `Except String ...`); that path is then '
                 'excluded from the comparison with Python. Do not guess what the external method does.\n')
    return METHOD_CONVENTIONS.format(what=what, cls=struct.cls, S=struct.lean, structure=struct.describe(),
                                     unmodelled=unmod)


def _function_block(fn: _Fn, lean_name: str, callees: list, context: str, struct=None) -> str:
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
    method = _method_block(fn, struct)
    if method:
        lines.append(method)
        if any(not (isinstance(d, ast.Constant)) for d in fn.node.args.defaults):
            lines.append('- A parameter whose default is an object sentinel or a function alias (e.g. '
                         '`cache_setitem=Cache.__setitem__`, `default=__marker`) is part of the method\'s '
                         'interface only when callers pass it. Omit an alias parameter that callers never '
                         'pass; for a sentinel, model the behaviour both when it is omitted and when a value '
                         'is passed (e.g. an `Option τ` parameter with default `none` if `None` is never '
                         'passed explicitly).')
    if callees:
        lines.append('Functions it calls that are already translated (call their Lean defs; they are '
                     'validated against Python):')
        for qual, lname, src in callees:
            lines.append(f'  {qual} is `{lname}`:\n```lean\n{src.strip()[:2500]}\n```')
    if context:
        lines += ['Module context (imports, constants, classes it may use):', '```python', context, '```']
    return '\n'.join(lines)


def _reply_keys_text(fn) -> str:
    if fn is None or not fn.has_receiver:
        return ''
    return ('"mutates" (true if the method can change the receiver: then "returns" is `τ × S` or '
            '`Except String (τ × S)` with S the receiver structure; false otherwise), ')


def prompt_a(block: str, fn=None) -> str:
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
            '"Except String Int"), ' + _reply_keys_text(fn) + '"lean" (the Lean source of the definitions).')


def prompt_b(block: str, fn=None) -> str:
    return ('Independent re-implementation check. Read the Python code below and write a Lean 4 function '
            'that returns exactly what the Python code returns (or raises exactly what it raises) for '
            'every argument tuple of the types you choose. Work directly from the code: do not describe '
            'it first, just translate each statement faithfully.\n' + CONVENTIONS + '\n' + block +
            '\n\nReply with JSON keys: "params" ([{"name", "type", "kind", "default"}] in Python order), '
            '"returns" (the Lean return type of NAME), ' + _reply_keys_text(fn) +
            '"lean" (the Lean definitions).')


def repair_prompt(base: str, cand: dict, problem: str) -> str:
    prev = {k: cand.get(k) for k in ('params', 'returns', 'mutates', 'lean') if k in cand}
    return (base + '\n\n## Your previous answer was rejected\n```json\n' + json.dumps(prev, indent=1,
                                                                                     ensure_ascii=False)
            + '\n```\n' + problem.strip() +
            '\n\nReply with the complete corrected answer (all keys). Fix the translation so it matches '
            'Python on these inputs and on all others; do not special-case the listed inputs.')


def _module_context(fn: _Fn, limit: int = 5000) -> str:
    text = fn.mod.text
    extra = ''
    own = []
    if fn.cls is not None and fn.kind != 'static':
        # the receiver's repository base classes from other modules, in full (up to a bound)
        own = [c.node for c in fn.cls.mro()]
        others = [c for c in fn.cls.mro()[1:] if c.mod is not fn.mod]
        segs = [f'# {c.mod.rel}\n' + (ast.get_source_segment(c.mod.text, c.node) or '') for c in others]
        extra = '\n'.join(segs)[:6000]
        limit = max(limit, 9000)
    if len(text) <= limit:
        return (text.strip() + ('\n\n' + extra if extra else '')).strip()
    parts = []
    for node in fn.mod.tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        seg = ast.get_source_segment(text, node) or ''
        if isinstance(node, ast.ClassDef) and node not in own and len(seg) > 1500:
            seg = seg[:1500] + '\n    ...'
        parts.append(seg)
    return ('\n'.join(parts)[:limit] + ('\n\n' + extra if extra else '')).strip()


# ---------------------------------------------------------------- one Lean run

@dataclass
class Candidate:
    data: dict
    sig: Sig | None = None
    problems: list = field(default_factory=list)


def _truthy(x) -> bool:
    return x is True or str(x).strip().lower() == 'true'


def _candidate(data: dict, lean_name: str, fn: _Fn | None = None, struct: 'Structure | None' = None,
               structs=()) -> Candidate:
    c = Candidate(data)
    kind = fn.kind if fn is not None and fn.kind != 'static' else 'function'
    try:
        c.sig = parse_sig(data.get('params') or [], data.get('returns') or '', structs=structs, kind=kind,
                          struct=struct.lean if struct is not None else None,
                          mutates=_truthy(data.get('mutates')) if kind in ('method', 'property') else False)
    except (TypeError_, ValueError) as exc:
        c.problems.append(f'signature: {exc}')
    lean = data.get('lean')
    if not isinstance(lean, str):
        c.problems.append('"lean" must be a string of Lean source')
    else:
        c.problems += lean_problems(lean, lean_name)
    return c


def entry_name(qual: str, kind: str) -> str:
    """The dispatcher entry a differential test evaluates: a method's `#post` entry, which
    also returns the receiver after the call."""
    return qual + '#post' if kind in ('method', 'property') else qual


def scratch_file(module: str, callee_src: str, cand_src: str, wrap: str, qual: str, lean_name: str,
                 points: list, kernel: list, structs_src: str = '', kind: str = 'function') -> tuple:
    """(text, spans); spans['check'] is the first line of the evaluation section."""
    ns = f'Autoform.NLModel.{module}'
    parts = [HEADER, f'namespace {ns}', 'open Autoform.Core', PRELUDE, structs_src, callee_src, '-- candidate']
    text = '\n'.join(parts) + '\n'
    spans = {'candidate': text.count('\n') + 1}
    text += cand_src.rstrip() + '\n\n'
    spans['wrapper'] = text.count('\n') + 1
    entry = entry_name(qual, kind)
    text += wrap + '\n' + dispatcher([(qual, lean_name, kind)]) + f'end {ns}\n\n'
    spans['check'] = text.count('\n') + 1
    text += 'namespace AutoformNLCheck\nopen Autoform.Core\n' + RENDER
    text += 'def pts : List (List Val) := [\n  ' + ',\n  '.join(
        '[' + ', '.join(pv.lean_lit(t) for t in p) + ']' for p in points) + ']\n'
    text += (f'#eval (pts.zipIdx.forM fun (p, i) => IO.println ("AFR " ++ toString i ++ " " ++ '
             f'rr ({ns}.call {pv.lean_str(entry)} p)))\n')
    spans['kernel'] = {}
    for i, lit in kernel:
        spans['kernel'][text.count('\n') + 1] = i
        args = '[' + ', '.join(pv.lean_lit(t) for t in points[i]) + ']'
        text += (f'theorem kchk_{i} : sameR ({ns}.call {pv.lean_str(entry)} {args}) {lit} = true := by\n'
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
    unmodelled: int = 0                           # points on a path the model marks nl:unmodelled
    disagreements: list = field(default_factory=list)
    kernel_failures: list = field(default_factory=list)
    kernel_checked: int = 0
    seconds: float = 0.0


def evaluate(module: str, lean_root: Path, work: Path, stem: str, callee_src: str, cand: Candidate,
             lean_name: str, qual: str, points: list, runtime: list | None, kernel_points: int = KERNEL_POINTS,
             structs_src: str = '', kind: str = 'function') -> Evaluation:
    ev = Evaluation()
    wrap = wrapper(lean_name, cand.sig)
    kernel = []
    if runtime is not None and kernel_points:
        # one point per outcome kind first (a return and a raise, when both occur), then fill
        lits = [(i, pv.lean_outcome(r), r.get('k')) for i, r in enumerate(runtime)]
        lits = [x for x in lits if x[1] is not None]
        for k in ('ok', 'exn'):
            first = next((x for x in lits if x[2] == k), None)
            if first:
                kernel.append(first[:2])
        for x in lits:
            if len(kernel) >= kernel_points:
                break
            if x[0] not in [j for j, _ in kernel]:
                kernel.append(x[:2])
        kernel = kernel[:kernel_points]
    text, spans = scratch_file(module, callee_src, cand.data['lean'], wrap, qual, lean_name, points, kernel,
                               structs_src, kind)
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
                'the generated dispatcher (does the def match the declared "params"/"returns"/"mutates"?)' \
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
        if i is not None and not (ev.outputs[i] or '').startswith('hole nl:unmodelled'):
            ev.kernel_failures.append({'point': i, 'error': msg[:500]})
    ev.kernel_checked = len([i for i, _ in kernel if not (ev.outputs[i] or '').startswith('hole nl:unmodelled')])
    if runtime is not None:
        compare(ev, points, runtime)
    return ev


def compare(ev: Evaluation, points: list, runtime: list):
    """Fill compared/skipped/unmodelled/disagreements from the model outputs and CPython outcomes."""
    for i, (p, r) in enumerate(zip(points, runtime)):
        rt = pv.canon_outcome(r)
        if rt is None:
            ev.skipped += 1
            continue
        if (ev.outputs[i] or '').startswith('hole nl:unmodelled'):
            ev.unmodelled += 1
            continue
        ev.compared += 1
        if ev.outputs[i] != rt:
            ev.disagreements.append({'point': i, 'inputs': pv.show_args(p), 'model': pv.display(ev.outputs[i]),
                                     'runtime': pv.display(rt), 'model_raw': ev.outputs[i], 'runtime_raw': rt})


def counterexample_text(ev: Evaluation, name: str, kind: str = 'function') -> str:
    what = (' (a method\'s outcome is shown as (result, receiver after the call))'
            if kind in ('method', 'property') else '')
    lines = [f'Differential test: {len(ev.disagreements)} of {ev.compared} inputs disagree with the real Python '
             f'function. Examples (Python arguments → real Python outcome vs. your Lean model){what}:']
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
    runtime: list = field(default_factory=list)
    cost: float = 0.0
    seconds: float = 0.0
    log: list = field(default_factory=list)

    @property
    def entry(self) -> str:
        return entry_name(self.fn.info.name, self.fn.kind)


def _ask(prompt: str, keys: list, work: Path, ask) -> tuple:
    try:
        return (ask or llm.ask_json)(prompt, keys, cwd=str(work))
    except llm.LLMError as exc:
        return None, str(exc)


@dataclass
class _Context:
    """What every function of one run shares: the receiver structures and their states."""
    structs: dict = field(default_factory=dict)      # class dotted -> Structure
    receivers: dict = field(default_factory=dict)    # class dotted -> [tagged states] (fitting)

    @property
    def names(self) -> set:
        return {s.lean for s in self.structs.values()}

    @property
    def text(self) -> str:
        return structures_text(list(self.structs.values()))

    def struct_of(self, fn: _Fn):
        if fn.cls is None or fn.kind == 'static':
            return None
        return self.structs.get(fn.cls.dotted)

    def outside(self, outcomes: list) -> list:
        """Outcomes whose returned object or receiver after the call has attributes outside
        its class's structure (e.g. an attribute set only for some constructor arguments)
        cannot be represented by the model: they become 'outside-structure' (not compared)."""
        out = []
        for r in outcomes:
            objs = [r[k] for k in ('v', 'post') if r.get('k') == 'ok' and isinstance(r.get(k), list)
                    and r[k][:1] == ['O']]
            if any(o[1] in self.structs and not self.structs[o[1]].fits(o) for o in objs):
                r = {'k': 'outside-structure'}
            out.append(r)
        return out


def model_function(fn: _Fn, lean_name: str, module: str, lean_root: Path, work: Path, traced: list,
                   done: dict, *, repairs: int = 3, second: bool = True, ask=None, ctx: _Context | None = None
                   ) -> _Result:
    t0 = time.time()
    ctx = ctx or _Context()
    work.mkdir(parents=True, exist_ok=True)
    res = _Result(fn, lean_name)
    struct = ctx.struct_of(fn)
    receivers = ctx.receivers.get(fn.cls.dotted, []) if struct is not None else []
    if struct is not None and fn.has_receiver:
        kept = [p for p in traced if p and struct.fits(p[0])]
        if len(kept) != len(traced):
            res.log.append(f'{len(traced) - len(kept)} traced calls skipped: receiver does not fit {struct.lean}')
        traced = kept
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
                            _module_context(fn), struct)
    runtime = Runtime(fn, work, {s.cls for s in ctx.structs.values()})
    base = prompt_a(block, fn)
    keys = _keys(KEYS_A, fn)
    prompt = base
    best = None          # (score, round, cand, ev, points, rt)
    rounds = 0
    for rnd in range(repairs + 1):
        rounds = rnd
        data, c = _ask(prompt, keys, work, ask)
        if data is None:
            res.log.append(f'round {rnd}: model error: {c}')
            break
        res.cost += c
        cand = _candidate(data, lean_name, fn, struct, ctx.names)
        if cand.problems:
            problem = 'It was rejected before Lean ran:\n' + '\n'.join('- ' + p for p in cand.problems)
            res.log.append(f'round {rnd}: ' + '; '.join(cand.problems))
            prompt = repair_prompt(base, data, problem)
            continue
        points = list(traced[:MAX_POINTS])
        for p in boundary_points(cand.sig, fn.info.source, receivers=receivers):
            if len(points) >= MAX_POINTS:
                break
            if p not in points:
                points.append(p)
        rt = ctx.outside(runtime.run(points)) if points else []
        ev = evaluate(module, lean_root, work, f'a{rnd}', callee_src, cand, lean_name, fn.info.name, points, rt,
                      structs_src=ctx.text, kind=fn.kind)
        # fuzz.py: once the model agrees on traced + boundary inputs, search for more (coverage-guided,
        # shrunk); minimal counterexamples land in ev.disagreements and feed the repair below. Methods
        # are not fuzzed yet (fuzz inputs cannot build receivers); their state is compared above.
        if fn.kind == 'function':
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
                       f'{len(ev.kernel_failures)} kernel failures, {ev.skipped} skipped, '
                       f'{ev.unmodelled} unmodelled')
        if best is None or score <= best[0]:
            best = (score, rnd, cand, ev, points, rt)
        if score[0] == 0:
            break
        prompt = repair_prompt(base, data, counterexample_text(ev, fn.info.source_name, fn.kind))
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
    res.sig, res.data, res.points, res.outputs, res.runtime = cand.sig, cand.data, points, ev.outputs, rt
    rec.lean_source = cand.data['lean'].rstrip() + '\n'
    params = ' '.join(f"({p['name']} : {show_type(p['type'])})" for p in cand.sig.params)
    rec.signature = f'{params} : {show_type(cand.sig.returns)}'.strip()
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
    if fn.has_receiver:
        notes.append(f'receiver {struct.lean}; outcomes compared as (result, receiver after the call); '
                     f'mutates={cand.sig.mutates}')
    if ev.unmodelled:
        notes.append(f'{ev.unmodelled} inputs reach an unmodelled call (nl:unmodelled) and were not compared: '
                     + '; '.join(fn.unmodelled))
    if runtime.error:
        notes.append('runtime: ' + runtime.error[:300])
    if cand.data.get('english'):
        notes.append('english: ' + ' '.join(str(cand.data['english']).split())[:1200])
    rec.status = status
    rec.repairs = best[1]
    # --- translation B
    if second and ev.elaborates:
        rec.second_translation, bnote, bcost = second_translation(
            fn, lean_name, module, lean_root, work, block, callee_src, points, rt, ev, ask, ctx)
        res.cost += bcost
        notes.append(bnote)
    rec.level = 'L0' if status == 'VALIDATED' and rec.second_translation != 'disagrees' else 'none'
    # Agreement on inputs that reach little of the function is weak evidence (a model that
    # types `headers` as a list agreed on every input because line 1 always raised): withhold L0.
    fuzz_record = Path(work) / 'fuzz.json'
    if rec.level == 'L0' and fuzz_record.is_file():
        warning = json.loads(fuzz_record.read_text()).get('warning')
        if warning:
            rec.level = 'none'
            notes.append('L0 withheld: ' + warning)
    rec.notes = '\n'.join(notes)
    res.record = rec
    res.seconds = round(time.time() - t0, 1)
    res.log.append(f'cost ${res.cost:.4f}, {res.seconds}s')
    return res


def second_translation(fn, lean_name, module, lean_root, work, block, callee_src, points, rt, ev_a, ask,
                       ctx: _Context | None = None):
    """('agrees'|'disagrees'|'not_run', note, cost). One Lean-error repair; no semantic feedback."""
    ctx = ctx or _Context()
    struct = ctx.struct_of(fn)
    base = prompt_b(block, fn)
    prompt, cost = base, 0.0
    for attempt in range(2):
        data, c = _ask(prompt, _keys(KEYS_B, fn), work, ask)
        if data is None:
            return 'not_run', f'translation B: model error: {c}', cost
        cost += c
        cand = _candidate(data, lean_name, fn, struct, ctx.names)
        if cand.problems:
            prompt = repair_prompt(base, data, 'Rejected before Lean ran:\n' + '\n'.join(cand.problems))
            continue
        ev = evaluate(module, lean_root, work, f'b{attempt}', callee_src, cand, lean_name, fn.info.name,
                      points, None, kernel_points=0, structs_src=ctx.text, kind=fn.kind)
        if not ev.elaborates:
            prompt = repair_prompt(base, data, ev.errors)
            continue
        diff, vs_python = [], 0
        compared = 0
        for i, (a, b) in enumerate(zip(ev_a.outputs, ev.outputs)):
            if any(x in (a or '') or x in (b or '') for x in ('nl:arg-type', 'nl:unmodelled')):
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


# ---------------------------------------------------------------- structures

def struct_ident(cls: _Class, taken: set) -> str:
    base = 'S_' + re.sub(r'_+', '_', re.sub(r'[^A-Za-z0-9_]', '_', cls.qual)).strip('_')
    if base in taken:
        base = 'S_' + re.sub(r'[^A-Za-z0-9_]', '_', cls.mod.rel.rsplit('.', 1)[0]) + '_' + base[2:]
    name, k = base, 2
    while name in taken:
        name, k = f'{base}_{k}', k + 1
    taken.add(name)
    return name


def build_structures(classes: dict, states: dict, lean_root: Path, work: Path, module: str,
                     check: bool = True) -> tuple:
    """Infer one structure per class and validate it in Lean: the structures must elaborate,
    and every observed state (up to 12 per class) must round-trip `eObj (dObj state)` to its
    own canonical encoding. A structure whose inferred types do not elaborate falls back to
    `Val` fields. Returns (_Context, report)."""
    taken: set = set()
    ctx = _Context()
    for dotted in sorted(classes):
        st = infer_structure(classes[dotted], states.get(dotted, []), struct_ident(classes[dotted], taken))
        ctx.structs[dotted] = st
        fits = [s for s in states.get(dotted, []) if st.fits(s)]
        fits.sort(key=lambda s: len(json.dumps(s)))
        uniq = []
        for s in fits:
            if s not in uniq:
                uniq.append(s)
        ctx.receivers[dotted] = uniq[:6] + [s for s in uniq[6:][-2:]]
    report = {d: {'structure': s.lean, 'fields': [[a, lf, show_type(t)] for a, lf, t in s.fields],
                  'source': s.source, 'observed': s.observed, 'decodable': s.decodable}
              for d, s in ctx.structs.items()}
    if not check or not ctx.structs:
        return ctx, report
    for attempt in range(2):
        rows = []
        for d, s in ctx.structs.items():
            for st in [x for x in states.get(d, []) if s.fits(x)][:12]:
                rows.append((d, s, st))
        ns = f'Autoform.NLModel.{module}'
        text = (HEADER + f'namespace {ns}\nopen Autoform.Core\n' + PRELUDE + ctx.text + f'end {ns}\n'
                + 'namespace AutoformNLCheck\nopen Autoform.Core\n' + RENDER
                + ''.join(f'#eval IO.println ("AFS {i} " ++ (match ({ns}.dObj_{s.lean} {pv.lean_lit(st)}).map '
                          f'{ns}.eObj_{s.lean} with | some v => rv v | none => "none"))\n'
                          for i, (_, s, st) in enumerate(rows))
                + 'end AutoformNLCheck\n')
        work.mkdir(parents=True, exist_ok=True)
        path = work / f'structures{attempt}.lean'
        path.write_text(text)
        code, log, _ = run_lean(lean_root, path)
        errs = lean_errors(log, path)
        if code == 0 and not errs:
            outs = {int(m.group(1)): m.group(2) for m in re.finditer(r'^AFS (\d+) (.*)$', log, re.M)}
            for d in report:
                report[d]['roundtrip_checked'] = report[d]['roundtrip_ok'] = 0
            for i, (d, s, st) in enumerate(rows):
                report[d]['roundtrip_checked'] += 1
                report[d]['roundtrip_ok'] += outs.get(i) == pv.canon(st)
            return ctx, report
        # fall back to Val-typed fields for every structure and try once more
        for d, s in ctx.structs.items():
            s.fields = [(a, lf, 'Val') for a, lf, _ in s.fields]
            report[d]['fields'] = [[a, lf, 'Val'] for a, lf, _ in s.fields]
            report[d]['note'] = 'inferred types did not elaborate; fields typed Val: ' + log[-400:]
    raise RuntimeError('generated structures do not elaborate:\n' + log[-2000:])


# ---------------------------------------------------------------- module, build, driver

MODULE_MARK = '-- Generated by autoform.nl.model'


def module_text(module: str, results: list, structs_src: str = '') -> str:
    ns = f'Autoform.NLModel.{module}'
    body = [MODULE_MARK + ' (per-run build product; not tracked).', HEADER.rstrip(), '',
            '/-! Plain Lean models of Python functions, written by a language model and validated',
            'against CPython by differential testing (autoform.nl.model). See models.json for the',
            'evidence behind each definition; nothing here is trusted beyond it. -/', '',
            f'namespace {ns}', 'open Autoform.Core', PRELUDE, structs_src]
    for r in results:
        body.append(f'-- model of {r.fn.info.name}: {r.record.status}'
                    + (f' ({r.record.level})' if r.record.level != 'none' else ''))
        body.append(r.lean_src.rstrip())
        body.append(f'-- end model of {r.fn.info.name}\n')
    body.append(dispatcher([(r.fn.info.name, r.lean_name, r.fn.kind) for r in results]))
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
            rows.append(f'({pv.lean_str(r.entry)}, [' + ', '.join(pv.lean_lit(t) for t in p) + '])')
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


SAMPLES = 24          # validated input points kept per function for the check stage's domain
SAMPLE_BYTES = 4000


def _samples(r: _Result, nested=()) -> list:
    """Input points on which the model agreed with CPython, small ones, never a nested
    call's (possibly mid-update) receiver; they are the check stage's domain for Val binders.

    Kept round-robin across distinct first arguments (receivers), so one receiver crossed
    with boundary values cannot fill the quota. Within a receiver, first the points whose
    other arguments occur inside it (a key the cache holds): membership preconditions need
    them. Otherwise the original order (traced first) is kept."""
    agreeing = []
    for p, o, rt in zip(r.points, r.outputs, r.runtime or [None] * len(r.points)):
        if rt is None or pv.canon_outcome(rt) != o or len(json.dumps(p)) > SAMPLE_BYTES or p in nested:
            continue
        if p not in agreeing:
            agreeing.append(p)
    return spread_samples(agreeing, SAMPLES)


def _member(arg, holder) -> bool:
    """`arg` (a tagged value) occurs as a component of `holder` (a tagged value)."""
    if holder == arg:
        return True
    if isinstance(holder, list):
        return any(_member(arg, h) for h in holder)
    return False


def spread_samples(points: list, limit: int) -> list:
    groups: dict = {}
    for p in points:
        key = json.dumps(p[0], sort_keys=True) if len(p) > 1 else ''
        groups.setdefault(key, []).append(p)
    queues = [sorted(g, key=lambda p: not any(_member(a, p[0]) for a in p[1:])) for g in groups.values()]
    out = []
    while len(out) < limit and any(queues):
        for q in queues:
            if q and len(out) < limit:
                out.append(q.pop(0))
    return out


def model(source_root, out_dir, lean_root, *, module=None, functions=None, parallel=3, repairs=3,
          second=True, tests=(), ask=None, do_build=True, budget_usd=None) -> schema.Translation:
    """Model every pure-enough function and method; write translation.json, models.json and
    the module. `tests`: extra test directories (besides <source>/tests and <source>/test).
    `budget_usd`: no new function is started once the spend reaches it."""
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
        found = {f.info.name for f in fns} | {f.info.source_name for f in fns} | {f.qual for f in fns} \
            | {f.info.file for f in fns}
        notes += [f'requested function {w!r} not found' for w in functions if w not in found]
    t_trace = time.time()
    classes = {f.cls.dotted: f.cls for f in attempt if f.cls is not None and f.kind != 'static'}
    traced, trace_stats = trace_tests(attempt, source_root, _test_dirs(source_root, tests), work / 'trace',
                                      classes=list(classes))
    states = trace_stats.pop('states', {}) or {}
    nested = trace_stats.pop('nested', {}) or {}
    trace_stats['receiver_states'] = {c: len(v) for c, v in states.items()}
    trace_secs = round(time.time() - t_trace, 1)
    ctx, struct_report = build_structures(classes, states, lean_root, work / 'structures', module,
                                          check=do_build or ask is None)
    # a method needs receiver states to be tested against
    late = []
    for f in attempt:
        st = ctx.struct_of(f)
        if f.has_receiver and st is not None and not ctx.receivers.get(f.cls.dotted) and not traced.get(f.info.name):
            late.append((f, f'no instance of {f.cls.dotted} fitting its structure was observed in the tests '
                            '(no receiver states to test the method on)'))
    for f, why in late:
        f.reason = why
        attempt.remove(f)
        skipped.append(f)
        notes.append(f'skipped {f.info.name}: {why}')
    taken: set = set()
    names = {f.info.name: lean_ident(f.info.name, taken) for f in attempt}
    done: dict = {}
    order = []
    spent = [0.0]
    over_budget = []
    for level in _levels(attempt):
        def job(f):
            if budget_usd is not None and spent[0] >= budget_usd:
                over_budget.append(f.info.name)
                return None
            stem = re.sub(r'[^A-Za-z0-9_]', '_', names[f.info.name])
            r = model_function(f, names[f.info.name], module, lean_root, work / stem,
                               traced.get(f.info.name, []), dict(done), repairs=repairs, second=second, ask=ask,
                               ctx=ctx)
            spent[0] += r.cost
            return r
        with ThreadPoolExecutor(max_workers=max(1, parallel)) as pool:
            for r in pool.map(job, level):
                if r is None:
                    continue
                done[r.fn.info.name] = r
                order.append(r)
    if over_budget:
        notes.append(f'budget ${budget_usd} reached: {len(over_budget)} functions not attempted: '
                     + ', '.join(over_budget[:40]))
    modelled = [r for r in order if r.lean_src]
    build_info = {}
    if modelled:
        text = module_text(module, modelled, ctx.text)
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
            info.params = [schema.Param(sp['name'], sort_of(sp['type']) if sp['kind'] == 'positional' else 'any')
                           for sp in r.sig.params]
            info.lean_types = [('*' if sp['kind'] == 'varargs' else '') + show_type(sp['type'])
                               for sp in r.sig.params]   # '*': the varargs parameter
            info.returns = sort_of(r.sig.result)
            info.mutates = r.sig.mutates
        info.samples = _samples(r, nested.get(info.name, []))
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
    kinds = {}
    for f in fns:
        kinds.setdefault(f.kind, {'discovered': 0, 'attempted': 0})
        kinds[f.kind]['discovered'] += 1
        kinds[f.kind]['attempted'] += f.info.name in {r.fn.info.name for r in order}
    meta = {
        'module': module, 'discovered': len(fns), 'attempted': len(order), 'skipped': len(skipped),
        'not_attempted_budget': len(over_budget), 'by_kind': kinds,
        'statuses': {s: sum(1 for r in order if r.record.status == s)
                     for s in ('VALIDATED', 'DISAGREES', 'UNTESTABLE', 'FAILED')},
        'L0': sum(1 for r in order if r.record.level == 'L0'),
        'cost_usd': round(sum(r.cost for r in order), 4), 'seconds': round(time.time() - t0, 1),
        'trace_seconds': trace_secs, 'trace': trace_stats, 'structures': struct_report, 'build': build_info,
        'skip_reasons': _reason_counts(skipped),
        'functions': [{'function': r.fn.info.name, 'kind': r.fn.kind, 'lean_name': r.lean_name,
                       'status': r.record.status, 'tests_run': r.record.tests_run, 'repairs': r.record.repairs,
                       'second_translation': r.record.second_translation, 'level': r.record.level,
                       'mutates': bool(r.sig and r.sig.mutates),
                       'cost_usd': round(r.cost, 4), 'seconds': r.seconds, 'log': r.log} for r in order],
    }
    (out_dir / 'model.meta.json').write_text(json.dumps(meta, indent=1, default=str))
    return tr


def _reason_counts(skipped: list) -> dict:
    out = {}
    for f in skipped:
        key = re.sub(r'\(.*', '', re.sub(r'calls \S+, which', 'calls X, which', f.reason or '')).strip()[:80]
        out[key] = out.get(key, 0) + 1
    return dict(sorted(out.items(), key=lambda kv: -kv[1]))


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
    ap.add_argument('--budget-usd', type=float, help='start no new function once the spend reaches this')
    ap.add_argument('--no-second', action='store_true', help='skip the independent translation B')
    ap.add_argument('--no-build', action='store_true')
    fuzz.add_arguments(ap)
    a = ap.parse_args(argv)
    fuzz.configure(a)
    from .pipeline import default_lean_root
    tr = model(a.source, a.out, a.lean_root or default_lean_root(), module=a.module, functions=a.function,
               parallel=a.parallel, repairs=a.repairs, second=not a.no_second, tests=a.tests,
               do_build=not a.no_build, budget_usd=a.budget_usd)
    meta = json.loads((a.out / 'model.meta.json').read_text())
    for f in meta['functions']:
        print(f"{f['status']:10s} {f['level']:4s} tests={f['tests_run']:<4d} repairs={f['repairs']} "
              f"B={f['second_translation']:9s} ${f['cost_usd']:<7} {f['function']}")
    print(f"module Autoform.NLModel.{tr.module}: {meta['statuses']}, L0 {meta['L0']}, "
          f"skipped {meta['skipped']}, ${meta['cost_usd']}, {meta['seconds']}s -> {a.out}")
    return 0 if meta['statuses'].get('VALIDATED') else 1


if __name__ == '__main__':
    sys.exit(main())
