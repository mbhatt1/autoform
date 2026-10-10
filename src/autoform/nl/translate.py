"""Translate stage: a repository → a built Lean model of each function (`schema.Translation`).

    source (Git URL or directory)
      ── acquire ──► checkout + revision              (autoform.repository)
      ── joern ────► cpg.bin → ast.json               (cartographer/export_ast.sc)
      ── render ───► Autoform/Generated/<M>.lean      (cartographer/render_lean.py)
      ── lake ─────► built module
      ── index ────► FunctionInfo per function        (autoform.harness.cpir)
      ── init ─────► Autoform/NL/<M>.lean             (initialized entry, when needed)

Why an initialized entry. `runFunc` starts from the empty heap: module initializers never
ran, so a function that reads a module-level name (a constant, an imported function, a
class, a module object `<module>pkg/mod.py`) meets an unbound name and the model answers a
hole, not a behaviour. `Autoform/NL/<M>.lean` runs the initializers once — `initGlobals
program 5000 moduleInits` — freezes the resulting heap into a literal (so the kernel does
not re-run every initializer for every evaluated case) and PROVES the literal equal to
that `initGlobals` term by `decide +kernel` (structural equality from
`Autoform/NL/Basis.lean`). `call name args` then applies the function from that heap, with
the same `Ctx` `initGlobals` used. Nothing about the literal is trusted: if the Repr
round-trip were wrong, `init_eq` would not check.

Module names default to `NL<CamelCaseRepoName>`; every generated file is named `NL*`, so
they never collide with tracked modules and `.gitignore` can exclude them.
"""
from __future__ import annotations

import argparse
import ast as pyast
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

from autoform.harness import cpir
from autoform.harness.environment import interpreter_builtins
from autoform.nl import schema
from autoform import repository

REPO = Path(__file__).resolve().parents[3]
FUEL = 1000
INIT_FUEL = 5000
LANGUAGES = {'.py': 'python', '.c': 'c', '.h': 'c', '.cc': 'cpp', '.cpp': 'cpp', '.hpp': 'cpp',
             '.java': 'java', '.js': 'javascript', '.ts': 'typescript', '.go': 'go', '.kt': 'kotlin'}
TEST_FILE = re.compile(r'(^test_.*|.*_test|.*Test|.*\.test|.*\.spec|^conftest)\.[A-Za-z]+$')
TEST_SUFFIXES = set(LANGUAGES)
MAX_SOURCE = 6000
MAX_TESTS = 8


class TranslateError(RuntimeError):
    pass


# --------------------------------------------------------------------------------------
# Names and tools
# --------------------------------------------------------------------------------------

def default_module(name: str) -> str:
    """`cachetools-7.1.7-sdist` → `NLCachetools717Sdist`."""
    parts = [p for p in re.split(r'[^A-Za-z0-9]+', name) if p]
    camel = ''.join(p[:1].upper() + p[1:] for p in parts) or 'Repo'
    return 'NL' + camel


def repo_name(source: str, subdir: str | None = None) -> str:
    if repository.is_git_url(source):
        tail = re.split(r'[/:]', source.rstrip('/'))[-1]
        base = tail[:-4] if tail.endswith('.git') else tail
    else:
        base = Path(source).resolve().name
    if subdir and subdir not in ('.', ''):
        base += '-' + Path(subdir).name
    return base


def choose_module(source: str, module: str | None, lean_root: Path, subdir=None) -> str:
    if module:
        if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*', module):
            raise TranslateError(f'module name {module!r} must be a capitalized Lean identifier')
        if module in _committed(lean_root):
            raise TranslateError(f'module {module!r} is a tracked module; choose another name')
        return module
    base = default_module(repo_name(source, subdir))
    committed = _committed(lean_root)
    candidate, n = base, 1
    while candidate in committed:
        n += 1
        candidate = f'{base}{n}'
    return candidate


def _committed(lean_root: Path) -> set:
    try:
        out = subprocess.run(['git', '-C', str(lean_root), 'ls-files', 'Autoform/Generated',
                              'Autoform/NL'], capture_output=True, text=True, timeout=60).stdout
    except (OSError, subprocess.TimeoutExpired):
        return set()
    return {Path(l).stem for l in out.splitlines()}


def joern_home() -> Path:
    home = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (home / 'joern-cli').is_dir():
        home = home / 'joern-cli'
    if not (home / 'joern').exists():
        raise TranslateError(f'joern not found under {home} (set JOERN_HOME)')
    return home


def tool_env() -> dict:
    env = dict(os.environ)
    elan = str(Path.home() / '.elan/bin')
    env['PATH'] = elan + os.pathsep + env.get('PATH', '')
    return env


def run(cmd, cwd, log: Path, timeout=3600, env=None):
    started = time.time()
    try:
        r = subprocess.run([str(c) for c in cmd], cwd=str(cwd), capture_output=True, text=True,
                           timeout=timeout, env=env or tool_env())
    except subprocess.TimeoutExpired as exc:
        raise TranslateError(f'{Path(str(cmd[0])).name} timed out after {timeout}s') from exc
    log.write_text(f'$ {" ".join(map(str, cmd))}\n(cwd {cwd}, {time.time() - started:.1f}s, '
                   f'rc {r.returncode})\n--- stdout\n{r.stdout}\n--- stderr\n{r.stderr}')
    if r.returncode:
        tail = (r.stdout + r.stderr)[-3000:]
        raise TranslateError(f'{" ".join(map(str, cmd[:3]))} failed (rc {r.returncode}); '
                             f'see {log}\n{tail}')
    return r


def source_revision(root: Path, record: dict) -> str:
    if record.get('commit'):
        return 'git:' + record['commit']
    path = REPO / 'scripts/provenance.py'
    if path.is_file():
        try:
            spec = importlib.util.spec_from_file_location('_af_provenance', path)
            mod = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(mod)
            return mod.source_revision(root)
        except Exception:  # noqa: BLE001 - fall back to a local digest
            pass
    digest = hashlib.sha256()
    for p in sorted(Path(root).rglob('*')):
        if p.is_file() and '.git' not in p.parts:
            digest.update(str(p.relative_to(root)).encode() + b'\0' + p.read_bytes())
    return 'sha256:' + digest.hexdigest()


# --------------------------------------------------------------------------------------
# Function index (pure Python; unit-tested without Joern)
# --------------------------------------------------------------------------------------

def _walk(node):
    stack = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, dict):
            yield cur
            stack.extend(v for k, v in cur.items() if k != 'k')
        elif isinstance(cur, list):
            stack.extend(cur)


def hole_labels(body) -> list:
    labels = []
    for n in _walk(body):
        if n.get('k') in ('hole', 'holeS'):
            label = str(n.get('label', ''))
            if label not in labels:
                labels.append(label)
    return sorted(labels)


def bound_names(entry: dict) -> set:
    """Parameters plus every name the body binds locally."""
    bound = set(entry.get('params') or [])
    for key in ('vararg', 'kwarg'):
        if isinstance(entry.get(key), str):
            bound.add(entry[key])
    if (entry.get('pythonSignature') or {}).get('isMethod'):
        bound |= {'self', 'cls'}
    declared = set()
    for n in _walk(entry.get('body')):
        k = n.get('k')
        if k in ('assign', 'forIn', 'tryCatch') and isinstance(n.get('x'), str):
            bound.add(n['x'])
        elif k == 'declGlobal' and isinstance(n.get('x'), str):
            declared.add(n['x'])
    return bound - declared


def free_names(entry: dict) -> set:
    """Names the body reads (or calls by bare name) that it does not bind."""
    bound = bound_names(entry)
    found = set()
    for n in _walk(entry.get('body')):
        k = n.get('k')
        if k == 'name' and isinstance(n.get('v'), str):
            found.add(n['v'])
        elif k == 'call' and isinstance(n.get('f'), str) and ':' not in n['f'] \
                and not n['f'].startswith('<'):
            found.add(n['f'])
    return found - bound


def module_globals(entries: list) -> tuple:
    """(globals, builtin aliases): every `setGlobal`/`declGlobal` target in the program,
    split into names bound to something the initializers compute and names whose every
    binding is a `__builtin.*` function reference (`len`, `iter` bound by the exporter),
    which the interpreter resolves the same way with or without initialization."""
    bound, other = set(), set()
    for e in entries:
        for n in _walk(e.get('body')):
            if n.get('k') in ('setGlobal', 'declGlobal') and isinstance(n.get('x'), str):
                bound.add(n['x'])
                v = n.get('e') or {}
                if not (n.get('k') == 'setGlobal' and v.get('k') == 'fnref'
                        and str(v.get('v', '')).startswith('__builtin.')):
                    other.add(n['x'])
    return other, bound - other


def core_builtins(lean_root: Path) -> set:
    """Names the Core interpreter implements, from every Core semantics source (the
    harness's list reads only Semantics.lean and so misses e.g. `iter`/`next`)."""
    names = set(interpreter_builtins(lean_root))
    for path in (Path(lean_root) / 'Autoform/Lang/Core').glob('*.lean'):
        names |= set(re.findall(r'\|\s*"([A-Za-z_][A-Za-z0-9_]*)"\s*(?:,|=>)', path.read_text()))
    return names


def needs_init(entry: dict, globals_: set, builtins: set) -> bool:
    """True iff the body reads a non-local, non-parameter name that initialization binds or
    the interpreter cannot supply by itself: a module global, a module object, or any other
    free name (a closure capture) that is not an interpreter builtin."""
    for name in free_names(entry):
        if name.startswith('<module>') or name.startswith('<classattr>') or name in globals_:
            return True
        if name not in builtins and not name.startswith('__builtin'):
            return True
    return False


class CallResolver:
    """Resolve call sites to translated functions.

    The Python exporter lowers a call of a module-level function to a call of a MODULE
    OBJECT's field: `callV (field (name "<module>pkg/m.py") "f") args`, and an imported
    name to a field the importing module's initializer copied from another module object.
    `cpir` sees those as `<dynamic>`; this follows them. Verdict per call site:
      a qualified function name       — resolved (callers/callees),
      an interpreter builtin/operator — closed, no callee,
      a method name some translated class defines, or a class constructor — closed,
      anything else (a parameter called, an untranslated import) — open."""

    def __init__(self, entries: list, builtins: set):
        self.table = {e['name'] for e in entries}
        self.by_source = {}
        for e in entries:
            if e.get('sourceName'):
                self.by_source.setdefault(e['sourceName'], set()).add(e['name'])
        self.methods = {n.rsplit('.', 1)[-1] for n in self.table}
        self.classes = {n.rsplit('.', 1)[0] for n in self.table if '.' in n}
        self.builtins = builtins
        # (module object, field) -> expression the initializers store there
        self.fields = {}
        for e in entries:
            for n in _walk(e.get('body')):
                r = n.get('r') or {}
                if n.get('k') == 'setField' and r.get('k') == 'name' \
                        and str(r.get('v', '')).startswith('<module>'):
                    self.fields.setdefault((r['v'], n.get('f')), n.get('v'))

    def _target(self, expr, depth=0):
        """A callee expression → ('fn', qualified) | ('class', qualified) | ('builtin', n) | None."""
        if not isinstance(expr, dict) or depth > 8:
            return None
        k = expr.get('k')
        if k == 'fnref':
            v = str(expr.get('v', ''))
            if v.startswith('__builtin'):
                return ('builtin', v)
            return self._named(v)
        if k == 'field' and (expr.get('a') or {}).get('k') == 'name' \
                and str(expr['a'].get('v', '')).startswith('<module>'):
            mod, attr = expr['a']['v'], expr.get('f')
            hit = self._named(f'{mod[len("<module>"):]}:<module>.{attr}')
            if hit:
                return hit
            return self._target(self.fields.get((mod, attr)), depth + 1)
        if k == 'name' and isinstance(expr.get('v'), str):
            return self._bare(expr['v'])
        return None

    def _named(self, q: str):
        if q.endswith('<meta>'):
            q = q[:-len('<meta>')]
        if q in self.table:
            return ('fn', q)
        if q + '.__init__' in self.table:
            return ('fn', q + '.__init__')      # constructing a class runs its __init__
        if q in self.classes:
            return ('class', q)
        return None

    def _bare(self, f: str):
        if f in self.table:
            return ('fn', f)
        if f.startswith('<operator>') or f in self.builtins or f.startswith('__builtin'):
            return ('builtin', f)
        hits = self.by_source.get(f) or set()
        if len(hits) == 1:
            return ('fn', next(iter(hits)))
        return self._named(f)

    def sites(self, entry: dict) -> list:
        """[(callee description, verdict)] with verdict 'fn:<q>' | 'closed' | 'open'."""
        out = []
        for n in _walk(entry.get('body')):
            k = n.get('k')
            if k == 'call' and isinstance(n.get('f'), str):
                hit = self._bare(n['f'])
                desc = n['f']
            elif k == 'callV':
                hit = self._target(n.get('f'))
                desc = '<dynamic>'
            elif k == 'mcall':
                m = str(n.get('m', ''))
                recv = n.get('recv') or {}
                if recv.get('k') == 'name' and str(recv.get('v', '')).startswith('<module>'):
                    hit = self._target(dict(k='field', a=recv, f=m))
                else:
                    hit = ('builtin', m) if (m in self.builtins or m in self.methods) else None
                desc = '.' + m
            else:
                continue
            if hit is None:
                out.append((desc, 'open'))
            elif hit[0] == 'fn':
                out.append((hit[1], 'fn:' + hit[1]))
            else:
                out.append((desc, 'closed'))
        return out

    def callees(self, entry: dict) -> set:
        return {v[3:] for _, v in self.sites(entry) if v.startswith('fn:')}

    def closed(self, entry: dict) -> bool:
        return all(v != 'open' for _, v in self.sites(entry))


def _python_defs(path: Path):
    """({qualname: [(lineno, start, end, doc, owner_class)]}, lines) for a Python file.

    Qualified names follow Joern's (`Cls.meth`, `outer.inner`), so a method is found under
    its own class and not at the first `def` of the same name in the file."""
    try:
        text = path.read_text(errors='replace')
        tree = pyast.parse(text)
    except (OSError, SyntaxError, ValueError):
        return {}, []
    lines = text.splitlines()
    out = {}

    def visit(node, prefix, owner):
        for child in pyast.iter_child_nodes(node):
            if isinstance(child, (pyast.FunctionDef, pyast.AsyncFunctionDef)):
                q = prefix + [child.name]
                start = min([child.lineno] + [d.lineno for d in child.decorator_list])
                out.setdefault('.'.join(q), []).append(
                    (child.lineno, start, getattr(child, 'end_lineno', child.lineno),
                     pyast.get_docstring(child) or '', owner))
                visit(child, q, None)
            elif isinstance(child, pyast.ClassDef):
                visit(child, prefix + [child.name], child.name)
            else:
                visit(child, prefix, owner if isinstance(child, (pyast.If, pyast.Try)) else None)
    visit(tree, [], None)
    return out, lines


def locate(source_root: Path, fn: cpir.Function, cache: dict):
    """(line, source text, doc, owner class) of a translated function in its source file.

    Python: the `ast` module, matching the qualified class path + name and slicing
    lineno..end_lineno (decorators included). Other languages: the regex locator of
    `autoform.harness.evidence`, which matches the first definition of the name."""
    if not fn.file or source_root is None:
        return None, '', '', None
    path = Path(source_root) / fn.file
    if not path.is_file():
        return None, '', '', None
    if path.suffix == '.py':
        if path not in cache:
            cache[path] = _python_defs(path)
        defs, lines = cache[path]
        qual = fn.name.split(':<module>.', 1)[1] if ':<module>.' in fn.name else fn.source_name
        index = 0
        m = re.search(r'<redefined>(\d+)$', qual)
        if m:
            index = int(m.group(1)) + 1       # `<redefined>0` is the second definition
            qual = qual[:m.start()]
        qual = re.sub(r'<redefined>\d+', '', qual)
        parts = qual.split('.')
        if len(parts) >= 2:           # undo private-name mangling: `_Cls__f` is `__f` in `Cls`
            mangled = '_' + parts[-2].lstrip('_') + '__'
            if parts[-1].startswith(mangled):
                parts[-1] = parts[-1][len(mangled) - 2:]
                qual = '.'.join(parts)
        hits = defs.get(qual) or []
        if not hits:
            return None, '', '', None
        line, start, end, doc, owner = hits[min(index, len(hits) - 1)]
        text = '\n'.join(lines[start - 1:end]) + '\n'
        return line, text[:MAX_SOURCE], doc, owner
    from autoform.harness import evidence
    snippet, location, doc = evidence.source_snippet(source_root, fn)
    line = int(location.rsplit(':', 1)[1]) if location else None
    return line, snippet[:MAX_SOURCE], doc, None


class TestIndex:
    """Test files read once; per-function lookups are regex scans over memory.

    A bare `name(` match is noise for common method names (`get(`), so matches are
    restricted and tagged: a method's calls count only in files that mention its class
    (`high` when the line names the class or a receiver built by `Cls(...)`, else `low`);
    a module function's calls are bare or module-qualified (`high` when the file imports
    the name or its module, else `low`). High-confidence references come first."""

    def __init__(self, roots, primary=None):
        self.files = []
        seen = set()
        for root in roots:
            root = Path(root)
            if not root.is_dir():
                continue
            for path in sorted(root.rglob('*')):
                if (path in seen or not path.is_file() or path.suffix not in TEST_SUFFIXES
                        or '.git' in path.parts):
                    continue
                parts = set(path.relative_to(root).parts[:-1])
                if not (TEST_FILE.match(path.name) or parts & {'tests', 'test', 'testing'}):
                    continue
                seen.add(path)
                try:
                    text = path.read_text(errors='replace')
                except OSError:
                    continue
                rel = path.relative_to(root)
                where = str(rel) if primary and root == Path(primary) else f'{root.name}/{rel}'
                self.files.append((where, text, text.splitlines()))

    def lookup(self, name: str, owner: str | None = None, module: str = '',
               limit=MAX_TESTS) -> list:
        if not name or name.startswith('<'):
            return []
        dunder = name.startswith('__') and name.endswith('__')
        if dunder and not (owner and name == '__init__'):
            return []
        if owner and name == '__init__':
            pattern = re.compile(r'(?<![\w.])' + re.escape(owner) + r'\s*\(')
        elif owner:
            pattern = re.compile(r'\.' + re.escape(name) + r'\s*\(')
        else:
            pattern = re.compile(r'(?<![\w.])' + re.escape(name) + r'\s*\(|\b'
                                 + re.escape(module or '\0') + r'\.' + re.escape(name) + r'\s*\(')
        high, low = [], []
        for rel, text, lines in self.files:
            if owner and not re.search(r'\b' + re.escape(owner) + r'\b', text):
                continue
            if owner:
                receivers = set(re.findall(r'(\w+)\s*=\s*[\w.]*\b' + re.escape(owner) + r'\s*\(', text))
            else:
                imported = bool(re.search(r'^\s*(from|import)\b.*\b(' + re.escape(name) + '|'
                                          + re.escape(module or '\0') + r')\b', text, re.M))
            for i, line in enumerate(lines, 1):
                if not pattern.search(line) or re.match(r'\s*(async\s+)?(def|class)\s', line):
                    continue
                if owner:
                    recv = re.search(r'(\w+)\.' + re.escape(name) + r'\s*\(', line)
                    sure = owner in line or bool(recv and recv.group(1) in receivers)
                else:
                    sure = imported
                ref = dict(location=f'{rel}:{i}', text=line.strip()[:200],
                           confidence='high' if sure else 'low')
                (high if sure else low).append(ref)
            if len(high) >= limit:
                break
        return (high + low)[:limit]



def function_infos(ast_path: Path, module: str, source_root: Path | None, lean_root: Path,
                   test_roots=()) -> list:
    """FunctionInfo for every non-synthetic function of a Core AST."""
    entries = json.loads(Path(ast_path).read_text())
    by_name = {e['name']: e for e in entries if isinstance(e, dict) and isinstance(e.get('name'), str)}
    program = cpir.build(ast_path, module, str(source_root) if source_root else None)
    globals_, aliases = module_globals(entries)
    builtins = core_builtins(lean_root) | aliases
    calls = CallResolver(list(by_name.values()), builtins)
    callers = {}
    for name, entry in by_name.items():
        for callee in calls.callees(entry):
            if callee != name:
                callers.setdefault(callee, set()).add(name)
    tests = TestIndex(([source_root] if source_root else []) + list(test_roots), primary=source_root)
    cache = {}
    out = []
    for fn in program.functions:
        if fn.synthetic:
            continue
        entry = by_name[fn.name]
        labels = hole_labels(entry.get('body'))
        line, text, doc, owner = locate(source_root, fn, cache)
        stem = Path(fn.file).stem if fn.file else ''
        if stem == '__init__':
            stem = Path(fn.file).parent.name
        out.append(schema.FunctionInfo(
            name=fn.name, source_name=fn.source_name, file=fn.file, line=line,
            params=[schema.Param(p.name, p.sort, p.integer_type) for p in fn.params],
            returns=fn.return_sort, hole_free=not labels, holes=labels,
            call_closed=calls.closed(entry),
            needs_init=needs_init(entry, globals_, builtins), source=text, doc=doc,
            tests=tests.lookup(fn.source_name, owner, stem),
            callers=sorted(callers.get(fn.name, ()))))
    return out


def language_of(ast_path: Path) -> str:
    counts = {}
    for e in json.loads(Path(ast_path).read_text()):
        lang = LANGUAGES.get(Path(e.get('file') or '').suffix)
        if lang:
            counts[lang] = counts.get(lang, 0) + 1
    return max(counts, key=counts.get) if counts else 'unknown'


# --------------------------------------------------------------------------------------
# The initialized entry
# --------------------------------------------------------------------------------------

def has_module_inits(generated: Path) -> bool:
    return re.search(r'^def moduleInits : List Func', generated.read_text(), re.M) is not None


def frozen_init(module: str, lean_root: Path, work: Path):
    """Evaluate `initGlobals program INIT_FUEL moduleInits` once; return (heap, gref)."""
    probe = work / f'InitProbe{module}.lean'
    probe.write_text(
        f'import Autoform.Generated.{module}\n'
        f'open Autoform.Core Autoform.Generated.{module}\n'
        '#eval do\n'
        f'  let gp := initGlobals Autoform.Generated.{module}.program {INIT_FUEL} '
        f'Autoform.Generated.{module}.moduleInits\n'
        '  IO.println ("@@" ++ ((repr gp.1).pretty (width := 100000000)))\n'
        '  IO.println ("##" ++ toString gp.2)\n')
    r = run(['lake', 'env', 'lean', probe], lean_root, work / 'init-probe.log', timeout=3600)
    heap = gref = None
    for line in r.stdout.splitlines():
        if line.startswith('@@'):
            heap = line[2:]
        elif line.startswith('##'):
            gref = line[2:].strip()
    if heap is None or gref is None:
        raise TranslateError('could not evaluate the module initializers; see '
                             + str(work / 'init-probe.log'))
    return heap, gref


def init_module_text(module: str, heap: str, gref: str) -> str:
    g = f'Autoform.Generated.{module}'
    return f'''import Autoform.NL.Basis
import {g}

/-!
# `{module}` — initialized entry point (generated by `autoform.nl.translate`; do not edit)

`runFunc` starts from the empty heap, so a function that reads a module-level name holes.
`call` applies a function from the heap the module initializers build instead.
`heap0` is `initGlobals program {INIT_FUEL} moduleInits`, evaluated once and frozen so the
kernel does not re-run the initializers per evaluated case; `init_eq` proves the literal
IS that term, by kernel computation, so nothing about the freezing is trusted.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Autoform.NL.{module}
open Autoform.Core

abbrev program : Program := {g}.program

/-- Fuel for every call through `call`; the translation's `fuel`. -/
def fuel : Nat := {FUEL}

/-- The heap after every module initializer ran (frozen literal, see `init_eq`). -/
def heap0 : Heap := {heap}

/-- Address of the globals frame. -/
def gref : Ref := {gref}

/-- Initialized state: heap and globals frame. -/
def init : Heap × Ref := (heap0, gref)

/-- The frozen literal is exactly what the initializers produce. -/
theorem init_eq : initGlobals program {INIT_FUEL} {g}.moduleInits = init := by
  decide +kernel

/-- The context `initGlobals` runs in: the program's table with the globals frame. -/
def ctx : Ctx := {{ dialect := program.dialect, table := program.table, globals := init.2,
                   builtinBases := program.builtinBases, properties := program.properties,
                   excClasses := program.excClasses, classDecls := program.classDecls }}

/-- Apply `name` to `args` from the initialized heap, with explicit fuel; the final heap
too, so a result `.ref r` can be dereferenced. -/
def callH (fuel : Nat) (name : String) (args : List Val) : Heap × EResult :=
  match ctx.resolve name with
  | none    => (init.1, .hole s!"entry:{{name}}")
  | some fn => applyFunc ctx fuel init.1 fn none args []

/-- Apply `name` to `args` from the initialized heap, with explicit fuel. -/
def callF (fuel : Nat) (name : String) (args : List Val) : EResult := (callH fuel name args).2

/-- Apply `name` to `args` from the initialized heap. -/
def call (name : String) (args : List Val) : EResult := callF fuel name args

end Autoform.NL.{module}
'''


# --------------------------------------------------------------------------------------
# The stage
# --------------------------------------------------------------------------------------

def translate(source: str, module: str | None, lean_root: Path, out_dir: Path, *, ref=None,
              subdir=None, build=True, ast: Path | None = None, test_roots=(),
              language_arg: str | None = None) -> schema.Translation:
    """Translate `source` into a built Lean model; write `out_dir/translation.json`.

    `ast` skips Joern and uses an existing Core AST (the source is still indexed for
    line/source/doc/tests). `build=False` renders and indexes but runs no Lean.
    `test_roots` are extra directories searched for calls from tests."""
    lean_root = Path(lean_root).resolve()
    out_dir = Path(out_dir).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    work = out_dir / 'translate'
    work.mkdir(exist_ok=True)
    module = choose_module(str(source), module, lean_root, subdir)
    timings = {}
    notes = []

    t = time.time()
    root, record = repository.resolve_source(str(source), out_dir, module, ref=ref, subdir=subdir)
    revision = source_revision(root, record)
    timings['acquire'] = round(time.time() - t, 2)

    ast_path = out_dir / f'ast-{module}.json'
    if ast is not None:
        shutil.copyfile(ast, ast_path)
        notes.append(f'AST supplied: {ast}')
    else:
        t = time.time()
        joern = joern_home()
        lang = language_arg or os.environ.get('AUTOFORM_FRONTEND')
        extra = ['--language', lang] if lang else []
        run([joern / 'joern-parse', root, '--output', work / 'cpg.bin', *extra], work,
            work / 'parse.log')
        timings['parse'] = round(time.time() - t, 2)
        t = time.time()
        r = run([joern / 'joern', '--script', lean_root / 'cartographer/export_ast.sc',
                 '--param', f'cpgPath={work / "cpg.bin"}', '--param', f'out={ast_path}',
                 '--param', 'dataModel=' + os.environ.get('AUTOFORM_DATA_MODEL', 'lp64')],
                work, work / 'export.log')
        if not re.search(r'^exported', r.stdout + r.stderr, re.M) or not ast_path.is_file():
            raise TranslateError('Joern export produced no AST; see ' + str(work / 'export.log'))
        timings['export'] = round(time.time() - t, 2)

    t = time.time()
    generated = lean_root / 'Autoform/Generated' / f'{module}.lean'
    run([sys.executable, lean_root / 'cartographer/render_lean.py', ast_path, generated, module],
        lean_root, work / 'render.log')
    timings['render'] = round(time.time() - t, 2)
    if build:
        t = time.time()
        run(['lake', 'build', f'Autoform.Generated.{module}'], lean_root, work / 'build.log',
            timeout=4 * 3600)
        timings['build'] = round(time.time() - t, 2)

    t = time.time()
    functions = function_infos(ast_path, module, root, lean_root,
                               test_roots=list(test_roots) + ([record['checkout']] if
                                                              record.get('checkout') and
                                                              Path(record['checkout']) != root
                                                              else []))
    timings['index'] = round(time.time() - t, 2)

    program_const = f'Autoform.Generated.{module}.program'
    init_const = None
    call_template = f'runFunc {program_const} {FUEL} {{name}} {{args}}'
    nl_file = lean_root / 'Autoform/NL' / f'{module}.lean'
    if any(f.needs_init for f in functions):
        if not has_module_inits(generated):
            notes.append('functions read module-level names but the rendered module has no '
                         'moduleInits; they run from the empty heap and may hole')
        elif build:
            t = time.time()
            heap, gref = frozen_init(module, lean_root, work)
            nl_file.parent.mkdir(parents=True, exist_ok=True)
            nl_file.write_text(init_module_text(module, heap, gref))
            timings['init_eval'] = round(time.time() - t, 2)
            t = time.time()
            try:
                run(['lake', 'build', f'Autoform.NL.{module}'], lean_root,
                    work / 'build-init.log', timeout=4 * 3600)
            except TranslateError as exc:
                # The model is still usable from the empty heap; say so rather than fail.
                nl_file.unlink(missing_ok=True)
                notes.append('initialized entry did not build (functions with needs_init run '
                             f'from the empty heap and may hole): {str(exc)[:500]}')
            else:
                init_const = f'Autoform.NL.{module}.init'
                call_template = f'Autoform.NL.{module}.call {{name}} {{args}}'
            timings['init_build'] = round(time.time() - t, 2)
        else:
            notes.append('build=False: the initialized entry was not generated')
    notes.append('timings(s): ' + json.dumps(timings))
    notes.append('initialized entry: `call` applies a function from the frozen heap of '
                 '`initGlobals`; for a function that reads no module state it agrees with '
                 '`runFunc` except that fresh heap references start after the initialized '
                 'heap' if init_const else 'no function reads module-level state; runFunc '
                 'from the empty heap is the entry point')

    tr = schema.Translation(
        module=module, language=language_of(ast_path), lean_root=str(lean_root),
        source_root=str(root), source_revision=revision, ast=str(ast_path),
        program_const=program_const, init_const=init_const, call_template=call_template,
        fuel=FUEL, functions=functions, notes=notes)
    schema.dump(tr, out_dir / schema.FILES['translation'])
    return tr


def summary(tr: schema.Translation) -> dict:
    fs = tr.functions
    return dict(module=tr.module, functions=len(fs),
                hole_free=sum(f.hole_free for f in fs),
                call_closed=sum(f.call_closed for f in fs),
                hole_free_and_closed=sum(f.hole_free and f.call_closed for f in fs),
                needs_init=sum(f.needs_init for f in fs),
                with_tests=sum(bool(f.tests) for f in fs),
                init_const=tr.init_const, call_template=tr.call_template)


def main(argv=None):
    ap = argparse.ArgumentParser(prog='python -m autoform.nl.translate', description=__doc__.split('\n')[0])
    ap.add_argument('source', help='Git URL or directory')
    ap.add_argument('--module', help='Lean module suffix (default NL<RepoName>)')
    ap.add_argument('--out', required=True, help='run directory')
    ap.add_argument('--lean-root', default=str(REPO), help='Lean project (lake root)')
    ap.add_argument('--ref')
    ap.add_argument('--subdir')
    ap.add_argument('--ast', help='use this Core AST instead of running Joern')
    ap.add_argument('--tests', action='append', default=[], help='extra test directory')
    ap.add_argument('--language', help='joern-parse --language')
    ap.add_argument('--no-build', action='store_true')
    a = ap.parse_args(argv)
    try:
        tr = translate(a.source, a.module, Path(a.lean_root), Path(a.out), ref=a.ref,
                       subdir=a.subdir, build=not a.no_build, ast=Path(a.ast) if a.ast else None,
                       test_roots=a.tests, language_arg=a.language)
    except (TranslateError, ValueError) as exc:
        print(f'translate: {exc}', file=sys.stderr)
        return 1
    print(json.dumps(summary(tr), indent=1))
    print(tr.notes[-2])
    return 0


if __name__ == '__main__':
    sys.exit(main())
