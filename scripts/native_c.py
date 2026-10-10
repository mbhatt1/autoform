"""Compile Joern-identified scalar entry points in their original translation units."""
from pathlib import Path
import collections
import ctypes
import hashlib
import json
import math
import os
import platform
import re
import shlex
import signal
import subprocess
import sys
import tempfile

import source_context

TYPES = {'i8': ('int8_t', ctypes.c_int8), 'u8': ('uint8_t', ctypes.c_uint8),
         'i16': ('int16_t', ctypes.c_int16), 'u16': ('uint16_t', ctypes.c_uint16),
         'i32': ('int32_t', ctypes.c_int32), 'u32': ('uint32_t', ctypes.c_uint32),
         'i64': ('int64_t', ctypes.c_int64), 'u64': ('uint64_t', ctypes.c_uint64)}
DEFAULT_TIMEOUT = 3.0


class NativeExecutionError(RuntimeError):
    def __init__(self, result):
        self.result = result
        super().__init__('native execution: ' + json.dumps(result, sort_keys=True))


def worker(request, timeout=None):
    """Load and invoke native code outside this process, with a parent deadline.

    This contains crashes and hangs, including constructors and descendants that
    remain in the worker's process group. It is not a filesystem/network sandbox.
    """
    timeout = DEFAULT_TIMEOUT if timeout is None else timeout
    if not isinstance(timeout, (int, float)) or not math.isfinite(timeout) or timeout <= 0:
        raise ValueError('native timeout must be positive and finite')
    try:
        read_fd, write_fd = os.pipe()
    except OSError as exc:
        return dict(status='launch_error', detail=str(exc))
    proc = None
    try:
        try:
            proc = subprocess.Popen(
                [sys.executable, '-I', str(Path(__file__).with_name('native_c_worker.py')), str(write_fd)],
                stdin=subprocess.PIPE, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                pass_fds=(write_fd,), start_new_session=True)
        finally:
            os.close(write_fd)
        try:
            proc.communicate(json.dumps(request).encode(), timeout=timeout)
        except subprocess.TimeoutExpired:
            return dict(status='timeout', timeout_seconds=timeout)
        if proc.returncode < 0:
            return dict(status='signal', signal=-proc.returncode)
        if proc.returncode:
            return dict(status='exit', exit_code=proc.returncode)
        # Never wait for EOF: a native descendant may retain the pipe after its
        # parent exits. The worker response is bounded and written before exit.
        os.set_blocking(read_fd, False)
        payload = bytearray()
        while len(payload) <= 8192:
            try:
                chunk = os.read(read_fd, 8193 - len(payload))
            except BlockingIOError:
                break
            if not chunk:
                break
            payload.extend(chunk)
        try:
            result = json.loads(payload)
        except (ValueError, UnicodeError):
            return dict(status='protocol_error', detail='missing or invalid native worker result')
        if not isinstance(result, dict) or result.get('status') not in ('ok', 'error'):
            return dict(status='protocol_error', detail='invalid native worker status')
        return result
    except OSError as exc:
        return dict(status='launch_error', detail=str(exc))
    finally:
        os.close(read_fd)
        if proc is not None:
            # Kill the group even after the leader exits: forked descendants must
            # not outlive a case or keep descriptors and CPU resources forever.
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                pass
            proc.wait()
            if proc.stdin is not None:
                proc.stdin.close()


class NativeFunction:
    """A library/symbol/ABI description; it never dlopens in the parent."""
    def __init__(self, path, symbol, arguments, result):
        self.path, self.symbol = str(Path(path).resolve()), symbol
        self.arguments, self.result = list(arguments), result
        self.argtypes = [TYPES[t][1] for t in arguments]
        self.restype = TYPES[result][1]

    def observe(self, values, repeat=1, timeout=None):
        if repeat not in (1, 2):
            raise ValueError('native repeat must be one or two')
        if len(values) != len(self.arguments) or any(
                type(v) is not int or c(v).value != v for c, v in zip(self.argtypes, values)):
            return dict(status='input_error', detail='arguments are outside the declared integer ABI')
        result = worker(dict(operation='call', library=self.path, symbol=self.symbol,
                             arguments=self.arguments, result=self.result,
                             values=list(values), repeat=repeat), timeout=timeout)
        if result['status'] == 'ok':
            returned = result.get('values')
            if (not isinstance(returned, list) or len(returned) != repeat or any(
                    type(v) is not int or self.restype(v).value != v for v in returned)):
                return dict(status='protocol_error', detail='result is outside the declared integer ABI')
        return result

    def __call__(self, *values):
        result = self.observe(values)
        if result['status'] != 'ok':
            raise NativeExecutionError(result)
        return result['values'][0]


def identity(f):
    return f['name'], f.get('file', '')


class NativeLibrary:
    def __init__(self, context):
        self.functions = {}
        self.libraries = []
        self.skipped = {}
        self.info = dict(context=context, units=[], dependencies_sha256={},
                         files_attempted=0, files_compiled=0, entry_points=0,
                         execution=dict(worker='subprocess', timeout_seconds=DEFAULT_TIMEOUT,
                                        parent_loads_library=False, sandboxed=False))

    def __call__(self, f):
        return self.functions.get(identity(f))

    def load(self, path, funcs):
        outcome = worker(dict(operation='probe', library=str(Path(path).resolve()),
                              symbols=[symbol for _, symbol in funcs]))
        if outcome['status'] != 'ok':
            raise NativeExecutionError(outcome)
        loaded = {}
        for f, symbol in funcs:
            fn = NativeFunction(path, symbol, f['paramIntegerTypes'], f['returnIntegerType'])
            loaded[identity(f)] = fn
        self.libraries.append(str(path))
        self.functions.update(loaded)


def _link_failure(diagnostics):
    """The unit compiled; only undefined external symbols stopped the link."""
    return (' error:' not in diagnostics.replace('clang: error: linker', '')
            .replace('collect2: error: ld', '')
            and ('linker command failed' in diagnostics or 'undefined reference' in diagnostics
                 or 'Undefined symbols' in diagnostics or 'ld returned' in diagnostics))


def compile_sources(source, funcs, work):
    source, work = Path(source).resolve(), Path(work)
    work.mkdir(parents=True, exist_ok=True)
    # dlopen caches by path, even if the file at that path was rebuilt. Reusing
    # names in one process silently executes the previous corpus's library.
    work = Path(tempfile.mkdtemp(prefix='build-', dir=work))
    context = source_context.profile(source)
    result = NativeLibrary(context)
    if not context['native_model_matches_host']:
        result.info['status'] = 'unsupported: target integer model differs from host ABI'
        return result
    # A real kernel compilation database describes a kernel target, not a host
    # shared-library ABI. Do not substitute a portability build for that target.
    if context['compilation_database']:
        result.info['status'] = 'unsupported: configured target requires a matching runtime adapter'
        return result
    by_file = collections.defaultdict(list)
    counts = collections.Counter((f.get('file'), f.get('sourceName', f['name'])) for f in funcs)
    for idx, f in enumerate(funcs):
        path = (source / f.get('file', '')).resolve()
        name = f.get('sourceName', f['name'])
        tags = f.get('paramIntegerTypes', [])
        if (not path.is_file() or path.suffix not in ('.c', '.cc', '.cpp', '.cxx')
                or not path.is_relative_to(source)):
            reason = 'entry point is not in a source translation unit'
        elif (f.get('returnIntegerType') not in TYPES or len(tags) != len(f['params'])
              or any(t not in TYPES for t in tags)):
            reason = 'scalar integer ABI unavailable'
        elif not re.fullmatch(r'[A-Za-z_]\w*(?:::[A-Za-z_]\w*)*', name):
            reason = 'source callable identity unavailable'
        elif counts[(f.get('file'), name)] > 1:
            reason = 'ambiguous conditional or overloaded entry point'
        else:
            by_file[path].append((idx, f))
            continue
        result.skipped[f['name']] = reason
    units = []
    if not context['kernel_root']:
        # Link dependencies even if they expose no scalar entry point (for example
        # a void helper called by an integer-valued function in another file).
        for path in source.rglob('*'):
            if path.suffix in ('.c', '.cc', '.cpp', '.cxx') and path.is_file():
                by_file.setdefault(path.resolve(), [])
    for index, (path, members) in enumerate(sorted(by_file.items())):
        cpp = path.suffix != '.c'
        unit = work / ('unit%d' % index + ('.cpp' if cpp else '.c'))
        lines = ['#include <stdint.h>', '#include ' + json.dumps(str(path), ensure_ascii=False)]
        bindings = []
        for idx, f in members:
            name = f.get('sourceName', f['name'])
            symbol = 'autoform_native_%d' % idx
            params = ', '.join(TYPES[t][0] + ' a%d' % n for n, t in enumerate(f['paramIntegerTypes'])) or 'void'
            args = ', '.join('a%d' % n for n in range(len(f['params'])))
            prefix = 'extern "C" ' if cpp else ''
            lines.append('%s%s %s(%s) { return %s(%s); }' %
                         (prefix, TYPES[f['returnIntegerType']][0], symbol, params, name, args))
            bindings.append((f, symbol))
        unit.write_text('\n'.join(lines) + '\n')
        units.append((unit, path, bindings))
    result.info['files_attempted'] = len(units)
    flags = source_context.native_flags(context, work) + shlex.split(os.environ.get('AUTOFORM_CFLAGS', ''))
    arch = ['-arch', platform.machine()] if sys.platform == 'darwin' else []
    suffix = '.dylib' if sys.platform == 'darwin' else '.so'

    def build(selected, label, partners=()):
        output, deps = work / (label + suffix), work / (label + '.d')
        compiler = 'c++' if any(u.suffix == '.cpp' for u, _, _ in selected) else 'cc'
        inputs = [arg for u, _, _ in selected for arg in
                  ('-x', 'c++' if u.suffix == '.cpp' else 'c', str(u))]
        # Link partners are sibling sources compiled in unchanged, without wrappers:
        # they supply definitions, not entry points.
        inputs += [arg for p in partners for arg in
                   ('-x', 'c++' if p.suffix != '.c' else 'c', str(p))]
        command = [compiler, '-shared', '-fPIC', '-O0', *arch, *flags,
                   '-MMD', '-MF', str(deps), '-MT', 'autoform', '-o', str(output),
                   *inputs]
        record = dict(files=[str(p.relative_to(source)) for _, p, _ in selected], command=command)
        if partners:
            record['link_partners'] = [str(p.relative_to(source)) for p in partners]
        try:
            proc = subprocess.run(command, capture_output=True, text=True, timeout=60)
            record.update(exit_code=proc.returncode, diagnostics=proc.stdout + proc.stderr)
            if proc.returncode:
                return False, record
            if len(selected) + len(partners) > 1:
                # A shared -MF is overwritten by each translation unit. Ask for
                # the union before accepting evidence from the combined library.
                dep = subprocess.run([compiler, *arch, *flags, '-MM', '-MT', 'autoform', *inputs],
                                     capture_output=True, text=True, timeout=60)
                if dep.returncode:
                    record.update(exit_code=dep.returncode, diagnostics=dep.stderr)
                    return False, record
                deps.write_text(dep.stdout)
            result.load(output, [binding for _, _, bs in selected for binding in bs])
            # Dependency files use Make escaping; shlex handles escaped spaces and
            # line continuations after stripping the target. Hash actual header bytes.
            if deps.exists():
                content = deps.read_text().replace('\\\n', '')
                for word in shlex.split(content.replace('autoform:', '')):
                    path = Path(word)
                    if path.is_file() and not path.is_relative_to(work):
                        result.info['dependencies_sha256'][str(path.resolve())] = hashlib.sha256(path.read_bytes()).hexdigest()
            return True, record
        except NativeExecutionError as exc:
            record.update(load_result=exc.result, diagnostics=str(exc))
            return False, record
        except (OSError, AttributeError, subprocess.TimeoutExpired) as exc:
            record.update(exit_code=None, diagnostics=str(exc))
            return False, record

    # Preserve cross-file dependencies for ordinary C projects. Kernel sources
    # span mutually exclusive architectures and need per-unit portability probes.
    if units and not context['kernel_root']:
        ok, record = build(units, 'combined')
        result.info['combined_build'] = record
        if ok:
            result.info.update(files_compiled=len(units), entry_points=len(result.functions), status='available')
            return result
    compiled, link_failed = [], []
    for index, unit in enumerate(units):
        ok, record = build([unit], 'library%d' % index)
        result.info['units'].append(record)
        if ok:
            result.info['files_compiled'] += 1
            compiled.append(unit[1])
        elif record.get('exit_code') and _link_failure(record.get('diagnostics', '')):
            link_failed.append((index, unit))
        else:
            for f, _ in unit[2]:
                result.skipped[f['name']] = 'translation unit compile/load failed: ' + str(unit[1].relative_to(source))
    # A kernel unit that compiled but did not link calls into a sibling file
    # (`lcm` -> `gcd`). Retry it with the siblings that built on their own, which
    # are exactly the definitions this portability build can already stand behind.
    for index, unit in link_failed:
        partners = [p for p in compiled if p != unit[1]]
        ok, record = build([unit], 'linked%d' % index, partners) if partners else (False, None)
        if record is not None:
            result.info['units'].append(record)
        if ok:
            result.info['files_compiled'] += 1
        else:
            for f, _ in unit[2]:
                result.skipped[f['name']] = ('translation unit link failed: ' +
                                             str(unit[1].relative_to(source)))
    result.info['entry_points'] = len(result.functions)
    result.info['status'] = ('available' if result.functions else 'unsupported: no translation unit could be executed')
    return result
