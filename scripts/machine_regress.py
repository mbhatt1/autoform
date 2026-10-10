#!/usr/bin/env python3
"""machine_regress.py -- do two commits' compiled functions compute the same thing?

For each function, both versions are compiled for a Linux target (AArch64 by
default), lifted through Ghidra's SLEIGH descriptions into Autoform's p-code Lean
model, and compared:

1. **Search.** Candidate inputs are the typed width boundaries of each parameter
   (powers of two straddling 32 and 64 bits, the type's extremes) plus seeded
   random values. When this host can execute the target's calling convention
   (an arm64 host for AArch64 integer functions), both versions are also compiled
   for the host and run natively, which makes large searches cheap. Otherwise the
   lifted Lean models themselves are executed on the candidates.
2. **Confirmation.** Every diverging input is re-run on both lifted models, which
   must reproduce the native results, and then **kernel-checked**: a Lean theorem
   per version states the exact return register value the machine code produces
   on that input, proved by `rfl`.

Searching is sampling: "no divergence found" is reported with the number of
candidates tried and never as equivalence. A found divergence is a proof, about
the lifted machine code, that the two commits compute different results on that
input; which one is right is a separate question.

Library:  run(base_dir, head_dir, files, functions, target=..., out=...)
CLI:      machine_regress.py BASE_DIR HEAD_DIR --file lib/lcm.c --file lib/gcd.c
                             --function lcm [--target aarch64] --out DIR
Exit status: 0 no divergence found; 1 at least one kernel-checked divergence;
2 invocation or build failure.
"""
from __future__ import annotations

import argparse
import ctypes
import datetime
import hashlib
import itertools
import json
import os
from pathlib import Path
import platform
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

from boundary_values import integer_boundary_pool  # noqa: E402
from dwarf_signature import SignatureError, read_signature  # noqa: E402

SCHEMA_VERSION = 1
SHIM = ROOT / 'scripts' / 'kernel_shim' / 'include'
COMMON_FLAGS = ['-O2', '-g', '-ffreestanding', '-fno-builtin', '-nostdinc',
                '-fno-stack-protector']
STACK, RETURN = 0x7ff0000, 0x7fff000
FUEL = 200000


class RegressError(RuntimeError):
    """A build, lift or Lean step failed; the message says which."""


TARGETS = {
    # Kernel builds use -mgeneral-regs-only on arm64 and regparm(3) on i386.
    'aarch64': dict(triple='aarch64-unknown-linux-gnu', cflags=['-mgeneral-regs-only', '-fno-pic'],
                    ld='aarch64linux', abi='aapcs64',
                    native=platform.machine() in ('arm64', 'aarch64')),
    'x86_64': dict(triple='x86_64-unknown-linux-gnu', cflags=['-mgeneral-regs-only', '-fno-pic'],
                   ld='elf_x86_64', abi='sysv', native=platform.machine() in ('x86_64', 'AMD64')),
    'i386': dict(triple='i386-unknown-linux-gnu', cflags=['-march=i686', '-mregparm=3', '-fno-pic'],
                 ld='elf_i386', abi='i386-regparm3', native=False),
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def tool(name, *candidates):
    found = shutil.which(name) or next((c for c in candidates if Path(c).is_file()), None)
    if not found:
        raise RegressError(f'{name} not found; install it (for ld.lld: brew install lld)')
    return found


def run_command(command, cwd=None, timeout=600):
    proc = subprocess.run([str(c) for c in command], cwd=cwd, text=True, capture_output=True,
                          timeout=timeout)
    return proc.returncode, proc.stdout + proc.stderr


# --------------------------------------------------------------------- building

def build(source_dir, files, target, out_dir, *, includes=(), defines=()):
    """Compile `files` of one source tree for `target` and link them into one ELF.

    Linking resolves calls between the files (the kernel's `lcm` calls `gcd` in
    another translation unit). Unresolved external symbols are allowed: a call to
    one reaches an address outside the lifted image and the model reports it.
    """
    spec = TARGETS[target]
    clang, lld = tool('clang'), tool('ld.lld', '/opt/homebrew/bin/ld.lld', '/usr/local/opt/lld/bin/ld.lld')
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    flags = COMMON_FLAGS + spec['cflags'] + ['-isystem', str(SHIM)]
    flags += [arg for inc in includes for arg in ('-I', str(inc))] + ['-D' + d for d in defines]
    objects, commands = [], []
    for index, name in enumerate(files):
        source = Path(source_dir) / name
        if not source.is_file():
            raise RegressError(f'{source}: not found in this tree')
        obj = out_dir / f'unit{index}.o'
        command = [clang, '-target', spec['triple'], *flags, '-c', source, '-o', obj]
        code, output = run_command(command)
        commands.append([str(c) for c in command])
        if code:
            raise RegressError(f'compiling {name} for {target} failed:\n{output[-3000:]}')
        objects.append(obj)
    elf = out_dir / 'image.elf'
    command = [lld, '-m', spec['ld'], '-static', '-e', '0', '--unresolved-symbols=ignore-all',
               '-o', elf, *objects]
    code, output = run_command(command)
    commands.append([str(c) for c in command])
    if code:
        raise RegressError(f'linking failed:\n{output[-3000:]}')
    return elf, commands


def build_host(source_dir, files, out_dir, *, includes=(), defines=()):
    """The same sources compiled for this host, for fast native execution."""
    clang = tool('clang')
    out = Path(out_dir) / ('host.dylib' if sys.platform == 'darwin' else 'host.so')
    flags = COMMON_FLAGS + ['-isystem', str(SHIM), '-fPIC']
    if sys.platform == 'darwin':
        # The library is loaded by this interpreter's architecture; clang's default target
        # depends on how clang itself was launched, which once produced an unloadable
        # x86_64 dylib under an arm64 Python in the full test run.
        flags += ['-arch', platform.machine()]
    if platform.machine() in ('arm64', 'aarch64'):
        flags.append('-mgeneral-regs-only')
    flags += [arg for inc in includes for arg in ('-I', str(inc))] + ['-D' + d for d in defines]
    shared = ['-dynamiclib', '-undefined', 'dynamic_lookup'] if sys.platform == 'darwin' else ['-shared']
    command = [clang, *flags, *shared, '-o', out, *(Path(source_dir) / f for f in files)]
    code, output = run_command(command)
    if code:
        raise RegressError(f'host build failed:\n{output[-3000:]}')
    return out


def function_symbols(elf):
    """name -> (address, size) for every defined function symbol."""
    from elftools.elf.elffile import ELFFile
    out = {}
    with open(elf, 'rb') as stream:
        image = ELFFile(stream)
        for section in image.iter_sections():
            if section.name != '.symtab':
                continue
            for symbol in section.iter_symbols():
                if (symbol['st_info']['type'] == 'STT_FUNC' and symbol['st_shndx'] != 'SHN_UNDEF'
                        and symbol['st_size']):
                    out[symbol.name] = (symbol['st_value'], symbol['st_size'])
    return out


def function_bytes(elf, address, size):
    from elftools.elf.elffile import ELFFile
    with open(elf, 'rb') as stream:
        image = ELFFile(stream)
        for segment in image.iter_segments():
            start = segment['p_vaddr']
            if segment['p_type'] == 'PT_LOAD' and start <= address and address + size <= start + segment['p_filesz']:
                return segment.data()[address - start:address - start + size]
    return b''


# ------------------------------------------------------------------ call setup

def call_setup(target, signature, args):
    """Registers and memory for calling a function, and where its result lands.

    Only what the calling convention defines is written: arguments, the stack
    pointer, a return address (the stop point) and zeroed callee-saved registers
    (the function saves and restores them, so their values cannot matter, but the
    model refuses to read uninitialized state). Nothing else is invented.
    """
    abi = TARGETS[target]['abi']
    registers, memory = {}, {}
    params = signature.params
    if len(args) != len(params):
        raise RegressError(f'{signature.name} takes {len(params)} arguments, got {len(args)}')

    def bits(value, size):
        return value % (1 << (8 * size))

    if abi == 'aapcs64':
        if len(params) > 8:
            raise RegressError('more than eight arguments need the stack; not supported')
        for index, (param, value) in enumerate(zip(params, args)):
            registers[f'x{index}'] = bits(value, param.size)
        for index in list(range(19, 29)) + [29]:
            registers[f'x{index}'] = 0
        registers.update(x30=RETURN, sp=STACK)
        result = ['w0'] if signature.ret.size <= 4 else ['x0']
    elif abi == 'sysv':
        order = ['RDI', 'RSI', 'RDX', 'RCX', 'R8', 'R9']
        if len(params) > len(order):
            raise RegressError('more than six arguments need the stack; not supported')
        for name, param, value in zip(order, params, args):
            registers[name] = bits(value, param.size)
        for name in ('RBX', 'RBP', 'R12', 'R13', 'R14', 'R15'):
            registers[name] = 0
        registers['RSP'] = STACK
        memory[f'ram:{STACK}:8'] = RETURN
        result = ['EAX'] if signature.ret.size <= 4 else ['RAX']
    elif abi == 'i386-regparm3':
        free = ['EAX', 'EDX', 'ECX']
        for param, value in zip(params, args):
            value = bits(value, param.size)
            if param.size <= 4 and free:
                registers[free.pop(0)] = value
            elif param.size == 8 and len(free) >= 2:
                registers[free.pop(0)] = value & 0xFFFFFFFF
                registers[free.pop(0)] = value >> 32
            else:
                raise RegressError('an argument would be passed on the stack; not supported')
        for name in ('EBX', 'ESI', 'EDI', 'EBP'):
            registers[name] = 0
        registers['ESP'] = STACK
        memory[f'ram:{STACK}:4'] = RETURN
        result = ['EAX'] if signature.ret.size <= 4 else ['EAX', 'EDX']
    else:
        raise RegressError(f'unknown ABI {abi}')
    return registers, memory, result


def combine_result(values, signature):
    """The return value from its result registers (low word first)."""
    value = 0
    for index, part in enumerate(values):
        value |= part << (32 * index) if len(values) > 1 else part
    return value % (1 << (8 * signature.ret.size)) if signature.ret.size else 0


# ------------------------------------------------------------------ the model

class LiftedFunction:
    """One function of one linked image, lifted to the p-code Lean model."""

    def __init__(self, elf, symbol, target, module, work):
        import formalize_machine as fm
        from binary_loader import load_image
        self.fm = fm
        self.elf, self.symbol, self.target, self.module = Path(elf), symbol, target, module
        self.work = Path(work)
        self.work.mkdir(parents=True, exist_ok=True)
        symbols = function_symbols(elf)
        if symbol not in symbols:
            raise RegressError(f'{symbol} is not a defined function in {elf}')
        self.address, self.size = symbols[symbol]
        self.signature = read_signature(elf, symbol)
        if not self.signature.integer_class():
            raise RegressError(f'{symbol}: only integer-class signatures are supported '
                               f'({[p.kind for p in self.signature.params]} -> {self.signature.ret.kind})')
        image = load_image(self.elf, 'elf', None, 0, self.address)
        self.doc = fm.lift_image(image)
        self.model = fm.render_model(self.doc, module)
        coverage = fm.coverage(self.doc)
        self.coverage = coverage
        self.unmodelled = coverage['unsupported_operations']

    def _varnode(self, name):
        v = self.doc['registers'][name]
        return self.fm.lean_var(v)

    def evaluate(self, inputs):
        """Run the Lean model on each argument tuple; returns value or error text."""
        if not inputs:
            return []
        text, namespace = self._runner(inputs)
        text += '\n'.join([
            f'namespace {namespace}',
            f'open Autoform.PCode Autoform.Machine.{self.module}',
            '#eval cases.forM fun c => IO.println (match runWith c rets with',
            '  | .ok vs => "@@ok " ++ toString vs',
            '  | .error e => "@@error " ++ e)',
            f'end {namespace}', ''])
        path = self.work / f'Eval{len(list(self.work.glob("Eval*.lean")))}.lean'
        path.write_text(text, encoding='utf-8')
        code, output = lean(['env', 'lean', path])
        lines = [line[2:] for line in output.splitlines() if line.startswith('@@')]
        if code or len(lines) != len(inputs):
            raise RegressError(f'evaluating {self.symbol} on the model failed:\n{output[-3000:]}')
        results = []
        for line in lines:
            if line.startswith('ok '):
                parts = [int(x) for x in re.findall(r'\d+', line[3:])]
                results.append(combine_result(parts, self.signature))
            else:
                results.append('error: ' + line[6:])
        return results

    def fault_check(self, args, why, label):
        """A Lean theorem, decided by the kernel, that the function faults with `why` on `args`."""
        text, namespace = self._runner([args])
        text += '\n'.join([
            f'namespace {namespace}',
            f'open Autoform.PCode Autoform.Machine.{self.module}',
            'theorem faults : (match runWith (cases.headD []) rets with',
            f'    | .error e => e == {json.dumps(why)} | .ok _ => false) = true := by decide +kernel',
            '#print axioms faults',
            f'end {namespace}', ''])
        path = self.work / f'Fault_{label}.lean'
        path.write_text(text, encoding='utf-8')
        code, output = lean(['env', 'lean', path])
        if code or 'sorryAx' in output:
            raise RegressError(f'kernel check of the fault in {self.symbol}({args}) failed:\n{output[-3000:]}')
        return str(path)

    def _runner(self, inputs):
        rows = []
        for args in inputs:
            registers, memory, _ = call_setup(self.target, self.signature, args)
            writes = []
            for spec, value in memory.items():
                space, address, size = spec.split(':')
                v = {'space': space, 'offset': int(address), 'size': int(size)}
                writes.append(f'({self.fm.lean_var(v)}, {value})')
            writes += [f'({self._varnode(name)}, {value})' for name, value in registers.items()]
            rows.append('[' + ', '.join(writes) + ']')
        _, _, result = call_setup(self.target, self.signature, inputs[0])
        rets = '[' + ', '.join(self._varnode(name) for name in result) + ']'
        namespace = f'Autoform.Machine.{self.module}.Eval'
        text = self.model + '\n' + '\n'.join([
            f'namespace {namespace}',
            f'open Autoform.PCode Autoform.Machine.{self.module}',
            'def runWith (writes : List (Varnode × Nat)) (rets : List Varnode) : Except String (List Nat) := do',
            f'  let s ← writes.foldlM (fun s (v, x) => write program s v x) (initialState {self.address})',
            f'  match run program [{RETURN}] {FUEL} s with',
            '  | .stopped final => rets.mapM (read program final)',
            '  | .hole why _ => throw why',
            "  | .outOfFuel _ => throw \"out-of-fuel\"",
            'def cases : List (List (Varnode × Nat)) := [',
            ',\n'.join('  ' + row for row in rows), ']',
            f'def rets : List Varnode := {rets}',
            f'end {namespace}', ''])
        return text, namespace

    def kernel_check(self, args, expected, label):
        """A Lean theorem, proved by the kernel, that the function returns `expected`."""
        registers, memory, result = call_setup(self.target, self.signature, args)
        if len(result) == 1:
            observed = {result[0]: expected}
        else:
            observed = {result[0]: expected & 0xFFFFFFFF, result[1]: expected >> 32}
        assertions = self.fm.render_assertions(self.doc, self.module, registers, memory,
                                               [RETURN], observed, FUEL)
        path = self.work / f'Check_{label}.lean'
        path.write_text(self.model + '\n' + assertions, encoding='utf-8')
        code, output = lean(['env', 'lean', path])
        if code:
            raise RegressError(f'kernel check of {self.symbol}({args}) failed:\n{output[-3000:]}')
        return str(path)


def lean(args, timeout=3600):
    env = dict(os.environ)
    env['PATH'] = str(Path.home() / '.elan/bin') + os.pathsep + env.get('PATH', '')
    proc = subprocess.run(['lake', *[str(a) for a in args]], cwd=ROOT, env=env, text=True,
                          capture_output=True, timeout=timeout)
    return proc.returncode, proc.stdout + proc.stderr


def ensure_semantics_built():
    code, output = lean(['build', 'Autoform.Lang.PCode.Semantics'])
    if code:
        raise RegressError('building the p-code semantics failed:\n' + output[-3000:])


# ------------------------------------------------------------------ searching

def candidates(signature, limit, seed):
    """Boundary combinations first (deterministic), then seeded random tuples."""
    pools = [integer_boundary_pool(8 * p.size, p.signed) + [0] for p in signature.params]
    pools = [sorted(set(pool), key=lambda v: (abs(v), v)) for pool in pools]
    rng = random.Random(seed)
    total = 1
    for pool in pools:
        total *= len(pool)
    if total <= limit:
        tuples = list(itertools.product(*pools))
    else:
        tuples = [tuple(rng.choice(pool) for pool in pools) for _ in range(limit)]
    extra = max(0, limit // 4)
    for _ in range(extra):
        tuples.append(tuple(
            rng.randrange(-(1 << (8 * p.size - 1)), 1 << (8 * p.size - 1)) if p.signed
            else rng.randrange(0, 1 << (8 * p.size)) for p in signature.params))
    seen, out = set(), []
    for t in tuples:
        if t not in seen:
            seen.add(t)
            out.append(t)
    return out


NATIVE_WORKER = r'''
import ctypes, json, sys
spec = json.loads(sys.stdin.read())
def load(path):
    lib = ctypes.CDLL(path)
    fn = getattr(lib, spec["symbol"])
    types = {(1, False): ctypes.c_uint8, (2, False): ctypes.c_uint16, (4, False): ctypes.c_uint32,
             (8, False): ctypes.c_uint64, (1, True): ctypes.c_int8, (2, True): ctypes.c_int16,
             (4, True): ctypes.c_int32, (8, True): ctypes.c_int64}
    fn.argtypes = [types[(p["size"], p["signed"])] for p in spec["params"]]
    fn.restype = types[(spec["ret"]["size"], spec["ret"]["signed"])]
    return fn
base, head = load(spec["base"]), load(spec["head"])
mask = (1 << (8 * spec["ret"]["size"])) - 1
found = []
for args in spec["inputs"]:
    b, h = base(*args) & mask, head(*args) & mask
    if b != h:
        found.append([args, b, h])
        if len(found) >= spec["max"]:
            break
print(json.dumps(found))
'''


def native_divergences(base_lib, head_lib, signature, inputs, maximum, timeout=600):
    """Run both host builds on every input in a separate process (a crash or hang in
    kernel code must not take the harness down)."""
    spec = dict(base=str(base_lib), head=str(head_lib), symbol=signature.name,
                params=[dict(size=p.size, signed=p.signed) for p in signature.params],
                ret=dict(size=signature.ret.size, signed=signature.ret.signed),
                inputs=[list(t) for t in inputs], max=maximum)
    proc = subprocess.run([sys.executable, '-c', NATIVE_WORKER], input=json.dumps(spec),
                          text=True, capture_output=True, timeout=timeout)
    if proc.returncode:
        raise RegressError('native search failed (a crash or signal in the compiled code?):\n'
                           + proc.stderr[-2000:])
    return [(tuple(args), b, h) for args, b, h in json.loads(proc.stdout)]


def model_divergences(base, head, inputs, maximum, chunk=100):
    """Execute both lifted models in batches, stopping at the first batch that has
    enough divergences (interpreting the model is far slower than native code)."""
    found, evaluated = [], 0
    for start in range(0, len(inputs), chunk):
        batch = inputs[start:start + chunk]
        evaluated += len(batch)
        for args, b, h in zip(batch, base.evaluate(batch), head.evaluate(batch)):
            faulted = [v for v in (b, h) if isinstance(v, str)]
            if b != h and (isinstance(b, int) or isinstance(h, int)) and \
                    not any('out-of-fuel' in v for v in faulted):
                # A value on one side and a fault (e.g. division by zero) on the other is a
                # divergence too: it is how a crash fix, or a newly introduced crash, looks.
                found.append((args, b, h))
        if len(found) >= maximum:
            break
    return found, evaluated


# ------------------------------------------------------------------ the run

def compare_function(symbol, base_elf, head_elf, target, work, *, native_libs=None,
                     limit=20000, seed=20260926, witnesses=2, given=()):
    started = time.monotonic()
    work = Path(work)
    record = dict(subject=symbol, status='error', witnesses=[])
    base = LiftedFunction(base_elf, symbol, target, 'Base', work / 'base')
    head = LiftedFunction(head_elf, symbol, target, 'Head', work / 'head')
    record['signature'] = base.signature.to_json()
    record['lift'] = {'base': dict(address=base.address, size=base.size, **base.coverage),
                      'head': dict(address=head.address, size=head.size, **head.coverage)}
    if base.unmodelled or head.unmodelled:
        record.update(status='unmodelled-operations',
                      detail='the lifted code uses p-code operations the Lean model does not execute')
        return record
    if [p.size for p in base.signature.params] != [p.size for p in head.signature.params]:
        record.update(status='signature-changed', detail='parameter shapes differ between commits')
        return record
    # Inputs a person supplied (a commit message's reproducer, a test vector) come
    # first and are always reported when they diverge; the search adds its own.
    given = [tuple(g) for g in given if len(g) == len(base.signature.params)]
    inputs = given + [t for t in candidates(base.signature, limit, seed) if t not in set(given)]
    if native_libs:
        method = 'native'
        found = native_divergences(native_libs[0], native_libs[1], base.signature, inputs, 50)
        evaluated = len(inputs)
    else:
        method = 'lean-model'
        inputs = inputs[:min(len(inputs), 1000)]
        found, evaluated = model_divergences(base, head, inputs, witnesses + len(given))
    record['search'] = dict(method=method, candidates=evaluated, divergences=len(found),
                            seconds=round(time.monotonic() - started, 1),
                            exhaustive=False, seed=seed)
    confirmed = []
    for args, b_native, h_native in found:
        if len(confirmed) >= witnesses + len(given) or (len(confirmed) >= witnesses and args not in given):
            continue
        b_model, h_model = base.evaluate([args])[0], head.evaluate([args])[0]
        entry = dict(inputs=list(args), base=b_model, head=h_model, native_confirmed=False,
                     kernel_checked=False, origin='given' if args in given else 'search')
        if not isinstance(b_model, int) and not isinstance(h_model, int):
            entry['note'] = 'the lifted model did not return on this input'
            record['witnesses'].append(entry)
            continue
        if not (isinstance(b_model, int) and isinstance(h_model, int)):
            if any('out-of-fuel' in str(v) for v in (b_model, h_model)):
                entry['note'] = 'one version did not finish within the fuel budget; not a fault'
                record['witnesses'].append(entry)
                continue
            label = '_'.join(str(a) for a in args)[:80]
            checks = {}
            for side, fn, value in (('base', base, b_model), ('head', head, h_model)):
                checks[side] = (fn.kernel_check(args, value, f'{side}_{label}') if isinstance(value, int)
                                else fn.fault_check(args, value[len('error: '):], f'{side}_{label}'))
            entry.update(lean_checks=checks, kernel_checked=True, kind='fault',
                         note='one version faults in the lifted model where the other returns')
            record['witnesses'].append(entry)
            confirmed.append(entry)
            continue
        if method == 'native':
            if (b_model, h_model) != (b_native, h_native):
                entry.update(note='the lifted model disagrees with native execution',
                             native=[b_native, h_native])
                record['witnesses'].append(entry)
                continue
            entry['native_confirmed'] = True
        if b_model == h_model:
            continue
        label = '_'.join(str(a) for a in args)[:80]
        entry['lean_checks'] = {'base': base.kernel_check(args, b_model, 'base_' + label),
                                'head': head.kernel_check(args, h_model, 'head_' + label)}
        entry['kernel_checked'] = True
        record['witnesses'].append(entry)
        confirmed.append(entry)
    record['search']['seconds'] = round(time.monotonic() - started, 1)
    record['status'] = 'diverges' if confirmed else 'no-divergence-found'
    return record


def run(base_dir, head_dir, files, functions, *, target='aarch64', out, includes=(),
        defines=(), native=True, limit=20000, base_label=None, head_label=None, given=()):
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    ensure_semantics_built()
    base_elf, base_cmds = build(base_dir, files, target, out / 'base' / 'build',
                                includes=includes, defines=defines)
    head_elf, head_cmds = build(head_dir, files, target, out / 'head' / 'build',
                                includes=includes, defines=defines)
    if not functions:
        base_syms, head_syms = function_symbols(base_elf), function_symbols(head_elf)
        functions = sorted(name for name in set(base_syms) & set(head_syms)
                           if function_bytes(base_elf, *base_syms[name]) != function_bytes(head_elf, *head_syms[name]))
    libs = None
    if native and TARGETS[target]['native']:
        libs = (build_host(base_dir, files, out / 'base' / 'build', includes=includes, defines=defines),
                build_host(head_dir, files, out / 'head' / 'build', includes=includes, defines=defines))
    results = []
    for symbol in functions:
        try:
            results.append(compare_function(symbol, base_elf, head_elf, target, out / 'lean' / symbol,
                                            native_libs=libs, limit=limit, given=given))
        except (RegressError, SignatureError, subprocess.TimeoutExpired) as exc:
            results.append(dict(subject=symbol, status='error', detail=str(exc)[-2000:], witnesses=[]))
    changes = []
    for record in results:
        for w in record['witnesses']:
            if w.get('kernel_checked'):
                changes.append(dict(
                    subject=record['subject'], inputs=[None, [['int', a] for a in w['inputs']]],
                    base=['val', ['int', w['base']]], head=['val', ['int', w['head']]],
                    proven_both=True, kernel_checked=True, native_confirmed=w['native_confirmed'],
                    lean_checks=w['lean_checks'], origin='machine-' + record['search']['method']))
    errors = [r for r in results if r['status'] in ('error', 'unmodelled-operations', 'signature-changed')]
    report = dict(
        schema_version=SCHEMA_VERSION, mode='machine',
        generated_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        target=target, abi=TARGETS[target]['abi'], files=list(files),
        base=dict(label=base_label, source=str(base_dir), image=str(base_elf), image_sha256=sha(base_elf),
                  commands=base_cmds),
        head=dict(label=head_label, source=str(head_dir), image=str(head_elf), image_sha256=sha(head_elf),
                  commands=head_cmds),
        functions=results, behavior_changes=changes, regressions=[], improvements=[],
        added=[], removed=[], notes=[dict(kind='error', subject=r['subject'], detail=r.get('detail', r['status']))
                                     for r in errors],
        verdict='behavior-changed' if changes else ('incomplete' if errors else 'no-divergence-found'),
        scope=('Each divergence is kernel-checked on the SLEIGH-lifted machine code of both commits: '
               'Lean proves the exact result each version returns on that input. Lifting '
               'faithfulness is assumed (SLEIGH descriptions are trusted). Searches sample '
               'typed boundary and seeded random inputs; "no divergence found" is not equivalence. '
               'Kernel headers are replaced by scripts/kernel_shim declarations; the compared '
               'functions are compiled from each commit\'s own source.'))
    (out / 'regression.json').write_text(json.dumps(report, indent=2) + '\n')
    (out / 'regression.md').write_text(render_markdown(report))
    return report


def render_markdown(report):
    lines = [f"# Machine regression report ({report['target']}, {report['abi']})", '',
             f"- **base**: `{report['base']['label'] or report['base']['source']}` "
             f"(image `{report['base']['image_sha256'][:12]}`)",
             f"- **head**: `{report['head']['label'] or report['head']['source']}` "
             f"(image `{report['head']['image_sha256'][:12]}`)", '',
             f"**Verdict: {report['verdict']}**", '']
    for record in report['functions']:
        search = record.get('search', {})
        lines.append(f"## `{record['subject']}` — {record['status']}")
        if search:
            lines.append(f"Searched {search['candidates']} inputs ({search['method']}, "
                         f"{search['seconds']} s); {search['divergences']} diverging.")
        for w in record['witnesses']:
            args = ', '.join(hex(a) if isinstance(a, int) else str(a) for a in w['inputs'])
            fmt = lambda v: hex(v) if isinstance(v, int) else str(v)
            status = ('kernel-checked' if w.get('kernel_checked') else w.get('note', 'unconfirmed'))
            if w.get('origin') == 'given':
                status = 'supplied input, ' + status
            if w.get('native_confirmed'):
                status += ', natively confirmed'
            lines.append(f"- `{record['subject']}({args})`: base {fmt(w['base'])}, head {fmt(w['head'])} ({status})")
        if record.get('detail'):
            lines.append(f"- {record['detail'].splitlines()[0]}")
        lines.append('')
    lines += ['## Scope', '', report['scope'], '']
    return '\n'.join(lines)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('base_dir', type=Path)
    parser.add_argument('head_dir', type=Path)
    parser.add_argument('--file', dest='files', action='append', required=True,
                        help='source file relative to both trees (repeatable)')
    parser.add_argument('--function', dest='functions', action='append', default=[],
                        help='function to compare (default: every function whose code changed)')
    parser.add_argument('--target', choices=sorted(TARGETS), default='aarch64')
    parser.add_argument('--include', action='append', default=[], type=Path)
    parser.add_argument('--define', action='append', default=[])
    parser.add_argument('--no-native', action='store_true', help='search on the Lean models only')
    parser.add_argument('--limit', type=int, default=20000, help='search candidates per function')
    parser.add_argument('--input', dest='given', action='append', default=[],
                        type=lambda s: tuple(int(v, 0) for v in s.split(',')),
                        help='comma-separated arguments to try first and always report if they '
                             'diverge (for example a reproducer from a commit message)')
    parser.add_argument('--base-label')
    parser.add_argument('--head-label')
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        report = run(args.base_dir, args.head_dir, args.files, args.functions, target=args.target,
                     out=args.out, includes=args.include, defines=args.define, native=not args.no_native,
                     limit=args.limit, base_label=args.base_label, head_label=args.head_label,
                     given=args.given)
    except (RegressError, subprocess.TimeoutExpired, OSError) as exc:
        print(f'machine_regress: {exc}', file=sys.stderr)
        return 2
    print(render_markdown(report))
    return 1 if report['behavior_changes'] else 0


if __name__ == '__main__':
    sys.exit(main())
