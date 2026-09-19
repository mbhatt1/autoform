"""Build context shared by the Joern frontend and native C oracle.

An unconfigured kernel tree is explicitly a portable userspace experiment. It is
never described as a configured kernel build or a booted-kernel observation.
"""
from pathlib import Path
import argparse
import ctypes
import json
import os


KERNEL_ATTRIBUTES = (
    '__init', '__exit', '__initdata', '__initconst', '__exitdata', '__ref',
    '__cold', '__must_check', '__weak', '__maybe_unused', '__always_inline',
    '__pure', '__used', '__read_mostly', '__attribute_const__', '__noreturn',
    '__visible', '__force', '__user', '__kernel', '__iomem', '__percpu',
    '__rcu', '__private',
)


def kernel_root(source):
    source = Path(source).resolve()
    for root in (source, *source.parents):
        if all((root / p).is_file() for p in ('Kbuild', 'Kconfig', 'Makefile', 'include/linux/kernel.h')):
            return root
    return None


def profile(source):
    root = kernel_root(source)
    defines = [x for x in os.environ.get('CPP_DEFINES', '').split(',') if x]
    data_model = os.environ.get('AUTOFORM_DATA_MODEL', 'lp64')
    model_bits = {'lp64': 64, 'llp64': 32, 'ilp32': 32}.get(data_model)
    database = os.environ.get('AUTOFORM_COMPILE_COMMANDS')
    if not database:
        candidate = (root or Path(source)) / 'compile_commands.json'
        if candidate.is_file():
            database = str(candidate.resolve())
    if database and not Path(database).is_file():
        raise ValueError('compilation database does not exist: ' + database)
    if root and not database:
        user_names = {d.split('=', 1)[0] for d in defines}
        defaults = [name + '=' for name in KERNEL_ATTRIBUTES]
        if model_bits:
            defaults.append('BITS_PER_LONG=' + str(model_bits))
        defines = [d for d in defaults if d.split('=', 1)[0] not in user_names] + defines
    args = []
    if database:
        args += ['--compilation-database', str(Path(database).resolve())]
    for define in defines:
        # Pinned Joern splits NAME= with String.split, dropping the empty value
        # and crashing. A C comment is an empty replacement token sequence.
        args += ['--define', define + '/**/' if define.endswith('=') else define]
    host_matches = data_model == ('lp64' if ctypes.sizeof(ctypes.c_long) == 8 else 'ilp32')
    if root:
        word_bits = next((d.split('=', 1)[1] for d in defines if d.startswith('BITS_PER_LONG=')), None)
        if word_bits is not None and word_bits != str(ctypes.sizeof(ctypes.c_long) * 8):
            host_matches = False
    return dict(
        kind='linux' if root else 'source', source=str(Path(source).resolve()),
        kernel_root=str(root) if root else None, data_model=data_model,
        compilation_database=database, defines=defines,
        frontend_args=['--frontend-args', *args] if args else [],
        native_model_matches_host=host_matches,
        configuration=('compilation-database' if database else 'portable-userspace' if root else 'default'),
        limitations=([
            'No booted kernel runtime; native evidence covers only host-compilable scalar helpers.',
            'Function and coverage counts describe the CPG, not an independent compiler census.',
            'Concurrency, hardware and unmodeled memory operations remain explicit gaps.',
        ] if root else []),
    )


def native_flags(context, work):
    """Use unchanged kernel tools headers, with generated asm include redirects."""
    flags = ['-D' + d for d in context['defines']]
    root = context.get('kernel_root')
    if root:
        root = Path(root)
        headers = Path(work) / 'kernel-include' / 'asm'
        headers.mkdir(parents=True, exist_ok=True)
        for name in ('types', 'posix_types', 'bitsperlong'):
            (headers / (name + '.h')).write_text('#include <asm-generic/' + name + '.h>\n')
        # Native compilation resolves attributes via the actual headers. Parser-only
        # attribute substitutions must not override compiler semantics/linkage.
        flags = [f for f in flags if f[2:].split('=', 1)[0] not in KERNEL_ATTRIBUTES]
        for path in (headers.parent, root / 'tools/include', root / 'include/uapi', root / 'include'):
            flags += ['-I', str(path)]
    return flags


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('source')
    p.add_argument('output')
    p.add_argument('--args-file', required=True)
    a = p.parse_args()
    ctx = profile(a.source)
    language = os.environ.get('AUTOFORM_LANGUAGE')
    if language:
        ctx['language'] = language
        ctx['frontend'] = os.environ.get('AUTOFORM_FRONTEND')
        if language != 'c':
            ctx['frontend_args'] = []
    Path(a.output).write_text(json.dumps(ctx, indent=2) + '\n')
    Path(a.args_file).write_bytes(b''.join(s.encode() + b'\0' for s in ctx['frontend_args']))


if __name__ == '__main__':
    main()
