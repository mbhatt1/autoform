"""Build context shared by the Joern frontend and native C oracle.

An unconfigured kernel tree is explicitly a portable userspace experiment. It is
never described as a configured kernel build or a booted-kernel observation.
"""
from pathlib import Path
import argparse
import ctypes
import json
import os
import stat
import sys

import repository_inventory


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


# Extensions Joern's language guess weighs when `joern-parse` is given no --language
# (`guessMajorityLanguageInDir`: the language with the most files wins).
_GUESS_EXTENSIONS = {
    '.java': 'JAVASRC', '.kt': 'KOTLIN', '.py': 'PYTHONSRC', '.go': 'GOLANG',
    '.js': 'JSSRC', '.jsx': 'JSSRC', '.ts': 'JSSRC', '.tsx': 'JSSRC', '.c': 'C', '.h': 'C',
    '.cpp': 'C', '.cc': 'C', '.hpp': 'C', '.cs': 'CSHARPSRC', '.php': 'PHP', '.rb': 'RUBYSRC',
    '.swift': 'SWIFTSRC',
}


def guessed_frontend(source):
    """The frontend `joern-parse` will pick for `source`: AUTOFORM_FRONTEND, else the
    majority language by file count (hidden directories skipped, symlinks not followed)."""
    if os.environ.get('AUTOFORM_FRONTEND'):
        return os.environ['AUTOFORM_FRONTEND'].upper()
    counts = {}
    for directory, dirs, files in os.walk(source):
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        for name in files:
            frontend = _GUESS_EXTENSIONS.get(os.path.splitext(name)[1].lower())
            if frontend:
                counts[frontend] = counts.get(frontend, 0) + 1
    return max(counts, key=counts.get) if counts else None


def jvm_frontend_args(source):
    """`--delombok-mode` for the Java frontend, or [] for any other.

    Joern's default runs delombok on any project that uses Lombok and then parses the
    delombok OUTPUT; when delombok fails (it needs the project's dependency jars, which
    are not fetched) that output does not exist and javasrc2cpg writes an empty CPG with
    only warnings -- measured on a 1,472-file Gradle service: 0 functions exported.
    `types-only` parses the original sources and uses delombok for type information
    only, so a failed delombok costs types, never the code. AUTOFORM_DELOMBOK_MODE
    overrides it (no-delombok, default, types-only, run-delombok).
    """
    if guessed_frontend(source) != 'JAVASRC':
        return []
    return ['--delombok-mode', os.environ.get('AUTOFORM_DELOMBOK_MODE') or 'types-only']


HOST_HEADER_SHIMS = {
    'endian.h': (
        '/* autoform: glibc <endian.h> for hosts without it. */\n'
        '#pragma once\n'
        '#if defined(__has_include_next) && __has_include_next(<endian.h>)\n'
        '#include_next <endian.h>\n'
        '#else\n'
        '#ifndef __LITTLE_ENDIAN\n#define __LITTLE_ENDIAN 1234\n#endif\n'
        '#ifndef __BIG_ENDIAN\n#define __BIG_ENDIAN 4321\n#endif\n'
        '#ifndef __BYTE_ORDER\n'
        '#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__\n'
        '#define __BYTE_ORDER __BIG_ENDIAN\n'
        '#else\n#define __BYTE_ORDER __LITTLE_ENDIAN\n#endif\n'
        '#endif\n'
        '#endif\n'),
    'byteswap.h': (
        '/* autoform: glibc <byteswap.h> for hosts without it. */\n'
        '#pragma once\n'
        '#if defined(__has_include_next) && __has_include_next(<byteswap.h>)\n'
        '#include_next <byteswap.h>\n'
        '#else\n'
        '#define bswap_16(x) __builtin_bswap16(x)\n'
        '#define bswap_32(x) __builtin_bswap32(x)\n'
        '#define bswap_64(x) __builtin_bswap64(x)\n'
        '#endif\n'),
}


KERNEL_COMPAT_HEADER = (
    '/* autoform: helpers include/linux/kernel.h provides and tools/include lacks. */\n'
    '#pragma once\n'
    '#ifndef swap\n'
    '#define swap(a, b) \\\n'
    '\tdo { __typeof__(a) __tmp = (a); (a) = (b); (b) = __tmp; } while (0)\n'
    '#endif\n'
    '/* include/linux/kernel.h includes <linux/bitops.h> (__ffs, __fls, hweight);\n'
    ' * the tools copy does not, so lib/math/gcd.c\'s binary_gcd() could not see\n'
    ' * __ffs. The tools tree\'s own bitops.h is used where it exists. */\n'
    '#if defined(__has_include)\n'
    '#if __has_include(<linux/bitops.h>)\n'
    '#include <linux/bitops.h>\n'
    '#endif\n'
    '#endif\n')


# include/linux/gcd.h (since v6.17, "lib/math/gcd: use static key to select
# implementation at runtime") includes <linux/jump_label.h>, whose real body needs a
# configured Kbuild tree (WARN_ON_ONCE, <asm/jump_label.h>, self-patching code), so
# every unit reaching gcd.h failed to compile and lib/math had 0 observable units.
# Outside Kbuild a static key is a plain boolean read: DEFINE_STATIC_KEY_TRUE(k) is a
# key that is initially enabled and nothing in a portable-userspace build ever
# toggles it, so static_branch_likely(&k) is the key's initial value. That is the
# documented meaning of an untoggled key and the only part of jump-label semantics a
# scalar helper such as gcd() depends on. The shim shadows the real header through the
# generated include directory, which is searched first. It defines no function whose
# behaviour is under comparison; the kernel's own gcd.c is what gets compiled.
KERNEL_JUMP_LABEL_SHIM = (
    '/* autoform: <linux/jump_label.h> for a portable-userspace build. A static key\n'
    ' * reads as its initial value; nothing here can toggle one (no jump labels). */\n'
    '#pragma once\n'
    'struct static_key_true { int enabled; };\n'
    'struct static_key_false { int enabled; };\n'
    '#define DECLARE_STATIC_KEY_TRUE(name) extern struct static_key_true name\n'
    '#define DECLARE_STATIC_KEY_FALSE(name) extern struct static_key_false name\n'
    '#define DEFINE_STATIC_KEY_TRUE(name) struct static_key_true name = { 1 }\n'
    '#define DEFINE_STATIC_KEY_FALSE(name) struct static_key_false name = { 0 }\n'
    '#define DEFINE_STATIC_KEY_TRUE_RO(name) DEFINE_STATIC_KEY_TRUE(name)\n'
    '#define DEFINE_STATIC_KEY_FALSE_RO(name) DEFINE_STATIC_KEY_FALSE(name)\n'
    '#define static_branch_likely(key) (!!(key)->enabled)\n'
    '#define static_branch_unlikely(key) (!!(key)->enabled)\n'
    '#define static_branch_maybe(config, key) (!!(key)->enabled)\n'
    '#define static_key_enabled(key) (!!(key)->enabled)\n')


def native_flags(context, work):
    """Use unchanged kernel tools headers, with generated asm include redirects."""
    flags = ['-D' + d for d in context['defines']]
    root = context.get('kernel_root')
    if root:
        root = Path(root)
        headers = Path(work) / 'kernel-include' / 'asm'
        headers.mkdir(parents=True, exist_ok=True)
        for name in ('types', 'posix_types', 'bitsperlong', 'errno'):
            (headers / (name + '.h')).write_text('#include <asm-generic/' + name + '.h>\n')
        # `tools/include/linux/kernel.h` includes glibc's <endian.h> and <byteswap.h>.
        # A host without them (macOS) could not compile ANY unit that reaches
        # kernel.h, which on lib/math left only int_pow.c observable. Defer to the
        # host's header when it exists; otherwise supply the three macros and the
        # byte-swap builtins those two headers are used for.
        for name, body in HOST_HEADER_SHIMS.items():
            (headers.parent / name).write_text(body)
        # The real include/linux/kernel.h reaches minmax.h, so kernel sources call
        # `swap()` after including only <linux/kernel.h>; the tools copy used here does
        # not, and such a unit failed to compile. Force-include the kernel's own
        # definition, guarded so a later minmax.h keeps its body.
        compat = headers.parent / 'autoform-kernel-compat.h'
        compat.write_text(KERNEL_COMPAT_HEADER)
        flags += ['-include', str(compat)]
        # <linux/gcd.h> includes <linux/jump_label.h>; see KERNEL_JUMP_LABEL_SHIM.
        (headers.parent / 'linux').mkdir(exist_ok=True)
        (headers.parent / 'linux' / 'jump_label.h').write_text(KERNEL_JUMP_LABEL_SHIM)
        # Native compilation resolves attributes via the actual headers. Parser-only
        # attribute substitutions must not override compiler semantics/linkage.
        flags = [f for f in flags if f[2:].split('=', 1)[0] not in KERNEL_ATTRIBUTES]
        for path in (headers.parent, root / 'tools/include', root / 'include/uapi', root / 'include'):
            flags += ['-I', str(path)]
    return flags


def oversized(source, limit):
    """Supported source files above ``limit`` bytes, in the inventory's terms.

    Joern is told to skip each one by absolute path. Its ``--exclude`` option splits
    on commas, so a path containing one cannot be named to it; that file is recorded
    as over the cap but still parsed, never dropped silently from either side.
    """
    if not limit:
        return []
    extensions = {e for adapter in repository_inventory.ADAPTERS.values() for e in adapter['extensions']}
    root, found = os.path.abspath(source), []
    for directory, names, files in os.walk(root):
        names[:] = sorted(n for n in names if n not in repository_inventory._VCS_NAMES)
        for name in sorted(files):
            path = os.path.join(directory, name)
            try:
                info = os.lstat(path)
            except OSError:
                continue
            if os.path.splitext(name)[1] in extensions and stat.S_ISREG(info.st_mode) \
                    and info.st_size > limit:
                found.append(dict(path=Path(os.path.relpath(path, root)).as_posix(),
                                  bytes=info.st_size, reason='max_file_bytes',
                                  frontend_excluded=',' not in path))
    return found


def context(source):
    """The frontend context for ``source``: `profile`'s preprocessor configuration,
    the AUTOFORM_LANGUAGE partition, the over-cap files (`oversized`) and the JVM
    delombok mode, with the assembled ``frontend_args`` -- the exact `--frontend-args`
    list for this tree (the `--language` of a forced AUTOFORM_FRONTEND is a separate
    argument the callers pass alongside it). `main()` writes it for `autoform.sh`;
    pr mode's export (scripts/pr_mode.py) passes it directly, so a pull request's
    head and base trees are parsed exactly as the pipeline parses them, and no
    caller can drift from the others. Over-cap files are reported on stderr whatever
    the caller. Raises ValueError when AUTOFORM_MAX_FILE_BYTES is not a number or
    the compilation database does not exist."""
    ctx = profile(source)
    language = os.environ.get('AUTOFORM_LANGUAGE')
    if language:
        ctx['language'] = language
        ctx['frontend'] = os.environ.get('AUTOFORM_FRONTEND')
        if language != 'c':
            ctx['frontend_args'] = []
    limit = repository_inventory.max_file_bytes()
    ctx['max_file_bytes'] = limit or None
    ctx['excluded_files'] = oversized(source, limit)
    if not language or language == 'java':
        jvm = jvm_frontend_args(source)
        if jvm:
            ctx['delombok_mode'] = jvm[1]
            ctx['frontend_args'] = (ctx['frontend_args'] or ['--frontend-args']) + jvm
    skip = [arg for entry in ctx['excluded_files'] if entry['frontend_excluded']
            for arg in ('--exclude', os.path.join(os.path.abspath(source), entry['path']))]
    if skip:
        ctx['frontend_args'] = (ctx['frontend_args'] or ['--frontend-args']) + skip
    for entry in ctx['excluded_files']:
        print('autoform: %s is %d bytes, over the %d-byte cap (AUTOFORM_MAX_FILE_BYTES); %s'
              % (entry['path'], entry['bytes'], limit, 'excluded from the frontend'
                 if entry['frontend_excluded'] else 'cannot be excluded (comma in path)'),
              file=sys.stderr)
    return ctx


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('source')
    p.add_argument('output')
    p.add_argument('--args-file', required=True)
    a = p.parse_args()
    try:
        ctx = context(a.source)
    except ValueError as exc:
        sys.exit('source_context: ' + str(exc))
    Path(a.output).write_text(json.dumps(ctx, indent=2) + '\n')
    Path(a.args_file).write_bytes(b''.join(s.encode() + b'\0' for s in ctx['frontend_args']))


if __name__ == '__main__':
    main()
