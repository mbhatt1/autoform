"""Bind replay evidence to the source, compiled modules and reports it checked."""
import hashlib
import os
from pathlib import Path


CONFIG = ('lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json')


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def key(root, path):
    # Keep symlink components: retargeting a package directory must invalidate the
    # snapshot even if the former target is still present on disk.
    return os.path.relpath(os.path.abspath(path), os.path.abspath(root))


def project_sources(root):
    root = Path(root)
    paths = [root / name for name in CONFIG] + [root / 'Autoform.lean']
    paths += sorted((root / 'Autoform').rglob('*.lean'))
    return {key(root, p): digest(p) if p.is_file() else None for p in paths}


def snapshot(root, modules, before, evidence=()):
    root = Path(root)
    paths = {root / name: False for name in CONFIG}
    for item in modules:
        name, compiled = item['name'], Path(item['olean'])
        if not compiled.is_absolute():
            compiled = root / compiled
        paths[compiled] = True
        # Lean 4.30 can load proof bodies from these additional parts. Record
        # absence too, so adding a previously absent part invalidates the audit.
        for suffix in ('.server', '.private'):
            paths[Path(str(compiled) + suffix)] = False
        if name == 'Autoform' or name.startswith('Autoform.'):
            source = root / (name.replace('.', '/') + '.lean')
            expected = root / '.lake/build/lib/lean' / (name.replace('.', '/') + '.olean')
            if compiled.resolve() != expected.resolve():
                raise ValueError('local module resolves outside its build directory: ' + name)
            paths[source] = True
            if key(root, source) not in before or before[key(root, source)] != digest(source):
                raise ValueError('source changed during build: ' + str(source))
    for name in CONFIG:
        p = root / name
        if before.get(name) != (digest(p) if p.is_file() else None):
            raise ValueError('build configuration changed: ' + name)
    for p in evidence:
        p = Path(p)
        paths[p if p.is_absolute() else root / p] = True
    result = {}
    for path, required in paths.items():
        if required and not path.is_file():
            raise ValueError('required audit artifact missing: ' + str(path))
        result[key(root, path)] = digest(path) if path.is_file() else None
    if not modules:
        raise ValueError('audit import inventory is empty')
    return dict(sorted(result.items()))


def changed(root, files):
    if not isinstance(files, dict) or not files:
        return ['artifact snapshot missing']
    mismatches = []
    for name, expected in files.items():
        if not isinstance(name, str) or not (expected is None or
                isinstance(expected, str) and len(expected) == 64):
            mismatches.append('invalid artifact snapshot entry')
            continue
        path = Path(root) / name
        try:
            actual = digest(path) if path.is_file() else None
        except OSError:
            actual = 'unreadable'
        if actual != expected:
            mismatches.append(name)
    return mismatches


def replay_current(root, snapshot, module):
    """Whether a stored replay still describes this module's source and binary."""
    if not isinstance(root, (str, Path)) or not isinstance(snapshot, dict):
        return False
    files = snapshot.get('files')
    if snapshot.get('status') != 'STABLE' or not isinstance(files, dict):
        return False
    name = module.replace('.', '/')
    required = (name + '.lean', '.lake/build/lib/lean/' + name + '.olean')
    return all(isinstance(files.get(p), str) for p in required) and not changed(root, files)
