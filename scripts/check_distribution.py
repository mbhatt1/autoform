#!/usr/bin/env python3
"""Check the actual wheel and sdist against this checkout; never installs or publishes."""
from __future__ import annotations

import argparse
import ast
import base64
import configparser
import csv
from email.parser import BytesParser
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import stat
import sys
import tarfile
import zipfile

try:
    import tomllib
except ModuleNotFoundError:  # Python 3.10; declared in the test extra.
    import tomli as tomllib

from packaging.markers import Marker
from packaging.requirements import Requirement
from packaging.specifiers import SpecifierSet
from packaging.utils import canonicalize_name

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from build_support import runtime_files, source_files
from scripts.compiler_sources import source_files as compiler_sources


def require(condition, message):
    if not condition:
        raise ValueError(message)


def safe_name(name):
    path = PurePosixPath(name)
    require(bool(name) and not path.is_absolute() and '\\' not in name and
            '\x00' not in name and '..' not in path.parts and
            path.as_posix() == name, 'unsafe archive path: ' + repr(name))


def zip_files(archive, label):
    names = archive.namelist()
    require(len(names) == len(set(names)), 'duplicate ' + label + ' entries')
    for entry in archive.infolist():
        safe_name(entry.filename)
        require(stat.S_IFMT(entry.external_attr >> 16) in (0, stat.S_IFREG) and
                not entry.is_dir(), label + ' contains a link or non-file entry')
    return set(names)


def check_record(archive, prefix):
    """Validate installed-file hashes as well as the bytes we know by source path."""
    record = prefix + 'RECORD'
    rows = list(csv.reader(io.StringIO(archive.read(record).decode('utf-8'))))
    require(all(len(row) == 3 for row in rows), 'malformed wheel RECORD')
    require(len(rows) == len({row[0] for row in rows}) and
            {row[0] for row in rows} == set(archive.namelist()),
            'wheel RECORD file set differs from archive')
    for name, digest, size in rows:
        if name == record:
            require(not digest and not size, 'wheel RECORD must not hash itself')
            continue
        content = archive.read(name)
        expected = base64.urlsafe_b64encode(hashlib.sha256(content).digest()).decode().rstrip('=')
        require(digest == 'sha256=' + expected and size == str(len(content)),
                'wheel RECORD mismatch: ' + name)


def check_entry_points(content):
    parser = configparser.ConfigParser(interpolation=None)
    parser.read_string(content.decode('utf-8'))
    require(not parser.defaults() and parser.sections() == ['console_scripts'] and
            dict(parser['console_scripts']) == {'autoform': 'autoform.cli:main'},
            'incorrect CLI entry points')


def dependency_contract(project):
    """Derive wheel and egg dependency contracts from the checked-out TOML."""
    require(not {'dependencies', 'optional-dependencies', 'requires-python'} &
            set(project.get('dynamic', [])), 'dynamic dependency metadata is unsupported')
    dependencies = set()
    sections = {('', ''): set()}
    groups = [('', project.get('dependencies', []))]
    groups.extend((canonicalize_name(extra), values) for extra, values in
                  project.get('optional-dependencies', {}).items())
    for extra, values in groups:
        sections.setdefault((extra, ''), set())
        for value in values:
            dependency = Requirement(value)
            marker = str(dependency.marker) if dependency.marker else ''
            plain = Requirement(value)
            plain.marker = None
            sections.setdefault((extra, marker), set()).add(plain)
            if extra:
                condition = f'extra == "{extra}"'
                dependency.marker = Marker(f'({marker}) and {condition}' if marker else condition)
            dependencies.add(dependency)
    return dependencies, sections


def check_dependency_metadata(metadata, project):
    require(metadata.get_all('Requires-Python') is not None and
            len(metadata.get_all('Requires-Python')) == 1 and
            SpecifierSet(metadata['Requires-Python']) == SpecifierSet(project['requires-python']),
            'Requires-Python differs from pyproject.toml')
    expected, _ = dependency_contract(project)
    actual = [Requirement(value) for value in metadata.get_all('Requires-Dist', [])]
    require(len(actual) == len(set(actual)) and set(actual) == expected,
            'Requires-Dist differs from pyproject.toml')
    extras = [canonicalize_name(value) for value in metadata.get_all('Provides-Extra', [])]
    require(len(extras) == len(set(extras)) and set(extras) ==
            {canonicalize_name(extra) for extra in project.get('optional-dependencies', {})},
            'Provides-Extra differs from pyproject.toml')


def check_egg_dependencies(content, project):
    # Egg requires.txt stores environment markers in [extra:marker] section
    # headers, with marker-free PEP 508 requirements beneath each header.
    # Parse requirements and markers with packaging, not string approximations.
    section = ('', '')
    sections = {section: set()}
    for raw_line in content.decode('utf-8').splitlines():
        line = raw_line.strip()
        if not line:
            continue
        if line.startswith('[') and line.endswith(']'):
            extra, separator, marker = line[1:-1].partition(':')
            require(bool(extra) or bool(separator and marker), 'empty requires.txt section')
            section = (canonicalize_name(extra), str(Marker(marker)) if separator else '')
            require(section not in sections, 'duplicate requires.txt section')
            sections[section] = set()
        else:
            dependency = Requirement(line)
            require(dependency.marker is None and dependency not in sections[section],
                    'invalid or duplicate requires.txt requirement')
            sections[section].add(dependency)
    _, expected = dependency_contract(project)
    require(sections == expected, 'requires.txt differs from pyproject.toml')


def check_compiler_sources(root, resources):
    """Check compile units independently of the builder's filename selection."""
    root = Path(root).resolve()
    for entry in sorted((root / 'cartographer').rglob('*.sc')):
        for source in compiler_sources(entry):
            name = source.resolve().relative_to(root).as_posix()
            require(name in resources, 'compiler source missing from runtime: ' + name)


def check(wheel, sdist, root=ROOT):
    wheel, sdist, root = Path(wheel), Path(sdist), Path(root)
    expected = runtime_files(root)
    check_compiler_sources(root, expected)
    project = tomllib.loads((root / 'pyproject.toml').read_text(encoding='utf-8'))['project']
    with zipfile.ZipFile(wheel) as archive:
        names = zip_files(archive, 'wheel')
        metadata_names = [n for n in archive.namelist() if n.endswith('.dist-info/METADATA')]
        require(len(metadata_names) == 1, 'expected one wheel metadata record')
        metadata_bytes = archive.read(metadata_names[0])
        metadata = BytesParser().parsebytes(metadata_bytes)
        check_dependency_metadata(metadata, project)
        require(metadata['Name'] == 'autoform-lean', 'wrong distribution name')
        require(metadata['License-Expression'] == 'Apache-2.0 AND MIT', 'missing distribution license expression')
        package = {p.name: p.read_bytes() for p in (root / 'src/autoform').glob('*.py')}
        for name, content in package.items():
            require(archive.read('autoform/' + name) == content, 'stale CLI source: ' + name)
        version = next(ast.literal_eval(node.value) for node in ast.parse(
            package['__init__.py']).body if isinstance(node, ast.Assign) and
            any(isinstance(t, ast.Name) and t.id == '__version__' for t in node.targets))
        require(metadata['Version'] == version, 'CLI and distribution versions disagree')
        require(wheel.name == f'autoform_lean-{version}-py3-none-any.whl', 'wheel filename mismatch')
        require(sdist.name == f'autoform_lean-{version}.tar.gz', 'sdist filename mismatch')
        metadata_prefix = f'autoform_lean-{version}.dist-info/'
        require(metadata_names[0] == metadata_prefix + 'METADATA', 'wheel metadata directory mismatch')
        notice_paths = ['LICENSE', 'NOTICE', *sorted(
            p.relative_to(root).as_posix() for p in (root / 'licenses').glob('*.txt'))]
        require(sorted(metadata.get_all('License-File', [])) == sorted(notice_paths),
                'missing or unexpected License-File records')
        prefix = metadata_prefix + 'licenses/'
        for name in notice_paths:
            require(archive.read(prefix + name) == (root / name).read_bytes(), 'stale notice: ' + name)
        expected_names = {'autoform/' + name for name in package} | {'autoform/runtime.zip'}
        expected_names.update(metadata_prefix + name for name in
                              ('METADATA', 'WHEEL', 'entry_points.txt', 'top_level.txt', 'RECORD'))
        expected_names.update(prefix + name for name in notice_paths)
        require(names == expected_names, 'wheel file set differs from declared package')
        wheel_metadata = BytesParser().parsebytes(archive.read(metadata_prefix + 'WHEEL'))
        require(wheel_metadata['Wheel-Version'] == '1.0' and
                wheel_metadata['Root-Is-Purelib'] == 'true' and
                wheel_metadata.get_all('Tag') == ['py3-none-any'], 'unsupported wheel layout or tags')
        entry_points = archive.read(metadata_prefix + 'entry_points.txt')
        check_entry_points(entry_points)
        require(archive.read(metadata_prefix + 'top_level.txt') == b'autoform\n',
                'unexpected top-level package metadata')
        check_record(archive, metadata_prefix)
        with zipfile.ZipFile(io.BytesIO(archive.read('autoform/runtime.zip'))) as runtime:
            require(zip_files(runtime, 'runtime') == set(expected), 'runtime archive file set differs from checkout')
            for name, content in expected.items():
                require(runtime.read(name) == content, 'stale runtime resource: ' + name)
    with tarfile.open(sdist, 'r:gz') as archive:
        members = archive.getmembers()
        require(len(members) == len({m.name for m in members}), 'duplicate sdist entries')
        require(all(m.isfile() or m.isdir() for m in members), 'sdist contains a link or special file')
        for member in members:
            safe_name(member.name)
        roots = {m.name.split('/')[0] for m in members}
        require(len(roots) == 1, 'sdist must contain one root')
        prefix = roots.pop() + '/'
        require(prefix == f'autoform_lean-{version}/', 'sdist root directory mismatch')
        files = {m.name[len(prefix):]: archive.extractfile(m).read() for m in members if m.isfile()}
        source = source_files(root)
        egg_info = 'src/autoform_lean.egg-info/'
        generated = {'PKG-INFO', 'setup.cfg'} | {egg_info + name for name in
                     ('PKG-INFO', 'SOURCES.txt', 'dependency_links.txt', 'entry_points.txt',
                      'requires.txt', 'top_level.txt')}
        require(set(files) == set(source) | generated, 'sdist file set differs from declared source')
        for name, content in source.items():
            require(files[name] == content, 'missing/stale sdist source: ' + name)
        require(files['PKG-INFO'] == metadata_bytes == files[egg_info + 'PKG-INFO'],
                'wheel and sdist metadata disagree')
        require(files['setup.cfg'] == b'[egg_info]\ntag_build = \ntag_date = 0\n\n',
                'unexpected generated setup configuration')
        require(files[egg_info + 'entry_points.txt'] == entry_points and
                files[egg_info + 'top_level.txt'] == b'autoform\n' and
                files[egg_info + 'dependency_links.txt'] == b'\n', 'unexpected sdist package metadata')
        check_egg_dependencies(files[egg_info + 'requires.txt'], project)
        inventory = files[egg_info + 'SOURCES.txt'].decode('utf-8').splitlines()
        require(len(inventory) == len(set(inventory)) and
                set(inventory) == set(files) - {'PKG-INFO', 'setup.cfg'}, 'stale sdist source inventory')
    return dict(status='passed', version=version, runtime_files=len(expected),
                artifacts={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in (wheel, sdist)})


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('dist', type=Path)
    args = parser.parse_args(argv)
    try:
        wheels, sdists = list(args.dist.glob('*.whl')), list(args.dist.glob('*.tar.gz'))
        require(len(wheels) == len(sdists) == 1, 'use a directory containing exactly one wheel and one sdist')
        print(json.dumps(check(wheels[0], sdists[0]), indent=2))
        return 0
    except (OSError, ValueError, KeyError, StopIteration, configparser.Error, csv.Error,
            tarfile.TarError, zipfile.BadZipFile) as error:
        print('distribution check failed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
