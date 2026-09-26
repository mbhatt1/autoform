"""Modular compiler changes must invalidate evidence, including dependency-only edits."""
import hashlib
import json
from pathlib import Path
import sys

import pytest

from test_reland_scope import check_provenance, provenance_tree

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from compiler_sources import source_files


def fingerprint(root, entry):
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in source_files(entry)}


def modular_record(root, directive='//> using file '):
    provenance_tree(root)
    entry = root / 'export.sc'
    unit = root / 'compiler' / 'Lowering.scala'
    unit.parent.mkdir()
    unit.write_text('object Lowering { val answer = 1 }\n')
    entry.write_text(directive + 'compiler/Lowering.scala\n@main def run() = ()\n')
    record_path = root / 'provenance/ast-Fresh.json.prov.json'
    record = json.loads(record_path.read_text())
    record['exporter_sha256'] = hashlib.sha256(entry.read_bytes()).hexdigest()
    record['exporter_sources'] = fingerprint(root, entry)
    record_path.write_text(json.dumps(record))
    return unit, record_path


@pytest.mark.parametrize('directive', ['//> using file ', '//> using file\t',
                                       '  //> using file   '])
def test_dependency_only_edit_invalidates_provenance(tmp_path, directive):
    unit, _ = modular_record(tmp_path, directive)
    check = lambda: check_provenance(tmp_path, '--artifact', 'ast-Fresh.json')
    initial = check()
    assert initial.returncode == 0, initial.stderr
    unit.write_text('object Lowering { val answer = 2 }\n')
    changed = check()
    assert changed.returncode == 1
    assert 'exporter source dependencies changed' in changed.stderr
    assert 'export.sc changed since' not in changed.stderr


def test_multi_file_exporter_requires_dependency_record(tmp_path):
    _, path = modular_record(tmp_path)
    record = json.loads(path.read_text())
    del record['exporter_sources']
    path.write_text(json.dumps(record))
    result = check_provenance(tmp_path, '--artifact', 'ast-Fresh.json')
    assert result.returncode == 1
    assert 'has no exporter_sources' in result.stderr


def test_missing_compile_unit_is_not_partial_evidence(tmp_path):
    unit, _ = modular_record(tmp_path)
    unit.unlink()
    result = check_provenance(tmp_path, '--artifact', 'ast-Fresh.json')
    assert result.returncode == 1
    assert 'cannot read exporter source dependencies' in result.stderr


def test_transitive_imports_resolve_from_each_importer_and_terminate(tmp_path):
    entry = tmp_path / 'main.sc'
    folder = tmp_path / 'units with spaces'
    folder.mkdir()
    child, leaf = folder / 'Child.scala', folder / 'Leaf.scala'
    entry.write_text('//> using file units with spaces/Child.scala\n')
    child.write_text('//> using file Leaf.scala\n//> using file ../main.sc\n')
    leaf.write_text('object Leaf {}\n')
    assert source_files(entry) == [entry, child, leaf]
    leaf.unlink()
    with pytest.raises(FileNotFoundError):
        source_files(entry)


def test_file_symlink_preserves_distinct_relative_import_bases(tmp_path):
    real, alias = tmp_path / 'real', tmp_path / 'alias'
    real.mkdir()
    alias.mkdir()
    entry = tmp_path / 'main.sc'
    entry.write_text('//> using file real/Imports.scala\n//> using file alias/Imports.scala\n')
    (real / 'Imports.scala').write_text('//> using file Leaf.scala\n')
    (alias / 'Imports.scala').symlink_to(real / 'Imports.scala')
    (real / 'Leaf.scala').write_text('object RealLeaf {}\n')
    leaf = alias / 'Leaf.scala'
    leaf.write_text('object AliasLeaf {}\n')
    before = fingerprint(tmp_path, entry)
    assert 'real/Leaf.scala' in before and 'alias/Leaf.scala' in before
    leaf.write_text('object AliasLeaf { val changed = true }\n')
    assert fingerprint(tmp_path, entry) != before
