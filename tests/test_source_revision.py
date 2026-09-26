"""Corpus identities must describe the supplied tree, including ignored fixtures."""
from pathlib import Path
import subprocess
import sys
import types

import pytest

from conftest import SCRIPTS, load


@pytest.fixture
def repository(tmp_path):
    def git(*args):
        return subprocess.check_output(['git', '-C', str(tmp_path), *args], text=True).strip()
    git('init', '-q')
    (tmp_path / 'pkg').mkdir()
    (tmp_path / 'pkg' / 'source.py').write_text('value = 1\n')
    (tmp_path / '.gitignore').write_text('fixtures/\npkg/ignored.py\n__pycache__/\n')
    git('add', '.')
    git('-c', 'user.name=Source identity test', '-c', 'user.email=source@example.invalid',
        '-c', 'commit.gpgsign=false', 'commit', '-qm', 'Source snapshot')
    return tmp_path, git('rev-parse', 'HEAD')


def provenance():
    return load(str(Path(SCRIPTS) / 'provenance.py'), 'source_identity_provenance')


def test_clean_tracked_subtree_keeps_commit(repository, differential):
    root, revision = repository
    source = root / 'pkg'
    (root / 'unrelated.txt').write_text('outside the supplied source tree')
    assert provenance().source_revision(source) == 'git:' + revision
    assert differential._corpus_commit(str(source)) == revision


@pytest.mark.parametrize('folder', ['fixtures', 'untracked'])
def test_untracked_nested_source_does_not_borrow_parent_commit(repository, differential, folder):
    root, revision = repository
    source = root / folder
    source.mkdir()
    (source / 'source.py').write_text('value = 7\n')
    identity = provenance().source_revision(source)
    assert identity.startswith('tree-sha256:')
    assert revision not in identity
    assert differential._corpus_commit(str(source)) == identity
    (source / 'source.py').write_text('value = 8\n')
    assert provenance().source_revision(source) != identity


@pytest.mark.parametrize('change', ['modified', 'untracked', 'ignored', 'staged'])
def test_changed_source_uses_content_identity(repository, differential, change):
    root, _ = repository
    source = root / 'pkg'
    name = 'ignored.py' if change == 'ignored' else 'extra\nfile.py' if change == 'untracked' else 'source.py'
    (source / name).write_text('value = 9\n')
    if change == 'staged':
        subprocess.run(['git', '-C', str(root), 'add', '.'], check=True)
    identity = provenance().source_revision(source)
    assert identity.startswith('tree-sha256:')
    assert differential._corpus_commit(str(source)) == identity
    (source / name).write_text('value = 10\n')
    assert provenance().source_revision(source) != identity


def test_ignored_runtime_cache_does_not_change_identity(repository):
    root, revision = repository
    cache = root / 'pkg' / '__pycache__'
    cache.mkdir()
    (cache / 'source.pyc').write_bytes(b'cache')
    assert provenance().source_revision(root / 'pkg') == 'git:' + revision


def test_missing_source_is_not_an_empty_tree(tmp_path, differential):
    missing = tmp_path / 'missing'
    with pytest.raises(FileNotFoundError, match='source root'):
        provenance().source_revision(missing)
    assert differential._corpus_commit(str(missing)).startswith('unavailable: FileNotFoundError')


def test_native_report_does_not_load_a_corpus_helper(repository, differential, monkeypatch):
    root, revision = repository
    corpus_module = types.SimpleNamespace(source_revision=lambda _: 'git:wrong-repository')
    monkeypatch.setitem(sys.modules, 'provenance', corpus_module)
    assert differential._corpus_commit(str(root / 'pkg')) == revision
    assert sys.modules['provenance'] is corpus_module
