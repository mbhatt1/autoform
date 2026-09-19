"""Unsupported and unreadable repository content must remain visible."""
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys

import pytest

from conftest import SCRIPTS, load


@pytest.fixture
def inventory():
    return load(str(Path(SCRIPTS) / "repository_inventory.py"), "af_repository_inventory_test")


def populate(root, files):
    for relative, content in files.items():
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)


def test_mixed_repository_is_complete_without_claiming_scala_support(tmp_path, inventory):
    populate(tmp_path, {"core/A.scala": "object A {}", "java/B.java": "class B {}",
                        "python/a.py": "def f(): return 1", "README.md": "docs",
                        "module.surprise": "opaque", "vendor/a.py": "third party"})
    report = inventory.discover(tmp_path)
    assert report["scan_complete"] and report["errors"] == []
    assert report["source"] == str(tmp_path)
    assert report["languages"]["scala"] == {
        "supported": False, "frontend": None, "files": ["core/A.scala"],
        "supported_files": [], "unsupported_files": ["core/A.scala"], "extensions": [".scala"]}
    assert report["languages"]["python"]["supported_files"] == ["python/a.py", "vendor/a.py"]
    assert report["languages"]["java"]["frontend"] == "JAVASRC"
    assert report["counts"]["source_files"] == 4
    assert report["counts"]["supported_source_files"] == 3
    assert report["counts"]["unclassified_files"] == 1
    assert report["counts"]["hashed_files"] == 6
    assert all(record["sha256"] == hashlib.sha256((tmp_path / record["path"]).read_bytes()).hexdigest()
               for record in report["files"])
    assert [f["path"] for f in report["files"]] == sorted(f["path"] for f in report["files"])


def test_unsupported_only_repository_retains_every_source(tmp_path, inventory):
    populate(tmp_path, {"a.scala": "", "b.R": "", "c.rs": "", "d.cs": "", "e.swift": "",
                        "f.rb": "", "g.php": "", "h.sh": "", "i.sql": "", "j.ipynb": "{}"})
    report = inventory.discover(tmp_path)
    assert report["scan_complete"]
    assert report["counts"]["unsupported_source_files"] == 10
    assert report["counts"]["supported_source_files"] == 0
    assert all(not language["supported"] for language in report["languages"].values())
    assert set(report["languages"]) == {"scala", "r", "rust", "csharp", "swift", "ruby", "php", "shell", "sql", "notebook"}


def test_adapter_registry_is_exact_renderer_native_intersection(inventory, render_lean, differential):
    actual = {ext: lang for lang, adapter in inventory.ADAPTERS.items() for ext in adapter["extensions"]}
    expected = {ext: lang for ext, lang in differential.LANG_BY_EXT.items() if ext in render_lean.DIALECT}
    assert actual == expected
    assert set(inventory.ADAPTERS) == {"python", "c", "java", "go", "js", "ts", "kotlin"}


def test_partial_language_coverage_and_extension_case_are_explicit(tmp_path, inventory):
    populate(tmp_path, {"a.py": "", "b.pyi": "", "c.PY": "", "d.kts": "", "e.mts": "",
                        "f.C": "", "g.c": "", "h.unknown": ""})
    report = inventory.discover(tmp_path)
    python = report["languages"]["python"]
    assert python["supported_files"] == ["a.py"]
    assert python["unsupported_files"] == ["b.pyi", "c.PY"]
    assert not python["supported"]
    assert report["languages"]["c"]["supported_files"] == ["g.c"]
    assert report["languages"]["c"]["unsupported_files"] == ["f.C"]
    assert report["languages"]["ts"]["unsupported_files"] == ["e.mts"]
    assert report["counts"]["unclassified_files"] == 1


def test_only_vcs_metadata_and_explicit_subtrees_are_excluded(tmp_path, inventory):
    populate(tmp_path, {".git/config": "secret", "pkg/.hg/data": "secret", ".svn/a": "secret",
                        "build/a.py": "x", "vendor/b.py": "x", "skip/c.py": "x", ".hidden": "x"})
    report = inventory.discover(tmp_path, exclude=[tmp_path / "skip"])
    assert [f["path"] for f in report["files"]] == [".hidden", "build/a.py", "vendor/b.py"]
    assert report["excluded"] == [
        {"path": ".git", "reason": "vcs_metadata"}, {"path": ".svn", "reason": "vcs_metadata"},
        {"path": "pkg/.hg", "reason": "vcs_metadata"}, {"path": "skip", "reason": "caller_excluded"}]
    assert report["scan_complete"]


@pytest.mark.parametrize("excluded", ["..", "a/../b", ".", "/outside-inventory-root"])
def test_invalid_exclusions_are_not_silently_accepted(tmp_path, inventory, excluded):
    (tmp_path / "a.py").write_text("x")
    report = inventory.discover(tmp_path, exclude=[excluded])
    assert not report["scan_complete"]
    assert report["errors"][0]["reason"].startswith("invalid exclusion:")
    assert report["counts"]["files"] == 1


def test_symlinks_and_fifo_are_recorded_without_following_or_blocking(tmp_path, inventory):
    source = tmp_path / "source"
    source.mkdir()
    outside = tmp_path / "outside"
    outside.mkdir()
    (outside / "secret.py").write_text("do not read")
    (source / "directory").symlink_to(outside, target_is_directory=True)
    (source / "link.py").symlink_to(outside / "secret.py")
    (source / "broken.py").symlink_to(outside / "absent")
    os.mkfifo(source / "pipe.py")
    # The subprocess timeout also catches accidental FIFO reads or symlink traversal loops.
    proc = subprocess.run([sys.executable, str(Path(SCRIPTS) / "repository_inventory.py"), str(source)],
                          capture_output=True, text=True, timeout=10)
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["scan_complete"] and report["counts"]["files"] == 4
    assert report["counts"]["hashed_files"] == 0
    assert report["counts"]["supported_source_files"] == 0
    assert report["counts"]["symlinks"] == 3
    assert report["counts"]["special_files"] == 1
    fifo = next(f for f in report["files"] if f["path"] == "pipe.py")
    assert fifo["special_type"] == stat.S_IFIFO
    assert all(f["bytes"] is None and f["sha256"] is None for f in report["files"])


def test_source_symlink_or_missing_source_fails_explicitly(tmp_path, inventory):
    target = tmp_path / "target"
    target.mkdir()
    link = tmp_path / "link"
    link.symlink_to(target, target_is_directory=True)
    for source in (link, tmp_path / "missing"):
        report = inventory.discover(source)
        assert not report["scan_complete"]
        assert report["errors"] and report["files"] == []


def test_failed_file_read_remains_visible(tmp_path, inventory, monkeypatch):
    (tmp_path / "unreadable.py").write_text("x")
    original = inventory.os.open

    def fail_file(path, flags, *args, **kwargs):
        if path == "unreadable.py":
            raise PermissionError(13, "Permission denied")
        return original(path, flags, *args, **kwargs)

    monkeypatch.setattr(inventory.os, "open", fail_file)
    report = inventory.discover(tmp_path)
    assert not report["scan_complete"]
    assert report["files"][0]["sha256"] is None
    assert report["files"][0]["supported"] is False
    assert report["errors"] == [{"path": "unreadable.py", "reason": "cannot hash file: Permission denied"}]


def test_failed_directory_traversal_is_explicit(tmp_path, inventory, monkeypatch):
    populate(tmp_path, {"closed/a.py": "x", "open/b.py": "x"})
    original = inventory.os.listdir
    closed_inode = (tmp_path / "closed").stat().st_ino

    def fail_closed(fd):
        if os.fstat(fd).st_ino == closed_inode:
            raise PermissionError(13, "Permission denied")
        return original(fd)

    monkeypatch.setattr(inventory.os, "listdir", fail_closed)
    report = inventory.discover(tmp_path)
    assert not report["scan_complete"]
    assert report["errors"] == [{"path": "closed", "reason": "cannot list directory: Permission denied"}]
    assert report["files"][0]["path"] == "open/b.py"


def test_file_replaced_by_symlink_before_open_is_not_hashed(tmp_path, inventory, monkeypatch):
    source = tmp_path / "source"
    source.mkdir()
    victim = source / "a.py"
    victim.write_text("safe")
    outside = tmp_path / "secret"
    outside.write_text("secret")
    original = inventory.os.open

    def replace(path, flags, *args, **kwargs):
        if path == "a.py":
            victim.unlink()
            victim.symlink_to(outside)
        return original(path, flags, *args, **kwargs)

    monkeypatch.setattr(inventory.os, "open", replace)
    report = inventory.discover(source)
    assert not report["scan_complete"]
    assert report["files"][0]["sha256"] is None
    assert any(e["path"] == "a.py" and "cannot hash" in e["reason"] for e in report["errors"])


def test_mutation_during_hash_is_an_error(tmp_path, inventory, monkeypatch):
    path = tmp_path / "a.py"
    path.write_text("initial")
    original = inventory.os.read
    mutated = False

    def mutate(fd, size):
        nonlocal mutated
        chunk = original(fd, size)
        if chunk and not mutated:
            mutated = True
            path.write_text("changed while reading")
        return chunk

    monkeypatch.setattr(inventory.os, "read", mutate)
    report = inventory.discover(tmp_path)
    assert not report["scan_complete"]
    assert report["files"][0]["sha256"] is None
    assert {"path": "a.py", "reason": "file changed while hashing"} in report["errors"]


def test_regular_file_replaced_by_fifo_before_open_is_not_read(tmp_path, inventory, monkeypatch):
    victim = tmp_path / "a.py"
    victim.write_text("safe")
    original = inventory.os.open

    def replace(path, flags, *args, **kwargs):
        if path == "a.py":
            assert flags & os.O_NONBLOCK
            victim.unlink()
            os.mkfifo(victim)
        return original(path, flags, *args, **kwargs)

    monkeypatch.setattr(inventory.os, "open", replace)
    report = inventory.discover(tmp_path)
    assert not report["scan_complete"]
    assert report["files"][0]["sha256"] is None
    assert {"path": "a.py", "reason": "file changed before hashing"} in report["errors"]


def test_directory_swapped_for_symlink_cannot_escape_source(tmp_path, inventory, monkeypatch):
    source = tmp_path / "source"
    populate(source, {"nested/a.py": "safe"})
    outside = tmp_path / "outside"
    populate(outside, {"secret.py": "secret"})
    original = inventory.os.open

    def replace(path, flags, *args, **kwargs):
        if path == "nested":
            (source / "nested").rename(source / "moved")
            (source / "nested").symlink_to(outside, target_is_directory=True)
        return original(path, flags, *args, **kwargs)

    monkeypatch.setattr(inventory.os, "open", replace)
    report = inventory.discover(source)
    assert not report["scan_complete"]
    assert report["files"] == []
    assert any(e["path"] == "nested" and "cannot traverse" in e["reason"] for e in report["errors"])


def test_added_directory_entry_during_hash_invalidates_scan(tmp_path, inventory, monkeypatch):
    (tmp_path / "a.py").write_text("initial")
    original = inventory.os.read
    mutated = False

    def add_file(fd, size):
        nonlocal mutated
        chunk = original(fd, size)
        if chunk and not mutated:
            mutated = True
            (tmp_path / "new.py").write_text("new")
        return chunk

    monkeypatch.setattr(inventory.os, "read", add_file)
    report = inventory.discover(tmp_path)
    assert not report["scan_complete"]
    assert {"path": ".", "reason": "directory changed during traversal"} in report["errors"]


def test_changes_include_added_deleted_content_mode_and_symlink_targets(tmp_path, inventory):
    populate(tmp_path, {"delete.py": "old", "change.py": "old", "mode.py": "same"})
    (tmp_path / "link").symlink_to("before")
    before = inventory.discover(tmp_path)
    (tmp_path / "delete.py").unlink()
    (tmp_path / "change.py").write_text("new")
    (tmp_path / "added.py").write_text("new")
    (tmp_path / "mode.py").chmod(0o700)
    (tmp_path / "link").unlink()
    (tmp_path / "link").symlink_to("after")
    after = inventory.discover(tmp_path)
    assert inventory.changed(before, after) == [
        {"path": "added.py", "reason": "added"}, {"path": "change.py", "reason": "changed"},
        {"path": "delete.py", "reason": "deleted"}, {"path": "link", "reason": "changed"},
        {"path": "mode.py", "reason": "changed"}]
    assert before["fingerprint"] != after["fingerprint"]


def test_fingerprint_is_deterministic_and_location_independent(tmp_path, inventory):
    first = tmp_path / "first"
    second = tmp_path / "second"
    populate(first, {"a.py": "content", "b.json": "{}"})
    populate(second, {"b.json": "{}", "a.py": "content"})
    a, b = inventory.discover(first), inventory.discover(second)
    assert a["fingerprint"] == b["fingerprint"]
    assert a["fingerprint"] == inventory.discover(first)["fingerprint"]
    assert inventory.changed(a, b) == []
    assert len(a["fingerprint"]) == 64


def test_changed_includes_exclusions_and_errors_even_without_file_changes(tmp_path, inventory):
    (tmp_path / ".git").mkdir()
    before = inventory.discover(tmp_path)
    (tmp_path / ".git").rmdir()
    after = inventory.discover(tmp_path)
    assert inventory.changed(before, after) == [{"path": ".git", "reason": "excluded removed: vcs_metadata"}]
    failed = dict(after, scan_complete=False, errors=[{"path": "lost", "reason": "permission"}])
    assert inventory.changed(after, failed) == [
        {"path": ".", "reason": "scan completeness changed"},
        {"path": "lost", "reason": "errors added: permission"}]


def test_cli_writes_report_and_failure_exit_code(tmp_path):
    output = tmp_path / "reports" / "inventory.json"
    proc = subprocess.run([sys.executable, str(Path(SCRIPTS) / "repository_inventory.py"),
                           str(tmp_path / "absent"), "--output", str(output)],
                          capture_output=True, text=True, timeout=10)
    assert proc.returncode == 2
    assert json.loads(output.read_text())["scan_complete"] is False
