"""Source-root and qualified-name resolution (`scripts/differential.py`).

`resolve_src_root` is the reason the conformance harness finds any test cases at all.
Pointed at a repository root when the AST's paths are relative to `src/`, it used to
resolve nothing and the harness reported *zero compared cases* — a green run that had
compared nothing, which is the failure mode this whole suite exists to make loud.

`differential.py` is owned by another workstream; nothing here modifies it.
"""
from __future__ import annotations

import io
import os
import sys

import pytest


@pytest.fixture
def R(differential):
    if not hasattr(differential, "resolve_src_root"):
        pytest.fail("scripts/differential.py no longer exports resolve_src_root; "
                    "re-point this test rather than deleting it — it guards the "
                    "'0 compared cases' failure")
    return differential.resolve_src_root


def tree(root, *rels):
    for r in rels:
        p = os.path.join(root, r)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        open(p, "w").write("x = 1\n")
    return root


class TestResolveSrcRoot:
    def test_already_correct_root_is_left_alone(self, R, tmp_path):
        root = tree(str(tmp_path), "pkg/a.py", "pkg/b.py")
        assert R(root, ["pkg/a.py", "pkg/b.py"]) == os.path.abspath(root)

    def test_the_src_layout_is_corrected(self, R, tmp_path, capsys):
        """Joern's paths are relative to the parsed directory; the natural thing to do
        is point the harness at the repo root, and that used to yield nothing."""
        root = tree(str(tmp_path), "src/pkg/a.py", "src/pkg/b.py", "tests/test_a.py")
        got = R(root, ["pkg/a.py", "pkg/b.py"])
        assert got == os.path.abspath(os.path.join(root, "src"))

    def test_the_correction_is_announced(self, R, tmp_path, capsys):
        """A silent correction is a correction nobody can audit."""
        root = tree(str(tmp_path), "src/pkg/a.py")
        R(root, ["pkg/a.py"])
        assert "source root corrected" in capsys.readouterr().out

    def test_a_non_src_layout_is_found_by_scan(self, R, tmp_path):
        root = tree(str(tmp_path), "mylib/pkg/a.py", "mylib/pkg/b.py")
        assert R(root, ["pkg/a.py", "pkg/b.py"]) == \
            os.path.abspath(os.path.join(root, "mylib"))

    def test_the_best_candidate_wins_not_the_first(self, R, tmp_path):
        root = tree(str(tmp_path), "src/pkg/a.py",
                    "lib/pkg/a.py", "lib/pkg/b.py", "lib/pkg/c.py")
        assert R(root, ["pkg/a.py", "pkg/b.py", "pkg/c.py"]) == \
            os.path.abspath(os.path.join(root, "lib"))

    def test_hidden_directories_are_not_searched(self, R, tmp_path):
        """`.git`, `.venv` and friends contain copies of everything; matching there
        would silently point the harness at vendored source."""
        root = tree(str(tmp_path), ".venv/pkg/a.py")
        assert R(root, ["pkg/a.py"]) == os.path.abspath(root)

    def test_no_relative_paths_means_no_correction(self, R, tmp_path):
        root = str(tmp_path)
        assert R(root, []) == root
        assert R(root, ["", None]) == root

    def test_nothing_resolves_anywhere_leaves_the_root_unchanged(self, R, tmp_path):
        """It must not invent a directory. Returning the given root means the caller's
        own 'none of the AST's source files resolve there' message fires."""
        root = tree(str(tmp_path), "src/other.py")
        assert R(root, ["pkg/a.py"]) == os.path.abspath(root)

    def test_an_unreadable_root_does_not_crash(self, R, tmp_path):
        missing = str(tmp_path / "does-not-exist")
        assert R(missing, ["pkg/a.py"]) == missing


class TestImportSideEffects:
    """Importing `differential.py` re-execs the *whole process* unless guarded.

    Found by this suite: a test file that imported it made `pytest` exit 0 with no
    output — every test silently unrun. The behaviour is deliberate (an unseeded
    interpreter samples different conformance cases), so the fix belongs in the
    importer, and this test pins both halves so neither can drift.
    """

    def test_importing_unguarded_re_execs(self, tmp_path):
        import subprocess
        prog = tmp_path / "imp.py"
        prog.write_text(
            "import os, sys, importlib.util as u\n"
            "print('MARK', flush=True)\n"
            "s = u.spec_from_file_location('d', sys.argv[1])\n"
            "m = u.module_from_spec(s)\n"
            "s.loader.exec_module(m)\n"
            "print('DONE', flush=True)\n")
        env = {k: v for k, v in os.environ.items()
               if k not in ("PYTHONHASHSEED", "AUTOFORM_NO_REEXEC")}
        r = subprocess.run([sys.executable, str(prog),
                            os.path.join(os.path.dirname(os.path.dirname(
                                os.path.abspath(__file__))), "scripts",
                                "differential.py")],
                           capture_output=True, text=True, env=env, timeout=300)
        assert r.stdout.count("MARK") == 2, (
            "expected the import to re-exec the process once; got %r" % r.stdout)

    def test_the_guard_variable_is_honoured(self, differential):
        """The fixture sets AUTOFORM_NO_REEXEC; reaching this line at all proves it
        worked, since a re-exec would have destroyed the pytest process."""
        assert hasattr(differential, "FUEL")


class TestZeroCasesIsLoud:
    def test_the_harness_still_says_so_when_nothing_resolves(self, differential):
        src = open(differential.__file__).read()
        assert "none of the AST's source files resolve" in src, (
            "the 'found a test suite but resolved none of it' message is gone; a "
            "conformance run that compares 0 cases must say why")
