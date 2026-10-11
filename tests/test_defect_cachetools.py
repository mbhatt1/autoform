"""Replays the cachetools 7.1.6 replace-grow witness (docs/evidence-cachetools.md).

The witness is tracked (tests/fixtures/defect/replace_grow). The two corpora it runs
against are not in the repository: they are digest-pinned sdists under
~/.cache/autoform/corpora (see the evidence document). A missing corpus is a named
SKIP, never a pass. The Lean-side replay needs `ast-DefectCachetools.json`, which is
gitignored (3.2 MB, over the 2 MB tracking limit) and regenerated from the corpus.
"""
import os
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
WITNESS = ROOT / "tests" / "fixtures" / "defect" / "replace_grow"
CORPORA = Path(os.path.expanduser("~/.cache/autoform/corpora"))
OLD = CORPORA / "cachetools-7.1.6-lib-7.1.7-tests"   # src/cachetools of 7.1.6, tests of 7.1.7
NEW = CORPORA / "cachetools-7.1.7-sdist-with-tests"  # 7.1.7 sdist, tests included


def _run_witness(corpus):
    env = dict(os.environ, PYTHONPATH=str(corpus))
    return subprocess.run(
        [sys.executable, "-m", "pytest", str(WITNESS), "-q", "-p", "no:cacheprovider",
         "--no-header", "-o", "addopts="],
        capture_output=True, text=True, env=env, cwd=str(WITNESS))


@pytest.mark.skipif(not (OLD / "cachetools").is_dir(),
                    reason="cachetools 7.1.6 corpus absent under ~/.cache/autoform/corpora")
def test_replace_grow_witness_fails_on_7_1_6():
    r = _run_witness(OLD)
    out = r.stdout + r.stderr
    assert r.returncode == 1, out[-800:]
    assert "1 failed, 2 passed" in out, out[-800:]
    assert "test_getsizeof_replace_grow" in out and "2 != 1" in out, out[-800:]


@pytest.mark.skipif(not (NEW / "cachetools").is_dir(),
                    reason="cachetools 7.1.7 corpus absent under ~/.cache/autoform/corpora")
def test_replace_grow_witness_passes_on_7_1_7():
    r = _run_witness(NEW)
    assert r.returncode == 0, (r.stdout + r.stderr)[-800:]
    assert "3 passed" in r.stdout, r.stdout[-800:]


TRACKED = ROOT / "artifacts" / "defect" / "DefectCachetools"
SETITEM = "cachetools/__init__.py:<module>.Cache.__setitem__"


def test_tracked_cross_revision_run_catches_the_replace_grow_call():
    """The tracked 7.1.6-model / 7.1.7-runtime run has exactly one divergence, on the
    replace-grow call (4, 7), and the 7.1.7 post-state keeps key 3 (docs/evidence-cachetools.md,
    "The catch")."""
    import json
    cross = json.loads((TRACKED / "cross-revision" / "conformance.json").read_text())
    assert cross["divergences"] == 1
    (row,) = cross["divergence_detail"]
    assert row["function"] == SETITEM
    assert row["case"]["args"] == [["int", 4], ["int", 7]]
    assert row["origin"] == "test-suite"
    post = row["observation"]["post_heap"]
    fields = dict((k, v) for k, v in post[0][1])
    assert fields["_Cache__currsize"] == ["int", 10]
    assert [["int", 3], ["int", 3]] in post[2][2][1]          # 7.1.7 keeps key 3


def test_tracked_same_revision_control_agrees_on_the_replace_grow_call():
    import json
    same = json.loads((TRACKED / "same-revision" / "conformance.json").read_text())
    assert same["divergences"] == 0
    rows = [r for r in same["runtime_cases"] if r.get("name") == SETITEM
            and r["args"] == [["int", 4], ["int", 7]]]
    assert rows and all(r["comparison"] == "agree" for r in rows)
