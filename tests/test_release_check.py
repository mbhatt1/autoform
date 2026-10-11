"""scripts/release_check.sh fails closed, with gh, curl and git's remote stubbed."""
import os
import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/release_check.sh"
pytestmark = pytest.mark.skipif(shutil.which("bash") is None, reason="needs bash")


def _repo(tmp_path, *, version="9.9.9", changelog="9.9.9", init="9.9.9"):
    repo = tmp_path / "repo"
    (repo / "scripts").mkdir(parents=True)
    (repo / "src/autoform").mkdir(parents=True)
    shutil.copy(SCRIPT, repo / "scripts/release_check.sh")
    (repo / "pyproject.toml").write_text(f'[project]\nname = "autoform-lean"\nversion = "{version}"\n')
    (repo / "src/autoform/__init__.py").write_text(f'__version__ = "{init}"\n')
    (repo / "CHANGELOG.md").write_text(f"# Changelog\n\n## [{changelog}] - x\n")
    env = {**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t",
           "GIT_COMMITTER_EMAIL": "t@t"}
    for cmd in (["git", "init", "-q"], ["git", "add", "."], ["git", "commit", "-qm", "x"],
                ["git", "remote", "add", "origin", str(repo)]):
        subprocess.run(cmd, cwd=repo, check=True, env=env)
    return repo


def _stubs(tmp_path, *, ci="success", pypi="404"):
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    gh = bin_dir / "gh"
    gh.write_text(f"#!/bin/sh\necho {ci}\n")
    curl = bin_dir / "curl"
    curl.write_text(f"#!/bin/sh\nprintf {pypi}\n")
    for tool in (gh, curl):
        tool.chmod(0o755)
    return bin_dir


def _run(repo, bin_dir):
    env = {**os.environ, "PATH": f"{bin_dir}:{os.environ['PATH']}"}
    return subprocess.run(["bash", "scripts/release_check.sh"], cwd=repo, env=env,
                          capture_output=True, text=True)


def test_ready_prints_commands_and_runs_none(tmp_path):
    result = _run(_repo(tmp_path), _stubs(tmp_path))
    assert result.returncode == 0, result.stderr
    assert "git tag -a v9.9.9" in result.stdout
    assert "gh release create v9.9.9" in result.stdout
    assert "READY" in result.stdout


def test_dirty_tree_fails(tmp_path):
    repo = _repo(tmp_path)
    (repo / "stray.txt").write_text("x")
    result = _run(repo, _stubs(tmp_path))
    assert result.returncode == 1 and "not clean" in result.stderr


def test_ci_not_green_fails(tmp_path):
    result = _run(_repo(tmp_path), _stubs(tmp_path, ci="failure"))
    assert result.returncode == 1 and "concluded 'failure'" in result.stderr


def test_no_run_on_head_fails(tmp_path):
    result = _run(_repo(tmp_path), _stubs(tmp_path, ci="none"))
    assert result.returncode == 1 and "no completed run" in result.stderr


def test_version_already_on_pypi_fails(tmp_path):
    result = _run(_repo(tmp_path), _stubs(tmp_path, pypi="200"))
    assert result.returncode == 1 and "already on PyPI" in result.stderr


def test_unanswerable_pypi_lookup_is_an_error_not_a_pass(tmp_path):
    result = _run(_repo(tmp_path), _stubs(tmp_path, pypi="000"))
    assert result.returncode == 2


def test_version_disagreement_fails(tmp_path):
    result = _run(_repo(tmp_path, changelog="9.9.8"), _stubs(tmp_path))
    assert result.returncode == 1 and "CHANGELOG.md" in result.stderr


def test_existing_tag_fails(tmp_path):
    repo = _repo(tmp_path)
    subprocess.run(["git", "tag", "v9.9.9"], cwd=repo, check=True)
    result = _run(repo, _stubs(tmp_path))
    assert result.returncode == 1 and "already exists" in result.stderr
