#!/usr/bin/env python3
"""pr_fixture.py -- a two-commit Git history for exercising `pr_mode.py` offline.

    pr_fixture.py <directory>

Creates `<directory>` as a Git repository with two commits: `base` holds
`examples/source/python/numbers.py` as it is in this checkout, `head` replaces it with
`tests/fixtures/pr/head/numbers.py`, which modifies `quotient`, adds `clamp`, `label`
and `first`, and leaves `add` and `fraction` alone. Prints a JSON object with the
repository path and both commit ids. The same history is what `tests/test_pr_mode.py`
and `.github/workflows/pr.yml` run the chain on, so the two cannot drift apart.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "examples/source/python/numbers.py"
HEAD = ROOT / "tests/fixtures/pr/head/numbers.py"


def git(repo, *args):
    env = dict(os.environ, GIT_AUTHOR_NAME="autoform", GIT_AUTHOR_EMAIL="autoform@localhost",
               GIT_COMMITTER_NAME="autoform", GIT_COMMITTER_EMAIL="autoform@localhost",
               GIT_CONFIG_GLOBAL="/dev/null", GIT_CONFIG_SYSTEM="/dev/null")
    return subprocess.run(["git", "-c", "core.hooksPath=/dev/null", "-c", "commit.gpgsign=false", *args],
                          cwd=str(repo), env=env, check=True, text=True, capture_output=True).stdout.strip()


def make_history(directory, base_file=BASE, head_file=HEAD):
    repo = Path(directory)
    if repo.exists():
        shutil.rmtree(repo)
    repo.mkdir(parents=True)
    git(repo, "init", "-q", "-b", "main")
    commits = {}
    for tag, source in (("base", base_file), ("head", head_file)):
        shutil.copy(source, repo / "numbers.py")
        git(repo, "add", "numbers.py")
        git(repo, "commit", "-q", "-m", f"{tag}: numbers.py from {Path(source).relative_to(ROOT)}")
        git(repo, "tag", tag)
        commits[tag] = git(repo, "rev-parse", "HEAD")
    return {"repo": str(repo.resolve()), **commits}


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if len(argv) != 1:
        print(__doc__, file=sys.stderr)
        return 2
    print(json.dumps(make_history(argv[0])))
    return 0


if __name__ == "__main__":
    sys.exit(main())
