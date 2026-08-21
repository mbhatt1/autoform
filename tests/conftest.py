"""Shared fixtures for the Python-tooling test suite.

Every test here exists because something in this repo failed *silently*. The suite's
job is not coverage for its own sake: it is to make each of those failure modes loud.
"""
from __future__ import annotations

import importlib.util
import json
import os
import shutil
import subprocess
import sys
import threading
import types

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCRIPTS = os.path.join(ROOT, "scripts")
CARTO = os.path.join(ROOT, "cartographer")


def load(path: str, name: str) -> types.ModuleType:
    """Import a script by path, without requiring it to be a package."""
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec and spec.loader, path
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="session")
def render_lean():
    return load(os.path.join(CARTO, "render_lean.py"), "af_render_lean")


@pytest.fixture(scope="session")
def mutate():
    return load(os.path.join(SCRIPTS, "mutate.py"), "af_mutate")


@pytest.fixture(scope="session")
def differential():
    """Import `scripts/differential.py` WITHOUT letting it re-exec the test process.

    At import time it calls `os.execve` to re-run itself with PYTHONHASHSEED=0 unless
    `AUTOFORM_NO_REEXEC` is set. Importing it from pytest therefore replaces the pytest
    process mid-collection: the run ends with status 0 and no output at all, which is a
    green light for a suite that never ran. Guard it.
    """
    prev = os.environ.get("AUTOFORM_NO_REEXEC")
    os.environ["AUTOFORM_NO_REEXEC"] = "1"
    try:
        return load(os.path.join(SCRIPTS, "differential.py"), "af_differential")
    finally:
        if prev is None:
            os.environ.pop("AUTOFORM_NO_REEXEC", None)
        else:
            os.environ["AUTOFORM_NO_REEXEC"] = prev


def run_script(script, *args, cwd=None):
    """Run one of the repo's scripts and return (rc, stdout+stderr)."""
    r = subprocess.run([sys.executable, script, *args], cwd=cwd or ROOT,
                       capture_output=True, text=True, timeout=900)
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def fn(name="m.py:<module>.f", file="m.py", params=(), body=None, **extra):
    d = {"name": name, "file": file, "params": list(params),
         "body": body if body is not None else {"k": "skip"}}
    d.update(extra)
    return d


def write_ast(path, funcs):
    """Serialise an AST. Deep ASTs are the point of several tests, and `json.dump`
    is itself recursive, so the write happens on a thread with a real stack rather
    than quietly capping how deep a test is allowed to go."""
    box = {}

    def go():
        try:
            with open(path, "w") as fh:
                json.dump(list(funcs), fh)
        except BaseException as e:            # noqa: BLE001
            box["e"] = e

    old = sys.getrecursionlimit()
    sys.setrecursionlimit(200_000)
    try:
        threading.stack_size(256 * 1024 * 1024)
    except (ValueError, RuntimeError):
        pass
    t = threading.Thread(target=go)
    t.start()
    t.join()
    sys.setrecursionlimit(old)
    if "e" in box:
        raise box["e"]
    return path


def seq_chain(n, leaf=None):
    """A right-nested `seq` of `n` statements — the shape that broke the renderer."""
    leaf = leaf or (lambda i: {"k": "assign", "x": "v%d" % i,
                               "e": {"k": "int", "v": i}})
    node = leaf(n - 1)
    for i in range(n - 2, -1, -1):
        node = {"k": "seq", "a": leaf(i), "b": node}
    return node


def make_repo(tmp_path, module="Sample", funcs=None, lean_text=None,
              record_manifest=True):
    """A minimal repo skeleton: scripts/, cartographer/, an AST, a generated module.

    Real copies of the scripts, so the tests exercise the shipped code, not a stub.
    """
    d = str(tmp_path)
    os.makedirs(os.path.join(d, "scripts"), exist_ok=True)
    os.makedirs(os.path.join(d, "cartographer"), exist_ok=True)
    os.makedirs(os.path.join(d, "Autoform", "Generated"), exist_ok=True)
    for s in ("check_render.py", "check_docs.py"):
        shutil.copy(os.path.join(SCRIPTS, s), os.path.join(d, "scripts", s))
    shutil.copy(os.path.join(CARTO, "render_lean.py"),
                os.path.join(d, "cartographer", "render_lean.py"))
    funcs = funcs if funcs is not None else [fn()]
    ast = os.path.join(d, "ast-%s.json" % module)
    write_ast(ast, funcs)
    gen = os.path.join(d, "Autoform", "Generated", "%s.lean" % module)
    if lean_text is None:
        subprocess.run([sys.executable, os.path.join(d, "cartographer", "render_lean.py"),
                        ast, gen, module], check=True, capture_output=True)
    else:
        with open(gen, "w") as fh:
            fh.write(lean_text)
    # check_render.py became manifest-driven with the 2026-08-19 artifact policy: a
    # module with an AST but no artifact-manifest.json entry is UNVERIFIABLE (exit 2),
    # not a pass and not a mismatch. Record the fixture's pair so the tests exercise the
    # agreement/disagreement paths rather than the no-entry path. Tests that want the
    # no-entry path build their own repo without calling --record.
    if record_manifest:
        subprocess.run([sys.executable, os.path.join(d, "scripts", "check_render.py"),
                        "--record", module], cwd=d, check=True, capture_output=True)
    return d, ast, gen
