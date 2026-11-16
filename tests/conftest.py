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


def exporter_source():
    """Inspect the actual compile units, including a modular entry's dependencies."""
    compiler = load(os.path.join(SCRIPTS, "compiler_sources.py"), "af_compiler_sources")
    return '\n'.join(path.read_text() for path in
                     compiler.source_files(os.path.join(CARTO, "export_ast.sc")))


def load(path: str, name: str) -> types.ModuleType:
    """Import a script by path, without requiring it to be a package."""
    # Executing a script normally adds its own directory to sys.path. Reproduce
    # that environment for sibling helper imports when loading it by file path.
    directory = os.path.dirname(os.path.abspath(path))
    if directory not in sys.path:
        sys.path.insert(0, directory)
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec and spec.loader, path
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="session")
def pipeline_model():
    """`make(module, source)`: the translated model of `source` as `Autoform.Generated.<module>`,
    built in this repository's lake root, and the path of its `ast-<module>.json`.

    The Lean-backed NL and harness tests read a pipeline model (`PipelinePython`,
    `PipelineSecurityScoped`, ...). Those are build products -- `ast-Pipeline*.json` and
    `Autoform/Generated/*.lean` are gitignored -- so the tests used to pass only where an
    earlier `autoform.sh` run had left them behind. Run the documented pipeline once per
    session when the AST or the module's .olean is missing; without Joern it is a named skip.
    """
    built = {}

    def make(module, source):
        ast = os.path.join(ROOT, "ast-%s.json" % module)
        olean = os.path.join(ROOT, ".lake/build/lib/lean/Autoform/Generated/%s.olean" % module)
        if module in built:
            return built[module]
        if not (os.path.isfile(ast) and os.path.isfile(olean)):
            joern = os.environ.get("JOERN_HOME", os.path.expanduser("~/joern"))
            if not os.path.exists(os.path.join(joern, "joern-cli", "joern-parse")) and \
                    not os.path.exists(os.path.join(joern, "joern-parse")):
                pytest.skip("pipeline model %s absent and Joern is not installed to build it "
                            "(autoform.sh %s %s)" % (module, source, module))
            run = subprocess.run(["bash", os.path.join(ROOT, "autoform.sh"), str(source), module],
                                 cwd=ROOT, capture_output=True, text=True)
            # autoform.sh exits 1 when the run finished with named gaps; the model is still built.
            assert run.returncode in (0, 1) and os.path.isfile(ast) and os.path.isfile(olean), \
                "autoform.sh %s %s did not build the model (exit %d):\n%s" % (
                    source, module, run.returncode, (run.stdout + run.stderr)[-3000:])
        built[module] = ast
        return ast

    return make


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
    for s in ("check_render.py", "check_docs.py", "deep_json.py"):
        shutil.copy(os.path.join(SCRIPTS, s), os.path.join(d, "scripts", s))
    for script in ("render_lean.py", "generator_lowering.py", "python_truth_lowering.py", "python_truth_values.py", "ast_tools.py"):
        shutil.copy(os.path.join(CARTO, script), os.path.join(d, "cartographer", script))
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


NL_FIXTURES = os.path.join(ROOT, "tests", "fixtures", "nl")
# The checkout the NL fixtures were recorded in; their lean_root/ast/source_root are under it.
NL_RECORDED_ROOT = "/Users/mbhatt/autoform"


def rebase_paths(value, root=ROOT, recorded=NL_RECORDED_ROOT):
    """`value` with every string path under the recording checkout moved under `root`."""
    if isinstance(value, str):
        return root + value[len(recorded):] if value == recorded or value.startswith(recorded + "/") else value
    if isinstance(value, list):
        return [rebase_paths(v, root, recorded) for v in value]
    if isinstance(value, dict):
        return {k: rebase_paths(v, root, recorded) for k, v in value.items()}
    return value


def nl_fixture(name):
    """A recorded NL fixture (tests/fixtures/nl/<name>) with its paths rebased onto this checkout."""
    with open(os.path.join(NL_FIXTURES, name), encoding="utf-8") as stream:
        return rebase_paths(json.load(stream))
