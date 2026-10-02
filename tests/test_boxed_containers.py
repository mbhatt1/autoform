"""Boxed Python containers, differentially: CPython against the Lean interpreter.

`docs/boxed-containers.md` steps 3-4. Every function in `tests/boxed_sample/boxed.py` is
run twice -- by CPython, and by `Autoform.Core.runMain` over the module the real renderer
(`cartographer/render_lean.py`) makes from the real exporter's output for that file
(`tests/boxed_sample/ast-BoxedSample.json`). The outcomes are three-valued, never two:

* **agree** -- same int/bool, or the same exception class;
* **hole** -- Core refused (`Expr.hole`), which is INCONCLUSIVE and never a pass;
* **diverge** -- a different answer, which is the failure this suite exists to catch.

The cases Core does not model (mutation during iteration, live dict views, slice
assignment) are pinned as holes, so that a future change which starts *answering* them
has to come here and justify the answer against CPython.

This needs a built Lean toolchain (`lake`, and `Autoform.Lang.Core.Semantics` built), so
it is skipped -- visibly, with the reason -- where there is none. That is the one place
this suite runs Lean; the alternative was to hand-write the Core terms, which tests the
semantics but not the exporter and renderer that produce them.

Regenerating the AST (pinned Joern 4.0.606 with pysrc2cpg; see docs/running.md):

    joern-parse --language pythonsrc tests/boxed_sample -o cpg.bin
    joern --script cartographer/export_ast.sc --param cpgPath=cpg.bin \\
          --param out=tests/boxed_sample/ast-BoxedSample.json
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SAMPLE = os.path.join(ROOT, "tests", "boxed_sample")
AST = os.path.join(SAMPLE, "ast-BoxedSample.json")
SRC = os.path.join(SAMPLE, "boxed.py")
PROV = os.path.join(SAMPLE, "provenance.json")
RENDER = os.path.join(ROOT, "cartographer", "render_lean.py")

# name -> expected Core verdict. "agree" cases must match CPython exactly; "hole" cases
# must come back as a hole (and are listed with the label, so a DIFFERENT refusal is
# noticed too).
AGREE = [
    "alias", "neg", "neg_read", "oob", "oob_neg", "oob_read", "dset", "dlit", "kerr",
    "app", "pop_tmp", "ext", "setdef", "nested", "call_mut", "comp_len", "comp_sum",
    "delk", "del_pos", "del_missing", "truth", "not_empty", "tup", "unhash", "eq", "is_",
    "in_", "order", "dict_eq", "copy_fresh", "iter_sum",
]
HOLES = {
    "mutate_iter": "forIn:container-mutated-during-iteration",
    "keys_view": "mcall:dict.keys:live-view-not-modelled",
    "slc": "assign:lhs:slice",
}


def _lake():
    for cand in (shutil.which("lake"), os.path.expanduser("~/.elan/bin/lake")):
        if cand and os.path.exists(cand):
            return cand
    return None


def _built():
    return os.path.exists(os.path.join(ROOT, ".lake", "build", "lib", "lean", "Autoform",
                                       "Lang", "Core", "Semantics.olean"))


def cpython_outcome(fn):
    """`('val', int|bool)` or `('exn', class name)`."""
    try:
        v = fn()
    except Exception as e:  # noqa: BLE001 -- the class name IS the observable
        return ("exn", type(e).__name__)
    assert isinstance(v, (bool, int)), (fn.__name__, v)
    return ("val", v)


def parse_core(line):
    kind, _, rest = line.partition(" ")
    if kind == "int":
        return ("val", int(rest))
    if kind == "bool":
        return ("val", rest == "true")
    if kind == "exn":
        return ("exn", rest)
    if kind == "hole":
        return ("hole", rest)
    return ("other", line)


RUNNER = """
open Autoform.Core Autoform.Generated.BoxedSample

def showR : EResult → String
  | .val (.int i)  => s!"int {i}"
  | .val (.bool b) => s!"bool {b}"
  | .exn (.str e)  => s!"exn {e}"
  | .hole l        => s!"hole {l}"
  | r              => s!"other {repr r}"

#eval (%s : List String).forM fun n =>
  IO.println ("@@" ++ n ++ " " ++ showR (runMain program 2000 moduleInits s!"boxed.py:<module>.{n}" []))
"""


@pytest.fixture(scope="module")
def core_results(tmp_path_factory):
    lake = _lake()
    if lake is None or not _built():
        pytest.skip("needs `lake` and a built Autoform.Lang.Core.Semantics "
                    "(run `lake build Autoform.Lang.Core.Semantics`)")
    d = tmp_path_factory.mktemp("boxed")
    gen = d / "BoxedSample.lean"
    subprocess.run([sys.executable, RENDER, AST, str(gen), "BoxedSample"], check=True,
                   capture_output=True)
    names = AGREE + list(HOLES)
    src = gen.read_text() + RUNNER % json.dumps(names)
    gen.write_text(src)
    out = subprocess.run([lake, "env", "lean", str(gen)], cwd=ROOT, capture_output=True,
                         text=True, timeout=1800)
    got = {}
    for line in out.stdout.splitlines():
        if line.startswith("@@"):
            n, _, rest = line[2:].partition(" ")
            got[n] = parse_core(rest)
    assert got, "Lean produced no results:\n" + out.stdout[-2000:] + out.stderr[-2000:]
    return got


@pytest.fixture(scope="module")
def cpython_results():
    spec = importlib.util.spec_from_file_location("boxed_sample", SRC)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return {n: cpython_outcome(getattr(mod, n)) for n in AGREE}


def test_ast_was_exported_from_this_source():
    # The same source<->AST binding as the tests/fixtures/* differential fixtures.
    prov = json.load(open(PROV))
    digest = hashlib.sha256(open(SRC, "rb").read()).hexdigest()
    assert prov["source_sha256"] == digest, (
        "boxed.py changed since ast-BoxedSample.json was exported; re-run the command in "
        "tests/boxed_sample/provenance.json")
    assert prov["ast_sha256"] == hashlib.sha256(open(AST, "rb").read()).hexdigest()


def test_the_ast_is_the_boxed_one():
    """The committed AST must carry the boxing, or this suite tests the old semantics.

    Nothing-to-check is a failure: the counts are asserted, not just the absence of
    `listE`."""
    blob = json.dumps(json.load(open(AST)))
    assert blob.count('"boxContainer"') >= 20
    assert blob.count('"delIndex"') == 3
    assert '"op:delete-index"' not in blob


@pytest.mark.parametrize("name", AGREE)
def test_core_agrees_with_cpython(name, core_results, cpython_results):
    assert name in core_results, f"{name}: Lean printed nothing for it"
    assert core_results[name] == cpython_results[name], (
        f"{name}: CPython {cpython_results[name]} vs Core {core_results[name]}")


@pytest.mark.parametrize("name", sorted(HOLES))
def test_unmodelled_shapes_stay_holes(name, core_results):
    assert core_results[name] == ("hole", HOLES[name])


def test_the_hole_cases_really_are_answered_by_cpython():
    """A hole is only honest if there was an answer to refuse: each of these runs fine in
    CPython, so Core answering them later would be checkable, and is not vacuous now."""
    spec = importlib.util.spec_from_file_location("boxed_sample2", SRC)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    assert mod.mutate_iter() == 2
    assert mod.keys_view() == 1
    assert mod.slc() == 5


def test_old_negative_index_was_wrong():
    """`Int.toNat` clamps, so the old `index` read `(7, 8, 9)[-1]` as element 0. CPython
    says 9; `neg_read` above pins the fixed answer."""
    i = -1
    assert max(i, 0) == 0 and (7, 8, 9)[max(i, 0)] == 7 != (7, 8, 9)[-1]
