"""Replays the cachetools 7.1.4 negative-size defect (docs/evidence-cachetools-negative-size.md).

Three layers, each skipped by NAME when what it needs is absent (a skip is not a pass):

* the witness test (tracked fixture) fails on 7.1.4 and passes on 7.1.5 -- needs the two
  digest-pinned corpora under ~/.cache/autoform/corpora;
* the tracked oracle evidence (artifacts/defect/DefectCachetoolsNeg) holds one
  `Cache.__setitem__` divergence whose expected value is the fixed runtime's `ValueError`,
  and none on the same-revision control -- needs nothing;
* the full replay regenerates the 7.1.4 AST (Joern + `cartographer/plain_class_values.py`),
  checks its digest, renders and builds the Lean module and re-runs the oracle -- needs the
  corpora, Joern 4.0.606 and the Lean toolchain. The AST is 3.2 MB and untracked.
"""
import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "cartographer"))
import plain_class_values  # noqa: E402

WITNESS = ROOT / "tests" / "fixtures" / "defect" / "getsizeof_negative"
EVIDENCE = ROOT / "artifacts" / "defect" / "DefectCachetoolsNeg"
CORPORA = Path(os.path.expanduser("~/.cache/autoform/corpora"))
OLD = CORPORA / "cachetools-7.1.4-lib-7.1.5-tests"   # src/cachetools of 7.1.4, tests of 7.1.5
NEW = CORPORA / "cachetools-7.1.5-sdist-with-tests"  # 7.1.5 sdist, tests included
AST_SHA256 = "557473f45fa6c50c9d7d6391b8805c9b31a5a8aab641e5b48c562a15750f5e5a"
SETITEM = "cachetools/__init__.py:<module>.Cache.__setitem__"
needs_old = pytest.mark.skipif(not (OLD / "cachetools").is_dir(),
                               reason="cachetools 7.1.4 corpus absent under ~/.cache/autoform/corpora")
needs_new = pytest.mark.skipif(not (NEW / "cachetools").is_dir(),
                               reason="cachetools 7.1.5 corpus absent under ~/.cache/autoform/corpora")


def _run_witness(corpus):
    env = dict(os.environ, PYTHONPATH=str(corpus))
    return subprocess.run(
        [sys.executable, "-m", "pytest", str(WITNESS), "-q", "-p", "no:cacheprovider",
         "--no-header", "-o", "addopts="],
        capture_output=True, text=True, env=env, cwd=str(WITNESS))


@needs_old
def test_negative_size_witness_fails_on_7_1_4():
    r = _run_witness(OLD)
    out = r.stdout + r.stderr
    assert r.returncode == 1, out[-800:]
    assert "1 failed" in out and "test_getsizeof_negative" in out, out[-800:]


@needs_new
def test_negative_size_witness_passes_on_7_1_5():
    r = _run_witness(NEW)
    assert r.returncode == 0 and "1 passed" in r.stdout, (r.stdout + r.stderr)[-800:]


def _evidence(run):
    return json.loads((EVIDENCE / run / "conformance.json").read_text())


def test_tracked_evidence_has_the_setitem_divergence_on_the_buggy_revision():
    cross = _evidence("cross-revision")
    rows = [d for d in cross["divergence_detail"] if d["function"] == SETITEM]
    assert len(rows) == 1, [d["function"] for d in cross["divergence_detail"]]
    row = rows[0]
    assert row["observation"]["outcome"] == ["exn", "ValueError"]     # the FIXED runtime
    assert "lean returned unit" in row["detail"] and row["origin"] == "test-suite"
    assert row["case"]["args"] == [["int", 1], ["int", 1]]
    assert cross["runtime_version"].startswith("Python 3")
    assert cross["source_root"].endswith("cachetools-7.1.5-sdist-with-tests")


def test_tracked_control_has_no_setitem_divergence_on_the_same_revision():
    same = _evidence("same-revision")
    assert same["source_root"].endswith("cachetools-7.1.4-lib-7.1.5-tests")
    assert all(d["function"] != SETITEM for d in same["divergence_detail"])
    # `agree` rows exist for the very method the defect is in: the control compared it.
    assert any(r["name"] == SETITEM and r["comparison"] == "agree"
               for r in same["runtime_cases"])


def _ast(owner_attrs, tail="skip"):
    return [{"name": "<module-objects>:<module>", "file": "", "params": [],
             "body": {"k": "seq", "a": {"k": "skip"}, "b": {"k": tail}}},
            {"name": "m.py:<module>", "file": "m.py", "classDeclarations": [
                {"name": "m.py:<module>.C", "shortName": "C", "bases": [],
                 "attributes": owner_attrs}]}]


def _pass(tmp_path, source):
    (tmp_path / "m.py").write_text(source)
    attrs = [{"name": "_C__s", "kind": "opaque", "value": plain_class_values.UNMODELED}]
    functions = _ast(attrs)
    edits = plain_class_values.rewrite(functions, str(tmp_path))
    return edits, functions[1]["classDeclarations"][0]["attributes"][0], functions[0]


def test_plain_class_values_models_a_plain_instance(tmp_path):
    edits, attribute, init = _pass(tmp_path, "class P:\n    __slots__ = ()\n"
                                   "    def __getitem__(self, k):\n        return 1\n"
                                   "class C:\n    __s = P()\n")
    assert edits == [("m.py:<module>.C", "C", "_C__s", "P")]
    assert attribute == {"name": "_C__s", "kind": "stored",
                         "value": "<classattr>m.py:<module>.C._C__s"}
    assert init["body"]["b"]["a"]["e"] == {"k": "alloc", "cls": "P", "args": []}


@pytest.mark.parametrize("helper", [
    "class P:\n    def __get__(self, o, t):\n        return 1\n",       # a descriptor
    "class P:\n    def __init__(self):\n        pass\n",             # runs code on construction
    "class P(dict):\n    pass\n",                                      # a base
    "class P:\n    x = 1\n",                                          # class-level state
])
def test_plain_class_values_refuses_what_it_cannot_prove_plain(tmp_path, helper):
    edits, attribute, _ = _pass(tmp_path, helper + "class C:\n    __s = P()\n")
    assert edits == [] and attribute["kind"] == "opaque"


def test_plain_class_values_refuses_a_class_defined_after_its_owner(tmp_path):
    edits, attribute, _ = _pass(tmp_path, "class C:\n    __s = P()\nclass P:\n    pass\n")
    assert edits == [] and attribute["kind"] == "opaque"


def _tool(name, *probe):
    found = shutil.which(name) or shutil.which(name, path=os.path.expanduser("~/.elan/bin"))
    return found


@needs_old
@needs_new
def test_full_replay_catches_the_defect_from_the_pinned_corpora(tmp_path):
    joern = Path(os.path.expanduser(os.environ.get("JOERN_HOME", "~/joern"))) / "joern-cli"
    if not (joern / "joern").is_file():
        pytest.skip("Joern not found under $JOERN_HOME (default ~/joern)")
    lake = _tool("lake")
    if lake is None:
        pytest.skip("lake not on PATH or ~/.elan/bin")
    env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + os.pathsep + os.environ["PATH"])
    subprocess.run([str(joern / "joern-parse"), str(OLD), "--output", str(tmp_path / "cpg.bin")],
                   check=True, capture_output=True, cwd=tmp_path)
    subprocess.run([str(joern / "joern"), "--script", str(ROOT / "cartographer/export_ast.sc"),
                    "--param", f"cpgPath={tmp_path / 'cpg.bin'}", "--param",
                    f"out={tmp_path / 'raw.json'}", "--param", "dataModel=lp64"],
                   check=True, capture_output=True, cwd=tmp_path)
    ast = tmp_path / "ast-DefectCachetoolsNeg.json"
    subprocess.run([sys.executable, str(ROOT / "cartographer/plain_class_values.py"),
                    str(tmp_path / "raw.json"), str(OLD), str(ast)], check=True, cwd=tmp_path)
    digest = hashlib.sha256(ast.read_bytes()).hexdigest()
    assert digest == AST_SHA256, "regenerated AST differs from the one the evidence was run on"
    module = ROOT / "Autoform" / "Generated" / "DefectCachetoolsNeg.lean"
    subprocess.run([sys.executable, str(ROOT / "cartographer/render_lean.py"), str(ast),
                    str(module), "DefectCachetoolsNeg", "--shard-functions", "0"],
                   check=True, capture_output=True, cwd=ROOT)
    subprocess.run([lake, "build", "Autoform.Generated.DefectCachetoolsNeg"], check=True,
                   capture_output=True, cwd=ROOT, env=env)
    run = subprocess.run(
        [sys.executable, str(ROOT / "scripts/differential.py"), str(ast), str(NEW),
         "DefectCachetoolsNeg", "100", "--tests", str(NEW / "tests" / "test_cache.py"),
         "--no-cache"], capture_output=True, text=True, cwd=tmp_path, env=env)
    out = run.stdout + run.stderr
    line = ("DIVERGENCE " + SETITEM + "(int 1, int 1): cpython raised ValueError, "
            "lean returned unit")
    assert line in out, out[-1500:]
    found = json.loads((tmp_path / "conformance.json").read_text())
    assert [d["function"] for d in found["divergence_detail"]].count(SETITEM) == 1
