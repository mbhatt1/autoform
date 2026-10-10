"""Real Python generators through Joern, frame lowering, Core and kernel proofs."""
import importlib.util
import json
import os
from pathlib import Path
import sys

import pytest

from test_source_numeric import SOURCE_RUNTIME, ROOT, numeric_env, run
from test_python_signatures import _decode

sys.path.insert(0, str(ROOT / "cartographer"))
from generator_lowering import lower_generators, walk


CASES = [(name, n) for name, values in [
    ("delayed", [2, 4]), ("independent", [2]), ("sending", [2, 4]),
    ("rejected_send", [3]), ("branches", [5]), ("drain", [0, 3]),
    ("nested_iteration", [0, 3]), ("cleanup_timing", [3]),
    ("catch_after_yield", [2]), ("closed_after_error", [2]), ("pep479", [2]),
    ("suspended_exception", [2]), ("suspended_return", [2]),
    ("deleted_local", [2]), ("callable_local", [2]), ("method_frame", [2]),
] for n in values]


def test_source_metadata_distinguishes_own_suspensions():
    records = {record["name"]: record for record in _decode('''
def outer(n):
    def inner():
        yield n
    return inner
def sequence(n):
    sent = yield n
    yield sent
factory = lambda n: (yield n)
async def asynchronous(n):
    yield n
''')["signatures"].values()}
    assert records["outer"]["generator"] is None
    assert records["inner"]["generator"]["captures"] == ["n"]
    assert records["sequence"]["generator"]["locals"] == ["n", "sent"]
    assert records["lambda"]["generator"]["parameters"] == ["n"]
    assert records["asynchronous"]["generator"]["async"] is True


def test_unannotated_suspension_is_an_explicit_gap():
    # An older or partial frontend must not silently turn a yield into a return.
    source = [{"name": "broken", "params": [],
               "body": {"k": "yieldS", "e": {"k": "int", "v": "3"}}}]
    assert lower_generators(source)[0]["body"] == {
        "k": "holeS", "label": "generator:missing-metadata"}
    assert source[0]["body"]["k"] == "yieldS"


def test_long_generator_body_does_not_depend_on_python_recursion_limit():
    body = {"k": "yieldS", "e": {"k": "int", "v": "2"}}
    for i in range(1500):
        body = {"k": "seq", "a": {"k": "assign", "x": "n",
                "e": {"k": "int", "v": str(i)}}, "b": body}
    function = {"name": "long_generator", "params": [], "body": body,
                "generator": {"locals": ["n"], "captures": [], "parameters": []}}
    compiled = lower_generators([function])[0]
    assert compiled["generatorHelpers"]
    assert sum(n.get("k") == "assign" for n in walk(compiled["analysisBody"])) == 1500
    assert not any(n.get("k") in ("yieldS", "holeS") for n in walk(compiled["analysisBody"]))
    assert sum(n.get("k") == "yieldS" for n in walk(function["body"])) == 1


def test_suspended_generators_source(tmp_path, numeric_env, monkeypatch):
    if not os.environ.get("AUTOFORM_TEST_JOERN"):
        pytest.skip("set AUTOFORM_TEST_JOERN=1 to compare actual source generators")
    joern = Path(os.environ.get("JOERN_HOME", Path.home() / "joern"))
    if (joern / "joern-cli").is_dir():
        joern /= "joern-cli"
    source = ROOT / "examples/python_control/generators.py"
    spec = importlib.util.spec_from_file_location("generator_probes", source)
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    expected = [getattr(probes, name)(n) for name, n in CASES]
    src = tmp_path / "src"
    src.mkdir()
    (src / "generators.py").write_text(source.read_text())
    run([joern / "joern-parse", src, "--language", "PYTHONSRC", "--output", "cpg.bin"],
        tmp_path, numeric_env, timeout=600)
    run([joern / "joern", "--script", ROOT / "cartographer/export_ast.sc",
         "--param", "cpgPath=cpg.bin", "--param", "out=ast.json"],
        tmp_path, numeric_env, timeout=600)
    functions = json.loads((tmp_path / "ast.json").read_text())
    lowered = lower_generators(functions)
    sys.path.insert(0, str(ROOT / "scripts"))
    monkeypatch.setenv("AUTOFORM_NO_REEXEC", "1")
    from core_oracle import count_ast_holes
    hole_count = count_ast_holes(functions)
    assert hole_count >= 3, "delegation, captured cells and return payloads are counted"
    assert len(lowered) == len(functions), "generated methods are not source functions"
    def find(suffix):
        return next(f for f in lowered if f["name"].endswith("." + suffix))
    assert find("delegated")["body"] == {"k": "holeS", "label": "generator:yieldFromS"}
    assert find("captured")["body"] == {"k": "holeS", "label": "generator:free-variable-cells"}
    assert "generator:return-value" in [v.get("label") for v in walk(find("returned_value")["analysisBody"])]
    assert find("counter")["generatorHelpers"]
    model = tmp_path / "Model.lean"
    run([sys.executable, ROOT / "cartographer/render_lean.py", tmp_path / "ast.json", model, "Generators"],
        ROOT, numeric_env)
    header = model.read_text() + "\nopen Autoform.Core Autoform.Generated.Generators\n"
    header += SOURCE_RUNTIME
    calls = [f'runSource program initialGlobals 300 "generators.py:<module>.{name}" [.int {n}]' for name, n in CASES]
    driver = header + "def main : IO Unit := do\n"
    for (name, _), call in zip(CASES, calls):
        driver += f'''  match {call} with
  | .val (.int n) => IO.println n
  | other => throw (IO.userError ({json.dumps(name + ': ')} ++ reprStr other))
'''
    (tmp_path / "Check.lean").write_text(driver)
    observed = run(["lake", "env", "lean", "--run", tmp_path / "Check.lean"], ROOT, numeric_env, timeout=600)
    assert [int(s) for s in observed.splitlines()] == expected
    proofs = (f"example : program.funcs.length = {len(functions)} := by rfl\n"
              f"example : program.holes.length = {hole_count} := by decide +kernel\n"
              "example : program.auxiliaryFuncs.isEmpty = false := by rfl\n")
    for call, result in zip(calls, expected):
        proofs += (f"example : (match {call} with\n"
                   f"  | .val (.int n) => n == ({result} : Int)\n"
                   "  | _ => false) = true := by decide +kernel\n")
    (tmp_path / "Proofs.lean").write_text(header + proofs)
    run(["lake", "env", "lean", tmp_path / "Proofs.lean"], ROOT, numeric_env, timeout=900)
