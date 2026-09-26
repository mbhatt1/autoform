"""Iterator state, mutation and protocol validation through source and the kernel."""
import importlib.util
import json
import os
from pathlib import Path
import sys

import pytest

from test_source_numeric import (SOURCE_RUNTIME, SOURCE_STATE_OUTPUT, ROOT,
                                 numeric_env, run, stage_source_initial_state)


CASES = [
    "list_live", "list_shrink", "exhaustion", "iterator_identity", "direct_container_method",
    "tuples", "unicode_characters", "none_item", "dict_values", "dict_value_loop",
    "dict_size_error", "dict_exhaustion", "sequence", "invalid_iter", "invalid_for",
    "sentinel", "iter_noniterable", "next_noniterator", "generator_list", "generator_dict",
    "sentinel_comparison", "sentinel_identity", "sequence_retry", "iterator_for",
    "sentinel_reentrant", "sentinel_retry",
    "sentinel_classmethod", "sentinel_staticmethod",
    "nested_dicts", "nested_iterators", "nested_sequences",
    "saved_callback",
]


def test_nested_iterators_kernel(tmp_path, numeric_env):
    # This regression runs without Joern: an inner loop must not replace the outer
    # iterator, whether the source is a dictionary or an explicit list iterator.
    expected = sum(a * 10 + b for a in {2: 0, 3: 0} for b in {1: 0, 2: 0})
    code = '''import Autoform.Lang.Core.Semantics
open Autoform.Core
def addPair : Stmt :=
  .assign "total" (.binop "+" (.name "total")
    (.binop "+" (.binop "*" (.name "a") (.lit (.int 10))) (.name "b")))
def nested (outer inner : Expr) : Program :=
  { funcs := [{ name := "probe", params := []
                body := .seq (.assign "total" (.lit (.int 0)))
                  (.seq (.forIn "a" outer (.forIn "b" inner addPair))
                    (.ret (.name "total"))) }] }
def dictPair (a b : Int) : Expr :=
  .dictE [(.lit (.int a), .lit .unit), (.lit (.int b), .lit .unit)]
def iterPair (a b : Int) : Expr :=
  .call "iter" [.listE [.lit (.int a), .lit (.int b)]]
set_option maxRecDepth 10000
set_option maxHeartbeats 0
'''
    for expression in ("dictPair", "iterPair"):
        code += (f'example : (match runFunc (nested ({expression} 2 3) ({expression} 1 2)) '
                 f'160 "probe" [] with | .val (.int n) => n == {expected} '
                 '| _ => false) = true := by decide +kernel\n')
    path = tmp_path / "NestedIterators.lean"
    path.write_text(code)
    run(["lake", "env", "lean", path], ROOT, numeric_env)


def test_iterators_source(tmp_path, numeric_env):
    if not os.environ.get("AUTOFORM_TEST_JOERN"):
        pytest.skip("set AUTOFORM_TEST_JOERN=1 to compare actual source iterators")
    joern = Path(os.environ.get("JOERN_HOME", Path.home() / "joern"))
    if (joern / "joern-cli").is_dir():
        joern /= "joern-cli"
    source = ROOT / "examples/python_control/iterators.py"
    spec = importlib.util.spec_from_file_location("iterator_probes", source)
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    expected = [getattr(probes, name)(2) for name in CASES]
    src = tmp_path / "src"
    src.mkdir()
    (src / "iterators.py").write_text(source.read_text())
    run([joern / "joern-parse", src, "--language", "PYTHONSRC", "--output", "cpg.bin"],
        tmp_path, numeric_env, timeout=600)
    run([joern / "joern", "--script", ROOT / "cartographer/export_ast.sc",
         "--param", "cpgPath=cpg.bin", "--param", "out=ast.json"], tmp_path, numeric_env, timeout=600)
    model = tmp_path / "Model.lean"
    run([sys.executable, ROOT / "cartographer/render_lean.py", tmp_path / "ast.json", model, "Iterators"],
        ROOT, numeric_env)
    header = model.read_text() + "\nopen Autoform.Core Autoform.Generated.Iterators\n"
    header += SOURCE_RUNTIME
    calls = [f'runSource program initialGlobals 400 "iterators.py:<module>.{name}" [.int 2]' for name in CASES]
    driver = header + "def main : IO Unit := do\n"
    for name, call in zip(CASES, calls):
        driver += f'''  match {call} with
  | .val (.int n) => IO.println n
  | other => throw (IO.userError ({json.dumps(name + ': ')} ++ reprStr other))
'''
    driver += SOURCE_STATE_OUTPUT
    (tmp_path / "Check.lean").write_text(driver)
    observed = run(["lake", "env", "lean", "--run", tmp_path / "Check.lean"], ROOT, numeric_env, timeout=600)
    header, lines = stage_source_initial_state(header, observed)
    assert [int(value) for value in lines] == expected
    proofs = ""
    for call, result in zip(calls, expected):
        proofs += (f"example : (match {call} with\n"
                   f"  | .val (.int n) => n == ({result} : Int)\n"
                   "  | _ => false) = true := by rw [initialGlobals_correct]; decide +kernel\n")
    for name, label in [("changed_dict_keys", "iterator:dict-keys-changed"),
                        ("private_fields", "call:getattr"),
                        ("result_protocol", "iterator:result-protocol"),
                        ("result_protocol_for", "iterator:result-protocol")]:
        proofs += (f'example : (match runSource program initialGlobals 400 "iterators.py:<module>.{name}" [.int 2] with\n'
                   f'  | .hole {json.dumps(label)} => true\n'
                   '  | _ => false) = true := by rw [initialGlobals_correct]; decide +kernel\n')
    (tmp_path / "Proofs.lean").write_text(header + proofs)
    run(["lake", "env", "lean", tmp_path / "Proofs.lean"], ROOT, numeric_env, timeout=900)
