"""Lazy expressions, implicit protocol calls and source-owned coverage evidence."""
import importlib.util
import json
import os
from pathlib import Path
import sys

import pytest

from test_source_numeric import (SOURCE_RUNTIME, SOURCE_STATE_OUTPUT, ROOT,
                                 numeric_env, run, stage_source_initial_state)
from test_python_signatures import _decode

sys.path.insert(0, str(ROOT / "cartographer"))
from generator_lowering import lower_generators, name, node, seq, walk
from render_lean import render_func


CASES = ["stored", "first_iterator", "deferred_failure", "creation_failure", "nested",
         "destructured", "live_source", "collect_list", "collect_tuple", "short_any",
         "short_all", "exhausted_any", "exhausted_all", "shadow_consumer", "later_argument",
         "no_length", "exhausted", "consume_returned", "pep479"]


# The native run observes fuel 500. Kernel computation at a sufficient smaller
# budget is transported to that SAME claim using the interpreter's proved theorem.
# No native result or proposed budget is trusted: both termination and the result
# at fuel 64 must first pass kernel computation.
PROOF_SUPPORT = '''
private theorem runSourceFuelMono {p : Program} {initial : Heap × Ref}
    {k k' : Nat} {entry : String} {args : List Val}
    (hk : k ≤ k') (hne : runSource p initial k entry args ≠ .outOfFuel) :
    runSource p initial k' entry args = runSource p initial k entry args := by
  unfold runSource at hne ⊢
  generalize hc : ({ dialect := p.dialect, table := p.table, globals := initial.2, builtinBases := p.builtinBases, properties := p.properties, excClasses := p.excClasses, classDecls := p.classDecls } : Ctx) = ctx at hne ⊢
  cases hf : ctx.resolve entry with
  | none => simp only [hf]
  | some fn =>
    simp only [hf] at hne ⊢
    rcases he : applyFunc ctx k initial.1 fn none args [] with ⟨heap, result⟩
    have ready : result ≠ .outOfFuel := by simpa only [he] using hne
    rw [applyFunc_fuel_mono_all hk he ready]

private theorem observationFuelMono {p : Program} {initial : Heap × Ref}
    {k k' : Nat} {entry : String} {args : List Val}
    {check : EResult → Bool} (hk : k ≤ k') (rejectsFuel : check .outOfFuel = false)
    (small : check (runSource p initial k entry args) = true) :
    check (runSource p initial k' entry args) = true := by
  have ready : runSource p initial k entry args ≠ .outOfFuel := by
    intro exhausted
    rw [exhausted, rejectsFuel] at small
    contradiction
  rw [runSourceFuelMono hk ready]
  exact small
'''


def observation_proof(call, check):
    _, entry, arguments = call.split('"', 2)
    return (f"example : ({check}) ({call}) = true := by\n"
            "  rw [initialGlobals_correct]\n"
            f"  exact observationFuelMono (p := program) (initial := initialGlobalsLiteral) (entry := {json.dumps(entry)}) "
            f"(args := {arguments.strip()}) (check := {check}) "
            "(k := 64) (k' := 500) (by decide) (by rfl) (by decide +kernel)\n")


def test_generator_expression_metadata_separates_first_iterable_and_cells():
    metadata = _decode('''
def probe(values, offset):
    plain = (x + 1 for x in values)
    captured = (x + offset for x in values)
    return plain, captured
''')["genexpressions"]
    assert metadata["3:13"]["captures"] == []
    assert metadata["4:16"]["captures"] == ["offset"]


def test_generator_expression_body_stays_in_source_coverage():
    source = [{"name": "probe", "params": [], "body": node("ret", e=node(
        "genExpr", sink="tmp", generator={"locals": ["x"], "captures": []},
        body=node("forIn", x="x", e=node("listE", items=[]), body=node("exprS", e=node(
            "mcall", recv=name("tmp"), m="append", args=[node("hole", label="probe:body")])))))}]
    result = lower_generators(source)
    assert len(result) == len(source)
    assert result[0]["generatorHelpers"]
    assert [item["label"] for item in walk(result[0]["analysisBody"])
            if item.get("k") == "hole"] == ["probe:body"]
    assert not any(item.get("k") in ("genExpr", "yieldS") for item in walk(result))


def test_reports_count_lowering_refusals_without_counting_helpers(tmp_path, differential):
    import lang_matrix
    from generator_lowering import analysis_functions
    functions = [
        {"name": "plain", "file": "m.py", "params": [],
         "body": node("ret", e=node("int", v="1"))},
        {"name": "captured", "file": "m.py", "params": [],
         "generator": {"locals": [], "captures": ["cell"], "parameters": []},
         "body": node("yieldS", e=name("cell"))},
        {"name": "body_hole", "file": "m.py", "params": [],
         "generator": {"locals": [], "captures": [], "parameters": []},
         "body": node("yieldS", e=node("hole", label="source:unknown"))}]
    path = tmp_path / "ast.json"
    path.write_text(json.dumps(functions))
    report = lang_matrix.analyse(path)
    assert report["funcs"] == 3
    assert report["hole_free"] == 1
    assert report["causes"] == {"generator:free-variable-cells": 1, "source:unknown": 1}
    candidates = differential.python_sampling_candidates(analysis_functions(functions))
    assert [function["name"] for function in candidates] == ["plain"]


@pytest.mark.parametrize("expression", [False, True])
def test_implicit_iteration_ignores_shadowed_builtin_names(tmp_path, numeric_env, expression):
    # CPython's for statement and generator machinery use slots, not the globals
    # named iter/next. Explicit calls to those globals still have their source meaning.
    functions = [
        {"name": "iter", "params": ["value"], "body": node("ret", e=node("int", v="99"))},
        {"name": "next", "params": ["value"], "body": node("ret", e=node("int", v="88"))},
        {"name": "values", "params": [],
         "generator": {"locals": ["x"], "captures": [], "parameters": []},
         "body": node("forIn", x="x", e=node("listE", items=[node("int", v="1"), node("int", v="2")]),
                      body=node("yieldS", e=name("x")))},
        {"name": "probe", "params": [], "body": seq(
            node("assign", x="generator", e=node("call", f="values", args=[])),
            node("ret", e=node("binop", op="+", a=node("binop", op="*",
                a=node("mcall", recv=name("generator"), m="__next__", args=[]), b=node("int", v="10")),
                b=node("mcall", recv=name("generator"), m="__next__", args=[]))))}]
    if expression:
        loop = functions[2]["body"]
        loop["body"] = node("exprS", e=node("mcall", recv=name("tmp"), m="append", args=[name("x")]))
        functions[2] = {"name": "values", "params": [], "body": node("ret", e=node(
            "genExpr", sink="tmp", generator={"locals": ["x"], "captures": []}, body=loop))}
    lowered = lower_generators(functions)
    helpers = [helper for function in lowered for helper in function.get("generatorHelpers", [])]
    all_functions = lowered + helpers
    code = "import Autoform.Lang.Core.Semantics\nopen Autoform.Core\n"
    code += "set_option maxRecDepth 10000\nset_option maxHeartbeats 0\n"
    for index, function in enumerate(all_functions):
        code += "\n".join(render_func(function, "function" + str(index))) + "\n"
    code += "def probeProgram : Program := { funcs := [" + ", ".join(
        "function" + str(i) for i in range(len(lowered))) + "], auxiliaryFuncs := [" + ", ".join(
        "function" + str(i) for i in range(len(lowered), len(all_functions))) + "] }\n"
    code += ('example : (match runFunc probeProgram 300 "probe" [] with '
             '| .val (.int 12) => true | _ => false) = true := by decide +kernel\n')
    path = tmp_path / "ShadowedIteration.lean"
    path.write_text(code)
    run(["lake", "env", "lean", path], ROOT, numeric_env)


def test_generator_expressions_source(tmp_path, numeric_env):
    if not os.environ.get("AUTOFORM_TEST_JOERN"):
        pytest.skip("set AUTOFORM_TEST_JOERN=1 for actual source generator expressions")
    joern = Path(os.environ.get("JOERN_HOME", Path.home() / "joern"))
    if (joern / "joern-cli").is_dir():
        joern /= "joern-cli"
    source = ROOT / "examples/python_control/generator_expressions.py"
    spec = importlib.util.spec_from_file_location("genexpr_probes", source)
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    expected = [getattr(probes, name)(2) for name in CASES]
    src = tmp_path / "src"
    src.mkdir()
    (src / source.name).write_text(source.read_text())
    run([joern / "joern-parse", src, "--language", "PYTHONSRC", "--output", "cpg.bin"],
        tmp_path, numeric_env, timeout=600)
    run([joern / "joern", "--script", ROOT / "cartographer/export_ast.sc",
         "--param", "cpgPath=cpg.bin", "--param", "out=ast.json"], tmp_path, numeric_env, timeout=600)
    functions = json.loads((tmp_path / "ast.json").read_text())
    lowered = lower_generators(functions)
    assert len(lowered) == len(functions)
    model = tmp_path / "Model.lean"
    run([sys.executable, ROOT / "cartographer/render_lean.py", tmp_path / "ast.json", model, "GenExpr"],
        ROOT, numeric_env)
    header = model.read_text() + "\nopen Autoform.Core Autoform.Generated.GenExpr\n"
    header += SOURCE_RUNTIME
    calls = [f'runSource program initialGlobals 500 "generator_expressions.py:<module>.{name}" [.int 2]' for name in CASES]
    driver = header + "def main : IO Unit := do\n"
    for name, call in zip(CASES, calls):
        driver += f'''  match {call} with
  | .val (.int n) => IO.println n
  | other => throw (IO.userError ({json.dumps(name + ': ')} ++ reprStr other))
'''
    # Native evaluation proposes a reusable initial state. The equality below is
    # checked by the kernel before that proposal can support any observation.
    driver += SOURCE_STATE_OUTPUT
    (tmp_path / "Check.lean").write_text(driver)
    observed = run(["lake", "env", "lean", "--run", tmp_path / "Check.lean"], ROOT, numeric_env, timeout=600)
    header, lines = stage_source_initial_state(header, observed)
    assert [int(value) for value in lines] == expected
    proofs = ""
    for call, result in zip(calls, expected):
        proofs += observation_proof(call,
            f"fun result => match result with | .val (.int n) => n == ({result} : Int) | _ => false")
    for name, label in [("captured_cell", "genexpr:free-variable-cells"),
                        ("custom_length_hint", "iterator:length-hint"),
                        ("floating_sum", "iterator:sum-type"),
                        ("nested_range", "call:range")]:
        proofs += observation_proof(
            f'runSource program initialGlobals 500 "generator_expressions.py:<module>.{name}" [.int 2]',
            f'fun result => match result with | .hole {json.dumps(label)} => true | _ => false')
    (tmp_path / "Proofs.lean").write_text("import Autoform.FuelMono\n" + header + PROOF_SUPPORT + proofs)
    run(["lake", "env", "lean", tmp_path / "Proofs.lean"], ROOT, numeric_env, timeout=900)
