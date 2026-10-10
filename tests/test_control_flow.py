"""Compare abrupt control-flow state with CPython, then check it in Lean's kernel."""
import importlib.util
import json
import os
from pathlib import Path
import sys

import pytest

from test_source_numeric import (ROOT, SOURCE_RUNTIME, SOURCE_STATE_OUTPUT,
                                 numeric_env, run, stage_source_initial_state)

SOURCE = ROOT / 'examples/python_control/control.py'
SUBJECTS = ['caught_raise', 'caught_expression', 'final_return', 'final_pending_return',
            'final_break', 'final_continue', 'final_exception', 'final_nested_return',
            'caller_environment', 'final_replaces_exception', 'final_raises']


def native_cases():
    spec = importlib.util.spec_from_file_location('native_control_fixture', SOURCE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return [(name, value, getattr(module, name)(value))
            for name in SUBJECTS for value in (-7, 0, 13)]


def test_finalizers_cannot_hide_incomplete_execution(tmp_path, numeric_env):
    run(['lake', 'build', 'Autoform.FuelMono'], ROOT, numeric_env, timeout=600)
    path = tmp_path / 'FinalizerSafety.lean'
    path.write_text('''import Autoform.FuelMono
open Autoform.Core
def ctx : Ctx := { table := [], dialect := .python }
def incomplete : Func := { name := "incomplete", params := [], body :=
  (.tryFinally (.loop (.lit (.bool true)) .skip) (.ret (.lit (.int 1)))) }
def unsupported : Func := { name := "unsupported", params := [], body :=
  (.tryFinally (.hole "untranslated") (.ret (.lit (.int 1)))) }
def complete : Func := { name := "complete", params := [], body :=
  (.tryFinally (.seq (.assign "x" (.lit (.int 13))) (.raise (.lit (.str "ValueError"))))
    (.ret (.name "x"))) }
example : (applyFunc ctx 32 [] incomplete none [] []).2 = .outOfFuel := by rfl
example : (applyFunc ctx 32 [] unsupported none [] []).2 = .hole "untranslated" := by rfl
example : applyFunc ctx 32 [] complete none [] [] = ([], .val (.int 13)) := by rfl
example (fuel : Nat) (hf : 32 ≤ fuel) :
    applyFunc ctx fuel [] complete none [] [] = ([], .val (.int 13)) := by
  exact applyFunc_fuel_mono_all hf (by rfl) (by simp)
example (fuel : Nat) (hf : 32 ≤ fuel) :
    applyFunc ctx fuel [] unsupported none [] [] = ([], .hole "untranslated") := by
  exact applyFunc_fuel_mono_all hf (by rfl) (by simp)
example : fuelMonoExclusions = [] := by rfl
''')
    run(['lake', 'env', 'lean', path], ROOT, numeric_env)


def test_exported_control_flow_matches_cpython(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for source control-flow translation')
    joern = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (joern / 'joern-cli').is_dir():
        joern /= 'joern-cli'
    source = tmp_path / 'source'
    source.mkdir()
    (source / SOURCE.name).write_bytes(SOURCE.read_bytes())
    run([joern / 'joern-parse', source, '--language', 'PYTHONSRC', '--output', 'cpg.bin'],
        tmp_path, numeric_env, timeout=600)
    run([joern / 'joern', '--script', ROOT / 'cartographer/export_ast.sc',
         '--param', 'cpgPath=cpg.bin', '--param', 'out=ast.json'], tmp_path, numeric_env, timeout=600)
    model = tmp_path / 'Model.lean'
    run([sys.executable, ROOT / 'cartographer/render_lean.py', tmp_path / 'ast.json',
         model, 'Control'], ROOT, numeric_env)
    header = model.read_text() + '\nopen Autoform.Core Autoform.Generated.Control\n'
    header += SOURCE_RUNTIME
    cases = native_cases()
    calls = [f'runSource program initialGlobals 256 "control.py:<module>.{name}" [.int ({value})]'
             for name, value, _ in cases]
    driver = header + 'def main : IO Unit := do\n'
    for call in calls:
        driver += f'''  match {call} with
  | .val (.int value) => IO.println value
  | other => IO.println ("unexpected:" ++ reprStr other)
'''
    driver += SOURCE_STATE_OUTPUT
    (tmp_path / 'Observe.lean').write_text(driver)
    output = run(['lake', 'env', 'lean', '--run', tmp_path / 'Observe.lean'], ROOT, numeric_env)
    header, observed = stage_source_initial_state(header, output)
    expected = [str(value) for _, _, value in cases]
    mismatches = [dict(subject=name, argument=arg, native=want, model=actual)
                  for (name, arg, want), actual in zip(cases, observed) if str(want) != actual]
    (tmp_path / 'native-comparison.json').write_text(json.dumps(dict(
        cases=len(cases), mismatches=mismatches, observed=observed), indent=2) + '\n')
    assert observed == expected, json.dumps(mismatches, indent=2)
    # Keep observations independent: expected integers above come from real CPython.
    proofs = header + '\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
    for call, (_, _, expected) in zip(calls, cases):
        proofs += (f'example : (match {call} with\n'
                   f'  | .val (.int value) => value == ({expected} : Int)\n'
                   '  | _ => false) = true := by\n'
                   '  rw [initialGlobals_correct]\n'
                   '  first | decide +kernel | fail "native control-flow result not established"\n')
    (tmp_path / 'Proofs.lean').write_text(proofs)
    run(['lake', 'env', 'lean', tmp_path / 'Proofs.lean'], ROOT, numeric_env)
