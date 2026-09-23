"""Source observations and kernel proofs for effectful truth tests in consumers."""
import importlib.util
import json
import os
from pathlib import Path
import sys

import pytest

from test_source_numeric import ROOT, numeric_env, run


SUBJECTS = ('if_statement', 'conditional', 'negate', 'and_value', 'or_value', 'and_short',
            'or_short', 'while_length', 'empty_containers', 'comparison_result',
            'membership_result', 'finalizer', 'boolean_length', 'if_and', 'if_or',
            'if_not_and', 'mixed_condition', 'conditional_condition', 'value_not_and',
            'value_and_chain', 'value_mixed_chain', 'value_or_chain', 'later_truth_test',
            'changing_value_truth', 'changing_condition_truth', 'independent_truth',
            'lifted_value', 'lifted_condition', 'lifted_not', 'lifted_selected_condition',
            'generator_lifted_condition')


def test_truth_conditions_source(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for source truth conditions')
    source = ROOT / 'examples/python_control/truth_conditions.py'
    spec = importlib.util.spec_from_file_location('truth_probes', source)
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    expected = [getattr(probes, name)(2) for name in SUBJECTS]
    folder = tmp_path / 'source'
    folder.mkdir()
    (folder / source.name).write_text(source.read_text())
    joern = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (joern / 'joern-cli').is_dir():
        joern /= 'joern-cli'
    run([joern / 'joern-parse', folder, '--language', 'PYTHONSRC', '--output', 'cpg.bin'],
        tmp_path, numeric_env, timeout=600)
    run([joern / 'joern', '--script', ROOT / 'cartographer/export_ast.sc',
         '--param', 'cpgPath=cpg.bin', '--param', 'out=ast.json'], tmp_path, numeric_env, timeout=600)
    model = tmp_path / 'Model.lean'
    run([sys.executable, ROOT / 'cartographer/render_lean.py', tmp_path / 'ast.json', model, 'TruthConditions'],
        ROOT, numeric_env)
    header = model.read_text() + '\nopen Autoform.Core Autoform.Generated.TruthConditions\n'
    calls = [f'runFunc program 200 "truth_conditions.py:<module>.{name}" [.int 2]' for name in SUBJECTS]
    driver = header + 'def main : IO Unit := do\n'
    for name, call in zip(SUBJECTS, calls):
        driver += f'''  match {call} with
  | .val (.int n) => IO.println n
  | result => throw (IO.userError ({json.dumps(name + ': ')} ++ reprStr result))
'''
    (tmp_path / 'Check.lean').write_text(driver)
    output = run(['lake', 'env', 'lean', '--run', tmp_path / 'Check.lean'], ROOT, numeric_env)
    assert [int(value) for value in output.splitlines()] == expected
    proofs = header
    for call, value in zip(calls, expected):
        proofs += (f'example : (match {call} with | .val (.int n) => n == ({value} : Int) '
                   '| _ => false) = true := by decide +kernel\n')
    for name, label in [('index_length', 'length:index-protocol'),
                        ('index_truth', 'length:index-protocol')]:
        proofs += (f'example : (match runFunc program 200 "truth_conditions.py:<module>.{name}" [.int 2] '
                   f'with | .hole {json.dumps(label)} => true | _ => false) = true := by decide +kernel\n')
    (tmp_path / 'Proofs.lean').write_text(proofs)
    run(['lake', 'env', 'lean', tmp_path / 'Proofs.lean'], ROOT, numeric_env, timeout=1200)
