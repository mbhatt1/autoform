"""Source observations and kernel proofs for effectful truth tests in consumers."""
import importlib.util
import json
import os
from pathlib import Path
import sys

import pytest

from test_source_numeric import ROOT, numeric_env, run


SUBJECTS = ('any_generator', 'all_generator', 'any_nested', 'all_nested', 'list_objects',
            'tuple_objects', 'length_objects', 'boolean_length', 'negative_length',
            'invalid_truth', 'raised_truth_leaves_generator_open', 'mutation_during_truth',
            'plain_containers', 'invalid_iterable')


def test_private_truth_unboxes_containers_and_preserves_named_gaps(tmp_path, numeric_env):
    path = tmp_path / 'Truth.lean'
    path.write_text('''import Autoform.Lang.Core.Semantics
open Autoform.Core
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def truthProgram : Program := { funcs := [{ name := "probe", params := [], body := .ret (.call "any" [.tupleE [.listE [], .dictE []]]) }] }
example : (match runFunc truthProgram 50 "probe" [] with
    | .val (.bool false) => true | _ => false) = true := by decide +kernel
example : Iteration.truthValue [{cls := "Ordinary", fields := []}] (.ref 0) =
    .hole "truth:unresolved-protocol" := by rfl
example : builtinDunderResult "bool" "__len__" (.int (-1)) = .exn (.str "ValueError") := by rfl
example : builtinDunderResult "bool" "__len__" (.bool true) = .val (.bool true) := by rfl
''')
    run(['lake', 'env', 'lean', path], ROOT, numeric_env)


def test_truth_consumers_source(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for source truth consumers')
    source = ROOT / 'examples/python_control/truth_consumers.py'
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
    run([sys.executable, ROOT / 'cartographer/render_lean.py', tmp_path / 'ast.json', model, 'TruthConsumers'],
        ROOT, numeric_env)
    header = model.read_text() + '\nopen Autoform.Core Autoform.Generated.TruthConsumers\n'
    calls = [f'runFunc program 200 "truth_consumers.py:<module>.{name}" [.int 2]' for name in SUBJECTS]
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
    for name, label in [('unknown_truth', 'truth:unresolved-protocol'),
                        ('platform_length', 'truth:length-platform')]:
        proofs += (f'example : (match runFunc program 200 "truth_consumers.py:<module>.{name}" [.int 2] '
                   f'with | .hole {json.dumps(label)} => true | _ => false) = true := by decide +kernel\n')
    (tmp_path / 'Proofs.lean').write_text(proofs)
    run(['lake', 'env', 'lean', tmp_path / 'Proofs.lean'], ROOT, numeric_env, timeout=1200)
