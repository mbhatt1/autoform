"""Compare saved builtin methods and lifted-argument lookup order with CPython."""
import importlib.util
import json
import os
from pathlib import Path
import sys

import pytest

from test_source_numeric import SOURCE_RUNTIME, ROOT, numeric_env, run


SUBJECTS = (
    'property_comprehension', 'property_keyword', 'saved_field_comprehension',
    'saved_method_walrus', 'missing_comprehension', 'raising_comprehension',
    'saved_append', 'append_comprehension', 'saved_pop', 'saved_get',
    'saved_clear', 'saved_next',
)


def test_bound_calls_source(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for source bound calls')
    source = ROOT / 'examples/python_control/bound_calls.py'
    spec = importlib.util.spec_from_file_location('lookup_probes', source)
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
    run([sys.executable, ROOT / 'cartographer/render_lean.py', tmp_path / 'ast.json', model, 'BoundCalls'],
        ROOT, numeric_env)
    header = model.read_text() + '\nopen Autoform.Core Autoform.Generated.BoundCalls\n'
    header += SOURCE_RUNTIME
    calls = [f'runSource program initialGlobals 150 "bound_calls.py:<module>.{name}" [.int 2]' for name in SUBJECTS]
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
    (tmp_path / 'Proofs.lean').write_text(proofs)
    run(['lake', 'env', 'lean', tmp_path / 'Proofs.lean'], ROOT, numeric_env, timeout=900)

