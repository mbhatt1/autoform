"""Compare lexical callbacks with CPython, including callee evaluation order."""
import ast
import importlib.util
import json
import os
from pathlib import Path
import sys

import pytest

from test_python_signatures import _decode
from test_source_numeric import ROOT, numeric_env, run


SOURCE = ROOT / 'examples/python_control/local_callables.py'
SUBJECTS = (
    'saved_classmethod', 'saved_instance_classmethod', 'saved_method',
    'parameter_collision', 'constructor_collision', 'captured_method',
    'nonlocal_method', 'saved_before_walrus', 'lifted_keyword',
    'local_function', 'local_class', 'builtin_collision', 'callback_factory',
)


def test_python_callable_scope_metadata():
    source = '''
class Base:
    pass
def probe(callback):
    Base = callback
    Base(1)
    callback(2)
    def inner():
        nonlocal callback
        return callback(3)
    return inner()
def known_class():
    class Local:
        pass
    return Local()
def global_call():
    global Base
    return Base()
class Outer:
    def method(self):
        class Local:
            pass
        return Local()
'''
    calls = _decode(source)['value_calls']
    selected = [ast.get_source_segment(source, node) for node in ast.walk(ast.parse(source))
                if isinstance(node, ast.Call)
                and f'{node.lineno}:{node.col_offset + 1}' in calls]
    assert sorted(selected) == ['Base(1)', 'callback(2)', 'callback(3)', 'inner()']


def test_local_callables_source(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for source callback comparisons')
    spec = importlib.util.spec_from_file_location('local_callable_probes', SOURCE)
    native = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(native)
    expected = [getattr(native, name)(2) for name in SUBJECTS]
    folder = tmp_path / 'source'
    folder.mkdir()
    (folder / SOURCE.name).write_bytes(SOURCE.read_bytes())
    joern = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (joern / 'joern-cli').is_dir():
        joern /= 'joern-cli'
    run([joern / 'joern-parse', folder, '--language', 'PYTHONSRC', '--output', 'cpg.bin'],
        tmp_path, numeric_env, timeout=600)
    run([joern / 'joern', '--script', ROOT / 'cartographer/export_ast.sc',
         '--param', 'cpgPath=cpg.bin', '--param', 'out=ast.json'], tmp_path, numeric_env, timeout=600)
    model = tmp_path / 'Model.lean'
    run([sys.executable, ROOT / 'cartographer/render_lean.py', tmp_path / 'ast.json', model,
         'LocalCallables'], ROOT, numeric_env)
    header = model.read_text() + '\nopen Autoform.Core Autoform.Generated.LocalCallables\n'
    calls = [f'runMain program 220 moduleInits "local_callables.py:<module>.{name}" [.int 2]'
             for name in SUBJECTS]
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
