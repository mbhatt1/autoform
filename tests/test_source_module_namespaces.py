"""A function and its module's attributes must share one defining namespace."""
import ast
import importlib
import json
import os
from pathlib import Path
import shutil
import sys

import pytest

from test_python_raises import lean_value
from test_python_signatures import _decode
from test_source_numeric import ROOT, numeric_env, run


def test_global_name_metadata_distinguishes_locals_captures_and_builtins():
    source = '''
value = 1
def outer(local):
    captured = 2
    def inner():
        return value + local + captured + len([])
    return inner()
def write():
    global value
    value += 1
    return value
'''
    metadata = _decode(source)
    selected = [node.id for node in ast.walk(ast.parse(source))
                if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
                and f'{node.lineno}:{node.col_offset + 1}' in metadata['global_names']]
    assert selected == ['value', 'value']
    assert not metadata['global_value_calls']


def test_module_namespaces_source(tmp_path, numeric_env, monkeypatch):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for module namespace comparisons')
    folder = tmp_path / 'source'
    shutil.copytree(ROOT / 'examples/python_control/module_namespaces', folder)
    subjects = ['observe', 'attribute_store', 'imported_constructors', 'rebound_callable',
                'import_snapshot', 'private_globals']
    monkeypatch.syspath_prepend(str(folder))
    expected = []
    for subject in subjects:
        for name in ('ns_entry', 'ns_left', 'ns_right'):
            monkeypatch.delitem(sys.modules, name, raising=False)
        module = importlib.import_module('ns_entry')
        expected.append(getattr(module, subject)())
    joern = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (joern / 'joern-cli').is_dir():
        joern /= 'joern-cli'
    run([joern / 'joern-parse', folder, '--language', 'PYTHONSRC', '--output', 'cpg.bin'],
        tmp_path, numeric_env, timeout=600)
    run([joern / 'joern', '--script', ROOT / 'cartographer/export_ast.sc',
         '--param', 'cpgPath=cpg.bin', '--param', 'out=ast.json'], tmp_path, numeric_env, timeout=600)
    model = tmp_path / 'Model.lean'
    run([sys.executable, ROOT / 'cartographer/render_lean.py', tmp_path / 'ast.json',
         model, 'ModuleNamespaces'], ROOT, numeric_env)
    code = model.read_text().replace('import Autoform.Lang.Core.Semantics',
                                     'import Autoform.SpecsGen.Basis')
    code += '\nopen Autoform.Core Autoform.SpecsGen Autoform.Generated.ModuleNamespaces\n'
    code += 'set_option maxRecDepth 20000\nset_option maxHeartbeats 0\n'
    code += '''private def observedExactly (got : EResult) (expected : Val) : Bool :=
  match got with
  | .val value => Val.stateEq value expected
  | _ => false
'''
    checks = []
    for subject, value in zip(subjects, expected):
        call = f'runMain program 240 moduleInits "ns_entry.py:<module>.{subject}" []'
        checks.append(f'observedExactly ({call}) ({lean_value(value)})')
    driver = tmp_path / 'Observe.lean'
    driver.write_text(code + 'def main : IO Unit := do\n' +
                      ''.join(f'  IO.println ({check})\n' for check in checks))
    results = run(['lake', 'env', 'lean', '--run', driver], ROOT, numeric_env, timeout=600).splitlines()
    assert results == ['true'] * len(checks), dict(zip(subjects, results))
    for check in checks:
        code += f'example : {check} = true := by decide +kernel\n'
    # `imported_constructors` calls the class VALUES `LeftBox`/`RightBox` that the
    # `from ... import Box as ...` bindings hold; each constructs its own module's
    # `Box`, so the two `.value` reads are compared with CPython like every other subject.
    (tmp_path / 'native.json').write_text(json.dumps(dict(
        compared=dict(zip(subjects, expected))), indent=2)+'\n')
    proof = tmp_path / 'Proofs.lean'
    proof.write_text(code)
    run(['lake', 'env', 'lean', proof], ROOT, numeric_env, timeout=600)
