"""Compare Python attribute lookup with source execution and kernel proofs."""
import importlib.util
import json
import os
from pathlib import Path
import sys

import pytest

from test_source_numeric import ROOT, numeric_env, run


SUBJECTS = (
    'unrelated_method', 'shadow_method', 'saved_field', 'saved_method',
    'property_order', 'property_exception', 'missing_before_argument',
    'static_method', 'class_method', 'captured_bound_method',
    'captured_method_call', 'captured_property', 'captured_static_method',
)


def test_object_lookup_source(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for source attribute lookup')
    source = ROOT / 'examples/python_control/object_lookup.py'
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
    run([sys.executable, ROOT / 'cartographer/render_lean.py', tmp_path / 'ast.json', model, 'ObjectLookup'],
        ROOT, numeric_env)
    header = model.read_text() + '\nopen Autoform.Core Autoform.Generated.ObjectLookup\n'
    calls = [f'runFunc program 150 "object_lookup.py:<module>.{name}" [.int 2]' for name in SUBJECTS]
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


def test_property_precedes_instance_field_kernel(tmp_path, numeric_env):
    class Probe:
        @property
        def value(self):
            self.trace += 1
            return 31

    obj = Probe()
    obj.trace = 0
    obj.__dict__['value'] = 99
    expected = (obj.value, obj.trace)
    assert expected == (31, 1)
    code = r'''import Autoform.Lang.Core.Semantics
open Autoform.Core
set_option maxRecDepth 10000
set_option maxHeartbeats 0
private def getter : Func :=
  { name := "probe.py:<module>.Probe.value", params := [],
    body := .seq
      (.setField (.name "self") "trace"
        (.binop "+" (.field (.name "self") "trace") (.lit (.int 1))))
      (.ret (.lit (.int 31))) }
private def ctx : Ctx :=
  { dialect := .python, table := [(getter.name, getter)], properties := [("Probe", "value")] }
private def h : Heap :=
  [{ cls := "Probe", fields := [("value", .int 99), ("trace", .int 0)] }]
private def result := evalExpr ctx 30 h [("obj", .ref 0)] (.field (.name "obj") "value")
example : (match result.2 with | .val (.int n) => n == EXPECTED | _ => false) = true := by decide +kernel
example : (match result.1.getField 0 "trace" with | .int n => n == TRACE | _ => false) = true := by decide +kernel
'''.replace('EXPECTED', str(expected[0])).replace('TRACE', str(expected[1]))
    path = tmp_path / 'PropertyShadow.lean'
    path.write_text(code)
    run(['lake', 'env', 'lean', path], ROOT, numeric_env)


def test_container_subclass_method_kernel(tmp_path, numeric_env):
    class UserList(list):
        def append(self, value):
            return value + 42

    obj = UserList([7])
    expected = obj.append(3)
    assert obj == [7]
    code = r'''import Autoform.Lang.Core.Semantics
open Autoform.Core
set_option maxRecDepth 10000
private def method : Func :=
  { name := "probe.py:<module>.UserList.append", params := ["value"],
    body := .ret (.binop "+" (.name "value") (.lit (.int 42))) }
private def ctx : Ctx := { dialect := .python, table := [(method.name, method)] }
private def h : Heap := [{ cls := "UserList", fields := [], payload := .list [.int 7] }]
private def result := evalExpr ctx 30 h [("obj", .ref 0)]
  (.mcall (.name "obj") "append" [.lit (.int 3)])
example : (match result.2 with | .val (.int n) => n == EXPECTED | _ => false) = true := by decide +kernel
example : (match result.1.payload 0 with | .list [.int 7] => true | _ => false) = true := by decide +kernel
'''.replace('EXPECTED', str(expected))
    path = tmp_path / 'ContainerSubclass.lean'
    path.write_text(code)
    run(['lake', 'env', 'lean', path], ROOT, numeric_env)
