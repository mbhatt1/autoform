"""Class-value callable attributes retain qualified owners and lexical captures."""
import importlib.util
import json
import os
from pathlib import Path
import sys

import pytest

from test_source_numeric import ROOT, numeric_env, run


def test_class_attributes_source(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for class attribute source probes')
    source = ROOT / 'examples/python_control/class_attributes.py'
    spec = importlib.util.spec_from_file_location('class_attribute_probes', source)
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    subjects = ('saved_static', 'static_identity', 'saved_classmethod',
                'saved_unbound', 'saved_local_static')
    expected = [getattr(probes, name)(2) for name in subjects]
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
    run([sys.executable, ROOT / 'cartographer/render_lean.py', tmp_path / 'ast.json', model,
         'ClassAttributes'], ROOT, numeric_env)
    header = model.read_text() + '\nopen Autoform.Core Autoform.Generated.ClassAttributes\n'
    calls = [f'runMain program 150 moduleInits "class_attributes.py:<module>.{name}" [.int 2]'
             for name in subjects]
    driver = header + 'def main : IO Unit := do\n'
    for name, call in zip(subjects, calls):
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


def test_class_attributes_preserve_owner_and_refuse_descriptors(tmp_path, numeric_env):
    proof = tmp_path / 'ClassAttributeBoundaries.lean'
    proof.write_text('''import Autoform.Lang.Core.Semantics
open Autoform.Core
def first : Func :=
  { name := "first.py:<module>.Same.read", params := []
  , body := .ret (.lit (.int 1)), pythonSignature := some { isMethod := some false } }
def second : Func :=
  { name := "second.py:<module>.Same.read", params := []
  , body := .ret (.lit (.int 2)), pythonSignature := some { isMethod := some false } }
def C : Ctx := { dialect := .python, table := [(first.name, first), (second.name, second)] }
example : (match (evalExpr C 4 [] []
    (.field (.fnref "second.py:<module>.Same<meta>") "read")).2 with
  | .val (.fn name) => name == second.name | _ => false) = true := by decide +kernel
example : (match (evalExpr { C with properties := [("Same", "read")] } 4 [] []
    (.field (.fnref "second.py:<module>.Same<meta>") "read")).2 with
  | .hole label => label == "class-attribute:read:property-descriptor" | _ => false) = true := by
  decide +kernel
example : (match (evalExpr C 4 [] []
    (.field (.fnref "first.py:<module>.Same.read") "read")).2 with
  | .hole label => label == "field:read:non-object" | _ => false) = true := by decide +kernel
example : (match (evalExpr C 4 [] []
    (.field (.fnref "third.py:<module>.Same<meta>") "read")).2 with
  | .hole label => label == "class-attribute:read:unresolved" | _ => false) = true := by
  decide +kernel
''')
    run(['lake', 'env', 'lean', proof], ROOT, numeric_env, timeout=120)
