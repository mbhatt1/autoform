"""Compare recovered C3 lookup, descriptors and construction with CPython."""
import importlib.util
import json
import os
from pathlib import Path
import sys

import pytest

from test_source_numeric import ROOT, numeric_env, run


def test_inheritance_source(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for inheritance source probes')
    source = ROOT / 'examples/python_control/inheritance.py'
    spec = importlib.util.spec_from_file_location('inheritance_probes', source)
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    subjects = ('diamond_method', 'saved_inherited_method', 'inherited_property',
                'first_namespace_before_descriptor', 'inherited_property_is_readonly',
                'saved_class_receiver', 'saved_instance_class_receiver', 'inherited_static',
                'bad_initializer_return', 'default_initializer_arguments',
                'missing_class_attribute')
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
         'Inheritance'], ROOT, numeric_env)
    header = model.read_text() + '\nopen Autoform.Core Autoform.Generated.Inheritance\n'
    calls = [f'runMain program 200 moduleInits "inheritance.py:<module>.{name}" [.int 2]'
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



def test_hierarchy_boundaries_kernel(tmp_path, numeric_env):
    path = tmp_path / 'ClassHierarchyBoundaries.lean'
    path.write_text(r'''import Autoform.Lang.Core.ClassHierarchy
open Autoform.Core
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def graph : List ClassDecl :=
  [{ name := "m.Root", shortName := "Root" },
   { name := "m.Left", shortName := "Left", bases := ["m.Root"] },
   { name := "m.Right", shortName := "Right", bases := ["m.Root"],
     attributes := [("value", .method "m.Right.value")] },
   { name := "m.Diamond", shortName := "Diamond", bases := ["m.Left", "m.Right"] }]
example : (ClassHierarchy.linearize graph "m.Diamond" ==
    .complete ["m.Diamond", "m.Left", "m.Right", "m.Root", "__builtin.object"]) = true := by
  decide +kernel
example : (ClassHierarchy.lookup graph "Diamond" "value" ==
    .found "m.Right" (.method "m.Right.value")) = true := by decide +kernel
example : (ClassHierarchy.lookup graph "Diamond" "absent" == .absent) = true := by
  decide +kernel
def inconsistent : List ClassDecl :=
  [{ name := "A", shortName := "A" }, { name := "B", shortName := "B" },
   { name := "X", shortName := "X", bases := ["A", "B"] },
   { name := "Y", shortName := "Y", bases := ["B", "A"] },
   { name := "Z", shortName := "Z", bases := ["X", "Y"],
     attributes := [("own", .method "Z.own")] }]
example : (ClassHierarchy.lookup inconsistent "Z" "own" ==
    .blocked "class-hierarchy:inconsistent-mro") = true := by decide +kernel
def unresolved : List ClassDecl :=
  [{ name := "D", shortName := "D", bases := ["External"],
     attributes := [("own", .method "D.own")] }]
example : (ClassHierarchy.lookup unresolved "D" "own" ==
    .blocked "class-hierarchy:unresolved-base:External") = true := by decide +kernel
def duplicates : List ClassDecl :=
  [{ name := "one.Same", shortName := "Same" },
   { name := "two.Same", shortName := "Same" }]
example : ClassHierarchy.canonicalName duplicates "Same" = none := by decide +kernel
example : ClassHierarchy.canonicalName duplicates "two.Same" = some "two.Same" := by
  decide +kernel
example : (ClassHierarchy.linearize
    [{ name := "A", shortName := "A", bases := ["A"] }] "A" ==
    .invalid "class-hierarchy:cycle-or-depth") = true := by decide +kernel
example : (ClassHierarchy.linearize
    [{ name := "A", shortName := "A", bases := ["__builtin.object", "__builtin.object"] }] "A" ==
    .invalid "class-hierarchy:duplicate-base") = true := by decide +kernel
''')
    run(['lake', 'env', 'lean', path], ROOT, numeric_env, timeout=120)
