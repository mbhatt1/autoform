"""Compare slot storage and inheritance with CPython."""
import importlib.util
import json
import os
from pathlib import Path
import sys

import pytest

from test_source_numeric import ROOT, numeric_env, run


def test_slots_source(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for slot source probes')
    source = ROOT / 'examples/python_control/slots.py'
    spec = importlib.util.spec_from_file_location('slots_probes', source)
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    subjects = ('slot_read', 'slot_write', 'private_slot', 'inherited_slot',
                'subclass_dictionary', 'explicit_dictionary', 'empty_slot_mixin',
                'string_slot', 'missing_slot', 'rejected_new_field',
                'rejected_method_shadow', 'slot_property')
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
         'Slots'], ROOT, numeric_env)
    header = model.read_text() + '\nopen Autoform.Core Autoform.Generated.Slots\n'
    calls = [f'runMain program 200 moduleInits "slots.py:<module>.{name}" [.int 2]'
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


def test_slot_storage_and_layout_kernel(tmp_path, numeric_env):
    path = tmp_path / 'SlotBoundaries.lean'
    path.write_text(r'''import Autoform.Lang.Core.Semantics
open Autoform.Core
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def declarations : List ClassDecl :=
  [{ name := "Base", shortName := "Base", slots := some ["value"],
     attributes := [("value", .slot "<slot>Base.value")] },
   { name := "Empty", shortName := "Empty", slots := some [] },
   { name := "Child", shortName := "Child", bases := ["Base", "Empty"], slots := some [] },
   { name := "DictChild", shortName := "DictChild", bases := ["Base"] },
   { name := "ExplicitDict", shortName := "ExplicitDict", bases := ["Base"],
     slots := some ["__dict__"] },
   { name := "Other", shortName := "Other", slots := some ["other"] },
   { name := "Bad", shortName := "Bad", bases := ["Base", "Other"] },
   { name := "DuplicateDict", shortName := "DuplicateDict", bases := ["DictChild"],
     slots := some ["__dict__"] },
   { name := "Shadow", shortName := "Shadow", bases := ["Base"],
     attributes := [("value", .method "Shadow.value")] }]
def ctx : Ctx := { table := [], dialect := .python, classDecls := declarations }
def object : Obj := { cls := "DictChild", fields := [("value", .int 99),
    ("<slot>Base.value", .int 7)] }
example : (match ctx.readSlot object "value" with
    | some (.val (.int 7)) => true | _ => false) = true := by decide +kernel
example : (match ctx.readSlot { object with fields := [("value", .int 99)] } "value" with
    | some (.exn (.str "AttributeError")) => true | _ => false) = true := by decide +kernel
example : ctx.readSlot { object with cls := "Shadow" } "value" = none := by decide +kernel
example : ClassHierarchy.allowsDict declarations "Child" = false := by decide +kernel
example : ClassHierarchy.allowsDict declarations "DictChild" = true := by decide +kernel
example : ClassHierarchy.allowsDict declarations "ExplicitDict" = true := by decide +kernel
example : (ClassHierarchy.linearize declarations "Child" ==
    .complete ["Child", "Base", "Empty", "__builtin.object"]) = true := by decide +kernel
example : (ClassHierarchy.linearize declarations "Bad" ==
    .invalid "class-layout:incompatible-slotted-bases") = true := by decide +kernel
example : (ClassHierarchy.linearize declarations "DuplicateDict" ==
    .invalid "class-layout:duplicate-dict-slot") = true := by decide +kernel
''')
    run(['lake', 'env', 'lean', path], ROOT, numeric_env, timeout=120)
