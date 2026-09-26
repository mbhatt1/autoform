"""Prove actual CPython heap effects after source translation, including aliasing."""
import importlib.util
import json
import os
from pathlib import Path
import sys

import pytest

from conftest import SCRIPTS, load
from test_source_numeric import ROOT, numeric_env, run


@pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_JOERN') != '1',
                    reason='set AUTOFORM_TEST_JOERN=1 for source heap observations')
def test_native_heap_effects_source(tmp_path, numeric_env, differential, monkeypatch):
    source = ROOT / 'examples/python_control/heap_effects.py'
    folder = tmp_path / 'source'
    folder.mkdir()
    copied = folder / source.name
    copied.write_bytes(source.read_bytes())
    joern = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (joern / 'joern-cli').is_dir():
        joern /= 'joern-cli'
    run([joern / 'joern-parse', folder, '--language', 'PYTHONSRC', '--output', 'cpg.bin'],
        tmp_path, numeric_env, timeout=600)
    run([joern / 'joern', '--script', ROOT / 'cartographer/export_ast.sc',
         '--param', 'cpgPath=cpg.bin', '--param', 'out=ast.json'],
        tmp_path, numeric_env, timeout=600)
    funcs = json.loads((tmp_path / 'ast.json').read_text())
    model = tmp_path / 'Model.lean'
    run([sys.executable, ROOT / 'cartographer/render_lean.py', tmp_path / 'ast.json', model,
         'HeapEffectsSource'], ROOT, numeric_env)

    spec = importlib.util.spec_from_file_location('heap_effect_probes', copied)
    native = importlib.util.module_from_spec(spec)
    monkeypatch.setitem(sys.modules, spec.name, native)
    spec.loader.exec_module(native)
    identities = differential.class_identity_index(funcs, folder)
    records = []

    def observe(name, fn, slf, args):
        enc = differential.GraphEncoder(identities)
        receiver = enc.enc(slf) if slf is not None else None
        encoded = [enc.enc(v) for v in args]
        enc.freeze()
        try:
            result = fn(*args) if slf is None else fn(slf, *args)
        except ValueError:
            outcome = ('exn', 'ValueError')
        else:
            outcome = ('val', enc.enc_result(result))
        records.append(differential.finish_record(enc, dict(
            name='heap_effects.py:<module>.' + name, self=receiver, args=encoded,
            outcome=outcome)))

    observe('Node.__init__', native.Node.__init__, object.__new__(native.Node), [2])
    node, detached = native.Node(1), native.Node(2)
    node.next = detached
    observe('Node.unlink', native.Node.unlink, node, [])
    observe('Node.unlink', native.Node.unlink, node, [])
    shared = [1]
    observe('append_alias', native.append_alias, None, [shared, shared])
    observe('fresh_cycle', native.fresh_cycle, None, [3])
    observe('detach', native.detach, None, [{'item': [1]}])
    observe('Appender.__init__', native.Appender.__init__, object.__new__(native.Appender), [])
    appender = native.Appender()
    observe('Appender.append', native.Appender.append, appender, [5])
    observe('detach', native.detach, None, [{'item': appender}])
    observe('mutate_then_raise', native.mutate_then_raise, None, [[1]])
    observe('fresh_shared', native.fresh_shared, None, [7])

    monkeypatch.setenv('AUTOFORM_NO_REEXEC', '1')
    synth = load(str(Path(SCRIPTS) / 'synth_specs.py'), 'af_source_heap_synth')
    code = model.read_text().replace('import Autoform.Lang.Core.Semantics',
                                     'import Autoform.SpecsGen.Basis')
    code += '''
open Autoform.Core Autoform.SpecsGen Autoform.Generated.HeapEffectsSource
set_option maxRecDepth 20000
set_option maxHeartbeats 0
private def gp : Heap × Ref := initGlobals program 300 moduleInits
private def h0 : Heap := gp.1
private def base : Nat := h0.length
private def ctx : Ctx :=
  { dialect := program.dialect, table := program.table, globals := gp.2,
    builtinBases := program.builtinBases, properties := program.properties,
    excClasses := program.excClasses, classDecls := program.classDecls }
'''
    for index, record in enumerate(records):
        fn = synth.lean_ident(record['name'])
        code += f'private def obs{index} : Obs := {synth.obs_lit(record)}\n'
        code += f'example : lawConform ctx 128 {fn} obs{index} = true := by decide +kernel\n'
    # Omit unlink's body while keeping its None return: the post-state must kill it.
    fn = synth.lean_ident(records[1]['name'])
    code += (f'example : lawConform ctx 128 {{ {fn} with body := .skip }} obs1 = false '
             ':= by decide +kernel\n')
    path = tmp_path / 'HeapEffectsProofs.lean'
    path.write_text(code)
    run(['lake', 'build', 'Autoform.SpecsGen.Basis'], ROOT, numeric_env, timeout=600)
    run(['lake', 'env', 'lean', path], ROOT, numeric_env, timeout=900)
