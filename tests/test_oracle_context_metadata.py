"""Every replay context must preserve property and exception-class semantics."""
import json
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

from conftest import ROOT, SCRIPTS, fn, load
from test_differential_backends import generated_module, _oracle_env, _skip_unless_runnable


PROGRAM = '''namespace Autoform.Generated.ContextMetadata
open Autoform.Core
def getter : Func := { name := "probe.py:<module>.Reader.value", params := [], body := .ret (.lit (.int 31)) }
def reader : Func := { name := "probe.py:<module>.Reader.read", params := [], body := .ret (.field (.name "self") "value") }
def failure : Func := { name := "probe.py:<module>.Reader.fail", params := [], body := .raise (.lit (.str "Marker")) }
def program : Program := { dialect := .python, funcs := [getter, reader, failure], properties := [("Reader", "value")], excClasses := ["Marker"] }
end Autoform.Generated.ContextMetadata
'''


@pytest.mark.parametrize('driver', ['synthesis', 'core_oracle'])
def test_generated_context_executes_properties_and_custom_exceptions(
        tmp_path, monkeypatch, differential, driver):
    env = _oracle_env()
    if not shutil.which('lake', path=env['PATH']):
        pytest.skip('Lean is not installed')
    monkeypatch.setenv('AUTOFORM_NO_REEXEC', '1')
    if driver == 'synthesis':
        module = load(str(Path(SCRIPTS) / 'synth_specs.py'), 'af_synth_metadata')
        text = module.HEADER % ('ContextMetadata', 'ContextMetadata', 'ContextMetadata',
                                20, '[]', '0', 20, 'ContextMetadata')
        text += '''
example : (match (applyFunc C 20 [{ cls := "Reader", fields := [] }] reader (some (.ref 0)) [] []).2
    with | .val (.int n) => n == 31 | _ => false) = true := by decide +kernel
example : (match (applyFunc C 20 [{ cls := "Reader", fields := [] }] failure (some (.ref 0)) [] []).2
    with | .exn (.str s) => s == "Marker" | _ => false) = true := by decide +kernel
end Autoform.SpecsGen.ContextMetadata
'''
    else:
        module = load(str(Path(SCRIPTS) / 'core_oracle.py'), 'af_core_metadata')
        text = module.HEADER.format(mod='ContextMetadata', fuel=20, inits='[]')
        for method, result in [('read', '.val (.int n) => n == 31'),
                               ('fail', '.exn (.str s) => s == "Marker"')]:
            text += (f'\nexample : (match orun {{ idx := 0, objs := [{{ cls := "Reader", fields := [] }}], '
                     f'fn := "probe.py:<module>.Reader.{method}", slf := some (.ref base), '
                     f'args := [], chk := [(0, "Reader")] }} with | {result} '
                     '| _ => false) = true := by decide +kernel\n')
    text = text.replace('import Autoform.Generated.ContextMetadata\n',
                        'import Autoform.Lang.Core.Semantics\n' + PROGRAM)
    path = tmp_path / 'Context.lean'
    path.write_text(text)
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT, env=env,
                            text=True, capture_output=True, timeout=120)
    assert result.returncode == 0, result.stdout + result.stderr


def test_native_oracle_preserves_program_metadata(tmp_path, generated_module):
    _skip_unless_runnable([])
    source = tmp_path / 'source'
    source.mkdir()
    (source / 'probe.py').write_text('''class Marker(Exception):
    pass

class Reader:
    @property
    def value(self):
        return 31

    def read(self):
        return self.value

    def fail(self):
        raise Marker
''')
    funcs = [fn('probe.py:<module>', 'probe.py', classProperties=[['Reader', 'value']],
                exceptionClasses=['Marker'])]
    for name, body in [
        ('value', {'k': 'ret', 'e': {'k': 'int', 'v': 31}}),
        ('read', {'k': 'ret', 'e': {'k': 'field', 'a': {'k': 'name', 'v': 'self'}, 'f': 'value'}}),
        ('fail', {'k': 'raise', 'e': {'k': 'str', 'v': 'Marker'}}),
    ]:
        funcs.append(fn('probe.py:<module>.Reader.' + name, 'probe.py', body=body,
                        pythonSignature={'positionalOnly': [], 'keywordOnly': [],
                                         'required': [], 'isMethod': True}))
    ast = tmp_path / 'ast.json'
    ast.write_text(json.dumps(funcs))
    generated_module('ContextMetadata', ast)
    work = tmp_path / 'run'
    work.mkdir()
    result = subprocess.run([sys.executable, str(Path(SCRIPTS) / 'differential.py'),
                             str(ast), str(source), 'ContextMetadata', '3'],
                            cwd=work, env=_oracle_env(), text=True,
                            capture_output=True, timeout=180)
    report = json.loads((work / 'conformance.json').read_text())
    assert result.returncode == 0, result.stdout + result.stderr
    assert report['divergences'] == 0, report['divergence_detail']
    assert report['inconclusive'] == 0, report['inconclusive_detail']
    assert {case['name'] for case in report['runtime_cases']} == {
        'probe.py:<module>.Reader.value', 'probe.py:<module>.Reader.read',
        'probe.py:<module>.Reader.fail'}
