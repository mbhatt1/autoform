"""Unsupported Python signatures must not yield plausible but wrong proofs."""
import importlib.util
import json
import os
from pathlib import Path
import sys
import subprocess

import pytest

from test_source_numeric import ROOT, numeric_env, run


SOURCE = ROOT / 'examples/python_control/signatures.py'


def test_signature_metadata_distinguishes_binding_rules():
    source = '''def ordinary(a, *args, **kwargs): pass
def default(a=None): pass
async def asynchronous(a=1): pass
def positional(a, /): pass
def keyword(*, a): pass
def keyword_default(*, a=1): pass
def computed(a=len("x")): pass
def mixed(a=1, b=len("x")): pass
mapper = lambda a=2: a
'''
    script = (ROOT / 'cartographer/export_ast.sc').read_text()
    decoder = script.split('  val pythonHandlerDecoder = """', 1)[1].split('\n"""', 1)[0]
    result = subprocess.run([sys.executable, '-I', '-S', '-c', decoder],
                            input=source, text=True, capture_output=True, timeout=30)
    assert result.returncode == 0, result.stderr
    records = {row['name']: row for row in json.loads(result.stdout)['signatures'].values()}
    assert records['ordinary'] == dict(name='ordinary', defaults=False, defaultValues=[],
        positional_only=False, keyword_only=False, parameters=['a', 'args', 'kwargs'],
        firstPositional='a', decorated=False, privateParameters=False, isMethod=False,
        positionalOnly=[], keywordOnly=[], required=['a'])
    # `defaults` means "carries a default this pipeline cannot model", which is what
    # holes the definition. A LITERAL default is modelled, so it clears the flag and
    # appears in `defaultValues` instead -- binding it at call time is indistinguishable
    # from binding it when the `def` ran, which is the only reason function-object state
    # is not needed.
    assert {name for name, row in records.items() if row['defaults']} == {'computed', 'mixed'}
    assert records['default']['defaultValues'] == [['a', {'k': 'unit'}]]
    assert records['asynchronous']['defaultValues'] == [['a', {'k': 'int', 'v': '1'}]]
    assert records['keyword_default']['defaultValues'] == [['a', {'k': 'int', 'v': '1'}]]
    assert records['lambda']['defaultValues'] == [['a', {'k': 'int', 'v': '2'}]]
    # All or nothing: `mixed` has one literal and one call, and emitting the literal
    # half would bind some defaults while silently dropping the other.
    assert records['mixed']['defaultValues'] == []
    assert {name for name, row in records.items() if row['positional_only']} == {'positional'}
    assert {name for name, row in records.items() if row['keyword_only']} == {'keyword', 'keyword_default'}


def test_python_signature_gaps(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for Python signature translation')
    source = tmp_path / 'source'
    source.mkdir()
    (source / SOURCE.name).write_bytes(SOURCE.read_bytes())
    joern = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (joern / 'joern-cli').is_dir():
        joern /= 'joern-cli'
    run([joern / 'joern-parse', source, '--language', 'PYTHONSRC', '--output', 'cpg.bin'],
        tmp_path, numeric_env, timeout=600)
    run([joern / 'joern', '--script', ROOT / 'cartographer/export_ast.sc',
         '--param', 'cpgPath=cpg.bin', '--param', 'out=ast.json'], tmp_path, numeric_env, timeout=600)
    model = tmp_path / 'Model.lean'
    run([sys.executable, ROOT / 'cartographer/render_lean.py', tmp_path / 'ast.json',
         model, 'Signatures'], ROOT, numeric_env)
    spec = importlib.util.spec_from_file_location('native_signature_fixture', SOURCE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    requests = [
        ('default_exception', [-7], {}), ('default_exception', [0], {}),
        ('default_exception', [13], {}), ('literal_default', [], {}),
        ('literal_default', [42], {}), ('none_default', [], {}),
        ('keyword_only', [13], {}), ('keyword_only', [], {'a': 13}),
        ('positional_only', [], {'a': 13}), ('positional_only', [13], {}),
        ('lambda_default', [13], {}), ('unused_default_error', [0], {}),
        ('unused_default_error', [2], {}),
        ('mutable_default', [13], {}), ('mutable_default', [13], {}),
        ('ordinary', [13], {}),
    ]
    observations, calls, expected = [], [], []
    for name, args, kwargs in requests:
        try:
            native = {'value': getattr(module, name)(*args, **kwargs)}
        except BaseException as error:
            native = {'exception': type(error).__name__}
        observations.append(dict(subject=name, arguments=args, keywords=kwargs, native=native))
        encoded = [f'.lit (.int ({value}))' for value in args]
        encoded += [f'.kwargE {json.dumps(key)} (.lit (.int ({value})))'
                    for key, value in kwargs.items()]
        # evalExpr accepts keyword argument syntax; runFunc only takes values.
        calls.append('(evalExpr { table := program.table, dialect := .python } 512 [] [] '
                     f'(.call "signatures.py:<module>.{name}" [{", ".join(encoded)}])).2')
        if name == 'ordinary':
            expected.append('value:13')
        elif name in ('keyword_only', 'positional_only'):
            expected.append('value:13' if 'value' in native else 'exception:TypeError')
        elif name in ('lambda_default', 'unused_default_error'):
            expected.append('hole:function:python-default-evaluation')
        else:
            kind = {'keyword_only': 'keyword-only', 'positional_only': 'positional-only'}.get(name, 'defaults')
            expected.append('hole:call:python-' + kind)
    header = model.read_text() + '\nopen Autoform.Core Autoform.Generated.Signatures\n'
    driver = header + 'def main : IO Unit := do\n'
    for call in calls:
        driver += (f'  match {call} with\n'
                   '  | .hole label => IO.println ("hole:" ++ label)\n'
                   '  | .val (.int n) => IO.println ("value:" ++ toString n)\n'
                   '  | .exn (.str n) => IO.println ("exception:" ++ n)\n'
                   '  | other => IO.println ("unexpected:" ++ reprStr other)\n')
    (tmp_path / 'Observe.lean').write_text(driver)
    observed = run(['lake', 'env', 'lean', '--run', tmp_path / 'Observe.lean'], ROOT, numeric_env).splitlines()
    for row, actual in zip(observations, observed):
        row['model'] = actual
    (tmp_path / 'native-comparison.json').write_text(json.dumps(observations, indent=2) + '\n')
    assert observed == expected, json.dumps(observations, indent=2)
    assert [row['native'] for row in observations] == [
        {'value': -7}, {'value': 0}, {'value': 13}, {'value': 17},
        {'value': 42}, {'value': True}, {'exception': 'TypeError'}, {'value': 13},
        {'exception': 'TypeError'}, {'value': 13}, {'value': 13},
        {'exception': 'ZeroDivisionError'}, {'value': 9}, {'value': 1}, {'value': 2},
        {'value': 13}]
    proofs = header + '\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
    # Unsupported default evaluation cannot be concealed by an earlier arity
    # result. Every already-evaluated argument shape reaches the explicit gap.
    for name in ('default_exception', 'literal_default', 'none_default'):
        proofs += ('example (ctx : Ctx) (fuel : Nat) (heap : Heap) (receiver : Option Val) '
                   '(args : List Val) (keywords : List (String × Val)) :\n'
                   f'  (applyFunc ctx (fuel + 2) heap f_signatures_py__module__{name} '
                   'receiver args keywords).2 = .hole "call:python-defaults" := by rfl\n')
    for call, want in zip(calls, expected):
        match = ('| .hole label => label == ' + json.dumps(want[5:])
                 if want.startswith('hole:') else
                 '| .exn (.str n) => n == "TypeError"' if want.startswith('exception:')
                 else '| .val (.int n) => n == 13')
        proofs += (f'example : (match {call} with\n  {match}\n  | _ => false) = true := by\n'
                   '  first | decide +kernel | fail "signature outcome was not established"\n')
    # Default evaluation also happens during module initialization, before calls.
    proofs += ('example : (match runFunc program 512 "signatures.py:<module>" [] with\n'
               '  | .hole label => label == "function:python-default-evaluation"\n'
               '  | _ => false) = true := by\n'
               '  first | decide +kernel | fail "default definition was silently skipped"\n')
    (tmp_path / 'Proofs.lean').write_text(proofs)
    run(['lake', 'env', 'lean', tmp_path / 'Proofs.lean'], ROOT, numeric_env)
