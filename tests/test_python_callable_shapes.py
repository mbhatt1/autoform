"""Native checks for lexical method identity and unsupported callable rewriting."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

import pytest
from conftest import exporter_source

from test_source_numeric import PROGRAM_CONTEXT, ROOT, numeric_env, run


SOURCE = ROOT / 'examples/python_control/callable_shapes.py'


def test_callable_lexical_metadata():
    script = exporter_source()
    decoder = script.split('  val pythonHandlerDecoder = """', 1)[1].split('\n"""', 1)[0]
    result = subprocess.run([sys.executable, '-I', '-S', '-c', decoder],
                            input=SOURCE.read_text(), text=True, capture_output=True, timeout=30)
    assert result.returncode == 0, result.stderr
    records = list(json.loads(result.stdout)['signatures'].values())
    assert all(not row['isMethod'] for row in records if row['name'] == 'inner')
    assert all(not row['isMethod'] for row in records if row['name'] in {'Outer', 'Collision'})
    assert next(row for row in records if row['name'] == 'decorated')['decorated']
    private = [row for row in records if row['privateParameters']]
    assert {row['name'] for row in private} == {'f', 'local'}
    assert next(row for row in records if row['name'] == 'local')['isMethod'] is False
    assert next(row for row in records if row['name'] == 'ordinary_private_name')['privateParameters'] is False


def test_source_python_callable_shapes(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for callable shape translation')
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
    functions = {row['name']: row for row in json.loads((tmp_path / 'ast.json').read_text())}
    prefix = SOURCE.name + ':<module>.'
    guarded = {'Private.f': 'call:python-private-parameters',
               'LexicalPrivate.outer.local': 'call:python-private-parameters'}
    for name, gap in guarded.items():
        row = functions[prefix + name]
        assert row['body'] == {'k': 'holeS', 'label': gap}
        assert row.get('vararg') and row.get('kwarg') and 'pythonSignature' not in row
    # CHANGED (decorators applied at definition time): `@replacement def decorated` is no
    # longer a `call:python-decorator-binding` gap. The raw body is exported under its own
    # name and the source name is an auxiliary entry reading the rebound module binding.
    raw = functions[prefix + 'decorated<undecorated>']
    assert raw['body'] == {'k': 'ret', 'e': {'k': 'name', 'v': 'a'}}
    assert raw['undecoratedOf'] == prefix + 'decorated'
    assert [entry['name'] for entry in raw['decoratedEntries']] == [prefix + 'decorated']
    assert prefix + 'decorated' not in functions
    for name in ('Outer.inner', 'Collision.inner', 'nested_extra.inner'):
        assert functions[prefix + name]['pythonSignature']['isMethod'] is False
    assert functions[prefix + 'Collision.inner']['params'] == ['self']
    model = tmp_path / 'Model.lean'
    run([sys.executable, ROOT / 'cartographer/render_lean.py', tmp_path / 'ast.json',
         model, 'CallableShapes'], ROOT, numeric_env)
    spec = importlib.util.spec_from_file_location('native_callable_shapes', SOURCE)
    native = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(native)
    requests = [
        # CHANGED: the source entry `decorated` is the decorated binding (`inner`, 9),
        # compared with CPython; the raw body is reached only as `decorated<undecorated>`.
        ('decorated', [], None, None),
        ('call_decorated', [], None, None),
        ('Outer', [23], None, None),
        ('private_positional', [], None, 'call:python-private-parameters'),
        ('private_keyword', [], None, 'call:python-private-parameters'),
        ('private_unmangled', [], None, 'call:python-private-parameters'),
        ('nested_call', [], None, None),
        ('Collision', [23], None, None),
        ('nested_extra', [23], None, None),
        ('nested_private', [], None, 'call:python-private-parameters'),
        ('ordinary_private_name', [], {'__value': 29}, None),
        ('dunder_keyword', [], None, None),
        ('underscore_class', [], None, None),
    ]
    calls, expected, observations = [], [], []
    for name, args, keywords, gap in requests:
        try:
            value = getattr(native, name)(*args, **(keywords or {}))
            outcome, want = {'value': value}, 'value:' + str(value)
        except BaseException as error:
            outcome = {'exception': type(error).__name__}
            want = 'exception:' + type(error).__name__
        if gap:
            want = 'hole:' + gap
        encoded = [f'.lit (.int ({value}))' for value in args]
        encoded += [f'.kwargE {json.dumps(key)} (.lit (.int ({value})))'
                    for key, value in (keywords or {}).items()]
        expression = f'(.call {json.dumps(prefix + name)} [{", ".join(encoded)}])'
        calls.append(f'(evalExpr sourceCtx 512 sourceGlobals.1 [] {expression}).2')
        expected.append(want)
        observations.append(dict(subject=name, args=args, keywords=keywords or {}, native=outcome,
                                 expected_model=want, compared=gap is None))
    header = model.read_text() + '\nopen Autoform.Core Autoform.Generated.CallableShapes\n'
    # Native functions were imported before these calls. Their defining module
    # must exist in Core too; a table-only context has no Python global namespace.
    header += 'private def sourceGlobals : Heap × Ref := initGlobals program 300 moduleInits\n'
    header += ('private def sourceCtx : Ctx := { (' + PROGRAM_CONTEXT +
               ' : Ctx) with globals := sourceGlobals.2 }\n')
    driver = header + 'def main : IO Unit := do\n'
    for call in calls:
        driver += (f'  match {call} with\n'
                   '  | .val (.int value) => IO.println ("value:" ++ toString value)\n'
                   '  | .exn (.str name) => IO.println ("exception:" ++ name)\n'
                   '  | .hole label => IO.println ("hole:" ++ label)\n'
                   '  | other => IO.println (reprStr other)\n')
    (tmp_path / 'Observe.lean').write_text(driver)
    observed = run(['lake', 'env', 'lean', '--run', tmp_path / 'Observe.lean'],
                   ROOT, numeric_env, timeout=600).splitlines()
    report = dict(native_cases=len(requests), observed=observed, results=observations)
    (tmp_path / 'native-comparison.json').write_text(json.dumps(report, indent=2) + '\n')
    assert observed == expected, json.dumps(report, indent=2)
    proofs = header + '\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
    for name, gap in guarded.items():
        symbol = 'f_callable_shapes_py__module__' + name.replace('.', '_')
        proofs += ('example (ctx : Ctx) (fuel : Nat) (heap : Heap) (receiver : Option Val) '
                   '(args : List Val) (keywords : List (String × Val)) :\n'
                   f'  (applyFunc ctx (fuel + 2) heap {symbol} receiver args keywords).2 '
                   f'= .hole {json.dumps(gap)} := by rfl\n')
    for call, want in zip(calls, expected):
        category, value = want.split(':', 1)
        pattern = (f'.val (.int value) => value == {value}' if category == 'value' else
                   f'.exn (.str name) => name == {json.dumps(value)}' if category == 'exception' else
                   f'.hole label => label == {json.dumps(value)}')
        proofs += (f'example : (match {call} with\n  | {pattern}\n  | _ => false) = true := by\n'
                   '  first | decide +kernel | fail "callable result was not established"\n')
    (tmp_path / 'Proofs.lean').write_text(proofs)
    run(['lake', 'env', 'lean', tmp_path / 'Proofs.lean'], ROOT, numeric_env, timeout=600)
