"""Native constructor outcomes and source raise behavior must survive kernel replay."""
from conftest import exporter_source
import ast
import importlib.util
import json
import os
from pathlib import Path
import sys
import subprocess

import pytest

from test_source_numeric import ROOT, numeric_env, run


def test_exception_class_metadata_respects_python_scopes():
    source = '''def f(ValueError=ValueError):
    return ValueError
g = lambda ValueError=ValueError: ValueError
xs = [ValueError for ValueError in (ValueError,)]
class C:
    ValueError = 1
    def method(self, x=ValueError):
        return ValueError
'''
    # Establish the binding behavior independently in CPython before checking
    # metadata. This does not claim Core already supports omitted defaults.
    namespace = {}
    exec(compile(source, '<scope fixture>', 'exec'), namespace)
    assert namespace['f'](13) == 13 and namespace['f'].__defaults__ == (ValueError,)
    assert namespace['g'](7) == 7 and namespace['g'].__defaults__ == (ValueError,)
    assert namespace['xs'] == [ValueError]
    assert namespace['C'].method.__defaults__ == (1,)
    assert namespace['C']().method() is ValueError
    script = exporter_source()
    decoder = script.split('  val pythonHandlerDecoder = """', 1)[1].split('\n"""', 1)[0]
    process = subprocess.run([sys.executable, '-I', '-S', '-c', decoder],
                             input=source, text=True, capture_output=True, timeout=30)
    assert process.returncode == 0, process.stderr
    tree = ast.parse(source)
    builtin_loads = [tree.body[0].args.defaults[0], tree.body[1].value.args.defaults[0],
                     tree.body[2].value.generators[0].iter.elts[0],
                     tree.body[3].body[1].body[0].value]
    expected = {f'{node.lineno}:{node.col_offset + 1}': 'ValueError' for node in builtin_loads}
    assert json.loads(process.stdout)['class_refs'] == expected


def lean_value(value):
    if value is None:
        return '.unit'
    if type(value) is bool:
        return '.bool ' + str(value).lower()
    if type(value) is int:
        return f'.int ({value})'
    if type(value) is str:
        return '.str ' + json.dumps(value, ensure_ascii=False)
    if type(value) in (list, tuple):
        kind = 'list' if type(value) is list else 'tuple'
        return f'.{kind} [' + ', '.join(lean_value(x) for x in value) + ']'
    if type(value) is dict:
        return '.dict [' + ', '.join(f'({lean_value(k)}, {lean_value(v)})'
                                    for k, v in value.items()) + ']'
    raise AssertionError(value)


def test_exception_constructor_boundaries(tmp_path, numeric_env):
    details = [None, False, 0, [], (), {}, 'abc', 'abcd', 'abcdef',
               [None, None, None, None], dict(enumerate(range(4)))]
    details += [list(range(n)) for n in range(8)]
    details += [tuple(range(n)) for n in range(8)]
    arguments = [[], ['bad'], ['bad', 1, 2]] + [['bad', value] for value in details]
    source = 'import Autoform.Lang.Core.Stdlib\nopen Autoform.Core\n'
    source += 'set_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
    cases = []
    for cls in (ValueError, SyntaxError, IndentationError):
        for args in arguments:
            try:
                cls(*args)
                kind, expected = 'val', cls.__name__
            except BaseException as error:
                kind, expected = 'exn', type(error).__name__
            cases.append(dict(constructor=cls.__name__, args=args, kind=kind, expected=expected))
            encoded = ', '.join(lean_value(v) for v in args)
            source += (f'example : (match Stdlib.builtin .python [] "{cls.__name__}" [{encoded}] with\n'
                       f'  | some (_, .{kind} (.str name)) => name == "{expected}"\n'
                       '  | _ => false) = true := by\n'
                       '  first | decide +kernel | fail "native constructor outcome not established"\n')
    (tmp_path / 'native-constructors.json').write_text(json.dumps(cases, indent=2) + '\n')
    (tmp_path / 'Constructors.lean').write_text(source)
    run(['lake', 'env', 'lean', tmp_path / 'Constructors.lean'], ROOT, numeric_env)


def test_source_raises_match_cpython(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for Python raise translation')
    fixture = ROOT / 'examples/python_control/raises.py'
    source = tmp_path / 'source'
    source.mkdir()
    (source / fixture.name).write_bytes(fixture.read_bytes())
    joern = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (joern / 'joern-cli').is_dir():
        joern /= 'joern-cli'
    run([joern / 'joern-parse', source, '--language', 'PYTHONSRC', '--output', 'cpg.bin'],
        tmp_path, numeric_env, timeout=600)
    run([joern / 'joern', '--script', ROOT / 'cartographer/export_ast.sc',
         '--param', 'cpgPath=cpg.bin', '--param', 'out=ast.json'], tmp_path, numeric_env, timeout=600)
    model = tmp_path / 'Model.lean'
    run([sys.executable, ROOT / 'cartographer/render_lean.py', tmp_path / 'ast.json',
         model, 'Raises'], ROOT, numeric_env)
    spec = importlib.util.spec_from_file_location('native_raise_fixture', fixture)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    subjects = [name for name in vars(module) if not name.startswith('_')
                and name not in ('ambiguous_exception_value', 'explicit_cause')]
    cases = [(name, value, getattr(module, name)(value))
             for name in subjects for value in (-7, 0, 13)]
    calls = [f'runFunc program 512 "raises.py:<module>.{name}" [.int ({value})]'
             for name, value, _ in cases]
    header = model.read_text() + '\nopen Autoform.Core Autoform.Generated.Raises\n'
    driver = header + 'def main : IO Unit := do\n'
    for call in calls:
        driver += f'''  match {call} with
  | .val (.int n) => IO.println n
  | other => IO.println ("unexpected:" ++ reprStr other)
'''
    (tmp_path / 'Observe.lean').write_text(driver)
    observed = run(['lake', 'env', 'lean', '--run', tmp_path / 'Observe.lean'], ROOT, numeric_env).splitlines()
    # Known gaps are kept separate from native agreements and pinned by label. The
    # last one, `invalid_dict` (`raise {"message": a}` lowered to item stores on a
    # boxed dict), closed once boxed containers accepted item stores: the model now
    # reaches CPython's `TypeError` handler and returns `a`.
    gaps = {}
    known_gaps = [dict(subject=name, argument=value, native=want, model=actual)
                  for (name, value, want), actual in zip(cases, observed) if name in gaps]
    mismatches = [dict(subject=name, argument=value, native=want, model=actual)
                  for (name, value, want), actual in zip(cases, observed)
                  if name not in gaps and str(want) != actual]
    (tmp_path / 'native-comparison.json').write_text(json.dumps(dict(
        cases=len(cases), compared=len(cases) - len(known_gaps), gaps=known_gaps,
        mismatches=mismatches, observed=observed), indent=2) + '\n')
    expected_observations = [f'unexpected:Autoform.Core.EResult.hole "{gaps[name]}"'
                             if name in gaps else str(want) for name, _, want in cases]
    assert observed == expected_observations, json.dumps(mismatches + known_gaps, indent=2)
    proofs = header + '\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
    for call, (name, _, expected) in zip(calls, cases):
        if name in gaps:
            proofs += (f'example : (match {call} with\n'
                       f'  | .hole label => label == "{gaps[name]}"\n'
                       '  | _ => false) = true := by\n'
                       '  first | decide +kernel | fail "known construction gap changed"\n')
            continue
        proofs += (f'example : (match {call} with\n'
                   f'  | .val (.int n) => n == ({expected} : Int)\n'
                   '  | _ => false) = true := by\n'
                   '  first | decide +kernel | fail "native raise result not established"\n')
    for name in ('ambiguous_exception_value', 'explicit_cause'):
        proofs += (f'example : (match runFunc program 512 "raises.py:<module>.{name}" [.int 13] with\n'
                   '  | .hole _ => true\n  | _ => false) = true := by\n'
                   '  first | decide +kernel | fail "unrepresented exception value was accepted"\n')
    (tmp_path / 'Proofs.lean').write_text(proofs)
    run(['lake', 'env', 'lean', tmp_path / 'Proofs.lean'], ROOT, numeric_env)
