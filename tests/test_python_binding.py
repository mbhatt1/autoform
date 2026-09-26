"""Compare evaluated Python call arguments with the real runtime and kernel."""
import importlib.util
import itertools
import json
import os
from pathlib import Path
import sys

import pytest

from test_python_raises import lean_value
from test_source_numeric import PROGRAM_CONTEXT, ROOT, numeric_env, run


SOURCE = ROOT / 'examples/python_control/binding.py'


def test_source_python_binding(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for Python call binding')
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
         model, 'Binding'], ROOT, numeric_env)
    spec = importlib.util.spec_from_file_location('native_binding_fixture', SOURCE)
    native = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(native)
    subjects = ['fixed', 'variadic', 'keywords', 'positional', 'named', 'mixed',
                'only_keywords', 'nothing', 'Receiver.method']
    keyword_cases = [[], [('a', 11)], [('b', 22)], [('c', 33)],
                     [('a', 11), ('b', 22)], [('b', 22), ('c', 33)],
                     [('a', 11), ('b', 22), ('c', 33), ('extra', 44)]]
    requests = [(name, list(range(1, count + 1)), kws)
                for name, count, kws in itertools.product(subjects, range(5), keyword_cases)]
    requests += [('closure_missing', [a], []) for a in [-7, 0, 13]]
    cases, calls, expected = [], [], []
    for name, args, kws in requests:
        function = native.Receiver().method if name == 'Receiver.method' else getattr(native, name)
        try:
            value = function(*args, **dict(kws))
            result = '.val (' + lean_value(value) + ')'
            outcome = dict(value=value)
        except BaseException as error:
            result = '.exn (.str ' + json.dumps(type(error).__name__) + ')'
            outcome = dict(exception=type(error).__name__)
        cases.append(dict(subject=name, arguments=args, keywords=kws, native=outcome))
        encoded = [f'.lit (.int ({v}))' for v in args]
        encoded += [f'.kwargE {json.dumps(k)} (.lit (.int ({v})))' for k, v in kws]
        calls.append(f'(evalExpr {PROGRAM_CONTEXT} 512 [] [] '
                     f'(.call "binding.py:<module>.{name}" [{", ".join(encoded)}])).2')
        expected.append(result)
    header = model.read_text() + '\nopen Autoform.Core Autoform.Generated.Binding\n'
    driver = header + 'def main : IO Unit := do\n'
    for call, want in zip(calls, expected):
        driver += f'  IO.println (reprStr ({call}) == reprStr ({want} : EResult))\n'
    (tmp_path / 'Observe.lean').write_text(driver)
    observed = run(['lake', 'env', 'lean', '--run', tmp_path / 'Observe.lean'], ROOT, numeric_env,
                   timeout=600).splitlines()
    mismatches = [row for row, result in zip(cases, observed) if result != 'true']
    (tmp_path / 'native-comparison.json').write_text(json.dumps(dict(
        cases=len(cases), observed=len(observed), mismatches=mismatches, results=cases), indent=2) + '\n')
    assert len(observed) == len(cases) and not mismatches, json.dumps(mismatches, indent=2)
    # Repr is only the observation transport; proof checks compare the actual
    # result constructor and structural value, without trusting native reduction.
    proofs = header + '\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
    for call, want in zip(calls, expected):
        proofs += f'example : {call} = ({want} : EResult) := by rfl\n'
    (tmp_path / 'Proofs.lean').write_text(proofs)
    run(['lake', 'env', 'lean', tmp_path / 'Proofs.lean'], ROOT, numeric_env, timeout=600)
