"""Unsupported receiver binding must stay visible at every argument boundary.

The native results record what still needs modelling; an explicit hole is not
a conformance agreement. The kernel proofs establish that no arity check hides
the unsupported receiver behind a plausible value or exception.
"""
import importlib.util
import itertools
import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

from test_source_numeric import ROOT, numeric_env, run


SOURCE = ROOT / 'examples/python_control/receivers.py'
SUBJECTS = ('absent', 'keyword', 'renamed', 'star_self', 'static',
            'class_named', 'class_self', 'collect')
GAP = 'call:python-receiver-signature'


def test_receiver_source_signature_metadata():
    script = (ROOT / 'cartographer/export_ast.sc').read_text()
    decoder = script.split('  val pythonHandlerDecoder = """', 1)[1].split('\n"""', 1)[0]
    result = subprocess.run([sys.executable, '-I', '-S', '-c', decoder],
                            input=SOURCE.read_text(), text=True, capture_output=True, timeout=30)
    assert result.returncode == 0, result.stderr
    records = {row['name']: row for row in json.loads(result.stdout)['signatures'].values()}
    assert {name: records[name]['firstPositional'] for name in SUBJECTS} == {
        'absent': None, 'keyword': None, 'renamed': 'receiver', 'star_self': None,
        'static': 'self', 'class_named': 'cls', 'class_self': 'self', 'collect': 'self',
    }
    # `static` is deliberately absent. `@staticmethod`'s entire meaning is "bind no
    # receiver", which `isMethod: False` already says, so it leaves no decorator residue
    # for Core to refuse -- unlike `@classmethod`, which substitutes the class for the
    # receiver and is still unmodelled.
    assert {name for name in SUBJECTS if records[name]['decorated']} == {
        'class_named', 'class_self'}
    assert records['static']['staticMethod'] is True
    assert records['static']['isMethod'] is False
    # The adversarial part of this fixture: `@staticmethod def static(self, a)`. With no
    # receiver to bind, `self` is an ORDINARY PARAMETER and must not be stripped --
    # CPython binds `C.static(1, 2)` to `self=1, a=2`.
    assert records['static']['required'] == ['self', 'a']
    assert records['keyword']['keywordOnly'] == ['self']
    assert records['star_self']['parameters'] == ['self']
    assert records['positional_collect']['positionalOnly'] == ['self']


def test_source_python_receiver_gaps(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for Python receiver binding')
    source = tmp_path / 'source'
    source.mkdir()
    (source / SOURCE.name).write_bytes(SOURCE.read_bytes())
    joern = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (joern / 'joern-cli').is_dir():
        joern /= 'joern-cli'
    run([joern / 'joern-parse', source, '--language', 'PYTHONSRC', '--output', 'cpg.bin'],
        tmp_path, numeric_env, timeout=600)
    run([joern / 'joern', '--script', ROOT / 'cartographer/export_ast.sc',
         '--param', 'cpgPath=cpg.bin', '--param', 'out=ast.json'],
        tmp_path, numeric_env, timeout=600)
    functions = {row['name']: row for row in json.loads((tmp_path / 'ast.json').read_text())}
    for name in SUBJECTS:
        function = functions[f'receivers.py:<module>.Receiver.{name}']
        assert function['body'] == {'k': 'holeS', 'label': GAP}
        assert 'pythonSignature' not in function
        # Both collectors are needed: otherwise rejecting unknown keywords or
        # extra positional values can conceal the gap before its body executes.
        assert function.get('vararg') and function.get('kwarg')
    model = tmp_path / 'Model.lean'
    run([sys.executable, ROOT / 'cartographer/render_lean.py', tmp_path / 'ast.json',
         model, 'Receivers'], ROOT, numeric_env)
    spec = importlib.util.spec_from_file_location('native_receiver_fixture', SOURCE)
    native = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(native)
    receiver = native.Receiver()
    keyword_cases = [[], [('self', 7)], [('a', 11)], [('receiver', 13)], [('cls', 17)],
                     [('unknown', 19)], [('self', 7), ('a', 11)],
                     [('receiver', 13), ('a', 11)], [('cls', 17), ('a', 11)]]
    observations, calls, expected = [], [], []
    for name, count, keywords in itertools.product(SUBJECTS + ('positional_collect',),
                                                   range(4), keyword_cases):
        arguments = list(range(1, count + 1))
        try:
            outcome = {'value': getattr(receiver, name)(*arguments, **dict(keywords))}
        except BaseException as error:
            outcome = {'exception': type(error).__name__}
        encoded = [f'.lit (.int ({value}))' for value in arguments]
        encoded += [f'.kwargE {json.dumps(key)} (.lit (.int ({value})))'
                    for key, value in keywords]
        args = '[' + ', '.join(encoded) + ']'
        context = '{ table := program.table, dialect := .python }'
        calls.extend([
            f'(evalExpr {context} 512 [{{ cls := "Receiver", fields := [] }}] '
            f'[("receiver", .ref 0)] (.mcall (.name "receiver") {json.dumps(name)} {args})).2',
            f'(evalExpr {context} 512 [] [] '
            f'(.call "receivers.py:<module>.Receiver.{name}" {args})).2',
        ])
        if name == 'positional_collect':
            want = 'value:2' if 'value' in outcome else 'exception:TypeError'
        else:
            want = 'hole:' + GAP
        expected.extend([want, want])
        observations.append(dict(subject=name, arguments=arguments,
                                 keywords=keywords, native=outcome))
    header = model.read_text() + '\nopen Autoform.Core Autoform.Generated.Receivers\n'
    driver = header + 'def main : IO Unit := do\n'
    for call in calls:
        driver += (f'  match {call} with\n'
                   '  | .hole label => IO.println ("hole:" ++ label)\n'
                   '  | .val (.int value) => IO.println ("value:" ++ toString value)\n'
                   '  | .exn (.str name) => IO.println ("exception:" ++ name)\n'
                   '  | other => IO.println ("unexpected:" ++ reprStr other)\n')
    (tmp_path / 'Observe.lean').write_text(driver)
    observed = run(['lake', 'env', 'lean', '--run', tmp_path / 'Observe.lean'],
                   ROOT, numeric_env, timeout=600).splitlines()
    for index, row in enumerate(observations):
        row['model'] = dict(zip(('instance_dispatch', 'direct_lookup'),
                               observed[index * 2:index * 2 + 2]))
    report = dict(native_cases=len(observations), model_calls=len(calls),
                  observed=len(observed), results=observations)
    (tmp_path / 'native-comparison.json').write_text(json.dumps(report, indent=2) + '\n')
    assert observed == expected, json.dumps(report, indent=2)
    # Pin the original wrong answers and successful native descriptor/vararg
    # calls: an all-TypeError native setup would fail to challenge the guard.
    def native_outcome(name, arguments, keywords=()):
        return next(row['native'] for row in observations
                    if row['subject'] == name and row['arguments'] == arguments
                    and row['keywords'] == list(keywords))
    assert native_outcome('absent', []) == {'exception': 'TypeError'}
    assert native_outcome('keyword', []) == {'exception': 'TypeError'}
    assert native_outcome('renamed', [1]) == {'value': 1}
    assert native_outcome('star_self', []) == {'value': 1}
    assert native_outcome('star_self', [1, 2, 3]) == {'value': 4}
    assert native_outcome('static', [1, 2]) == {'value': (1, 2)}
    assert native_outcome('static', [], [('self', 7), ('a', 11)]) == {'value': (7, 11)}
    assert native_outcome('class_named', [], [('a', 11)]) == {'value': 11}
    assert native_outcome('class_self', [1]) == {'value': 1}
    assert native_outcome('collect', [], [('self', 7)]) == {'exception': 'TypeError'}
    assert native_outcome('positional_collect', [], [('self', 7)]) == {'value': 2}
    assert native_outcome('positional_collect', [1]) == {'exception': 'TypeError'}
    proofs = header + '\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
    # Universal application checks cover more than the finite observed matrix:
    # every evaluated argument list, keyword list, heap and receiver must reach
    # the gap. Two fuel steps suffice to enter the guarded function body.
    for name in SUBJECTS:
        function = 'f_receivers_py__module__Receiver_' + name
        proofs += (
            'example (ctx : Ctx) (fuel : Nat) (heap : Heap) (receiver : Option Val) '
            '(args : List Val) (keywords : List (String × Val)) :\n'
            f'    (applyFunc ctx (fuel + 2) heap {function} receiver args keywords).2 '
            f'= .hole {json.dumps(GAP)} := by rfl\n'
            'example (ctx : Ctx) (fuel : Nat) (heap : Heap) '
            '(captured : List (String × Val)) (args : List Val) '
            '(keywords : List (String × Val)) :\n'
            f'    (applyClosure ctx (fuel + 2) heap {function} captured args keywords).2 '
            f'= .hole {json.dumps(GAP)} := by rfl\n')
    # Check dispatch reaches each guarded method once, plus every supported
    # positional-only collector outcome. The universal checks above cover its
    # argument-binding guard independently of dispatch.
    proof_indexes = []
    for index, row in enumerate(observations):
        if row['subject'] == 'positional_collect':
            proof_indexes.extend([index * 2, index * 2 + 1])
        elif not row['arguments'] and not row['keywords']:
            proof_indexes.append(index * 2)
    for index in proof_indexes:
        call, want = calls[index], expected[index]
        match = ('| .hole label => label == ' + json.dumps(GAP)
                 if want.startswith('hole:') else
                 '| .exn (.str name) => name == "TypeError"'
                 if want.startswith('exception:') else '| .val (.int value) => value == 2')
        proofs += (f'example : (match {call} with\n'
                   f'  {match}\n'
                   '  | _ => false) = true := by\n'
                   '  first | decide +kernel | fail "receiver gap was not established"\n')
    (tmp_path / 'Proofs.lean').write_text(proofs)
    run(['lake', 'env', 'lean', tmp_path / 'Proofs.lean'], ROOT, numeric_env, timeout=600)
