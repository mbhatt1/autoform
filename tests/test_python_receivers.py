"""Unsupported receiver binding must stay visible at every argument boundary.

The native results record what still needs modelling; an explicit hole is not
a conformance agreement. The kernel proofs establish that no arity check hides
the unsupported receiver behind a plausible value or exception.
"""
from conftest import exporter_source
import importlib.util
import itertools
import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

from test_source_numeric import PROGRAM_CONTEXT, ROOT, numeric_env, run


SOURCE = ROOT / 'examples/python_control/receivers.py'
SUBJECTS = ('absent', 'keyword', 'renamed', 'star_self', 'static',
            'class_named', 'class_self', 'collect')
# The shapes that STAY holes: no first positional (`absent`, `keyword`, `star_self`) or a
# receiver not named `self` (`renamed`). Each is a different binding rule from "inject the
# receiver under `self`", and Core has exactly that one rule.
HOLED = ('absent', 'keyword', 'renamed', 'star_self')
# The shapes that bind and whose bodies return an int the observation matrix can read.
BOUND = {'collect': 1, 'positional_collect': 2}
# The shapes that bind through a decorator and are compared against CPython outcome by
# outcome (`static` returns a tuple, the classmethods an int or an arity TypeError).
COMPARED = ('static', 'class_named', 'class_self')
GAP = 'call:python-receiver-signature'


def test_receiver_source_signature_metadata():
    script = exporter_source()
    decoder = script.split('  val pythonHandlerDecoder = """', 1)[1].split('\n"""', 1)[0]
    result = subprocess.run([sys.executable, '-I', '-S', '-c', decoder],
                            input=SOURCE.read_text(), text=True, capture_output=True, timeout=30)
    assert result.returncode == 0, result.stderr
    records = {row['name']: row for row in json.loads(result.stdout)['signatures'].values()}
    assert {name: records[name]['firstPositional'] for name in SUBJECTS} == {
        'absent': None, 'keyword': None, 'renamed': 'receiver', 'star_self': None,
        'static': 'self', 'class_named': 'cls', 'class_self': 'self', 'collect': 'self',
    }
    # Nothing here is `decorated`. `@staticmethod`'s entire meaning is "bind no
    # receiver", which `isMethod: False` already says, and `@classmethod` substitutes
    # the class for the receiver, which `applyFunc` now does (`receiverKind: class`); so
    # neither leaves a decorator residue for Core to refuse.
    assert {name for name in SUBJECTS if records[name]['decorated']} == set()
    assert {name for name in SUBJECTS if records[name]['classMethod']} == {
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
    # A receiver followed by nothing but collectors is its own, bindable shape: the
    # receiver is `self`, every other parameter is `*args`/`**kwargs`. It binds because
    # the exporter records the stripped receiver's name (`receiverName`) and Core refuses
    # a `self=` keyword that would otherwise vanish into `**kwargs`.
    assert {name for name in SUBJECTS + ('positional_collect',)
            if records[name]['receiverThenCollectors']} == {'collect', 'positional_collect'}


def encode_native(outcome):
    """CPython's outcome in the driver's print format: ints, tuples of ints, exceptions."""
    if 'exception' in outcome:
        return 'exception:' + outcome['exception']
    value = outcome['value']
    if isinstance(value, tuple):
        return 'value:tuple:' + ','.join(str(v) for v in value)
    return 'value:' + str(value)


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
    # The two `@classmethod`s translate: the class is bound as the first positional, so
    # they are not receiver gaps any more and carry the signature that says so.
    for name in ('class_named', 'class_self'):
        function = functions[f'receivers.py:<module>.Receiver.{name}']
        assert function['body'] != {'k': 'holeS', 'label': GAP}
        assert function['pythonSignature']['receiverKind'] == 'class'
    # `@staticmethod def static(self, a)` translates too: no receiver is bound, so `self`
    # is an ordinary first parameter and the body is `return (self, a)` verbatim.
    static = functions['receivers.py:<module>.Receiver.static']
    assert static['body'] == {'k': 'ret', 'e': {'k': 'tupleE', 'items': [
        {'k': 'name', 'v': 'self'}, {'k': 'name', 'v': 'a'}]}}
    assert static['pythonSignature']['isMethod'] is False
    # `collect(self, **kw)` translates: `self` is stripped and RECORDED, so a `self=`
    # keyword is refused instead of landing in `kw`. `positional_collect(self, /, **kw)`
    # needs no record -- CPython really does put `self=7` in `kw` there.
    collect = functions['receivers.py:<module>.Receiver.collect']
    assert collect['body'] == {'k': 'ret', 'e': {'k': 'int', 'v': '1'}}
    assert collect['kwarg'] == 'kw' and 'vararg' not in collect
    assert collect['pythonSignature']['receiverName'] == 'self'
    assert 'receiverName' not in functions[
        'receivers.py:<module>.Receiver.positional_collect']['pythonSignature']
    for name in HOLED:
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
    # `static` and the two classmethods return tuples/the class and are covered by
    # tests/test_python_signatures.py; this matrix reads ints and holes only.
    for name, count, keywords in itertools.product(HOLED + tuple(BOUND) + COMPARED,
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
        context = PROGRAM_CONTEXT
        calls.extend([
            f'(evalExpr {context} 512 [{{ cls := "Receiver", fields := [] }}] '
            f'[("receiver", .ref 0)] (.mcall (.name "receiver") {json.dumps(name)} {args})).2',
            f'(evalExpr {context} 512 [] [] '
            f'(.call "receivers.py:<module>.Receiver.{name}" {args})).2',
        ])
        if name in BOUND or name in COMPARED:
            # These translate, so the model must reproduce CPython: the value (an int, or
            # `static`'s `(self, a)` tuple of ints) or the arity `TypeError`.
            want = encode_native(outcome)
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
                   '  | .val (.tuple vs) => IO.println ("value:tuple:" ++ ",".intercalate '
                   '(vs.map (fun v => match v with | .int i => toString i | _ => "?")))\n'
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
    # The three shapes not in the matrix, checked natively so the fixture stays honest.
    assert receiver.static(1, 2) == (1, 2) and receiver.static(self=7, a=11) == (7, 11)
    assert receiver.class_named(a=11) == 11 and receiver.class_self(1) == 1
    # The `self=` keyword is exactly where `collect` and `positional_collect` differ.
    assert native_outcome('collect', [], [('self', 7)]) == {'exception': 'TypeError'}
    assert native_outcome('collect', [], [('a', 11)]) == {'value': 1}
    assert native_outcome('collect', [1]) == {'exception': 'TypeError'}
    assert native_outcome('positional_collect', [], [('self', 7)]) == {'value': 2}
    assert native_outcome('positional_collect', [1]) == {'exception': 'TypeError'}
    proofs = header + '\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
    # Universal application checks cover more than the finite observed matrix:
    # every evaluated argument list, keyword list, heap and receiver must reach
    # the gap. Two fuel steps suffice to enter the guarded function body.
    for name in HOLED:
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
                 if want.startswith('exception:') else
                 '| .val (.int value) => value == ' + want.removeprefix('value:'))
        proofs += (f'example : (match {call} with\n'
                   f'  {match}\n'
                   '  | _ => false) = true := by\n'
                   '  first | decide +kernel | fail "receiver gap was not established"\n')
    (tmp_path / 'Proofs.lean').write_text(proofs)
    run(['lake', 'env', 'lean', tmp_path / 'Proofs.lean'], ROOT, numeric_env, timeout=600)
