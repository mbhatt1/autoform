"""Native evidence for typed Python handlers, including refused representation gaps."""
import importlib.util
import json
import os
from pathlib import Path
import sys

import pytest

from test_source_numeric import ROOT, numeric_env, run


SOURCE = ROOT / 'examples/python_control/handlers.py'
SUBJECTS = ('mismatched', 'matched', 'lookup_parent', 'arithmetic_parent', 'ordered',
            'first_match', 'tuple_handler', 'exception_excludes_exit', 'base_includes_exit',
            'bare_includes_interrupt', 'nested_outer', 'handler_exception_escapes',
            'else_exception_escapes', 'else_skipped', 'finally_overrides_unmatched',
            'synthetic_name_collision', 'empty_tuple')


def test_exception_fallback_sampling_preserves_holes_and_coverage(differential):
    ordinary = {'name': 'ordinary', 'body': {'k': 'skip'}}
    guarded = {'name': 'guarded', 'body': {'k': 'ifte',
        'c': {'k': 'bool', 'v': True}, 't': {'k': 'ret', 'e': {'k': 'int', 'v': 1}},
        'e': {'k': 'holeS', 'label': 'control:TRY-exception-representation'}}}
    unsupported = {'name': 'unsupported', 'body': {'k': 'holeS', 'label': 'unsupported'}}
    unlabelled = {'name': 'unlabelled', 'body': {'k': 'holeS'}}
    funcs = [ordinary, guarded, unsupported, unlabelled]
    assert differential.python_sampling_candidates(funcs) == [ordinary, guarded]
    assert differential.has_hole(guarded['body'])
    assert differential.compared_hole_coverage([ordinary], {'ordinary', 'guarded'}) == {
        'compared_hole_free': 1, 'compared_with_holes': 1,
        'compared_fraction_of_hole_free': 1.0}
    assert differential.compared_hole_coverage([], {'guarded'}) == {
        'compared_hole_free': 0, 'compared_with_holes': 1,
        'compared_fraction_of_hole_free': 0.0}


@pytest.fixture(scope='module')
def handler_model(tmp_path_factory, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for Python handler translation')
    work = tmp_path_factory.mktemp('python-handlers')
    source = work / 'source'
    source.mkdir()
    (source / SOURCE.name).write_bytes(SOURCE.read_bytes())
    joern = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (joern / 'joern-cli').is_dir():
        joern /= 'joern-cli'
    run([joern / 'joern-parse', source, '--language', 'PYTHONSRC', '--output', 'cpg.bin'],
        work, numeric_env, timeout=600)
    run([joern / 'joern', '--script', ROOT / 'cartographer/export_ast.sc',
         '--param', 'cpgPath=cpg.bin', '--param', 'out=ast.json'], work, numeric_env, timeout=600)
    model = work / 'Model.lean'
    run([sys.executable, ROOT / 'cartographer/render_lean.py', work / 'ast.json',
         model, 'Handlers'], ROOT, numeric_env)
    return work, model.read_text() + '\nopen Autoform.Core Autoform.Generated.Handlers\n'


def test_typed_handlers_match_cpython(handler_model, numeric_env):
    work, header = handler_model
    spec = importlib.util.spec_from_file_location('native_handler_fixture', SOURCE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    cases = []
    for name in SUBJECTS:
        for value in (-7, 0, 13):
            try:
                expected = f'value:{getattr(module, name)(value)}'
            except BaseException as error:
                expected = f'exception:{type(error).__name__}'
            cases.append((name, value, expected))
    calls = [f'runFunc program 512 "handlers.py:<module>.{name}" [.int ({value})]'
             for name, value, _ in cases]
    driver = header + 'def main : IO Unit := do\n'
    for call in calls:
        driver += f'''  match {call} with
  | .val (.int value) => IO.println ("value:" ++ toString value)
  | .exn (.str name) => IO.println ("exception:" ++ name)
  | other => IO.println ("unexpected:" ++ reprStr other)
'''
    (work / 'Observe.lean').write_text(driver)
    observed = run(['lake', 'env', 'lean', '--run', work / 'Observe.lean'], ROOT, numeric_env).splitlines()
    expected = [want for _, _, want in cases]
    mismatches = [dict(subject=name, argument=value, native=want, model=actual)
                  for (name, value, want), actual in zip(cases, observed) if want != actual]
    (work / 'native-comparison.json').write_text(json.dumps(dict(
        cases=len(cases), mismatches=mismatches, observed=observed), indent=2) + '\n')
    assert observed == expected, json.dumps(mismatches, indent=2)
    proofs = header + '\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
    for call, (_, _, want) in zip(calls, cases):
        if want.startswith('value:'):
            result = f'| .val (.int value) => value == ({want.split(":")[1]} : Int)'
        else:
            result = f'| .exn (.str name) => name == "{want.split(":")[1]}"'
        proofs += (f'example : (match {call} with\n  {result}\n  | _ => false) = true := by\n'
                   '  first | decide +kernel | fail "native handler result not established"\n')
    (work / 'Proofs.lean').write_text(proofs)
    run(['lake', 'env', 'lean', work / 'Proofs.lean'], ROOT, numeric_env)


def test_unrepresented_handlers_are_explicit_gaps(handler_model, numeric_env):
    work, header = handler_model
    code = header
    for name in ('dynamic_handler', 'shadowed_handler', 'exception_binding'):
        code += (f'example : (match runFunc program 512 "handlers.py:<module>.{name}" [.int 13] with\n'
                 '  | .hole _ => true\n  | _ => false) = true := by\n'
                 '  first | decide +kernel | fail "unsupported handler was silently translated"\n')
    (work / 'Gaps.lean').write_text(code)
    run(['lake', 'env', 'lean', work / 'Gaps.lean'], ROOT, numeric_env)


def test_unavailable_header_decoder_cannot_make_a_catch_all(handler_model, numeric_env):
    work, _ = handler_model
    joern = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (joern / 'joern-cli').is_dir():
        joern /= 'joern-cli'
    env = dict(numeric_env, AUTOFORM_PYTHON=str(work / 'missing-python'))
    run([joern / 'joern', '--script', ROOT / 'cartographer/export_ast.sc',
         '--param', 'cpgPath=cpg.bin', '--param', 'out=unavailable.json'], work, env, timeout=600)
    ast = json.loads((work / 'unavailable.json').read_text())
    subject = next(f for f in ast if f['name'] == 'handlers.py:<module>.mismatched')
    text = json.dumps(subject['body'])
    assert 'control:TRY-source-metadata' in text
    assert 'tryCatch' not in text
