"""Same-line scope identities must not depend on symtable child traversal order."""
import ast
import importlib.util
import json
import os
from pathlib import Path
import sys

import pytest

from test_python_signatures import _decode
from test_source_numeric import ROOT, numeric_env, run


def test_same_line_scope_metadata_matches_each_original_expression():
    source = '''
def probe(captured):
    gens = ((x for x in [1]), (y + captured for y in [2]))
    funcs = (lambda ValueError: ValueError, lambda TypeError: ValueError)
    tricky = lambda callback=(lambda ValueError: ValueError): ValueError
    lists = [(lambda ValueError: ValueError, lambda TypeError: ValueError) for k in [1]]
    dictionaries = {(lambda ValueError: ValueError): (lambda TypeError: ValueError) for k in [1]}
    conditional = ((lambda ValueError: ValueError) if (lambda TypeError: ValueError) else (lambda KeyError: ValueError))
'''
    result = _decode(source)
    for expression in ast.walk(ast.parse(source)):
        if isinstance(expression, ast.GeneratorExp):
            key = f'{expression.lineno}:{expression.col_offset + 1}'
            assert result['genexpressions'][key]['captures'] == (
                ['captured'] if isinstance(expression.elt, ast.BinOp) else [])
        elif isinstance(expression, ast.Lambda):
            key = f'{expression.lineno}:{expression.col_offset + 1}'
            arguments = [parameter.arg for parameter in expression.args.args]
            assert result['signatures'][key]['parameters'] == arguments
            body = expression.body
            body_key = f'{body.lineno}:{body.col_offset + 1}'
            assert (body_key in result['class_refs']) == ('ValueError' not in arguments)


def test_metadata_positions_survive_unicode_and_crlf():
    source = ('def probe(captured):\r\n'
              '    label = "é😀"; a = (x for x in [1]); b = (y + captured for y in [2])\r\n')
    result = _decode(source)
    expressions = [node for node in ast.walk(ast.parse(source)) if isinstance(node, ast.GeneratorExp)]
    assert [result['genexpressions'][f'{node.lineno}:{node.col_offset + 1}']['captures']
            for node in expressions] == [[], ['captured']]


def test_duplicate_scopes_do_not_change_unambiguous_metadata():
    source = '''
def probe(ValueError):
    generator = (x for x in [1])
    inner = lambda TypeError: ValueError
    try:
        raise TypeError
    except TypeError:
        return generator
'''
    before = _decode(source)
    # Extra same-line scopes activate formatting elsewhere in the file. Metadata
    # for the original declarations and exception names must remain identical.
    after = _decode(source + '\nfirst = lambda x: x; second = lambda y: y\n')
    for table in ('tries', 'raises', 'class_refs', 'signatures', 'genexpressions'):
        assert {key: after[table][key] for key in before[table]} == before[table]


def test_same_line_scopes_source(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for source scope comparisons')
    source = ROOT / 'examples/python_control/scope_collisions.py'
    spec = importlib.util.spec_from_file_location('scope_probes', source)
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    subjects = ('paired_generators', 'paired_consumers', 'nested_iterables',
                'paired_lambdas', 'paired_lists', 'unicode_columns', 'unicode_lambdas',
                'unicode_raise')
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
    run([sys.executable, ROOT / 'cartographer/render_lean.py', tmp_path / 'ast.json', model, 'Scopes'],
        ROOT, numeric_env)
    header = model.read_text() + '\nopen Autoform.Core Autoform.Generated.Scopes\n'
    calls = [f'runFunc program 180 "scope_collisions.py:<module>.{name}" [.int 2]' for name in subjects]
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
