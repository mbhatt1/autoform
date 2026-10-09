"""A bare annotation (`target: annotation`, no value) is not a read of its target.

Joern keeps only the target expression of `self.name: str`, which used to lower as an
attribute LOAD: click's `Parameter.__init__` raised AttributeError in Core where CPython
runs on (the re-land's one divergence). Language Reference §7.2.2: the target's
sub-expressions are evaluated, never its final access, and the annotation itself only
outside a function body and without `from __future__ import annotations`.
"""
import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

from conftest import exporter_source
from test_source_numeric import numeric_env, run  # noqa: F401  (fixture)

FUNCTION_SOURCE = '''class P:
    def __init__(self, xs):
        self.name: str
        xs[0]: int
        y: Undefined
        self.__hidden: int
        self.name = 1

    def touch(self):
        self.name
'''
MODULE_SOURCE = 'x: int\nz: Undefined\nw: "text"\n'
POSTPONED_SOURCE = 'from __future__ import annotations\nz: Undefined\n'


def decode(source):
    script = exporter_source()
    decoder = script.split('  val pythonHandlerDecoder = """', 1)[1].split('\n"""', 1)[0]
    result = subprocess.run([sys.executable, '-I', '-S', '-c', decoder],
                            input=source, text=True, capture_output=True, timeout=30)
    assert result.returncode == 0, result.stderr
    return json.loads(result.stdout)['bareAnnotations']


def test_bare_annotation_metadata():
    assert decode(FUNCTION_SOURCE) == {
        '3:9': {'target': 'attribute', 'name': 'name', 'annotation': 'unevaluated'},
        '4:9': {'target': 'subscript', 'name': None, 'annotation': 'unevaluated'},
        '5:9': {'target': 'name', 'name': 'y', 'annotation': 'unevaluated'},
        '6:9': {'target': 'attribute', 'name': '__hidden', 'annotation': 'unevaluated'},
    }
    # Module scope evaluates the annotation: a builtin or a constant is inert, an
    # arbitrary expression (which may raise NameError) is not.
    assert decode(MODULE_SOURCE) == {
        '1:1': {'target': 'name', 'name': 'x', 'annotation': 'inert'},
        '2:1': {'target': 'name', 'name': 'z', 'annotation': 'evaluated'},
        '3:1': {'target': 'name', 'name': 'w', 'annotation': 'inert'},
    }
    assert decode(POSTPONED_SOURCE)['2:1']['annotation'] == 'unevaluated'


def test_bare_annotation_lowering(tmp_path, numeric_env):  # noqa: F811
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for bare-annotation lowering')
    root = Path(__file__).resolve().parents[1]
    source = tmp_path / 'source'
    source.mkdir()
    (source / 'm.py').write_text(FUNCTION_SOURCE)
    (source / 'n.py').write_text(MODULE_SOURCE)
    joern = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (joern / 'joern-cli').is_dir():
        joern /= 'joern-cli'
    run([joern / 'joern-parse', source, '--language', 'PYTHONSRC', '--output', 'cpg.bin'],
        tmp_path, numeric_env, timeout=600)
    run([joern / 'joern', '--script', root / 'cartographer/export_ast.sc',
         '--param', 'cpgPath=cpg.bin', '--param', 'out=ast.json'],
        tmp_path, numeric_env, timeout=600)
    functions = {row['name']: row for row in json.loads((tmp_path / 'ast.json').read_text())}
    init = json.dumps(functions['m.py:<module>.P.__init__']['body'])
    # Only the receiver and the subscript operands are evaluated; no load survives.
    assert '"k": "field"' not in init and '"k": "index"' not in init
    assert '{"k": "exprS", "e": {"k": "name", "v": "self"}}' in init
    assert '{"k": "exprS", "e": {"k": "name", "v": "xs"}}' in init
    assert '{"k": "name", "v": "y"}' not in init
    # An ordinary expression statement still reads the attribute.
    assert functions['m.py:<module>.P.touch']['body'] == {
        'k': 'exprS', 'e': {'k': 'field', 'a': {'k': 'name', 'v': 'self'}, 'f': 'name'}}
    module = json.dumps(functions['n.py:<module>']['body'])
    assert module.count('stmt:annotation-evaluation') == 1
    # The frontend's synthetic `int = __builtins__.int` shares the 1:1 anchor; it survives.
    assert '"f": "int"' in module
