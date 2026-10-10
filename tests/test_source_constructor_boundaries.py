"""Calling an imported class value constructs the instance, as the lexical form does."""
import os
from pathlib import Path
import sys

import pytest

from test_source_numeric import ROOT, numeric_env, run


def test_imported_constructor_boundary(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for constructor boundary export')
    source = tmp_path / 'source'
    source.mkdir()
    (source / 'provider.py').write_text('''
class Base:
    def __init__(self, value):
        self.value = value
''')
    (source / 'consumer.py').write_text('''
from provider import Base

def make(value):
    return Base(value).value
''')
    joern = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (joern / 'joern-cli').is_dir():
        joern /= 'joern-cli'
    run([joern / 'joern-parse', source, '--language', 'PYTHONSRC', '--output', 'cpg.bin'],
        tmp_path, numeric_env, timeout=600)
    run([joern / 'joern', '--script', ROOT / 'cartographer/export_ast.sc',
         '--param', 'cpgPath=cpg.bin', '--param', 'out=ast.json'], tmp_path, numeric_env, timeout=600)
    # The importing module binds the exact class value `provider.py:<module>.Base<meta>`;
    # `Expr.callValue` on a class value re-dispatches to the `alloc` rule, so the
    # constructor runs and the instance's field is readable. CPython: `make(2) == 2`.
    model = tmp_path / 'Boundary.lean'
    run([sys.executable, ROOT / 'cartographer/render_lean.py', tmp_path / 'ast.json', model,
         'ConstructorBoundary'], ROOT, numeric_env)
    model.write_text(model.read_text() + f'''
open Autoform.Core Autoform.Generated.ConstructorBoundary
example : (match runMain program 80 moduleInits "consumer.py:<module>.make" [.int 2] with
    | .val (.int value) => value == 2
    | _ => false) = true := by decide +kernel
''')
    run(['lake', 'env', 'lean', model], ROOT, numeric_env, timeout=180)
