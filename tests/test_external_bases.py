"""External base contracts: `class C(collections.abc.MutableMapping)` is resolvable.

`scripts/external_bases.py` is the source of truth; `Autoform/Lang/Core/ExternalBases.lean`
is emitted from it; the exporter marks such bases `<external>module.qualname`; the kernel
answers lookups through them; and the oracle verifies each contract against the live
class before it encodes a receiver. Each of those links is checked here.
"""
import importlib
import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

from conftest import exporter_source
from test_source_numeric import ROOT, numeric_env, run  # noqa: F401  (fixture)

sys.path.insert(0, str(ROOT / 'scripts'))
import external_bases  # noqa: E402


def test_lean_mirror_is_in_sync():
    lean = (ROOT / 'Autoform/Lang/Core/ExternalBases.lean').read_text(encoding='utf-8')
    assert lean == external_bases.lean_text(), (
        'Autoform/Lang/Core/ExternalBases.lean differs from scripts/external_bases.py; '
        'regenerate it with: python scripts/external_bases.py --emit-lean '
        'Autoform/Lang/Core/ExternalBases.lean')


def test_contracts_against_the_running_interpreter():
    """On the pinned interpreter every contract matches. On another version the ones
    that drifted must be REFUSED by `verify` -- the oracle then declines to encode a
    receiver through them instead of comparing against a wrong model."""
    drifted = []
    for name in sorted(external_bases.CONTRACTS):
        module, _, qual = name.rpartition('.')
        cls = getattr(importlib.import_module(module), qual)
        reason = external_bases.verify(cls)
        if reason is not None:
            drifted.append(reason)
            assert reason.startswith('external-base-contract-mismatch:'), reason
    pinned = tuple(int(x) for x in external_bases.PINNED_PYTHON.split('.'))
    if sys.version_info[:2] == pinned:
        assert drifted == [], drifted
    # A storage-bearing ABC is never contracted, whatever the version: it is absent from
    # the table, and `has_storage` is why.
    import collections.abc
    assert 'collections.abc.KeysView' not in external_bases.CONTRACTS
    assert external_bases.has_storage(collections.abc.KeysView)
    assert external_bases.verify(collections.abc.KeysView) == \
        'external-base-uncontracted:collections.abc.KeysView'
    assert external_bases.verify(dict) == 'external-base-uncontracted:builtins.dict'


SOURCE = '''import collections.abc
from collections.abc import Sized as SizedABC
import json
from .base import Base, Outer
import os, os.path
try:
    import yaml
except ImportError:
    yaml = None
class C(collections.abc.MutableMapping): pass
class D(Base): pass
class E(json.JSONEncoder): pass
class F(SizedABC): pass
class G(Outer.Inner): pass
class H(yaml.YAMLObject): pass
class I(os.path.X): pass
def f():
    import json
    class J(json.JSONDecoder): pass
'''


def test_decoder_records_imported_bases():
    script = exporter_source()
    decoder = script.split('  val pythonHandlerDecoder = """', 1)[1].split('\n"""', 1)[0]
    result = subprocess.run([sys.executable, '-I', '-S', '-c', decoder],
                            input=SOURCE, text=True, capture_output=True, timeout=30)
    assert result.returncode == 0, result.stderr
    rows = {c['shortName']: [b['imported'] for b in c['bases']]
            for c in json.loads(result.stdout)['classDeclarations']}
    assert rows['C'] == [{'level': 0, 'module': 'collections', 'attribute': 'abc.MutableMapping'}]
    assert rows['D'] == [{'level': 1, 'module': 'base', 'attribute': 'Base'}]
    assert rows['E'] == [{'level': 0, 'module': 'json', 'attribute': 'JSONEncoder'}]
    assert rows['F'] == [{'level': 0, 'module': 'collections.abc', 'attribute': 'Sized'}]
    assert rows['G'] == [{'level': 1, 'module': 'base', 'attribute': 'Outer.Inner'}]
    # `import os, os.path` binds `os` once (to the same module), so the base is an
    # attribute path inside it; a conditional import is rebound by assignment, and a
    # function-local import is not a module binding -- those two are not known imports.
    assert rows['I'] == [{'level': 0, 'module': 'os', 'attribute': 'path.X'}]
    assert rows['H'] == [None] and rows['J'] == [None]


def test_exporter_resolves_bases(tmp_path, numeric_env):  # noqa: F811
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for exporter base resolution')
    package = tmp_path / 'source' / 'pkg'
    package.mkdir(parents=True)
    (package / '__init__.py').write_text(SOURCE.replace('class H', 'class H_')
                                         .replace('(yaml.YAMLObject)', '(object)')
                                         .replace('class I(os.path.X)', 'class I_(object)'))
    (package / 'base.py').write_text('class Base:\n    pass\n\nclass Outer:\n    class Inner:\n        pass\n')
    joern = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (joern / 'joern-cli').is_dir():
        joern /= 'joern-cli'
    run([joern / 'joern-parse', tmp_path / 'source', '--language', 'PYTHONSRC', '--output', 'cpg.bin'],
        tmp_path, numeric_env, timeout=600)
    run([joern / 'joern', '--script', ROOT / 'cartographer/export_ast.sc',
         '--param', 'cpgPath=cpg.bin', '--param', 'out=ast.json'],
        tmp_path, numeric_env, timeout=600)
    bases = {d['name'].split('.')[-1]: d['bases']
             for f in json.loads((tmp_path / 'ast.json').read_text())
             for d in f.get('classDeclarations', [])}
    assert bases['C'] == ['<external>collections.abc.MutableMapping']
    assert bases['F'] == ['<external>collections.abc.Sized']
    assert bases['E'] == ['<external>json.JSONEncoder']        # uncontracted: Lean leaves it unresolved
    assert bases['D'] == ['pkg/base.py:<module>.Base']
    assert bases['G'] == ['pkg/base.py:<module>.Outer.Inner']
    assert bases['J'] == ['<unresolved-base>pkg/__init__.py:<module>.f.J:0']


def test_contracted_lookup_kernel(tmp_path, numeric_env):  # noqa: F811
    path = tmp_path / 'ExternalBaseLookup.lean'
    path.write_text(r'''import Autoform.Lang.Core.ClassHierarchy
open Autoform.Core
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def graph : List ClassDecl :=
  [{ name := "m.Cache", shortName := "Cache", bases := ["<external>collections.abc.MutableMapping"],
     attributes := [("__getitem__", .method "m.Cache.__getitem__"), ("__setitem__", .method "m.Cache.__setitem__"),
                    ("__delitem__", .method "m.Cache.__delitem__"), ("__iter__", .method "m.Cache.__iter__"),
                    ("__len__", .method "m.Cache.__len__"), ("size", .method "m.Cache.size")] },
   { name := "m.Partial", shortName := "Partial", bases := ["<external>collections.abc.MutableMapping"],
     attributes := [("__getitem__", .method "m.Partial.__getitem__")] },
   { name := "m.Odd", shortName := "Odd", bases := ["<external>foo.Bar"] }]
-- The contracted base is one node of a complete order.
example : (ClassHierarchy.linearize graph "m.Cache" ==
    .complete ["m.Cache", "<external>collections.abc.MutableMapping", "__builtin.object"]) = true := by
  decide +kernel
-- An own member is found; a name the ABC provides is an opaque member of the base; a
-- name neither defines is absent (CPython: AttributeError); `__init__` falls to object.
example : (ClassHierarchy.lookup graph "Cache" "size" == .found "m.Cache" (.method "m.Cache.size")) = true := by
  decide +kernel
example : (ClassHierarchy.lookup graph "Cache" "get" == .found "<external>collections.abc.MutableMapping"
    (.opaque "class-attribute:external-base:<external>collections.abc.MutableMapping:get")) = true := by
  decide +kernel
example : (ClassHierarchy.lookup graph "Cache" "nothing" == .absent) = true := by decide +kernel
example : (ClassHierarchy.lookup graph "Cache" "__init__" ==
    .found "__builtin.object" (.opaque "class-attribute:object:__init__")) = true := by decide +kernel
-- Abstract methods: all implemented, or the first unimplemented one by name.
example : ClassHierarchy.unimplementedAbstract graph
    ["m.Cache", "<external>collections.abc.MutableMapping", "__builtin.object"] = none := by decide +kernel
example : ClassHierarchy.unimplementedAbstract graph
    ["m.Partial", "<external>collections.abc.MutableMapping", "__builtin.object"] = some "__delitem__" := by
  decide +kernel
-- An uncontracted external base is unresolved, exactly as before.
example : (ClassHierarchy.lookup graph "Odd" "size" ==
    .blocked "class-hierarchy:unresolved-base:<external>foo.Bar") = true := by decide +kernel
''')
    run(['lake', 'env', 'lean', path], ROOT, numeric_env, timeout=300)
