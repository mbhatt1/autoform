"""The NL autoformalizer's translate stage (`autoform.nl.translate`).

Pure-Python tests index committed Core ASTs. `AUTOFORM_TEST_LEAN=1` also builds the
initialized entry for the committed `ast-NLGlobals.json` and kernel-checks what the check
stage relies on; `AUTOFORM_TEST_JOERN=1` (with JOERN_HOME) runs the whole stage from source.
"""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))

from autoform.nl import schema, translate as T  # noqa: E402

PY_AST = ROOT / 'artifacts/compiler-rewrite/languages/PipelinePython/ast.json'
PY_SRC = ROOT / 'examples/source/python'
GLOBALS_AST = ROOT / 'tests/fixtures/nl/ast-NLGlobals.json'
GLOBALS_SRC = ROOT / 'tests/fixtures/nl/source-globals'


def by_source(infos):
    return {f.source_name: f for f in infos}


# --------------------------------------------------------------------------------------
# FunctionInfo extraction (no Joern, no Lean)
# --------------------------------------------------------------------------------------

def test_function_infos_pipeline_python():
    infos = by_source(T.function_infos(PY_AST, 'PipelinePython', PY_SRC, ROOT))
    assert sorted(infos) == ['add', 'fraction', 'quotient']      # synthetic inits dropped
    for name, line in (('add', 1), ('quotient', 4), ('fraction', 7)):
        f = infos[name]
        assert f.name == f'numbers.py:<module>.{name}'
        assert f.file == 'numbers.py' and f.line == line
        assert f.source.startswith(f'def {name}(a, b):') and 'return a' in f.source
        assert [p.name for p in f.params] == ['a', 'b']
        assert f.hole_free and f.holes == [] and f.call_closed and not f.needs_init
        assert f.callers == [] and f.tests == []


def test_function_infos_globals_fixture():
    infos = by_source(T.function_infos(GLOBALS_AST, 'NLGlobals', GLOBALS_SRC, ROOT))
    add, over, clamp, scaled = infos['add'], infos['over_limit'], infos['clamp'], infos['scaled']
    # Reading a module global (through the module object) needs the initialized heap.
    assert not add.needs_init and over.needs_init and clamp.needs_init and scaled.needs_init
    # A module-level call is lowered to a call of the module object's field; it resolves.
    assert over.callers == ['limits.py:<module>.clamp']
    assert add.callers == ['limits.py:<module>.Counter.bump']
    assert infos['__init__'].callers == ['tests/limits_cases.py:<module>.test_counter']
    assert all(f.call_closed and f.hole_free for f in infos.values())
    assert clamp.doc == 'Cap x at LIMIT.' and add.doc == 'Sum of two numbers.'
    # Methods are found under their class, not at the first `def` of that name.
    assert infos['bump'].line == 31 and infos['bump'].source.lstrip().startswith('def bump(self)')
    assert infos['bump'].tests[0] == dict(location='tests/limits_cases.py:12',
                                          text='assert c.bump() == 2', confidence='high')
    assert [t['text'] for t in clamp.tests] == ['assert clamp(5) == 3', 'assert clamp(2) == 2']


def test_free_names_and_needs_init():
    entry = {'name': 'm.py:<module>.f', 'params': ['x'], 'pythonSignature': {'isMethod': True},
             'body': {'k': 'seq',
                      'a': {'k': 'assign', 'x': 'y', 'e': {'k': 'name', 'v': 'x'}},
                      'b': {'k': 'ret', 'e': {'k': 'binop', 'op': '+',
                                              'a': {'k': 'field', 'a': {'k': 'name', 'v': 'self'},
                                                    'f': 'n'},
                                              'b': {'k': 'call', 'f': 'len',
                                                    'args': [{'k': 'name', 'v': 'y'}]}}}}}
    assert T.free_names(entry) == {'len'}
    assert not T.needs_init(entry, set(), {'len'})
    assert T.needs_init(entry, {'len'}, set())                # rebound at module level
    reads_module = {'name': 'g', 'params': [], 'body': {'k': 'ret', 'e': {
        'k': 'field', 'a': {'k': 'name', 'v': '<module>m.py'}, 'f': 'LIMIT'}}}
    assert T.needs_init(reads_module, set(), set())
    captured = {'name': 'h', 'params': [], 'body': {'k': 'ret', 'e': {'k': 'name', 'v': 'outer'}}}
    assert T.needs_init(captured, set(), set())               # a closure capture is non-local
    declared = {'name': 'k', 'params': [], 'body': {'k': 'seq',
                'a': {'k': 'declGlobal', 'x': 'N'},
                'b': {'k': 'assign', 'x': 'N', 'e': {'k': 'name', 'v': 'N'}}}}
    assert T.free_names(declared) == {'N'}


def test_builtin_aliases_are_not_module_state():
    entries = [{'name': '<init>', 'body': {'k': 'seq',
                'a': {'k': 'setGlobal', 'x': 'len', 'e': {'k': 'fnref', 'v': '__builtin.len'}},
                'b': {'k': 'setGlobal', 'x': 'LIMIT', 'e': {'k': 'int', 'v': '3'}}}}]
    assert T.module_globals(entries) == ({'LIMIT'}, {'len'})


def test_call_resolver_open_and_closed():
    entries = [
        {'name': 'm.py:<module>.f', 'params': ['g'], 'body': {'k': 'seq',
         'a': {'k': 'exprS', 'e': {'k': 'callV', 'f': {'k': 'name', 'v': 'g'}, 'args': []}},
         'b': {'k': 'exprS', 'e': {'k': 'callV', 'f': {'k': 'field', 'a': {
             'k': 'name', 'v': '<module>m.py'}, 'f': 'h'}, 'args': []}}}},
        {'name': 'm.py:<module>.h', 'params': [], 'body': {'k': 'ret', 'e': {'k': 'call',
         'f': 'len', 'args': [{'k': 'str', 'v': 'x'}]}}},
    ]
    r = T.CallResolver(entries, {'len'})
    assert r.callees(entries[0]) == {'m.py:<module>.h'}
    assert not r.closed(entries[0])            # calling the parameter `g` is dynamic
    assert r.closed(entries[1])                # a builtin is closed


def test_locate_methods_and_mangled_names(tmp_path):
    (tmp_path / 'm.py').write_text(
        'class A:\n'
        '    def get(self):\n'
        '        return 1\n'
        '\n'
        'class B:\n'
        '    @property\n'
        '    def get(self):\n'
        '        """B.get doc"""\n'
        '        return 2\n'
        '\n'
        '    def __touch(self):\n'
        '        return 3\n')
    from autoform.harness import cpir
    cache = {}

    def fn(name, source_name):
        return cpir.Function('F', name, source_name, 'm.py', [], 'any')
    line, text, doc, owner = T.locate(tmp_path, fn('m.py:<module>.B.get', 'get'), cache)
    assert (line, owner, doc) == (7, 'B', 'B.get doc')
    assert text.startswith('    @property\n    def get(self):') and 'return 2' in text
    assert T.locate(tmp_path, fn('m.py:<module>.A.get', 'get'), cache)[0] == 2
    assert T.locate(tmp_path, fn('m.py:<module>.B._B__touch', '_B__touch'), cache)[0] == 11


def test_test_index_confidence(tmp_path):
    (tmp_path / 'tests').mkdir()
    (tmp_path / 'tests/test_x.py').write_text(
        'from pkg import Cache\n'
        'c = Cache(3)\n'
        'assert c.get(1) is None\n'
        'assert other.get(2) is None\n')
    (tmp_path / 'tests/test_y.py').write_text('d = {}\nd.get(1)\n')
    idx = T.TestIndex([tmp_path], primary=tmp_path)
    refs = idx.lookup('get', owner='Cache')
    assert [(r['location'], r['confidence']) for r in refs] == [
        ('tests/test_x.py:3', 'high'), ('tests/test_x.py:4', 'low')]   # test_y never names Cache
    assert idx.lookup('__init__', owner='Cache')[0]['text'] == 'c = Cache(3)'
    assert idx.lookup('__repr__', owner='Cache') == []


def test_module_names():
    assert T.default_module('cachetools-7.1.7-sdist') == 'NLCachetools717Sdist'
    assert T.repo_name('https://github.com/psf/requests.git') == 'requests'
    assert T.choose_module('x', None, ROOT).startswith('NL')
    with pytest.raises(T.TranslateError):
        T.choose_module('x', 'Cachetools', ROOT)           # a tracked module
    with pytest.raises(T.TranslateError):
        T.choose_module('x', 'bad name', ROOT)


def test_translate_without_lean_writes_contract(tmp_path):
    tr = T.translate(str(PY_SRC), 'NLTestNoBuild', ROOT, tmp_path, ast=PY_AST, build=False)
    try:
        data = json.loads((tmp_path / schema.FILES['translation']).read_text())
        assert set(data) == set(schema.Translation.__dataclass_fields__)
        assert set(data['functions'][0]) == set(schema.FunctionInfo.__dataclass_fields__)
        assert data['language'] == 'python' and data['init_const'] is None
        assert data['call_template'] == \
            'runFunc Autoform.Generated.NLTestNoBuild.program 1000 {name} {args}'
        assert data['source_root'] == str(PY_SRC.resolve())
        assert data['source_revision']
        assert len(tr.functions) == 3
    finally:
        (ROOT / 'Autoform/Generated/NLTestNoBuild.lean').unlink(missing_ok=True)


def test_init_module_text_is_self_certifying():
    text = T.init_module_text('NLX', '[]', '0')
    assert 'theorem init_eq : initGlobals program 5000 Autoform.Generated.NLX.moduleInits = init' in text
    assert 'decide +kernel' in text and 'def call (name : String) (args : List Val) : EResult' in text
    for banned in ('sorry', 'native_decide', 'axiom '):
        assert banned not in text


# --------------------------------------------------------------------------------------
# Lean: the initialized entry, kernel-checked
# --------------------------------------------------------------------------------------

def lean_env():
    env = T.tool_env()
    if not shutil.which('lake', path=env['PATH']):
        pytest.skip('Lean is not installed')
    return env


GUARD = '''import Autoform.NL.{m}
open Autoform.Core
abbrev P := Autoform.Generated.{m}.program
-- no module state: `call` agrees with `runFunc`
example : Autoform.NL.{m}.call "limits.py:<module>.add" [.int 2, .int 3] =
    runFunc P 1000 "limits.py:<module>.add" [.int 2, .int 3] := by decide +kernel
example : Autoform.NL.{m}.call "limits.py:<module>.add" [.int 2, .int 3] = .val (.int 5) := by
  decide +kernel
-- reads a module global: a value through `call` ...
example : Autoform.NL.{m}.call "limits.py:<module>.over_limit" [.int 5] = .val (.bool true) := by
  decide +kernel
example : Autoform.NL.{m}.call "limits.py:<module>.clamp" [.int 5] = .val (.int 3) := by
  decide +kernel
-- ... and a hole through the empty-heap `runFunc`
example : (match runFunc P 1000 "limits.py:<module>.over_limit" [.int 5] with
           | .hole _ => true | _ => false) = true := by decide +kernel
'''


def check_initialized_entry(tr, env, tmp_path):
    m = tr.module
    assert tr.init_const == f'Autoform.NL.{m}.init'
    assert tr.call_template == f'Autoform.NL.{m}.call {{name}} {{args}}'
    guard = tmp_path / 'Guard.lean'
    guard.write_text(GUARD.format(m=m))
    r = subprocess.run(['lake', 'env', 'lean', str(guard)], cwd=ROOT, env=env,
                       capture_output=True, text=True, timeout=1800)
    assert r.returncode == 0, r.stdout + r.stderr


def cleanup(module):
    for rel in (f'Autoform/Generated/{module}.lean', f'Autoform/NL/{module}.lean'):
        (ROOT / rel).unlink(missing_ok=True)


@pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_LEAN') != '1',
                    reason='set AUTOFORM_TEST_LEAN=1 to build the initialized entry')
def test_initialized_entry_kernel_checked(tmp_path):
    env = lean_env()
    try:
        tr = T.translate(str(GLOBALS_SRC), 'NLTestGlobals', ROOT, tmp_path / 'run',
                         ast=GLOBALS_AST)
        check_initialized_entry(tr, env, tmp_path)
    finally:
        cleanup('NLTestGlobals')


# --------------------------------------------------------------------------------------
# Joern: the whole stage from source
# --------------------------------------------------------------------------------------

def joern_or_skip():
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 (and JOERN_HOME) to run Joern')
    try:
        T.joern_home()
    except T.TranslateError as exc:
        pytest.skip(str(exc))


def test_translate_python_example_with_joern(tmp_path):
    joern_or_skip()
    env = lean_env()
    try:
        tr = T.translate(str(PY_SRC), 'NLTestPython', ROOT, tmp_path)
        fs = by_source(tr.functions)
        assert sorted(fs) == ['add', 'fraction', 'quotient']
        assert all(f.hole_free and f.call_closed and not f.needs_init for f in fs.values())
        assert fs['fraction'].line == 7 and fs['fraction'].source.startswith('def fraction')
        assert tr.init_const is None
        assert tr.call_template.startswith('runFunc Autoform.Generated.NLTestPython.program')
        loaded = schema.load(tmp_path / 'translation.json')
        assert loaded['module'] == 'NLTestPython' and Path(loaded['ast']).is_file()
        probe = tmp_path / 'Probe.lean'
        probe.write_text('import Autoform.Generated.NLTestPython\nimport Autoform.NL.Basis\n'
                         'open Autoform.Core\n'
                         'example : runFunc Autoform.Generated.NLTestPython.program 1000 '
                         '"numbers.py:<module>.add" [.int 2, .int 3] = .val (.int 5) := '
                         'by decide +kernel\n')
        r = subprocess.run(['lake', 'env', 'lean', str(probe)], cwd=ROOT, env=env,
                           capture_output=True, text=True, timeout=1800)
        assert r.returncode == 0, r.stdout + r.stderr
    finally:
        cleanup('NLTestPython')


def test_translate_globals_with_joern(tmp_path):
    joern_or_skip()
    env = lean_env()
    try:
        tr = T.translate(str(GLOBALS_SRC), 'NLTestGlobalsJ', ROOT, tmp_path / 'run')
        assert sum(f.needs_init for f in tr.functions) >= 4
        check_initialized_entry(tr, env, tmp_path)
    finally:
        cleanup('NLTestGlobalsJ')
