"""Decorators the program defines are applied when the definition executes.

Language Reference §8.7: `@d1 @d2 def g(...)` binds `g = d1(d2(<function g>))` in the
defining scope; the decorator expressions are evaluated top-down before the function
object exists, and the applications run bottom-up. The exporter keeps the RAW body under
`<name><undecorated>` and makes the source name an auxiliary entry that reads the rebound
binding. Every entry point of `examples/python_control/decorators.py` is compared with
CPython; every refusal is asserted by name.
"""
import importlib.util
import json
import os
from pathlib import Path
import sys

import pytest

from test_python_signatures import _decode
from test_source_numeric import PROGRAM_CONTEXT, ROOT, numeric_env, run


SOURCE = ROOT / 'examples/python_control/decorators.py'
PREFIX = 'decorators.py:<module>.'
# Entry points compared value-for-value with CPython, each called with the argument 2.
COMPARED = ('use_inc', 'use_plain', 'use_stacked', 'use_replaced', 'use_rebinding',
            'use_order', 'use_tags', 'use_local', 'use_method', 'use_bound', 'use_same',
            # the decorated source entries themselves: the auxiliary forwarding function
            'inc', 'plain', 'stacked', 'replaced', 'tagged_first', 'tagged_second')
# Entry points that stop at a named gap instead of computing a value.
REFUSED = {
    # `@_local` reads a name the class body binds; applying it in the module scope
    # would read a different binding, so the attribute stays opaque.
    'use_holder': 'class-attribute:decorator',
    # `functools.wraps` is external: calling it is a gap, never a guess (Milestone 3).
    'use_wraps': 'mcall:<absent:external>functools.wraps:not-a-class-method',
    # `Box.value(obj, 4)`: a class-value method call to a STORED attribute is not
    # dispatched by `.mcall` on a class value; it stays the existing named gap.
    'use_class_attribute': 'mcall:decorators.py:<module>.Box.value:not-a-class-method',
}
# Definitions whose decorators are applied: raw body, and whether a source entry exists.
APPLIED = {'inc': True, 'plain': True, 'stacked': True, 'replaced': True,
           'tagged_first': True, 'tagged_second': True, 'Box.value': True, 'Box.same': True,
           'use_local.inner': False, 'use_wraps.inner': False}
# The static gaps left in the translated bodies, by function.
STATIC_GAPS = {
    'wraps_deco.wrapper': 'decorator:external:functools.wraps',
    'Holder.m': 'decorator:class-body:class-local-name',
    'Holder._local': 'call:python-receiver-signature',
}


def _native():
    spec = importlib.util.spec_from_file_location('native_decorators', SOURCE)
    native = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(native)
    return native


def _labels(node):
    if isinstance(node, dict):
        if node.get('k') in ('hole', 'holeS'):
            yield node['label']
        for value in node.values():
            yield from _labels(value)
    elif isinstance(node, list):
        for value in node:
            yield from _labels(value)


def test_decorator_source_metadata():
    decoded = _decode(SOURCE.read_text())
    records = {}
    for row in decoded['signatures'].values():
        records.setdefault(row['name'], row)
    assert records['stacked']['decoratorNames'] == ['traced', 'traced', 'twice']
    assert records['plain']['decoratorNames'] == ['add']
    external = [row for row in decoded['signatures'].values()
                if row['decoratorNames'] == ['functools.wraps']]
    assert len(external) == 1 and external[0]['name'] == 'wrapper' and external[0]['decorated']
    # Only the class-body shape that reads a class-local name is refused.
    refused = {row['name']: row['decoratorRefusal'] for row in decoded['signatures'].values()
               if row['decoratorRefusal']}
    assert refused == {'m': 'decorator:class-body:class-local-name'}
    classes = {row['shortName']: {a['name']: a for a in row['attributes']}
               for row in decoded['classDeclarations']}
    assert classes['Box']['value']['kind'] == 'decorated'
    assert classes['Box']['same']['kind'] == 'decorated'
    assert classes['Box']['__init__']['kind'] == 'method'
    assert classes['Holder']['m']['kind'] == 'decorated'


def test_decorator_class_body_refusals_by_name():
    source = '''
def deco(f):
    return f
class Outer:
    class Inner:
        @deco
        def nested(self):
            return 1
    @deco
    def twice(self):
        return 1
    @deco
    def twice(self):
        return 2
    @(lambda f: f)
    def shaped(self):
        return 3
    @deco
    def fine(self):
        return 4
class Outer2:
    @Outer2
    def own_name(self):
        return 5
'''
    decoded = _decode(source)
    refused = sorted((row['name'], row['decoratorRefusal'])
                     for row in decoded['signatures'].values() if row['decoratorRefusal'])
    assert refused == [
        ('nested', 'decorator:class-body:nested-class'),
        ('own_name', 'decorator:class-body:class-local-name'),
        ('shaped', 'decorator:class-body:expression-shape'),
        ('twice', 'decorator:class-body:redefined-member'),
        ('twice', 'decorator:class-body:redefined-member'),
    ]


def test_differential_routes_raw_frames(differential):
    funcs = [{'name': PREFIX + 'inc<undecorated>', 'undecoratedOf': PREFIX + 'inc',
              'params': ['x'], 'body': {'k': 'skip'}},
             {'name': PREFIX + 'use_inc', 'params': ['x'], 'body': {'k': 'skip'}}]
    assert differential.undecorated_bodies(funcs) == {PREFIX + 'inc': PREFIX + 'inc<undecorated>'}
    # The raw body has no stable call site of its own; only its source name classifies.
    assert differential.classify(funcs[0]) is None
    assert differential.classify({'name': PREFIX + 'inc'}) == ('decorators.py', 'inc', False)


def test_python_decorators_source(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for decorator translation')
    native = _native()
    # CPython's order: decorator expressions top-down, applications bottom-up.
    assert native.trace == ['a', 'b', 'b!', 'a!']
    folder = tmp_path / 'source'
    folder.mkdir()
    (folder / SOURCE.name).write_bytes(SOURCE.read_bytes())
    joern = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (joern / 'joern-cli').is_dir():
        joern /= 'joern-cli'
    run([joern / 'joern-parse', folder, '--language', 'PYTHONSRC', '--output', 'cpg.bin'],
        tmp_path, numeric_env, timeout=600)
    run([joern / 'joern', '--script', ROOT / 'cartographer/export_ast.sc',
         '--param', 'cpgPath=cpg.bin', '--param', 'out=ast.json'], tmp_path, numeric_env, timeout=600)
    rows = json.loads((tmp_path / 'ast.json').read_text())
    functions = {row['name']: row for row in rows}

    # No in-program decorator is left as the old binding gap.
    assert 'call:python-decorator-binding' not in set(_labels(rows))
    # Raw bodies are distinct from the decorated source entries.
    for name, has_entry in APPLIED.items():
        raw = functions[PREFIX + name + '<undecorated>']
        assert raw['undecoratedOf'] == PREFIX + name
        assert not list(_labels(raw['body'])), name
        assert raw['pythonSignature']['isMethod'] is False
        assert PREFIX + name not in functions
        entries = [entry['name'] for entry in raw.get('decoratedEntries', [])]
        assert entries == ([PREFIX + name] if has_entry else []), name
    # A decorated method's raw body keeps `self`: it is the function object the
    # decorator receives, and the wrapper passes the instance positionally.
    assert functions[PREFIX + 'Box.value<undecorated>']['params'] == ['self', 'n']
    # Every static gap, by name and by function; nothing else is a hole.
    gaps = {name[len(PREFIX):]: sorted(set(_labels(row['body'])))
            for name, row in functions.items() if list(_labels(row['body']))}
    assert gaps == {name: [label] for name, label in STATIC_GAPS.items()}

    # The module body applies each decorator VALUE (never a static callee) to the raw body.
    init = json.dumps(functions['decorators.py:<module>']['body'])
    assert json.dumps({'k': 'setField', 'r': {'k': 'name', 'v': '<module>decorators.py'},
                       'f': 'inc', 'v': {'k': 'callV', 'f': {'k': 'field', 'a': {
                           'k': 'name', 'v': '<module>decorators.py'}, 'f': 'twice'},
                           'args': [{'k': 'fnref', 'v': PREFIX + 'inc<undecorated>'}]}}) in init
    assert '"k": "call", "f": "decorators.py:<module>.twice"' not in init
    # The class body's applications write the class attributes they bind.
    assert '"k": "setGlobal", "x": "<classattr>decorators.py:<module>.Box.value"' in init
    # A decorated definition is not pre-bound before the module body runs.
    objects = json.dumps(functions['<module-objects>:<module>']['body'])
    assert '"f": "inc"' not in objects and '"f": "plain"' not in objects
    declarations = {row['name']: {a['name']: (a['kind'], a['value']) for a in row['attributes']}
                    for row in functions['decorators.py:<module>']['classDeclarations']}
    assert declarations[PREFIX + 'Box']['value'] == ('stored', '<classattr>' + PREFIX + 'Box.value')
    assert declarations[PREFIX + 'Holder']['m'] == ('opaque', 'class-attribute:decorator')

    model = tmp_path / 'Model.lean'
    run([sys.executable, ROOT / 'cartographer/render_lean.py', tmp_path / 'ast.json', model,
         'Decorators'], ROOT, numeric_env)
    header = model.read_text() + '\nopen Autoform.Core Autoform.Generated.Decorators\n'
    # Every call starts after the module ran, as the native calls do after import.
    header += 'private def sourceGlobals : Heap × Ref := initGlobals program 600 moduleInits\n'
    header += ('private def sourceCtx : Ctx := { (' + PROGRAM_CONTEXT +
               ' : Ctx) with globals := sourceGlobals.2 }\n')
    subjects = list(COMPARED) + list(REFUSED) + ['inc<undecorated>', 'Box.same<undecorated>']
    expected = []
    for name in subjects:
        if name in REFUSED:
            expected.append('hole:' + REFUSED[name])
        elif name == 'inc<undecorated>':
            # The raw function object, as CPython holds it in the wrapper's closure.
            expected.append('value:' + str(native.inc.__closure__[0].cell_contents(2)))
        elif name == 'Box.same<undecorated>':
            # `@keep` returned the raw function unchanged; call it as a plain function.
            expected.append('value:' + str(native.Box.same(native.Box(2), 2)))
        else:
            expected.append('value:' + str(getattr(native, name)(2)))
    calls = []
    for name in subjects:
        if name == 'Box.same<undecorated>':
            # The raw method body takes `(self, n)` as a plain function: call it with a
            # real instance, as the bound method `@keep` leaves in the class would.
            expression = ('(.callValue (.fnref "' + PREFIX + 'Box.same<undecorated>") '
                          '[.alloc "' + PREFIX + 'Box" [.lit (.int 2)], .lit (.int 2)])')
        else:
            expression = f'(.call {json.dumps(PREFIX + name)} [.lit (.int 2)])'
        calls.append(f'(evalExpr sourceCtx 600 sourceGlobals.1 [] {expression}).2')
    driver = header + 'def main : IO Unit := do\n'
    for call in calls:
        driver += (f'  match {call} with\n'
                   '  | .val (.int value) => IO.println ("value:" ++ toString value)\n'
                   '  | .exn (.str name) => IO.println ("exception:" ++ name)\n'
                   '  | .hole label => IO.println ("hole:" ++ label)\n'
                   '  | other => IO.println (reprStr other)\n')
    (tmp_path / 'Observe.lean').write_text(driver)
    observed = run(['lake', 'env', 'lean', '--run', tmp_path / 'Observe.lean'],
                   ROOT, numeric_env, timeout=600).splitlines()
    report = dict(subjects=subjects, observed=observed, expected=expected)
    (tmp_path / 'native-comparison.json').write_text(json.dumps(report, indent=2) + '\n')
    assert observed == expected, json.dumps(report, indent=2)
    # The same outcomes, checked by the kernel.
    proofs = header + '\nset_option maxRecDepth 20000\nset_option maxHeartbeats 0\n'
    for call, want in zip(calls, expected):
        category, value = want.split(':', 1)
        pattern = (f'.val (.int value) => value == ({value} : Int)' if category == 'value' else
                   f'.hole label => label == {json.dumps(value)}')
        proofs += (f'example : (match {call} with\n  | {pattern}\n  | _ => false) = true := by\n'
                   '  first | decide +kernel | fail "decorator outcome was not established"\n')
    (tmp_path / 'Proofs.lean').write_text(proofs)
    run(['lake', 'env', 'lean', tmp_path / 'Proofs.lean'], ROOT, numeric_env, timeout=1800)
