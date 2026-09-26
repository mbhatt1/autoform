"""Cross-runtime post-state observations must detect effects even with equal returns."""
import copy
import inspect
import os
from pathlib import Path

import pytest

from conftest import ROOT, SCRIPTS, load
from test_source_numeric import numeric_env, run


class Node:
    pass


def encoder(differential):
    return differential.GraphEncoder({(os.path.realpath(inspect.getsourcefile(Node)),
                                        'Node'): 'nodes.py:<module>.Node'})


def test_snapshots_keep_aliases_cycles_detached_inputs_and_fresh_results(differential):
    enc = encoder(differential)
    old = Node()
    old.next = old
    shared = [old]
    root = {'left': shared, 'right': shared}
    arg = enc.enc(root)
    enc.freeze()
    before = copy.deepcopy(enc.input_heap)
    shared.clear()
    old.next = None
    new = [root]
    new.append(new)
    record = differential.finish_record(enc, dict(args=[arg], self=None,
                                        outcome=('val', enc.enc_result(new))))
    assert record['heap'] == before
    assert record['heap'][0][2][1][0][1] == record['heap'][0][2][1][1][1]
    assert record['post_heap'][1] == ('list', [], ('list', []))
    assert record['post_heap'][2][1] == [('next', ('unit',))]
    assert record['outcome'] == ('val', ('ref', 3))
    assert record['post_heap'][3][2] == ('list', [('ref', 0), ('ref', 3)])


def test_unsupported_post_state_is_refused(differential):
    enc = encoder(differential)
    arg = []
    enc.enc(arg)
    enc.freeze()
    arg.append(set())
    with pytest.raises(differential.Unencodable):
        differential.finish_record(enc, {'outcome': ('val', ('unit',))})


def test_direct_exception_keeps_mutated_arguments(differential):
    def remove_then_raise(items):
        items.pop()
        raise ValueError()
    out = []
    differential._direct_cases(remove_then_raise,
        {'name': 'm.py:<module>.remove_then_raise', 'params': ['items']},
        {'items': [[1]]}, 1, out, lambda: encoder(differential))
    assert out[0]['outcome'] == ('exn', 'ValueError')
    assert out[0]['heap'][0][2] == ('list', [('int', 1)])
    assert out[0]['post_heap'][0][2] == ('list', [])


def test_graph_record_validation_never_downgrades(differential):
    from native_heap import validate_records
    enc = encoder(differential)
    arg = enc.enc([])
    enc.freeze()
    record = differential.finish_record(enc, dict(name='f', args=[arg], self=None,
        outcome=('val', arg), runtime='cpython'))
    report = {'measurement_basis': 'python+heap-graph-v1'}
    validate_records([record], report, [{'name': 'f'}])
    for broken, basis in [(dict(record, post_heap=[]), report),
                          ({k: v for k, v in record.items() if k != 'post_heap'}, report),
                          (record, {'measurement_basis': 'python'})]:
        with pytest.raises(ValueError, match='heap graph'):
            validate_records([broken], basis, [{'name': 'f'}])


def test_function_code_identity_and_changed_attributes(differential, tmp_path):
    from native_heap import function_identities
    path = tmp_path / 'mod.py'
    path.write_text('def f():\n    return 1\n')
    ns = {}
    exec(compile(path.read_text(), str(path), 'exec'), ns)
    funcs = [{'name': 'mod.py:<module>.f', 'file': 'mod.py'}]
    identities = function_identities(funcs, tmp_path)
    enc = differential.GraphEncoder({}, identities)
    assert enc.enc(ns['f']) == ('fn', 'mod.py:<module>.f')
    enc.freeze()
    ns['f'].changed = True
    with pytest.raises(differential.Unencodable, match='callable-attributes'):
        enc.post_state()
    path.write_text(path.read_text() + '\ndef f():\n    return 2\n')
    assert not function_identities(funcs, tmp_path)


@pytest.fixture
def plain_function(differential, tmp_path):
    from native_heap import function_identities
    path = tmp_path / 'plain.py'
    path.write_text('def f():\n    return 1\n')
    ns = {'__name__': 'plain'}
    exec(compile(path.read_text(), str(path), 'exec'), ns)
    identities = function_identities([{'name': 'plain.py:<module>.f', 'file': 'plain.py'}],
                                     tmp_path)
    return ns['f'], differential.GraphEncoder({}, identities)


@pytest.mark.parametrize('field', ['__module__', '__doc__'])
@pytest.mark.parametrize('after_call', [False, True])
def test_mutable_function_metadata_is_refused(differential, plain_function, field, after_call):
    fn, enc = plain_function
    if after_call:
        enc.enc(fn)
        enc.freeze()
    setattr(fn, field, [])
    with pytest.raises(differential.Unencodable, match='callable-metadata-state'):
        enc.post_state() if after_call else enc.enc(fn)


@pytest.mark.parametrize('field', ['__name__', '__qualname__', '__module__', '__doc__'])
def test_function_metadata_equality_hooks_never_run(differential, plain_function, field):
    class HookedString(str):
        def __eq__(self, other):
            pytest.fail('metadata equality hook ran')
        def __ne__(self, other):
            pytest.fail('metadata inequality hook ran')
    fn, enc = plain_function
    setattr(fn, field, HookedString('f'))
    with pytest.raises(differential.Unencodable, match='callable-metadata-state'):
        enc.enc(fn)


@pytest.mark.parametrize('field,reason', [
    ('__dict__', 'callable-attributes'),
    ('__annotations__', 'callable-annotations'),
    ('__kwdefaults__', 'callable-default-state'),
    ('__defaults__', 'callable-default-state'),
])
def test_function_state_truth_hooks_never_run(differential, plain_function, field, reason):
    class HookedDict(dict):
        def __bool__(self):
            pytest.fail('dictionary truth hook ran')
    class HookedTuple(tuple):
        def __len__(self):
            pytest.fail('tuple length hook ran')
    fn, enc = plain_function
    setattr(fn, field, HookedTuple() if field == '__defaults__' else HookedDict())
    with pytest.raises(differential.Unencodable, match=reason):
        enc.enc(fn)


@pytest.mark.parametrize('field', ['__name__', '__qualname__', '__module__', '__doc__'])
def test_primitive_function_metadata_changes_are_observed(differential, plain_function, field):
    fn, enc = plain_function
    assert enc.enc(fn) == ('fn', 'plain.py:<module>.f')
    enc.freeze()
    setattr(fn, field, 'changed')
    with pytest.raises(differential.Unencodable, match='callable-state-changed'):
        enc.post_state()


def test_equal_but_replaced_function_code_is_observed(differential, plain_function):
    fn, enc = plain_function
    enc.enc(fn)
    enc.freeze()
    old = fn.__code__
    fn.__code__ = old.replace()
    assert fn.__code__ == old and fn.__code__ is not old
    with pytest.raises(differential.Unencodable, match='callable-state-changed'):
        enc.post_state()


@pytest.mark.parametrize('nested', [False, True])
def test_mutable_function_code_constants_are_refused(differential, plain_function, nested):
    fn, enc = plain_function
    constant = ([] ,) if nested else []
    fn.__code__ = fn.__code__.replace(co_consts=(None, constant))
    assert fn() is constant
    with pytest.raises(differential.Unencodable, match='callable-code-state'):
        enc.enc(fn)


def test_function_filename_hooks_are_refused(differential, plain_function):
    class HookedString(str):
        def __fspath__(self):
            pytest.fail('filename hook ran')
        def __hash__(self):
            pytest.fail('filename hash hook ran')
    fn, enc = plain_function
    fn.__code__ = fn.__code__.replace(co_filename=HookedString(fn.__code__.co_filename))
    with pytest.raises(differential.Unencodable, match='callable-code-state'):
        enc.enc(fn)


def test_deferred_function_annotations_are_not_evaluated(differential, plain_function):
    import types
    if not hasattr(types.FunctionType, '__annotate__'):
        pytest.skip('deferred annotations require Python 3.14')
    fn, enc = plain_function
    def annotate(format):
        pytest.fail('deferred annotation hook ran')
    fn.__annotate__ = annotate
    with pytest.raises(differential.Unencodable, match='callable-annotations'):
        enc.enc(fn)


def test_local_functions_without_captures_keep_identity_gap(differential, tmp_path):
    from native_heap import function_identities
    path = tmp_path / 'factory.py'
    path.write_text('def make():\n    def inner():\n        return 1\n    return inner\n')
    ns = {}
    exec(compile(path.read_text(), str(path), 'exec'), ns)
    first, second = ns['make'](), ns['make']()
    assert first is not second and first.__code__ is second.__code__
    assert first.__closure__ is second.__closure__ is None
    funcs = [{'name': 'factory.py:<module>.' + name, 'file': 'factory.py'}
             for name in ('make', 'make.inner')]
    identities = function_identities(funcs, tmp_path)
    assert set(identities.values()) == {'factory.py:<module>.make'}
    enc = differential.GraphEncoder({}, identities)
    # User-writable names cannot turn a repeated local allocation into a stable
    # module function identity.
    first.__qualname__ = 'make'
    for fn in (first, second):
        with pytest.raises(differential.Unencodable, match='source-identity-unresolved'):
            enc.enc(fn)


@pytest.mark.parametrize('loop', ['for _ in range(2):', 'while len(made) < 2:'])
def test_module_loop_function_identities_are_refused(differential, tmp_path, loop):
    from native_heap import function_identities
    path = tmp_path / 'loop.py'
    path.write_text('made = []\n' + loop + '\n'
                    '    def f():\n        return 1\n    made.append(f)\n')
    ns = {}
    exec(compile(path.read_text(), str(path), 'exec'), ns)
    first, second = ns['made']
    assert first is not second and first.__code__ is second.__code__
    funcs = [{'name': 'loop.py:<module>.f', 'file': 'loop.py'}]
    identities = function_identities(funcs, tmp_path)
    assert not identities
    for fn in (first, second):
        with pytest.raises(differential.Unencodable, match='source-identity-unresolved'):
            differential.GraphEncoder({}, identities).enc(fn)


@pytest.mark.parametrize('after_call', [False, True])
def test_distinct_function_objects_cannot_share_an_identity(differential, tmp_path, after_call):
    from native_heap import function_identities
    import types
    path = tmp_path / 'cloned.py'
    path.write_text('def f():\n    return 1\n')
    ns = {}
    exec(compile(path.read_text(), str(path), 'exec'), ns)
    first = ns['f']
    second = types.FunctionType(first.__code__, first.__globals__)
    identities = function_identities([{'name': 'cloned.py:<module>.f', 'file': 'cloned.py'}],
                                     tmp_path)
    enc = differential.GraphEncoder({}, identities)
    assert enc.enc(first) == enc.enc(first) == ('fn', 'cloned.py:<module>.f')
    if after_call:
        # A duplicate discovered only in the post-state must refuse the whole
        # observation just like a collision between arguments does.
        items = [first]
        enc.enc(items)
        enc.freeze()
        items.append(second)
        with pytest.raises(differential.Unencodable, match='source-identity-collision'):
            enc.post_state()
    else:
        with pytest.raises(differential.Unencodable, match='source-identity-collision'):
            enc.enc(second)


def test_graph_checker_and_effect_mutations_kernel(tmp_path, numeric_env):
    run(['lake', 'build', 'Autoform.SpecsGen.Basis'], ROOT, numeric_env, timeout=600)
    path = tmp_path / 'HeapGraph.lean'
    path.write_text(r'''import Autoform.SpecsGen.Basis
open Autoform.Core Autoform.SpecsGen
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def cell (xs : List Val) : Obj := { cls := "list", fields := [], payload := .list xs }
def cycle : HeapObservation := { heap := [cell [.ref 0]], roots := [] }
example : cycle.compare [cell [], cell [.ref 1]] (.val (.ref 0)) (.val (.ref 1))
    = some true := by decide +kernel
example : cycle.compare [cell [], cell [.ref 0]] (.val (.ref 0)) (.val (.ref 1))
    = some false := by decide +kernel
def alias : HeapObservation := { heap := [cell [.ref 1, .ref 1], cell []], roots := [] }
example : alias.compare [cell [], cell [.ref 0, .ref 0]] (.val (.ref 0)) (.val (.ref 1))
    = some true := by decide +kernel
example : alias.compare [cell [], cell [.ref 0, .ref 2], cell []]
    (.val (.ref 0)) (.val (.ref 1)) = some false := by decide +kernel
def distinct : HeapObservation :=
  { heap := [cell [.ref 1, .ref 2], cell [], cell []], roots := [] }
example : distinct.compare [cell [.ref 1, .ref 1], cell []]
    (.val (.ref 0)) (.val (.ref 0)) = some false := by decide +kernel
def pinned : HeapObservation := { heap := [cell []], roots := [0] }
example : pinned.compare [cell [], cell []] (.val (.ref 0)) (.val (.ref 1))
    = some false := by decide +kernel
example : pinned.compare [cell [.int 1]] (.val .unit) (.val .unit)
    = some false := by decide +kernel
example : { pinned with budget := 0 }.compare [cell []] (.val .unit) (.val .unit)
    = none := by decide +kernel
def fieldsGraph : HeapObservation :=
  { heap := [{ cls := "C", fields := [("a", .int 1), ("b", .int 2)] }], roots := [0] }
example : fieldsGraph.compare [{ cls := "C", fields := [("b", .int 2), ("a", .int 1)] }]
    (.val .unit) (.val .unit) = some true := by decide +kernel
example : fieldsGraph.compare [{ cls := "C", fields := [("a", .int 1), ("a", .int 1)] }]
    (.val .unit) (.val .unit) = some false := by decide +kernel
example : fieldsGraph.compare
    [{ cls := "C", fields := [("a", .int 1), ("a", .int 99), ("b", .int 2)] }]
    (.val .unit) (.val .unit) = some true := by decide +kernel
example : fieldsGraph.compare
    [{ cls := "C", fields := [("a", .int 99), ("a", .int 1), ("b", .int 2)] }]
    (.val .unit) (.val .unit) = some false := by decide +kernel
def dictionary : HeapObservation :=
  { heap := [{ cls := "dict", fields := [], payload := .dict [(.int 1, .int 2), (.int 3, .int 4)] }],
    roots := [0] }
example : dictionary.compare
    [{ cls := "dict", fields := [], payload := .dict [(.int 3, .int 4), (.int 1, .int 2)] }]
    (.val .unit) (.val .unit) = some false := by decide +kernel
def scalarGraph : HeapObservation := { heap := [], roots := [] }
example : scalarGraph.compare [] (.val (.int 1)) (.val (.bool true))
    = some false := by decide +kernel
example : scalarGraph.compare [] (.val (.float (Fl.ofBits 0)))
    (.val (.float (Fl.ofBits 9223372036854775808))) = some false := by decide +kernel
def ctx : Ctx := { table := [], dialect := .python }
def append : Func :=
  { name := "append", params := ["xs"],
    body := .expr (.mcall (.name "xs") "append" [.lit (.int 2)]) }
def mutant : Func := { append with body := .skip }
def observation : Obs :=
  { case := { heap := [cell [.int 1]], self := none, args := [.ref 0] }, expected := .val .unit,
    post := some { heap := [cell [.int 1, .int 2]], roots := [0] } }
example : lawConform ctx 20 append observation = true := by decide +kernel
example : lawConform ctx 20 mutant observation = false := by decide +kernel
example : lawConform ctx 20 mutant { observation with post := none } = true := by decide +kernel
example : lawConform ctx 40 append observation = true := by
  exact lawConform_fuel_mono_all (by decide : 20 ≤ 40) (by decide +kernel) (by decide +kernel)
def overwrite : Func :=
  { name := "overwrite", params := [],
    body := .setField (.name "self") "value" (.lit (.int 2)) }
def overwriteObs : Obs :=
  { case := { heap := [{ cls := "C", fields := [("value", .int 1)] }],
              self := some (.ref 0), args := [] }, expected := .val .unit,
    post := some { heap := [{ cls := "C", fields := [("value", .int 2)] }], roots := [0] } }
example : lawConform ctx 20 overwrite overwriteObs = true := by decide +kernel
example : lawConform ctx 20 { overwrite with body := .skip } overwriteObs
    = false := by decide +kernel
''')
    run(['lake', 'env', 'lean', path], ROOT, numeric_env, timeout=180)


@pytest.mark.parametrize('correct', [True, False])
def test_generated_graph_proof_rejects_lost_effect(tmp_path, monkeypatch, differential,
                                                 numeric_env, correct):
    monkeypatch.setenv('AUTOFORM_NO_REEXEC', '1')
    synth = load(str(Path(SCRIPTS) / 'synth_specs.py'), 'af_graph_specs')
    items = [1]
    enc = encoder(differential)
    args = [enc.enc(items)]
    enc.freeze()
    items.append(2)
    row = differential.finish_record(enc, dict(args=args, self=None,
        outcome=('val', ('unit',))))
    candidate = synth.Cand('conform_append', 'conform', 'native graph', 'append', 'append',
                          'lawConform C FUEL append', [synth.obs_lit(row)], dom_kind='obs')
    candidate.extra.update(heap_graph=True, proof_fuel=20, fuel_mono=True)
    source, _, _ = synth.emit([candidate], 'GraphTest', [])
    body = '.expr (.mcall (.name "xs") "append" [.lit (.int 2)])' if correct else '.skip'
    program = '''namespace Autoform.Generated.GraphTest
open Autoform.Core
def append : Func := { name := "append", params := ["xs"], body := BODY }
def program : Program := { dialect := .python, funcs := [append] }
end Autoform.Generated.GraphTest
'''.replace('BODY', body)
    source = source.replace('import Autoform.Generated.GraphTest\n', program)
    path = tmp_path / 'GeneratedGraph.lean'
    path.write_text(source)
    import subprocess
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT, env=numeric_env,
                            capture_output=True, text=True, timeout=180)
    assert (result.returncode == 0) == correct, result.stdout + result.stderr
    if not correct:
        assert 'kernel computation did not establish the claim' in result.stdout
