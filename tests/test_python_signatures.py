"""Unsupported Python signatures must not yield plausible but wrong proofs."""
import importlib.util
import json
import os
from pathlib import Path
import sys
import subprocess

import pytest

from test_source_numeric import ROOT, numeric_env, run


SOURCE = ROOT / 'examples/python_control/signatures.py'


def test_signature_metadata_distinguishes_binding_rules():
    source = '''def ordinary(a, *args, **kwargs): pass
def default(a=None): pass
async def asynchronous(a=1): pass
def positional(a, /): pass
def keyword(*, a): pass
def keyword_default(*, a=1): pass
def computed(a=len("x")): pass
def mixed(a=1, b=len("x")): pass
mapper = lambda a=2: a
'''
    script = (ROOT / 'cartographer/export_ast.sc').read_text()
    decoder = script.split('  val pythonHandlerDecoder = """', 1)[1].split('\n"""', 1)[0]
    result = subprocess.run([sys.executable, '-I', '-S', '-c', decoder],
                            input=source, text=True, capture_output=True, timeout=30)
    assert result.returncode == 0, result.stderr
    records = {row['name']: row for row in json.loads(result.stdout)['signatures'].values()}
    assert records['ordinary'] == dict(name='ordinary', defaults=False, defaultValues=[],
        positional_only=False, keyword_only=False, parameters=['a', 'args', 'kwargs'],
        firstPositional='a', decorated=False, privateParameters=False, isMethod=False,
        staticMethod=False, property=False, classMethod=False, decoratorNames=[],
        overloadStub=False, receiverThenCollectors=False, generator=None,
        nonlocalUses=[], nonlocalDefines=[],
        positionalOnly=[], keywordOnly=[], required=['a'])
    # `defaults` means "carries a default this pipeline cannot model", which is what
    # holes the definition. A LITERAL default is modelled, so it clears the flag and
    # appears in `defaultValues` instead -- binding it at call time is indistinguishable
    # from binding it when the `def` ran, which is the only reason function-object state
    # is not needed.
    assert {name for name, row in records.items() if row['defaults']} == {'computed', 'mixed'}
    assert records['default']['defaultValues'] == [['a', {'k': 'unit'}]]
    assert records['asynchronous']['defaultValues'] == [['a', {'k': 'int', 'v': '1'}]]
    assert records['keyword_default']['defaultValues'] == [['a', {'k': 'int', 'v': '1'}]]
    assert records['lambda']['defaultValues'] == [['a', {'k': 'int', 'v': '2'}]]
    # All or nothing: `mixed` has one literal and one call, and emitting the literal
    # half would bind some defaults while silently dropping the other.
    assert records['mixed']['defaultValues'] == []
    assert {name for name, row in records.items() if row['positional_only']} == {'positional'}
    assert {name for name, row in records.items() if row['keyword_only']} == {'keyword', 'keyword_default'}


def test_python_signature_gaps(tmp_path, numeric_env):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 for Python signature translation')
    source = tmp_path / 'source'
    source.mkdir()
    (source / SOURCE.name).write_bytes(SOURCE.read_bytes())
    joern = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (joern / 'joern-cli').is_dir():
        joern /= 'joern-cli'
    run([joern / 'joern-parse', source, '--language', 'PYTHONSRC', '--output', 'cpg.bin'],
        tmp_path, numeric_env, timeout=600)
    run([joern / 'joern', '--script', ROOT / 'cartographer/export_ast.sc',
         '--param', 'cpgPath=cpg.bin', '--param', 'out=ast.json'], tmp_path, numeric_env, timeout=600)
    model = tmp_path / 'Model.lean'
    run([sys.executable, ROOT / 'cartographer/render_lean.py', tmp_path / 'ast.json',
         model, 'Signatures'], ROOT, numeric_env)
    spec = importlib.util.spec_from_file_location('native_signature_fixture', SOURCE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    requests = [
        ('default_exception', [-7], {}), ('default_exception', [0], {}),
        ('default_exception', [13], {}), ('literal_default', [], {}),
        ('literal_default', [42], {}), ('none_default', [], {}),
        ('keyword_only', [13], {}), ('keyword_only', [], {'a': 13}),
        ('positional_only', [], {'a': 13}), ('positional_only', [13], {}),
        ('lambda_default', [13], {}), ('unused_default_error', [0], {}),
        ('unused_default_error', [2], {}),
        ('mutable_default', [13], {}), ('mutable_default', [13], {}),
        ('ordinary', [13], {}),
    ]
    observations, calls, expected = [], [], []
    for name, args, kwargs in requests:
        try:
            native = {'value': getattr(module, name)(*args, **kwargs)}
        except BaseException as error:
            native = {'exception': type(error).__name__}
        observations.append(dict(subject=name, arguments=args, keywords=kwargs, native=native))
        encoded = [f'.lit (.int ({value}))' for value in args]
        encoded += [f'.kwargE {json.dumps(key)} (.lit (.int ({value})))'
                    for key, value in kwargs.items()]
        # evalExpr accepts keyword argument syntax; runFunc only takes values.
        calls.append('(evalExpr { table := program.table, dialect := .python } 512 [] [] '
                     f'(.call "signatures.py:<module>.{name}" [{", ".join(encoded)}])).2')
        if name == 'ordinary':
            expected.append('value:13')
        elif name in ('keyword_only', 'positional_only'):
            expected.append('value:13' if 'value' in native else 'exception:TypeError')
        elif name in ('lambda_default', 'unused_default_error'):
            expected.append('hole:function:python-default-evaluation')
        else:
            kind = {'keyword_only': 'keyword-only', 'positional_only': 'positional-only'}.get(name, 'defaults')
            expected.append('hole:call:python-' + kind)
    header = model.read_text() + '\nopen Autoform.Core Autoform.Generated.Signatures\n'
    driver = header + 'def main : IO Unit := do\n'
    for call in calls:
        driver += (f'  match {call} with\n'
                   '  | .hole label => IO.println ("hole:" ++ label)\n'
                   '  | .val (.int n) => IO.println ("value:" ++ toString n)\n'
                   '  | .exn (.str n) => IO.println ("exception:" ++ n)\n'
                   '  | other => IO.println ("unexpected:" ++ reprStr other)\n')
    (tmp_path / 'Observe.lean').write_text(driver)
    observed = run(['lake', 'env', 'lean', '--run', tmp_path / 'Observe.lean'], ROOT, numeric_env).splitlines()
    for row, actual in zip(observations, observed):
        row['model'] = actual
    (tmp_path / 'native-comparison.json').write_text(json.dumps(observations, indent=2) + '\n')
    assert observed == expected, json.dumps(observations, indent=2)
    assert [row['native'] for row in observations] == [
        {'value': -7}, {'value': 0}, {'value': 13}, {'value': 17},
        {'value': 42}, {'value': True}, {'exception': 'TypeError'}, {'value': 13},
        {'exception': 'TypeError'}, {'value': 13}, {'value': 13},
        {'exception': 'ZeroDivisionError'}, {'value': 9}, {'value': 1}, {'value': 2},
        {'value': 13}]
    proofs = header + '\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
    # Unsupported default evaluation cannot be concealed by an earlier arity
    # result. Every already-evaluated argument shape reaches the explicit gap.
    for name in ('default_exception', 'literal_default', 'none_default'):
        proofs += ('example (ctx : Ctx) (fuel : Nat) (heap : Heap) (receiver : Option Val) '
                   '(args : List Val) (keywords : List (String × Val)) :\n'
                   f'  (applyFunc ctx (fuel + 2) heap f_signatures_py__module__{name} '
                   'receiver args keywords).2 = .hole "call:python-defaults" := by rfl\n')
    for call, want in zip(calls, expected):
        match = ('| .hole label => label == ' + json.dumps(want[5:])
                 if want.startswith('hole:') else
                 '| .exn (.str n) => n == "TypeError"' if want.startswith('exception:')
                 else '| .val (.int n) => n == 13')
        proofs += (f'example : (match {call} with\n  {match}\n  | _ => false) = true := by\n'
                   '  first | decide +kernel | fail "signature outcome was not established"\n')
    # Default evaluation also happens during module initialization, before calls.
    proofs += ('example : (match runFunc program 512 "signatures.py:<module>" [] with\n'
               '  | .hole label => label == "function:python-default-evaluation"\n'
               '  | _ => false) = true := by\n'
               '  first | decide +kernel | fail "default definition was silently skipped"\n')
    (tmp_path / 'Proofs.lean').write_text(proofs)
    run(['lake', 'env', 'lean', tmp_path / 'Proofs.lean'], ROOT, numeric_env)


def _decode(source: str) -> dict:
    """Run the exporter's embedded Python source-metadata decoder on `source`."""
    script = (ROOT / 'cartographer/export_ast.sc').read_text()
    decoder = script.split('  val pythonHandlerDecoder = """', 1)[1].split('\n"""', 1)[0]
    result = subprocess.run([sys.executable, '-I', '-S', '-c', decoder],
                            input=source, text=True, capture_output=True, timeout=30)
    assert result.returncode == 0, result.stderr
    return json.loads(result.stdout)


class TestRaiseFromNone:
    """`raise X from None` is the idiom for SUPPRESSING exception chaining.

    Core represents an exception as the name of its class, so there is no object to
    carry a `__cause__` and no way to read one back — suppressing something that is not
    represented is a no-op, and CPython agrees: `raise X` and `raise X from None` both
    produce the same exception with `__cause__` None. A general cause expression is a
    different matter, since CPython evaluates it after the exception and propagates
    anything it raises, so those keep holing.
    """

    def test_from_none_is_not_a_hole(self):
        raises = _decode('def f():\n    raise ValueError("x") from None\n')['raises']
        assert [r['kind'] for r in raises.values()] == ['constructor']

    def test_a_real_cause_still_holes(self):
        """CPython evaluates the cause and propagates what it raises; dropping it would
        be a wrong answer, not a missing one."""
        raises = _decode('def f(e):\n    raise ValueError("x") from e\n')['raises']
        assert [r['label'] for r in raises.values()] == ['op:raise-cause']

    def test_a_module_that_reads_the_chain_keeps_holing(self):
        """The no-op argument only holds while nothing observes the chain. One read
        anywhere in the module withdraws it for every `raise ... from ...` in that
        module."""
        source = ('def g(exc):\n    return exc.__cause__\n\n'
                  'def f():\n    raise ValueError("x") from None\n')
        raises = _decode(source)['raises']
        assert [r['label'] for r in raises.values()] == ['op:raise-cause']

    def test_suppress_context_also_counts_as_reading_the_chain(self):
        source = ('def g(exc):\n    return exc.__suppress_context__\n\n'
                  'def f():\n    raise ValueError("x") from None\n')
        raises = _decode(source)['raises']
        assert [r['label'] for r in raises.values()] == ['op:raise-cause']


class TestStaticMethodBinding:
    """`@staticmethod` is a binding directive, not an unmodelled decorator.

    Core refuses a decorated method as `call:python-receiver-signature` because a
    decorator can change what calling the name MEANS, and Core injects an ordinary
    receiver under `self`. `staticmethod` is the one case where the decorator's entire
    content is "bind no receiver" — which `isMethod: False` already expresses exactly, so
    there is no residue left to model. `@property` changes an attribute ACCESS into a
    call; Core dispatches it through `Program.properties`, so it is reported under its own
    key rather than as an unmodelled decorator.
    """

    def test_a_static_method_is_reported_as_a_plain_function(self):
        source = ('class C:\n'
                  '    @staticmethod\n'
                  '    def f(a, b):\n'
                  '        return a\n')
        sig = next(iter(_decode(source)['signatures'].values()))
        assert sig['isMethod'] is False
        assert sig['decorated'] is False
        assert sig['staticMethod'] is True
        assert sig['required'] == ['a', 'b']

    def test_a_property_is_its_own_kind_not_a_residue(self):
        """`@property` turns an attribute ACCESS into a call. Core dispatches that now
        (`Program.properties`), so like `@staticmethod` it leaves no decorator residue to
        refuse; it is reported under its own key instead."""
        source = ('class C:\n'
                  '    @property\n'
                  '    def f(self):\n'
                  '        return 1\n')
        sig = next(iter(_decode(source)['signatures'].values()))
        assert sig['isMethod'] is True
        assert sig['property'] is True
        assert sig['decorated'] is False
        assert sig['staticMethod'] is False

    def test_staticmethod_alongside_another_decorator_still_holes(self):
        """The exemption is for a decorator with no residue. Two decorators have one."""
        source = ('class C:\n'
                  '    @staticmethod\n'
                  '    @other\n'
                  '    def f(a):\n'
                  '        return a\n')
        sig = next(iter(_decode(source)['signatures'].values()))
        assert sig['staticMethod'] is False
        assert sig['decorated'] is True

    def test_a_shadowed_staticmethod_is_not_the_builtin(self):
        """`staticmethod = something_else` at module scope means the name no longer
        denotes the binding directive, so the exemption must not apply."""
        source = ('staticmethod = None\n\n'
                  'class C:\n'
                  '    @staticmethod\n'
                  '    def f(a):\n'
                  '        return a\n')
        sig = [s for s in _decode(source)['signatures'].values() if s['name'] == 'f'][0]
        assert sig['staticMethod'] is False
        assert sig['decorated'] is True

    def test_an_ordinary_method_is_unchanged(self):
        source = 'class C:\n    def f(self, a):\n        return a\n'
        sig = next(iter(_decode(source)['signatures'].values()))
        assert sig['isMethod'] is True
        assert sig['decorated'] is False
        assert sig['staticMethod'] is False


class TestPropertyDispatch:
    """A `@property` read runs its getter, from `Program.properties`.

    `c.currsize` calls the getter in Python. Core used to lower it to a field read of a
    field that does not exist (`Cache.__init__` stores the mangled `_Cache__currsize`),
    and a missing field on an ordinary object evaluated to `unit` SILENTLY -- a wrong
    answer in the tracked corpus (docs/languages.md §12). Holing the access fixed the
    wrong answer; recording `(class, name)` and dispatching on a field miss makes it
    right. The extractor is authoritative because the frontend does not keep decorators.
    """

    def test_a_sole_property_getter_is_a_method_with_its_pair_recorded(self):
        source = ('class C:\n'
                  '    @property\n'
                  '    def n(self):\n'
                  '        return 1\n\n'
                  'def use(c):\n'
                  '    return c.n\n')
        out = _decode(source)
        assert out['propertyPairs'] == [['C', 'n']]
        assert out['propertiesUnmodelled'] == []
        sig = [v for v in out['signatures'].values() if v['name'] == 'n'][0]
        assert sig['property'] is True
        assert sig['isMethod'] is True        # receiver under `self`, like any method
        assert sig['decorated'] is False      # no residue left for Core to refuse

    def test_a_property_with_company_stays_unmodelled(self):
        """A setter stack changes what a WRITE means too; Core has only the read."""
        source = ('class C:\n'
                  '    @property\n'
                  '    @other\n'
                  '    def n(self):\n'
                  '        return 1\n')
        out = _decode(source)
        assert out['propertyPairs'] == []
        assert out['propertiesUnmodelled'] == ['n']
        sig = [v for v in out['signatures'].values() if v['name'] == 'n'][0]
        assert sig['property'] is False and sig['decorated'] is True

    def test_a_property_built_by_call_at_class_level_stays_unmodelled(self):
        """`x = property(getx)`: the getter is not syntactically a method of the class,
        so there is no `(class, name)` for Core to dispatch to. Its reads keep holing
        rather than falling back to the silent `unit`."""
        source = ('class C:\n'
                  '    def getx(self):\n'
                  '        return 1\n'
                  '    x = property(getx)\n')
        out = _decode(source)
        assert out['propertyPairs'] == []
        assert out['propertiesUnmodelled'] == ['x']

    def test_a_shadowed_property_is_not_the_builtin(self):
        source = ('property = None\n\n'
                  'class C:\n'
                  '    @property\n'
                  '    def n(self):\n'
                  '        return 1\n')
        out = _decode(source)
        assert out['propertyPairs'] == []
        sig = [v for v in out['signatures'].values() if v['name'] == 'n'][0]
        assert sig['property'] is False and sig['decorated'] is True

    def test_only_unmodelled_properties_hole_at_the_access(self):
        """Both lowering paths -- `callExpr` and `exprV` -- consult the same rule, and
        that rule now reads `propertiesUnmodelled`, not every property name."""
        src = (ROOT / 'cartographer/export_ast.sc').read_text()
        assert src.count('call:python-property-access') == 2
        assert '_("propertiesUnmodelled").arr.exists(_.str == f)' in src
        assert 'obj("classProperties") = ujson.Arr.from(pairs.toList)' in src


class TestNonlocalBoxing:
    """`nonlocal x` writes, via the exporter's existing local-boxing machinery.

    `Expr.closure` captures the environment BY VALUE, so a plain write can never reach
    the frame that owns the variable — which is why this was the hole
    `scope:nonlocal-write`. Capturing a `Val.ref` by value still shares the object behind
    it, so the enclosing scope boxes the name and both scopes read and write the one
    cell. Core needs nothing new: `boxNew`/`field`/`setField` already do this.

    The safety condition is the whole content. The box must exist when the closure
    captures it, so the enclosing function has to bind the name by a plain assignment at
    the top level of its body BEFORE the first nested `def`. A binding inside an `if`
    does not dominate the capture, and treating the name as boxed anyway would read a
    field off an integer — a wrong answer where the hole was right.
    """

    def test_the_safe_idiom_is_boxed_on_both_sides(self):
        source = ('def counter():\n'
                  '    hits = 0\n\n'
                  '    def bump():\n'
                  '        nonlocal hits\n'
                  '        hits += 1\n\n'
                  '    return hits\n')
        recs = {v['name']: v for v in _decode(source)['signatures'].values()}
        assert recs['counter']['nonlocalDefines'] == ['hits']
        assert recs['counter']['nonlocalUses'] == []
        assert recs['bump']['nonlocalUses'] == ['hits']
        assert recs['bump']['nonlocalDefines'] == []

    def test_a_binding_that_does_not_dominate_the_capture_is_refused(self):
        """`n = 0` inside an `if` leaves the parent unboxed, so the child must NOT be
        told the name is boxed — it would read `n.v` off a plain integer."""
        source = ('def unsafe():\n'
                  '    if True:\n'
                  '        n = 0\n\n'
                  '    def bump():\n'
                  '        nonlocal n\n'
                  '        n += 1\n\n'
                  '    return n\n')
        recs = {v['name']: v for v in _decode(source)['signatures'].values()}
        assert recs['unsafe']['nonlocalDefines'] == []
        assert recs['bump']['nonlocalUses'] == []

    def test_a_binding_after_the_def_is_refused(self):
        """Lexical order matters: the closure is created before the box exists."""
        source = ('def late():\n'
                  '    def bump():\n'
                  '        nonlocal n\n'
                  '        n += 1\n'
                  '    n = 0\n'
                  '    return n\n')
        recs = {v['name']: v for v in _decode(source)['signatures'].values()}
        assert recs['late']['nonlocalDefines'] == []
        assert recs['bump']['nonlocalUses'] == []

    def test_the_declaration_parser_is_not_the_global_one(self):
        """`globalDeclNames` strips the literal prefix `global`, which leaves
        `nonlocal x` as the name `"nonlocal x"` — silently, and the caller then keeps a
        hole that should have gone. That cost a debugging cycle."""
        src = (ROOT / 'cartographer/export_ast.sc').read_text()
        assert 'def nonlocalDeclNames' in src
        assert 'nonlocalDeclNames(u).forall(capturedBoxes.contains)' in src

    def test_captured_boxes_get_no_allocation_prologue(self):
        """Allocating in the closure would rebind the name to a fresh box and destroy
        the alias the box exists to create. `prologues` iterates `boxedLocals` only."""
        src = (ROOT / 'cartographer/export_ast.sc').read_text()
        assert 'val prologues: List[ujson.Obj] = boxedLocals.toList.sorted.map' in src
        assert 'capturedBoxes' in src


class TestFunctionReferenceDefaults:
    """`def f(k=keys.hashkey)` — a default whose value is an in-program function.

    Same time-invariance argument as a literal: `def f(k=g)` stores `g` itself, and `g`
    is the same object whenever it is looked up, so binding it at call time cannot be
    told apart from binding it when the `def` ran. That is what lets Core do this without
    the function-object state it does not have.

    Resolution is the risk, and it is why the rule requires uniqueness: the source says
    `Cache.__getitem__`, the CPG says
    `cachetools/__init__.py:<module>.Cache.__getitem__`, and two classes defining
    `__getitem__` would make the source text ambiguous. Picking one would be a silent
    wrong answer.
    """

    def test_a_dotted_default_is_recorded_for_resolution(self):
        source = ('class C:\n'
                  '    def pick(self, x):\n'
                  '        return x\n\n'
                  'def f(a, g=C.pick):\n'
                  '    return g(a, a)\n')
        recs = {v['name']: v for v in _decode(source)['signatures'].values()}
        assert recs['f']['defaultValues'] == [
            ['g', {'k': 'dotted', 'v': 'C.pick', 'moduleBase': False}]]
        # `defaults` is the "cannot be modelled" flag: a dotted name is a candidate, so
        # it does not set it. The exporter still holes if resolution is not unique.
        assert recs['f']['defaults'] is False

    def test_a_call_default_is_still_unmodellable(self):
        source = 'def f(a, g=len("x")):\n    return a\n'
        recs = {v['name']: v for v in _decode(source)['signatures'].values()}
        assert recs['f']['defaults'] is True
        assert recs['f']['defaultValues'] == []

    def test_resolution_requires_exactly_one_match(self):
        src = (ROOT / 'cartographer/export_ast.sc').read_text()
        assert 'if (ms.size == 1) Some(ms.head) else None' in src
        # An unresolved name must drop the WHOLE signature to the hole: binding some
        # defaults and skipping others is worse than binding none.
        assert 'if (defaultsUnresolved) refuseBinding("call:python-defaults")' in src

    def test_core_takes_a_closed_two_constructor_default(self):
        """`DefaultValue` is `lit | fnref` and nothing else, so a default that is not
        time-invariant cannot be written into a rendered corpus at all."""
        syntax = (ROOT / 'Autoform/Lang/Core/Syntax.lean').read_text()
        assert 'inductive DefaultValue where' in syntax
        assert '| lit   : Lit → DefaultValue' in syntax
        assert '| fnref : String → DefaultValue' in syntax
        assert 'defaults : List (String × DefaultValue) := []' in syntax


class TestModuleAttributeDefaults:
    """`timer=time.monotonic` — an attribute of an imported module.

    The value is a function object Core cannot model, but the BINDING exists, and that
    distinction is already `absentModule`'s: bind an opaque marker, and let every use of
    it — a call, an attribute read — hole locally. Holing the whole signature instead
    takes out every other default in it, including the literals, which is how
    `TTLCache.__init__` lost `getsizeof=None` to `timer=time.monotonic`.
    """

    def test_a_module_attribute_default_is_marked(self):
        source = 'import time\n\ndef f(a, timer=time.monotonic):\n    return a\n'
        recs = {v['name']: v for v in _decode(source)['signatures'].values()}
        assert recs['f']['defaultValues'] == [
            ['timer', {'k': 'dotted', 'v': 'time.monotonic', 'moduleBase': True}]]

    def test_a_non_module_base_is_not_marked(self):
        """`someobj.attr` is an attribute of a value, not of a module: its identity is
        not established by an import and re-reading it is not the same thing."""
        source = 'def f(a, g=someobj.attr):\n    return a\n'
        recs = {v['name']: v for v in _decode(source)['signatures'].values()}
        assert recs['f']['defaultValues'] == [
            ['g', {'k': 'dotted', 'v': 'someobj.attr', 'moduleBase': False}]]

    def test_the_marker_is_the_one_absentModule_uses(self):
        """One representation for "the binding exists and its value is unmodellable",
        not two that can drift apart."""
        src = (ROOT / 'cartographer/export_ast.sc').read_text()
        assert 'externalModule(value("v").str, "external")' in src
        assert 'def externalModule(path: String, why: String)' in src


class TestClassMethodBinding:
    """`@classmethod` receives the CLASS as its first argument.

    `@staticmethod` was the decorator whose entire meaning is "bind no receiver".
    `@classmethod` is the other one with no residue: "the receiver is the class". Core
    implements it without a new receiver mechanism at all — the receiving parameter
    (`cls`, by convention, but any name) is KEPT in `params` instead of being stripped
    like `self`, and every `.mcall` site passes the class value as the first positional
    with no separate receiver. That is exactly how an unbound method reached through the
    class was already called, so `applyFunc` is untouched.

    Both call paths must agree with CPython, which passes `cls = C` for each:

        class C:
            @classmethod
            def make(cls, n): return cls(n)
        C.make(3)        # via the class value
        C(1).make(3)     # via an instance -- the class is rebuilt from the method's name
    """

    def test_a_class_method_keeps_its_receiver_parameter(self):
        source = ('class C:\n'
                  '    @classmethod\n'
                  '    def make(cls, n):\n'
                  '        return cls(n)\n')
        sig = next(iter(_decode(source)['signatures'].values()))
        assert sig['classMethod'] is True
        assert sig['isMethod'] is True          # still lexically a method: dispatch finds it
        assert sig['decorated'] is False        # the decorator has no residue left to model
        assert sig['staticMethod'] is False
        # `cls` is an ordinary first positional, not a stripped receiver.
        assert sig['parameters'] == ['cls', 'n']
        assert sig['required'] == ['cls', 'n']
        assert sig['firstPositional'] == 'cls'

    def test_classmethod_alongside_another_decorator_still_holes(self):
        """The exemption is for a decorator with no residue. Two decorators have one."""
        source = ('class C:\n'
                  '    @classmethod\n'
                  '    @other\n'
                  '    def make(cls):\n'
                  '        return cls\n')
        sig = next(iter(_decode(source)['signatures'].values()))
        assert sig['classMethod'] is False
        assert sig['decorated'] is True

    def test_a_shadowed_classmethod_is_not_the_builtin(self):
        source = ('classmethod = None\n\n'
                  'class C:\n'
                  '    @classmethod\n'
                  '    def make(cls):\n'
                  '        return cls\n')
        sig = [v for v in _decode(source)['signatures'].values() if v['name'] == 'make'][0]
        assert sig['classMethod'] is False
        assert sig['decorated'] is True

    def test_a_module_level_classmethod_is_just_a_decorator(self):
        """Outside a class there is no class to receive, so the directive means nothing
        and the function is decorated like any other."""
        source = '@classmethod\ndef f(cls):\n    return cls\n'
        sig = next(iter(_decode(source)['signatures'].values()))
        assert sig['classMethod'] is False
        assert sig['decorated'] is True
        assert sig['isMethod'] is False

    def test_an_ordinary_method_is_unchanged(self):
        source = 'class C:\n    def f(self, a):\n        return a\n'
        sig = next(iter(_decode(source)['signatures'].values()))
        assert sig['classMethod'] is False
        assert sig['isMethod'] is True

    def test_the_exporter_keeps_cls_and_records_the_receiver_kind(self):
        """Source assertions on the Scala side, since the exporter is not run here: the
        receiver-stripping filter, the shape check and the gap check all exempt a
        classmethod, and the emitted signature says what the receiver is."""
        src = (ROOT / 'cartographer/export_ast.sc').read_text()
        assert '.filterNot(p => isMethodDecl && !isClassMethodDecl && p.name == "self")' in src
        assert '.filterNot(p => isMethodDecl && !isClassMethodDecl && p == "self")' in src
        assert 'if (isMethodDecl && !isClassMethodDecl &&' in src
        assert 'List("receiverKind" -> ujson.Str("class"))' in src

    def test_core_passes_the_class_at_every_call_site(self):
        """Three `.mcall`/`.call` sites, one rule: a classmethod gets its class as the
        first positional and no receiver. The class is rebuilt from the method's own
        qualified name when the call comes through an instance."""
        sem = (ROOT / 'Autoform/Lang/Core/Semantics.lean').read_text()
        assert 'def Func.isClassMethod (fn : Func) : Bool :=' in sem
        assert 'def Func.ownerClassValue (fn : Func) : Val :=' in sem
        # via an instance: class rebuilt from the method name
        assert 'applyFunc ctx n h₂ fn none (fn.ownerClassValue :: vs) kws' in sem
        # via the class value: the receiver IS the class
        assert 'applyFunc ctx n h₂ fn none ((.fn g) :: vs) kws' in sem
        # as a bound value (`f = C.make; f(3)`)
        assert 'applyFunc ctx n h₁ fn none (fn.ownerClassValue :: vs) kws' in sem
        syntax = (ROOT / 'Autoform/Lang/Core/Syntax.lean').read_text()
        assert 'receiverKind : Option String := none' in syntax

    def test_the_renderer_emits_and_gates_the_receiver_kind(self):
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            'render_lean', ROOT / 'cartographer/render_lean.py')
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        fn = {'name': 'C.make', 'file': 'm.py', 'params': ['cls', 'n'],
              'body': {'k': 'ret', 'e': {'k': 'name', 'v': 'cls'}},
              'pythonSignature': {'positionalOnly': [], 'keywordOnly': [],
                                  'required': ['cls', 'n'], 'isMethod': True,
                                  'receiverKind': 'class'}}
        text = '\n'.join(mod.render_func(fn, 'f_make'))
        assert 'receiverKind := some "class"' in text
        # The only receiver kind Core knows. Anything else must fail loudly rather than
        # render as a binding the semantics has no rule for.
        fn['pythonSignature']['receiverKind'] = 'metaclass'
        with pytest.raises(ValueError, match='unknown Python receiver kind'):
            mod.render_func(fn, 'f_make')

class TestClassAttributeDefaults:
    """`def pop(self, key, default=__marker)` — the sentinel default.

    `__marker = object()` is a CLASS attribute: bound once when the class body runs, the
    same object at every later lookup, and its whole meaning is an identity no caller can
    pass. That makes it time-invariant like a literal — but it lives on the heap, so Core
    resolves it in `applyFunc` (which has the heap) rather than `bindParams` (which must
    stay heap-free). Two things have to agree for `default is self.__marker` to be right:
    the default seeded from the globals frame, and the body's read of `self.__marker`
    through the instance. Both use `classAttrKey`, and the mangled name is computed by the
    same rule on both sides.
    """

    def test_a_class_attribute_default_is_recorded_with_its_mangled_name(self):
        source = ('class Cache:\n'
                  '    __marker = object()\n\n'
                  '    def pop(self, key, default=__marker):\n'
                  '        return default\n')
        out = _decode(source)
        recs = {v['name']: v for v in out['signatures'].values()}
        assert recs['pop']['defaults'] is False
        assert recs['pop']['defaultValues'] == [
            ['default', {'k': 'classAttr', 'cls': 'Cache', 'attr': '_Cache__marker'}]]
        # ...and the sentinel itself is reported so the module initialiser can allocate it.
        assert out['classAttrSentinels'] == [{'cls': 'Cache', 'attr': '_Cache__marker'}]

    def test_mangling_follows_cpython(self):
        """Two leading underscores and at most one trailing mangle; `__x__`, `_x` and an
        all-underscore class do not."""
        source = ('class _Foo:\n'
                  '    __a = object()\n'
                  '    __b__ = object()\n'
                  '    _c = object()\n\n'
                  '    def f(self, p=__a, q=__b__, r=_c):\n'
                  '        return p\n')
        out = _decode(source)
        rec = [v for v in out['signatures'].values() if v['name'] == 'f'][0]
        assert rec['defaultValues'] == [
            ['p', {'k': 'classAttr', 'cls': '_Foo', 'attr': '_Foo__a'}],
            ['q', {'k': 'classAttr', 'cls': '_Foo', 'attr': '__b__'}],
            ['r', {'k': 'classAttr', 'cls': '_Foo', 'attr': '_c'}]]
        assert {s['attr'] for s in out['classAttrSentinels']} == {'_Foo__a', '__b__', '_c'}

    def test_a_name_not_bound_in_the_class_is_not_a_class_attribute(self):
        """A module-level `MARKER` read from inside a class is a global, not a class
        attribute; it keeps the ordinary path (and today, the hole)."""
        source = ('MARKER = object()\n\n'
                  'class C:\n'
                  '    def f(self, d=MARKER):\n'
                  '        return d\n')
        rec = [v for v in _decode(source)['signatures'].values() if v['name'] == 'f'][0]
        assert rec['defaults'] is True
        assert rec['defaultValues'] == []

    def test_only_the_object_sentinel_shape_is_allocated(self):
        """`__size = _DefaultSize()` is a class attribute too, but its value is a real
        constructor call Core cannot pre-run here. It is not reported as a sentinel, so a
        default naming it holes at the call rather than being seeded with a guess."""
        source = ('class Cache:\n'
                  '    __marker = object()\n'
                  '    __size = _DefaultSize()\n')
        assert _decode(source)['classAttrSentinels'] == [{'cls': 'Cache', 'attr': '_Cache__marker'}]

    def test_core_and_exporter_share_one_key_format(self):
        src = (ROOT / 'cartographer/export_ast.sc').read_text()
        sem = (ROOT / 'Autoform/Lang/Core/Semantics.lean').read_text()
        assert '"<classattr>" + e("cls").str + "." + e("attr").str' in src
        assert 'def classAttrKey (cls attr : String) : String := "<classattr>" ++ cls ++ "." ++ attr' in sem
        # the sentinel is a fresh cell, never a constructor call
        assert '"k" -> "boxNew", "e" -> ujson.Obj("k" -> "unit")' in src

    def test_bindParams_stays_heap_free(self):
        """The reason `classAttr` is a separate field and not a `DefaultValue`: seeding
        happens in `applyFunc`, before `bindParams`, and after the arity checks."""
        sem = (ROOT / 'Autoform/Lang/Core/Semantics.lean').read_text()
        assert 'match seedClassAttrDefaults ctx h fn (selfEnv self?) vs kws with' in sem
        assert 'classAttrDefaults : List (String × String × String) := []' in \
            (ROOT / 'Autoform/Lang/Core/Syntax.lean').read_text()
        assert 'default:{p}:class-attr-unresolved' in sem


class TestReceiverThenCollectors:
    """`def f(self, *args, **kwargs)` -- a receiver followed by nothing but collectors.

    The exporter used to hole this whole shape as `call:python-receiver-signature`, for one
    reason: receiver stripping removes `self` from the signature Core checks, so
    `o.f(self=1)` -- `TypeError: got multiple values for argument 'self'` in CPython -- would
    land in `**kwargs` silently. The stripped receiver's NAME now travels in the signature
    (`receiverName`) and `kwargsRejected` refuses the keyword; the shape binds. Not for a
    positional-only `self` (`def f(self, /, **kw)`), where CPython really does put `self=1`
    in `kw`."""

    def test_the_decoder_marks_the_shape(self):
        source = ('class C:\n'
                  '    def f(self, *a, **k):\n'
                  '        return (a, k)\n'
                  '    def g(self, x, **k):\n'
                  '        return x\n'
                  '    @staticmethod\n'
                  '    def s(self, *a):\n'
                  '        return a\n'
                  '    def h(self, /, **k):\n'
                  '        return k\n')
        sigs = {row['name']: row for row in _decode(source)['signatures'].values()}
        assert sigs['f']['receiverThenCollectors'] is True
        assert sigs['h']['receiverThenCollectors'] is True
        assert sigs['g']['receiverThenCollectors'] is False   # an ordinary parameter after self
        assert sigs['s']['receiverThenCollectors'] is False   # no receiver to strip
        # The shape is not a decorator residue and is a method like any other.
        assert sigs['f']['decorated'] is False and sigs['f']['isMethod'] is True

    def test_the_exporter_records_the_name_instead_of_refusing(self):
        src = (ROOT / 'cartographer/export_ast.sc').read_text()
        assert 'receiverKeywordCollision' not in src
        assert 'List("receiverName" -> ujson.Str("self"))' in src
        # Only when the shadowing is possible: a keyword collector and a non-positional-only self.
        assert '!signature("positionalOnly").arr.contains(ujson.Str("self"))' in src

    def test_core_refuses_the_shadowing_keyword(self):
        """The one CPython behaviour the refusal was protecting is now a check."""
        sem = (ROOT / 'Autoform/Lang/Core/Semantics.lean').read_text()
        assert 'receiverName : Option String := none' in \
            (ROOT / 'Autoform/Lang/Core/Syntax.lean').read_text()
        assert '| some r => kws.any (fun kv => kv.1 == r)' in sem
        # Checked against CPython in Semantics.lean: ((1, 2), {'x': 3}) and the TypeError.
        assert '.kwargE "self" (.lit (.int 1))' in sem

    def test_the_renderer_emits_and_validates_the_name(self):
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            'render_lean', ROOT / 'cartographer/render_lean.py')
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        fn = {'name': 'm.py:<module>.C.f', 'params': ['a', 'k'], 'vararg': 'a', 'kwarg': 'k',
              'body': {'k': 'ret', 'e': {'k': 'int', 'v': '1'}},
              'pythonSignature': {'positionalOnly': [], 'keywordOnly': [], 'required': [],
                                  'isMethod': True, 'receiverName': 'self'}}
        text = '\n'.join(mod.render_func(fn, 'f_m_py__module__C_f'))
        assert 'receiverName := some "self"' in text
        # A receiver is a method's; a name that is also an ordinary parameter was not stripped.
        for bad in ({'isMethod': False, 'receiverName': 'self'},
                    {'isMethod': True, 'receiverName': 'a'},
                    {'isMethod': True, 'receiverName': ''}):
            broken = dict(fn, pythonSignature=dict(fn['pythonSignature'], **bad))
            with pytest.raises(ValueError):
                mod.render_func(broken, 'f_m_py__module__C_f')


class TestOverloadStubsAndDecoratorNames:
    """`@typing.overload` at run time binds the name to a dummy that raises
    `NotImplementedError` for any call; the un-decorated definition that follows rebinds
    it (docs.python.org/3/library/typing.html#typing.overload). The decoder names it so
    the exporter can translate the stub as exactly that raise, and records every
    decorator's dotted name so an external decorator is labelled rather than lumped."""

    def test_overload_through_a_module_alias_and_bare(self):
        source = ('import typing as t\n'
                  'from typing import overload\n'
                  '@t.overload\n'
                  'def f(x: int) -> int: ...\n'
                  '@overload\n'
                  'def f(x: str) -> str: ...\n'
                  'def f(x): return x\n')
        recs = list(_decode(source)['signatures'].values())
        assert [r['overloadStub'] for r in recs] == [True, True, False]
        assert recs[0]['decoratorNames'] == ['t.overload']
        assert recs[1]['decoratorNames'] == ['overload']

    def test_a_local_overload_is_not_typings(self):
        source = ('def overload(f): return f\n'
                  '@overload\n'
                  'def f(x): return x\n')
        rec = list(_decode(source)['signatures'].values())[1]
        assert rec['overloadStub'] is False and rec['decoratorNames'] == ['overload']

    def test_decorator_call_and_expression_shapes(self):
        source = ('import functools\n'
                  'def deco(f): return f\n'
                  '@functools.wraps(deco)\n'
                  '@deco\n'
                  '@(lambda g: g)\n'
                  'def f(x): return x\n')
        rec = next(r for r in _decode(source)['signatures'].values() if r['name'] == 'f')
        assert rec['decoratorNames'] == ['functools.wraps', 'deco', '<expr>']
        assert rec['decorated'] is True and rec['overloadStub'] is False

    def test_negative_numeric_defaults_are_literals(self):
        """`def read(self, n=-1)`: `-1` is evaluated once when the `def` executes
        (Language Reference §8.7) to the constant -1, so it binds like a literal."""
        source = ('def read(n=-1, x=-2.5, flag=-True): ...\n')
        rec = next(iter(_decode(source)['signatures'].values()))
        # `-True` is not a numeric constant in our sense and keeps the definition holed.
        assert rec['defaults'] is True
        source = ('def read(n=-1, x=-2.5): ...\n')
        rec = next(iter(_decode(source)['signatures'].values()))
        assert rec['defaults'] is False
        assert rec['defaultValues'][0] == ['n', {'k': 'int', 'v': '-1'}]
        assert rec['defaultValues'][1][0] == 'x' and rec['defaultValues'][1][1]['k'] == 'float'
