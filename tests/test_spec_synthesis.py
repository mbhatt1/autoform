"""Generated conformance proofs must terminate and reject incorrect observations."""
import os
from pathlib import Path
import shutil
import subprocess

import pytest

from conftest import ROOT, SCRIPTS, load


def test_native_subjects_keep_observed_paths_outside_static_core(monkeypatch, differential):
    monkeypatch.setenv('AUTOFORM_NO_REEXEC', '1')
    synth = load(str(Path(SCRIPTS) / 'synth_specs.py'), 'af_synth_observed_subjects')
    byname = {'partial': {'body': {'k': 'holeS', 'label': 'other-path'}},
              'unobserved': {'body': {'k': 'skip'}}}
    records = [{'name': 'partial'}, {'name': 'partial'}]
    assert synth.conformance_subjects(byname, records) == ['partial']
    with pytest.raises(ValueError, match='absent subjects: missing'):
        synth.conformance_subjects(byname, [{'name': 'missing'}])


@pytest.mark.parametrize('body,expected,status', [
    ('.ret (.lit (.int 1))', 1, 'candidate'),
    ('.ret (.lit (.int 1))', 2, 'refuted'),
    ('.loop (.lit (.bool true)) .skip', 1, 'not_checked'),
    ('.hole "untranslated"', 1, 'not_checked'),
    ('.ifte (.lit (.bool true)) (.ret (.lit (.int 1))) (.hole "other-path")', 1, 'candidate'),
    ('.ifte (.lit (.bool false)) (.ret (.lit (.int 1))) (.hole "other-path")', 1, 'not_checked'),
    ('.tryFinally (.loop (.lit (.bool true)) .skip) (.ret (.lit (.int 1)))', 1, 'not_checked'),
    ('.tryFinally (.hole "untranslated") (.ret (.lit (.int 1)))', 1, 'not_checked'),
])
def test_refutation_distinguishes_counterexample_from_incomplete_execution(
        tmp_path, monkeypatch, differential, body, expected, status):
    env=dict(os.environ,PATH=str(Path.home()/'.elan/bin')+os.pathsep+os.environ['PATH'])
    if not shutil.which('lake',path=env['PATH']):
        pytest.skip('Lean is not installed')
    monkeypatch.setenv('AUTOFORM_NO_REEXEC','1')
    synth=load(str(Path(SCRIPTS)/'synth_specs.py'),'af_refutation_fuel')
    monkeypatch.setattr(synth,'FUEL',8)
    program='''namespace Autoform.Generated.RefutationTest
open Autoform.Core
def f_probe : Func := { name := "probe", params := [], body := BODY }
def program : Program := { funcs := [f_probe] }
end Autoform.Generated.RefutationTest
'''.replace('BODY',body)
    run=synth.lean_run
    monkeypatch.setattr(synth,'lean_run',lambda source,*args,**kwargs:
                        run(source.replace('import Autoform.Generated.RefutationTest\n',program),
                            *args,**kwargs))
    case='{ case := { heap := [], self := none, args := [] }, expected := .val (.int %d) }' % expected
    candidate=synth.Cand('conform_probe','conform','native test','probe','f_probe',
                         'lawConform C FUEL f_probe',[case],dom_kind='obs')
    synth.refute([candidate],'RefutationTest')
    assert candidate.status == status, candidate.checked
    if 'loop' in body:
        assert candidate.checked['guard_failures']==1


@pytest.mark.parametrize("op,dialect,args,expected,result,tactic,success", [
    ("num:go:u64:<<", "cLike", [2, 18446744073709551615], 0, ".val (.int 0)", "rfl", True),
    ("num:go:u64:<<", "cLike", [2, 18446744073709551615], 1, ".val (.int 0)", "rfl", False),
    ("js:+", "javascript", [0, 1], 1, ".val (.float (Fl.ofBits 4607182418800017408))", "rfl", True),
    ("js:+", "javascript", [0, 1], 2, ".val (.float (Fl.ofBits 4607182418800017408))", "rfl", False),
    ("js:+", "javascript", [0, 1], 1, ".val (.float (Fl.ofBits 4611686018427387904))", "rfl", False),
    ("num:js:i32:|", "javascript", [1, -1], -1, ".val (.int (-1))", "cbv", True),
    ("num:js:i32:|", "javascript", [1, -1], 0, ".val (.int (-1))", "cbv", False),
    # The default proof checks the native observation directly, independently of
    # VM hints. Incorrect hints cannot establish an incorrect native observation.
    ("num:go:u64:<<", "cLike", [2, 18446744073709551615], 0, ".val (.int 1)", None, True),
    ("num:go:u64:<<", "cLike", [2, 18446744073709551615], 1, ".val (.int 1)", None, False),
    ("js:+", "javascript", [0, 1], 1, ".val (.float (Fl.ofBits 4611686018427387904))", None, True),
    ("js:+", "javascript", [0, 1], 2, ".val (.float (Fl.ofBits 4611686018427387904))", None, False),
    ("num:js:i32:|", "javascript", [1, -1], -1, ".val (.int 0)", None, True),
    ("num:js:i32:|", "javascript", [1, -1], 0, ".val (.int 0)", None, False),
])
def test_generated_execution_proof(tmp_path, monkeypatch, differential,
                                   op, dialect, args, expected, result, tactic, success):
    env = dict(os.environ, PATH=str(Path.home() / ".elan/bin") + os.pathsep + os.environ["PATH"])
    if not shutil.which("lake", path=env["PATH"]):
        if os.environ.get("AUTOFORM_REQUIRE_LEAN"):
            pytest.fail("Lean is required")
        pytest.skip("Lean is not installed")
    monkeypatch.setenv("AUTOFORM_NO_REEXEC", "1")
    synth = load(str(Path(SCRIPTS) / "synth_specs.py"), "af_synth_staged_test")
    case = ('{ case := { heap := [], self := none, args := [.int (%d), .int (%d)] }, '
            'expected := .val (.int (%d)) }' % (*args, expected))
    candidate = synth.Cand("conform_shift", "conform", "native test", "shift", "f_shift",
                           "lawConform C FUEL f_shift", [case], dom_kind="obs")
    candidate.extra.update(fuel_mono=True, proof_fuel=4, execution_results=[result])
    if tactic is not None:
        candidate.extra["execution_tactic"] = tactic
    generated, _, _ = synth.emit([candidate], "ShiftTest", [])
    # Supply the generated program inline, leaving the proof emitter unchanged.
    program = '''namespace Autoform.Generated.ShiftTest
open Autoform.Core
def f_shift : Func := { name := "shift", params := ["a", "b"], body := .ret (.binop "OP" (.name "a") (.name "b")) }
def program : Program := { dialect := .DIALECT, funcs := [f_shift] }
end Autoform.Generated.ShiftTest
'''.replace('OP', op).replace('DIALECT', dialect)
    generated = generated.replace("import Autoform.Generated.ShiftTest\n", program)
    path = tmp_path / "Staged.lean"
    path.write_text(generated)
    build = subprocess.run(["lake", "build", "Autoform.SpecsGen.Basis", "Autoform.Harness.Audit"],
                           cwd=ROOT, env=env, text=True, capture_output=True, timeout=300)
    assert build.returncode == 0, build.stdout + build.stderr
    result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, env=env,
                            text=True, capture_output=True, timeout=90)
    assert (result.returncode == 0) == success, result.stdout + result.stderr
    if not success:
        assert "error:" in result.stdout
        assert "unexpected" not in result.stdout


def test_large_corpus_header_keeps_all_functions_and_globals(tmp_path, monkeypatch, differential):
    """Linux lib/ exceeded the former recursion budget in both h0 and C_tfFree."""
    env = dict(os.environ, PATH=str(Path.home() / '.elan/bin') + os.pathsep + os.environ['PATH'])
    if not shutil.which('lake', path=env['PATH']):
        if os.environ.get('AUTOFORM_REQUIRE_LEAN'):
            pytest.fail('Lean is required')
        pytest.skip('Lean is not installed')
    monkeypatch.setenv('AUTOFORM_NO_REEXEC', '1')
    synth = load(str(Path(SCRIPTS) / 'synth_specs.py'), 'af_synth_large_test')
    fields = ', '.join('("g%d", .int %d)' % (i, i) for i in range(6000))
    heap = '[{ cls := "<globals>", fields := [' + fields + '] }]'
    source = synth.HEADER % ('LargeTest', 'LargeTest', 'LargeTest', 5000, heap, '0', 400, 'LargeTest')
    program = '''namespace Autoform.Generated.LargeTest
open Autoform.Core
def leaf : Func := { name := "leaf", params := [], body := .ret (.lit (.int 1)) }
def program : Program := { funcs := List.replicate 6500 leaf }
end Autoform.Generated.LargeTest
'''
    source = source.replace('import Autoform.Generated.LargeTest\n', program)
    source += '\nexample : h0.length = 1 := by rfl\nend Autoform.SpecsGen.LargeTest\n'
    path = tmp_path / 'Large.lean'
    path.write_text(source)
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT, env=env,
                            text=True, capture_output=True, timeout=180)
    assert result.returncode == 0, result.stdout + result.stderr


def test_finalizer_property_transports_to_every_larger_fuel(tmp_path, monkeypatch, differential):
    env = dict(os.environ, PATH=str(Path.home() / '.elan/bin') + os.pathsep + os.environ['PATH'])
    if not shutil.which('lake', path=env['PATH']):
        pytest.skip('Lean is not installed')
    monkeypatch.setenv('AUTOFORM_NO_REEXEC', '1')
    synth = load(str(Path(SCRIPTS) / 'synth_specs.py'), 'af_finalizer_transport')
    program = '''namespace Autoform.Generated.FinalizerTest
open Autoform.Core
def f_probe : Func := { name := "probe", params := ["a"], body :=
  (.tryFinally (.seq (.assign "x" (.name "a")) (.ret (.lit (.int 11))))
    (.ret (.name "x"))) }
def program : Program := { dialect := .python, funcs := [f_probe] }
end Autoform.Generated.FinalizerTest
'''
    case = '{ case := { heap := [], self := none, args := [.int 13] }, expected := .val (.int 13) }'
    candidate = synth.Cand('conform_probe', 'conform', 'native test', 'probe', 'f_probe',
                           'lawConform C FUEL f_probe', [case], dom_kind='obs')
    candidate.extra['try_finally'] = True
    original = synth.lean_run
    monkeypatch.setattr(synth, 'lean_run', lambda source, *args, **kwargs:
        original(source.replace('import Autoform.Generated.FinalizerTest\n', program), *args, **kwargs))
    synth.guard_pass([candidate], 'FinalizerTest')
    assert candidate.extra['fuel_mono'] is True
    candidate.extra['proof_fuel'] = 32
    generated, _, _ = synth.emit([candidate], 'FinalizerTest', [])
    path = tmp_path / 'FinalizerTransport.lean'
    path.write_text(generated.replace('import Autoform.Generated.FinalizerTest\n', program))
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT, env=env,
                            text=True, capture_output=True, timeout=120)
    assert result.returncode == 0, result.stdout + result.stderr


def test_nested_loop_call_proof_uses_native_expected_result(tmp_path, monkeypatch, differential):
    """Nested finite-field operations previously exhausted the proof budget.

    This tests proof construction, with a small explicit model and a separately
    compiled native observation. The real Linux run checks source translation.
    """
    env = dict(os.environ, PATH=str(Path.home() / '.elan/bin') + os.pathsep + os.environ['PATH'])
    if not shutil.which('lake', path=env['PATH']) or not shutil.which('cc'):
        if os.environ.get('AUTOFORM_REQUIRE_LEAN'):
            pytest.fail('Lean and a C compiler are required')
        pytest.skip('Lean or C compiler is not installed')
    source = tmp_path / 'native'
    source.mkdir()
    (source / 'field.c').write_text('''
#include <stdint.h>
static uint8_t multiply(uint8_t a, uint8_t b) {
    uint8_t v = 0;
    while (b != 0) {
        if (b & 1) v ^= a;
        a = (a << 1) ^ ((a & 128) ? 29 : 0);
        b >>= 1;
    }
    return v;
}
uint8_t power(uint8_t a, int b) {
    uint8_t v = 1;
    b %= 255;
    if (b < 0) b += 255;
    while (b != 0) {
        if (b & 1) v = multiply(v, a);
        a = multiply(a, a);
        b >>= 1;
    }
    return v;
}
''')
    f = dict(name='power', sourceName='power', file='field.c', params=['a', 'b'],
             paramIntegerTypes=['u8', 'i32'], returnIntegerType='u8')
    expected = differential.c_runtime(str(source), [f])(f)(237, -13)
    assert expected == 58
    monkeypatch.setenv('AUTOFORM_NO_REEXEC', '1')
    synth = load(str(Path(SCRIPTS) / 'synth_specs.py'), 'af_synth_nested_test')
    case = ('{ case := { heap := [], self := none, args := [.int 237, .int (-13)] }, '
            'expected := .val (.int %d) }' % expected)
    candidate = synth.Cand('conform_power', 'conform', 'native test', 'power', 'f_power',
                           'lawConform C FUEL f_power', [case], dom_kind='obs')
    candidate.extra.update(fuel_mono=True, proof_fuel=128)
    generated, _, _ = synth.emit([candidate], 'NestedTest', [])
    program = '''namespace Autoform.Generated.NestedTest
open Autoform.Core
private def lit (n : Int) : Expr := .lit (.int n)
private def var (n : String) : Expr := .name n
private def op (s : String) (a b : Expr) : Expr := .binop ("num:c:i32:" ++ s) a b
private def byte (e : Expr) : Expr := .unop "cast:u8" e
private def block (ss : List Stmt) : Stmt := ss.foldr .seq .skip
def f_multiply : Func := { name := "multiply", params := ["a", "b"], body := block [
  .assign "v" (lit 0),
  .loop (op "!=" (var "b") (lit 0)) (block [
    .ifte (op "&" (var "b") (lit 1))
      (.assign "v" (byte (op "^" (var "v") (var "a")))) .skip,
    .assign "a" (byte (op "^" (op "<<" (var "a") (lit 1))
      (.cond (op "&" (var "a") (lit 128)) (lit 29) (lit 0)))),
    .assign "b" (byte (op ">>" (var "b") (lit 1)))]),
  .ret (var "v")] }
def f_power : Func := { name := "power", params := ["a", "b"], body := block [
  .assign "v" (lit 1),
  .assign "b" (op "%" (var "b") (lit 255)),
  .ifte (op "<" (var "b") (lit 0)) (.assign "b" (op "+" (var "b") (lit 255))) .skip,
  .loop (op "!=" (var "b") (lit 0)) (block [
    .ifte (op "&" (var "b") (lit 1))
      (.assign "v" (byte (.call "multiply" [var "v", var "a"]))) .skip,
    .assign "a" (byte (.call "multiply" [var "a", var "a"])),
    .assign "b" (op ">>" (var "b") (lit 1))]),
  .ret (var "v")] }
def program : Program := { dialect := .cLike, funcs := [f_multiply, f_power] }
end Autoform.Generated.NestedTest
'''
    generated = generated.replace('import Autoform.Generated.NestedTest\n', program)
    path = tmp_path / 'Nested.lean'
    path.write_text(generated)
    build = subprocess.run(['lake', 'build', 'Autoform.SpecsGen.Basis', 'Autoform.Harness.Audit'],
                           cwd=ROOT, env=env, text=True, capture_output=True, timeout=300)
    assert build.returncode == 0, build.stdout + build.stderr
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT, env=env,
                            text=True, capture_output=True, timeout=60)
    assert result.returncode == 0, result.stdout + result.stderr
