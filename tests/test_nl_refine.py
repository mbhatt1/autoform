"""Model path (default), --deep, --deep-too, the L1 step (refine) and level-aware reports.

The model stage (autoform.nl.model) and the other stages are stubbed; the Lean-gated test
(AUTOFORM_TEST_LEAN=1) proves the hand-written model Autoform.NLModel.TestFixturePython
equal to the deep fixture translation Autoform.Generated.PipelinePython.
"""
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from autoform.harness import prover  # noqa: E402
from autoform.nl import pipeline, refine as nl_refine, report as nl_report  # noqa: E402
from autoform.nl.schema import FILES, LeanModel, dump  # noqa: E402
from test_nl_prove_pipeline import ADD, Refuse, Scripted, Stubs, _fake_lean, _src, fixture  # noqa: E402

LEAN = pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_LEAN') != '1', reason='set AUTOFORM_TEST_LEAN=1')
QUOT = 'numbers.py:<module>.quotient'
FRAC = 'numbers.py:<module>.fraction'
M = 'Autoform.NLModel.TestFixturePython'


def model_translation():
    t = fixture()
    t.update(module='TestFixturePython', program_const=None, fuel=0, call_template=M + '.call {name} {args}',
             notes=['model translation (test stub)'])
    return t


def models(frac_status='UNTESTABLE'):
    return [LeanModel(ADD, f'{M}.add', 'def add (a b : Int) : Int := a + b', 'Int → Int → Int', 'VALIDATED',
                      tests_run=48, second_translation='agrees', level='L0'),
            LeanModel(QUOT, f'{M}.quotient', 'def quotient ...', 'Int → Int → Except String Int', 'VALIDATED',
                      tests_run=40, second_translation='agrees', level='L0'),
            LeanModel(FRAC, f'{M}.fraction', '', '(a b : Int) → Int', frac_status, tests_run=0,
                      level='L0' if frac_status == 'VALIDATED' else 'none')]


class ModelStubs(Stubs):
    def __init__(self, fail=()):
        super().__init__(fail)
        self.kw = {}

    def model(self, source_root, out, lean_root, **kw):
        self.kw['model'] = dict(kw, source_root=source_root)
        t = model_translation()
        dump(t, Path(out) / FILES['translation'])
        dump(models(), Path(out) / FILES['models'])
        return t

    def translate(self, source, module, lean_root, out, **kw):
        self.kw['translate'] = dict(out=str(out))
        return super().translate(source, module, lean_root, out, **kw)

    def refine(self, translation, models_, deep, out, statements=None, budget_usd=None, **kw):
        self.kw['refine'] = dict(translation=translation['call_template'], deep=deep['call_template'],
                                 models=[m['function'] for m in models_], statements=len(statements or []))
        return [nl_refine.L1Result(ADD, ADD, 'PROVED', 'L1', cost_usd=0.25, shapes=[
                    {'kinds': ['int', 'int'], 'theorem': 'l1_add', 'statement': 'theorem l1_add : ...',
                     'status': 'PROVED', 'bounded': {'status': 'AGREES'}, 'certificate': 'l1.lean'}]),
                nl_refine.L1Result(QUOT, QUOT, 'FAILED', 'L0', reason='l1_quotient (int,int): agent gave up', shapes=[
                    {'kinds': ['int', 'int'], 'theorem': 'l1_quotient', 'status': 'FAILED',
                     'bounded': {'status': 'AGREES'}, 'reason': 'agent gave up'}]),
                nl_refine.L1Result(FRAC, None, 'SKIPPED', 'none', reason='model is not validated')]


# --- pipeline modes ------------------------------------------------------------------------

def test_model_path_is_the_default(tmp_path, monkeypatch):
    stubs = ModelStubs()
    monkeypatch.setattr(pipeline, '_impl', stubs.impl)
    src, out = _src(tmp_path), tmp_path / 'run'
    res = pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT)
    assert stubs.calls == list(pipeline.MODEL_STAGES) == ['model', 'describe', 'formalize', 'check', 'prove', 'emit']
    assert stubs.kw['model']['source_root'] == str(src.resolve()) and stubs.kw['model']['second'] is True
    run = json.loads((out / 'run.json').read_text())
    assert run['mode'] == 'model' and run['stages']['model']['output'] == 'translation.json, models.json'
    assert not (out / FILES['deep_translation']).exists() and 'refine' not in run['stages']
    rep = json.loads((out / 'report.json').read_text())
    lv = {f['source_name']: f['level'] for f in rep['functions']}
    assert lv == {'add': 'L0', 'quotient': 'L0', 'fraction': 'none'}
    add = rep['functions'][0]
    assert add['model']['tests_run'] == 48 and add['model']['second_translation'] == 'agrees'
    assert {p['trust'] for p in add['properties']} == {'L0'}
    assert rep['totals']['by_level']['L0'] == {'functions': 2, 'statements': 4, 'bounded_holds': 1, 'proved': 1}
    assert rep['totals']['functions_skipped'] == {'model untestable': 1}
    assert res['potential_bugs'] == 1 and rep['totals']['model_defects'] == 1
    # Resume: nothing reruns; --no-second reruns the model stage only (same outputs -> the rest resume).
    stubs.calls.clear()
    pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT)
    assert stubs.calls == []
    pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT, second=False)
    assert stubs.calls == ['model'] and stubs.kw['model']['second'] is False


def test_deep_flag_and_mode_switches(tmp_path, monkeypatch):
    stubs = ModelStubs()
    monkeypatch.setattr(pipeline, '_impl', stubs.impl)
    src, out = _src(tmp_path), tmp_path / 'run'
    pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT)
    stubs.calls.clear()
    res = pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT, deep=True)
    assert stubs.calls == list(pipeline.DEEP_STAGES)    # a different translation.json: everything reruns
    rep = json.loads(Path(res['report']).read_text())
    # A models.json left over from the model run is not read in deep mode.
    assert {f['level'] for f in rep['functions']} == {'deep'} and rep['totals']['models'] == 0
    assert 'runFunc' in rep['call_template']
    # Back to the model path: the model stage's recorded outputs were overwritten, so it reruns.
    stubs.calls.clear()
    pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT)
    assert stubs.calls[0] == 'model' and 'translate' not in stubs.calls


def test_cli_flags_reach_the_pipeline(tmp_path, monkeypatch):
    seen = {}

    def fake_run(source, **kw):
        seen.update(kw, source=source)
        out = tmp_path / 'o'
        out.mkdir(exist_ok=True)
        (out / FILES['translation']).write_text('{}')
        return {'out': str(out), 'run': {'stages': {}}, 'totals': {}, 'report_md': 'r.md', 'potential_bugs': 0}
    monkeypatch.setattr(pipeline, 'run', fake_run)
    monkeypatch.setattr(pipeline, 'preflight', lambda *a, **k: ([], []))
    assert pipeline.main(['src', 'Mod', '--no-second', '--repairs', '1']) == 0
    assert (seen['deep'], seen['deep_too'], seen['second'], seen['repairs'], seen['module']) == \
        (False, False, False, 1, 'Mod')
    pipeline.main(['src', '--deep'])
    assert seen['deep'] and not seen['deep_too']
    pipeline.main(['src', '--deep-too'])
    assert seen['deep_too'] and not seen['deep']
    with pytest.raises(SystemExit):
        pipeline.main(['src', '--deep', '--deep-too'])


def test_deep_too_runs_both_and_propagates_l1(tmp_path, monkeypatch):
    stubs = ModelStubs()
    monkeypatch.setattr(pipeline, '_impl', stubs.impl)
    src, out = _src(tmp_path), tmp_path / 'run'
    res = pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT, deep_too=True, budget_usd=10)
    assert stubs.calls == list(pipeline.DEEP_TOO_STAGES)
    assert stubs.kw['translate']['out'] == str(out / 'deep')
    assert stubs.kw['refine'] == {'translation': M + '.call {name} {args}',
                                  'deep': fixture()['call_template'], 'models': [ADD, QUOT, FRAC], 'statements': 4}
    run = res['run']
    assert run['mode'] == 'deep_too' and run['stages']['refine']['cost_usd'] == 0.25
    assert run['cost_usd'] == 2.25
    rep = json.loads(Path(res['report']).read_text())
    fns = {f['source_name']: f for f in rep['functions']}
    assert (fns['add']['level'], fns['quotient']['level'], fns['fraction']['level']) == ('L1', 'L0', 'none')
    assert fns['add']['l1']['shapes'][0]['theorem'] == 'l1_add'
    assert 'agent gave up' in fns['quotient']['l1']['reason']
    # Every add statement uses `.int a, .int b`, the proved shape: all inherit L1.
    assert {p['trust'] for p in fns['add']['properties']} == {'L1'}
    t = rep['totals']
    assert (t['l1_attempted'], t['l1_proved']) == (2, 1)
    assert t['by_level']['L1'] == {'functions': 1, 'statements': 4, 'bounded_holds': 1, 'proved': 1}
    assert t['by_level']['L0']['functions'] == 1 and t['by_level']['none']['functions'] == 1
    assert list(t['by_level']) == ['L1', 'L0', 'none']
    md = Path(res['report_md']).read_text()
    assert 'transfers to the deep translation' in md and 'L1 not established (FAILED)' in md
    assert '| L1 | 1 | 4 | 1 | 1 |' in md
    assert md.index('Potential bugs') < md.index('Model defects') < md.index('## Functions')
    # Resume: nothing reruns.
    stubs.calls.clear()
    pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT, deep_too=True, budget_usd=10)
    assert stubs.calls == []


def test_deep_too_falls_back_to_the_deep_translation(tmp_path, monkeypatch):
    stubs = ModelStubs(fail={'model'})
    monkeypatch.setattr(pipeline, '_impl', stubs.impl)
    res = pipeline.run(_src(tmp_path), module='PipelinePython', out=tmp_path / 'run', lean_root=ROOT, deep_too=True)
    st = res['run']['stages']
    assert st['model']['status'] == 'failed' and st['translate']['status'] == 'ok'
    assert st['describe']['status'] == 'ok' and st['refine']['status'] == 'blocked'
    assert 'deep translation' in res['run']['fallback']
    rep = json.loads(Path(res['report']).read_text())
    assert {f['level'] for f in rep['functions']} == {'deep'}


def test_model_failure_blocks_the_model_path(tmp_path, monkeypatch):
    stubs = ModelStubs(fail={'model'})
    monkeypatch.setattr(pipeline, '_impl', stubs.impl)
    res = pipeline.run(_src(tmp_path), module='PipelinePython', out=tmp_path / 'run', lean_root=ROOT)
    st = res['run']['stages']
    assert st['model']['status'] == 'failed' and 'model exploded' in st['model']['error']
    assert [st[s]['status'] for s in ('describe', 'formalize', 'check', 'prove')] == ['blocked'] * 4
    assert st['report']['status'] == 'ok'


# --- report ---------------------------------------------------------------------------------

def test_report_levels_and_findings_order(tmp_path):
    s = ModelStubs()
    t = model_translation()
    english = s.describe(t, tmp_path)
    stmts = s.formalize(t, english, tmp_path)
    checks = s.check(t, stmts, tmp_path)
    proofs = s.prove(t, [x.__dict__ for x in stmts], checks, tmp_path)
    ms = models()
    ms[0].status, ms[0].level = 'DISAGREES', 'none'      # add's model did not validate
    rep = nl_report.report(tmp_path, translation=t, english=english, statements=stmts, checks=checks,
                           proofs=proofs, models=ms, refine=[], deep_translation={})
    f = rep['findings']
    # REFUTED on an unvalidated model is not a bug; REFUTED_RUNTIME is a model defect.
    assert f['potential_bugs'] == [] and [x['id'] for x in f['refuted_unvalidated_model']] == ['add__p2', 'add__p3']
    assert [x['id'] for x in f['model_defects']] == ['add__p4']
    assert rep['functions'][0]['level'] == 'none' and rep['functions'][0]['skipped'] == ['model disagrees']
    assert 'L0' in rep['trust'] and 'L1' in rep['trust'] and 'second translation' in rep['trust']
    md = (tmp_path / 'report.md').read_text()
    assert 'Refuted on a model that did not validate' in md and '[none]' in md
    # An L1 claim for a model that never validated is not honoured.
    rep2 = nl_report.build(t, english, stmts, checks, proofs, models=ms,
                           refine=[{'function': ADD, 'level': 'L1', 'shapes': []}])
    assert rep2['functions'][0]['level'] == 'none'


def test_report_statement_shape_outside_l1_stays_l0(tmp_path):
    s = ModelStubs()
    t = model_translation()
    english = s.describe(t, tmp_path)
    stmts = s.formalize(t, english, tmp_path)
    for st in stmts:
        st.binders = [{'name': 'a', 'type': 'Int', 'val': '.int a'}, {'name': 'b', 'type': 'Int', 'val': '.int b'}]
    stmts[0].binders = [{'name': 's', 'type': 'String', 'val': '.str s'}]
    refined = ModelStubs().refine(t, [m.__dict__ for m in models()], fixture(), tmp_path)
    rep = nl_report.build(t, english, stmts, [], [], models=models(), refine=refined)
    trust = {p['id']: p['trust'] for p in rep['functions'][0]['properties']}
    assert trust == {'add__p1': 'L0', 'add__p2': 'L1', 'add__p3': 'L1', 'add__p4': 'L1'}
    # Partial L1: the (str) shape failed, so the function stays L0, but statements at the
    # proved (int, int) shape still inherit L1.
    partial = [dict(refined[0].__dict__, level='L0', status='FAILED',
                    shapes=refined[0].shapes + [{'kinds': ['str'], 'theorem': 'l1_add_1', 'status': 'FAILED'}])]
    rep = nl_report.build(t, english, stmts, [], [], models=models(), refine=partial)
    add = rep['functions'][0]
    assert add['level'] == 'L0'
    assert [p['trust'] for p in add['properties']] == ['L0', 'L1', 'L1', 'L1']


# --- refine (no Lean) -----------------------------------------------------------------------

def test_shapes():
    assert nl_refine.signature_shape('Int → Int → Int') == ('int', 'int')
    assert nl_refine.signature_shape('(a b : Int) → (s : String) → Except String Int') == ('int', 'int', 'str')
    assert nl_refine.signature_shape('Nat -> Bool') == ('nat',)
    assert nl_refine.signature_shape('List Int → Int') is None
    assert nl_refine.signature_shape('Int') == ()
    two = [{'name': 'a', 'type': 'Int', 'val': '.int a'}, {'name': 'f', 'type': 'Bool', 'val': 'Val.bool f'}]
    assert nl_refine.statement_shape({'binders': two}) == ('int', 'bool')
    assert nl_refine.statement_shape({'binders': [{'name': 'a', 'type': 'Int', 'val': '.int (a + 1)'}]}) is None
    assert nl_refine.module_of(model_translation()) == M
    assert nl_refine.module_of(fixture()) == 'Autoform.Generated.PipelinePython'
    # A deep translation with an initialized entry (Autoform.NL.<M>) is imported beside the model.
    deep = dict(fixture(), module='NLX', call_template='Autoform.NL.NLX.call {name} {args}')
    head = nl_refine.header(model_translation(), deep)
    assert head.startswith(f'import {M}\nimport Autoform.NL.NLX\nimport Autoform.Generated.NLX\n')
    assert 'af_eval' in head


def _refine_setup(monkeypatch, bounded):
    _fake_lean(monkeypatch)
    calls = []

    def fake_bounded(shapes, prefix, work, root, stem):
        calls.append([s.theorem for s in shapes])
        assert f'import {M}' in prefix and 'import Autoform.Generated.PipelinePython' in prefix
        return {s.tag: dict(bounded.get(s.theorem, {'status': 'AGREES', 'compared': 64}), points=len(s.points))
                for s in shapes}
    monkeypatch.setattr(nl_refine, 'bounded_check', fake_bounded)
    deep = fixture()
    deep['functions'][1]['hole_free'] = False      # fraction: holes in the deep translation
    return deep, calls


def test_refine_proves_l1_and_skips_disagreeing_models(tmp_path, monkeypatch):
    deep, calls = _refine_setup(monkeypatch, {'l1_quotient': {'status': 'DISAGREES', 'disagreement': {'a': 1, 'b': 0},
                                                              'detail': 'different results'}})
    agent = Scripted('<proof>by GOOD</proof>', cost=0.5)
    res = nl_refine.refine(model_translation(), models('VALIDATED'), deep, tmp_path, agent=agent, cache_dir=None)
    by = {r.function: r for r in res}
    assert calls == [['l1_add', 'l1_quotient']] and agent.calls == 1
    assert (by[ADD].status, by[ADD].level, by[ADD].cost_usd) == ('PROVED', 'L1', 0.5)
    sh = by[ADD].shapes[0]
    assert sh['statement'] == (f'theorem l1_add : ∀ (a : Int) (b : Int), {M}.call "{ADD}" [.int a, .int b] = '
                               f'runFunc Autoform.Generated.PipelinePython.program 1000 "{ADD}" [.int a, .int b]')
    assert (by[QUOT].status, by[QUOT].level) == ('DISAGREES', 'L0') and "{'a': 1, 'b': 0}" in by[QUOT].reason
    assert (by[FRAC].status, by[FRAC].level, by[FRAC].reason) == ('SKIPPED', 'L0', 'deep translation has holes')
    saved = json.loads((tmp_path / FILES['refine']).read_text())
    assert [r['level'] for r in saved] == ['L1', 'L0', 'L0']
    prompt = json.loads((tmp_path / 'refine/prover/l1_add/l1_add.attempt1.transcript.json').read_text())['prompt']
    assert 'AI-written Lean model' in prompt and 'return a + b' in prompt and 'af_eval' in prompt


def test_refine_failure_keeps_l0_and_records_why(tmp_path, monkeypatch):
    deep, _ = _refine_setup(monkeypatch, {})
    stmts = [{'id': 'x', 'function': ADD, 'elaborates': True,
              'binders': [{'name': 's', 'type': 'String', 'val': '.str s'}]}]
    agent = Scripted('<proof>FAILED</proof><reason>no idea</reason>')
    res = nl_refine.refine(model_translation(), models(), deep, tmp_path, statements=stmts, agent=agent,
                           attempts=1, cache_dir=None)
    add = res[0]
    # Two shapes: the signature's (int, int) and the statement's (str).
    assert [s['theorem'] for s in add.shapes] == ['l1_add_0', 'l1_add_1']
    assert (add.status, add.level) == ('FAILED', 'L0') and 'l1_add_0' in add.reason
    assert res[2].status == 'SKIPPED' and 'not validated' in res[2].reason and res[2].level == 'none'


def test_refine_budget_zero_does_not_call_the_agent(tmp_path, monkeypatch):
    deep, _ = _refine_setup(monkeypatch, {})
    res = nl_refine.refine(model_translation(), models(), deep, tmp_path, agent=Refuse(), budget_usd=0,
                           cache_dir=None)
    assert res[0].level == 'L0' and 'budget' in res[0].reason


def test_refine_pairs_by_file_and_source_name(tmp_path, monkeypatch):
    deep, _ = _refine_setup(monkeypatch, {})
    mt = model_translation()
    for f in mt['functions']:
        f['name'] = 'model:' + f['source_name']
    ms = models()
    for m in ms:
        m.function = 'model:' + m.function.rsplit('.', 1)[1]
    res = nl_refine.refine(mt, ms, deep, tmp_path, agent=Scripted('<proof>by GOOD</proof>'), cache_dir=None)
    assert res[0].deep_function == ADD and res[0].level == 'L1'
    assert f'{M}.call "model:add"' in res[0].shapes[0]['statement']


# --- Lean ---------------------------------------------------------------------------------------

class _ScriptedAgent:
    """Replies with a fixed proof for one theorem and gives up on the others."""
    name = 'scripted'

    def __init__(self, theorem, reply):
        self.theorem, self.reply, self.calls = theorem, reply, []

    def run(self, prompt, cwd):
        self.calls.append(prompt)
        if f'Theorem: `{self.theorem}`' in prompt:
            return self.reply, 0.0
        return '<proof>FAILED</proof><reason>scripted: not this one</reason>', 0.0


@LEAN
def test_l1_add_kernel_checked(tmp_path):
    # The model module is test-only (not imported by Autoform.lean): build it on demand.
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    built = subprocess.run([lake, 'build', M], cwd=ROOT, capture_output=True, text=True, timeout=3600)
    assert built.returncode == 0, built.stdout[-2000:]
    reply = ('<proof>by\n  intro a b\n  af_eval\n  simp [Autoform.NLModel.TestFixturePython.call, '
             'Autoform.NLModel.TestFixturePython.add]</proof>')
    agent = _ScriptedAgent('l1_add', reply)
    mt, deep = model_translation(), fixture()
    res = nl_refine.refine(mt, models('VALIDATED'), deep, tmp_path, agent=agent, attempts=1, cache_dir=None,
                           lean_root=ROOT)
    by = {r.function: r for r in res}
    add, quot, frac = by[ADD], by[QUOT], by[FRAC]
    assert add.shapes[0]['bounded']['status'] == 'AGREES', add.shapes[0]['bounded']
    assert (add.status, add.level) == ('PROVED', 'L1'), add.reason
    assert set(add.shapes[0]['axioms']) <= prover.ALLOWED_AXIOMS and Path(add.shapes[0]['certificate']).is_file()
    # quotient: the model agrees with the deep translation on the domain (floor division,
    # ZeroDivisionError), but the scripted agent gives up -> stays L0 with the reason.
    assert quot.shapes[0]['bounded']['status'] == 'AGREES', quot.shapes[0]['bounded']
    assert (quot.status, quot.level) == ('FAILED', 'L0') and 'l1_quotient' in quot.reason
    # fraction: the model has no case for it (a hole) while the deep translation returns a
    # float -> the bounded check finds a disagreement and no agent call is made.
    assert frac.shapes[0]['bounded']['status'] == 'DISAGREES' and frac.level == 'L0'
    assert len(agent.calls) == 2
    # A wrong proof is rejected by the kernel.
    bad = _ScriptedAgent('l1_add', '<proof>by\n  intro a b\n  exact Eq.refl EResult.outOfFuel</proof>')
    wrong = nl_refine.refine(mt, models()[:1], deep, tmp_path / 'wrong', agent=bad, attempts=1, cache_dir=None,
                             lean_root=ROOT, bounded=False)
    assert wrong[0].level == 'L0' and 'independent check failed' in wrong[0].reason


def test_cli_preflight_stops_before_spending(tmp_path, monkeypatch, capsys):
    called = []
    monkeypatch.setattr(pipeline, 'run', lambda *a, **k: called.append(1))
    monkeypatch.setattr(pipeline.shutil, 'which', lambda name: None)
    monkeypatch.setenv('ANTHROPIC_API_KEY', 'x')
    assert pipeline.main(['src', 'Mod', '--lean-root', str(tmp_path), '--budget-usd', '-1']) == 2
    err = capsys.readouterr().err
    assert called == []
    assert 'no Lean project' in err and 'claude CLI is not on PATH' in err and '--budget-usd must be' in err
    assert 'warning: ANTHROPIC_API_KEY is set but not used' in err
    monkeypatch.setenv('AUTOFORM_CLAUDE_AUTH', 'api-key')
    monkeypatch.delenv('ANTHROPIC_API_KEY')
    errors, _ = pipeline.preflight(None)
    assert any('ANTHROPIC_API_KEY is not set' in e for e in errors)
    monkeypatch.setenv('AUTOFORM_CLAUDE_AUTH', 'bogus')
    assert any('must be one of login, api-key, api' in e for e in pipeline.preflight(None)[0])
    errors, _ = pipeline.preflight(None, domain_size=0)
    assert any('--domain-size' in e for e in errors)
