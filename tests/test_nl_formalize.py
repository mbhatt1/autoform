"""Formalize stage (English -> Lean statements). Model calls are monkeypatched; the Lean
elaboration test runs with AUTOFORM_TEST_LEAN=1 and needs the PipelinePython module built
under the translation's lean_root (override with AUTOFORM_NL_LEAN_ROOT)."""
from __future__ import annotations

import json
import os
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))

from autoform.nl import formalize as F, llm, schema  # noqa: E402

FIX = ROOT / 'tests' / 'fixtures' / 'nl'


def translation(module='PipelinePython'):
    tr = schema.load(FIX / f'translation-{module}.json')
    tr['lean_root'] = os.environ.get('AUTOFORM_NL_LEAN_ROOT', tr['lean_root'])
    return tr


def fn(tr, short):
    return next(f for f in tr['functions'] if f['name'].endswith(short))


ADD_OK = {'binders': [{'name': 'a', 'type': 'Int'}, {'name': 'b', 'type': 'Int'}], 'pre': 'true',
          'post': 'match r with | .val (.int n) => n == a + b | _ => false'}
DIV0 = {'binders': [{'name': 'a', 'type': 'Int'}, {'name': 'b', 'type': 'Int'}], 'pre': 'b == 0',
        'post': 'r matches .exn (.str "ZeroDivisionError")'}


# ------------------------------------------------------------------ pure helpers

def test_lean_string_and_ids():
    assert F.lean_string('a"b\\c') == '"a\\"b\\\\c"'
    assert F.statement_id('numbers.py:<module>.add', 'p1') == 'numbers_py_module_add__p1'
    assert F.statement_id('1f', 'p2').startswith('f_1f')


def test_call_and_canonical_shape():
    tr = translation()
    call = F.build_call(tr['call_template'], 'numbers.py:<module>.add', ['.int a', '.int b'])
    assert call == ('runFunc Autoform.Generated.PipelinePython.program 1000 '
                    '"numbers.py:<module>.add" [.int a, .int b]')
    cand = F.parse_candidate(ADD_OK)
    prop = F.assemble(cand['binders'], cand['pre'], cand['post'], call)
    assert prop.startswith('∀ (a : Int), ∀ (b : Int), (((true) : Bool)) = true → (fun (r : EResult) => ((')
    assert prop.endswith(f'({call}) = true')


def test_parse_candidate_fills_vals_and_defaults():
    c = F.parse_candidate({'binders': [['s', 'String'], {'name': 'ok', 'type': 'Bool'}], 'pre': None,
                           'post': ' r matches .val _ '})
    assert [b['val'] for b in c['binders']] == ['.str s', '.bool ok']
    assert c['pre'] == 'true' and c['post'] == 'r matches .val _'


def test_shape_checks():
    f = fn(translation(), '.add')
    assert F.shape_problems(f, F.parse_candidate(ADD_OK)) == []
    ignores_r = dict(ADD_OK, post='a + b == b + a')
    assert any('does not inspect' in p for p in F.shape_problems(f, F.parse_candidate(ignores_r)))
    string_r = dict(ADD_OK, post='a == 0 && "r" == "r"')
    assert any('does not inspect' in p for p in F.shape_problems(f, F.parse_candidate(string_r)))
    too_few = dict(ADD_OK, binders=[{'name': 'a', 'type': 'Int'}])
    assert any('exactly 2 binder' in p for p in F.shape_problems(f, F.parse_candidate(too_few)))
    bad_name = dict(ADD_OK, binders=[{'name': 'r', 'type': 'Int'}, {'name': 'fun', 'type': 'Int'}])
    assert sum('identifier' in p for p in F.shape_problems(f, F.parse_candidate(bad_name))) == 2
    vacuous = dict(ADD_OK, pre='false')
    assert any('vacuous' in p for p in F.shape_problems(f, F.parse_candidate(vacuous)))
    pre_r = dict(ADD_OK, pre='r matches .val _')
    assert any('pre mentions' in p for p in F.shape_problems(f, F.parse_candidate(pre_r)))
    float_t = dict(ADD_OK, binders=[{'name': 'a', 'type': 'Float'}, {'name': 'b', 'type': 'Int'}])
    assert any("use Int, Bool or String" in p for p in F.shape_problems(f, F.parse_candidate(float_t)))
    sneaky = dict(ADD_OK, post='r matches .val _ || (by sorry)')
    assert any('plain term' in p for p in F.shape_problems(f, F.parse_candidate(sneaky)))
    c_add = fn(translation('PipelineC'), 'add')
    typed = dict(ADD_OK, binders=[{'name': 'a', 'type': 'String'}, {'name': 'b', 'type': 'Int'}])
    assert any('must have type Int' in p for p in F.shape_problems(c_add, F.parse_candidate(typed)))
    assert any('does not mention the call' in p
               for p in F.shape_problems(f, F.parse_candidate(ADD_OK), 'CALL', 'no call here'))


def test_prompt_assembly():
    tr = translation()
    f = fn(tr, '.quotient')
    spec = {'function': f['name'], 'summary': 'floor division', 'properties': []}
    prop = {'id': 'p1', 'text': 'If b is 0, quotient(a, b) raises ZeroDivisionError.', 'kind': 'exception'}
    p = F.build_prompt(tr, f, spec, prop)
    for needle in ('inductive EResult', '.exn (.str "ZeroDivisionError")', 'Int.fdiv', 'Val.beq',
                   'Worked examples', prop['text'], f['name'], 'quotient(a, b)'):
        assert needle in p
    rp = F.repair_prompt(p, F.parse_candidate(DIV0), 'line one\nline two', 'x.lean:2:3: error: boom')
    assert rp.startswith(p) and '   2  line two' in rp and 'error: boom' in rp


def test_prompt_includes_lean_body(tmp_path):
    tr = translation()
    gen = tmp_path / 'Autoform' / 'Generated'
    gen.mkdir(parents=True)
    (gen / 'PipelinePython.lean').write_text(
        'x\n\ndef f_add : Func :=\n  { name := "numbers.py:<module>.add"\n  , body := (.ret (.name "a")) }\n\nrest')
    tr['lean_root'] = str(tmp_path)
    assert F.lean_body(tr, fn(tr, '.add')).startswith('def f_add : Func :=')
    assert F.lean_body(tr, fn(tr, '.quotient')) == ''


def test_errors_only_keeps_errors():
    log = ('a.lean:3:0: warning: declaration uses `sorry`\n'
           'a.lean:5:8: error: unknown identifier `q`\n  more detail\n'
           'a.lean:9:0: warning: unused\n')
    assert F.errors_only(log) == 'a.lean:5:8: error: unknown identifier `q`\n  more detail'


def test_formalize_repairs_and_writes(tmp_path, monkeypatch):
    """Round 1 is shape-rejected (post ignores r); round 2 goes to (fake) Lean and passes."""
    tr = translation()
    answers = [dict(ADD_OK, post='a + b == a + b'), ADD_OK, DIV0]
    prompts, lean_files = [], []

    def fake_ask(prompt, keys, **kw):
        prompts.append(prompt)
        if 'raises ZeroDivisionError' in prompt.split('## The property to formalize')[1]:
            return DIV0, 0.01
        return answers.pop(0), 0.02

    def fake_lean(root, path, timeout=0):
        lean_files.append(Path(path).read_text())
        return True, ''

    monkeypatch.setattr(llm, 'ask_json', fake_ask)
    monkeypatch.setattr(F, 'run_lean', fake_lean)
    english = [{'function': fn(tr, '.add')['name'], 'summary': '', 'properties': [
                   {'id': 'p1', 'text': 'For all integers a and b, add(a, b) returns a + b.', 'kind': 'postcondition'}]},
               {'function': fn(tr, '.quotient')['name'], 'summary': '', 'properties': [
                   {'id': 'p1', 'text': 'If b is 0, quotient(a, b) raises ZeroDivisionError.', 'kind': 'exception'}]},
               {'function': 'nope', 'summary': '', 'properties': [{'id': 'p1', 'text': 'x', 'kind': 'example'}]}]
    stmts = F.formalize(tr, english, tmp_path, parallel=1)
    assert [s.attempts for s in stmts] == [2, 1] and all(s.elaborates for s in stmts)
    assert 'does not inspect' in stmts[0].elaboration_log
    assert '## Your previous answer was rejected' in prompts[1]
    assert stmts[1].binders == [{'name': 'a', 'type': 'Int', 'val': '.int a'},
                                {'name': 'b', 'type': 'Int', 'val': '.int b'}]
    assert any('theorem stmt_numbers_py_module_quotient__p1 :' in t and '#check fun (a : Int) (b : Int) =>' in t
               for t in lean_files)
    saved = json.loads((tmp_path / 'statements.json').read_text())
    assert [s['id'] for s in saved] == ['numbers_py_module_add__p1', 'numbers_py_module_quotient__p1']
    stats = json.loads((tmp_path / 'formalize-stats.json').read_text())
    assert stats['first_try'] == 1 and stats['after_repair'] == 1 and stats['skipped'][0]['function'] == 'nope'
    assert abs(stats['cost_usd'] - 0.05) < 1e-9


def test_formalize_gives_up(tmp_path, monkeypatch):
    tr = translation()
    monkeypatch.setattr(llm, 'ask_json', lambda p, k, **kw: (dict(ADD_OK, post='true'), 0.0))
    stmts = F.formalize(tr, [{'function': fn(tr, '.add')['name'], 'summary': '', 'properties': [
        {'id': 'p1', 'text': 't', 'kind': 'postcondition'}]}], tmp_path, repairs=2)
    assert not stmts[0].elaborates and stmts[0].attempts == 3


# ------------------------------------------------------------------ Lean-gated

@pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_LEAN') != '1', reason='set AUTOFORM_TEST_LEAN=1')
@pytest.mark.parametrize('cand,expect', [
    (ADD_OK, True),
    (DIV0, True),
    # `n == a + b` where n : Int but compared against a String binder: ill-typed
    ({'binders': [{'name': 'a', 'type': 'String'}, {'name': 'b', 'type': 'Int'}], 'pre': 'true',
      'post': 'match r with | .val (.int n) => n == a + b | _ => false'}, False),
    # unknown constructor
    (dict(DIV0, post='r matches .raise (.str "ZeroDivisionError")'), False),
])
def test_lean_elaboration(tmp_path, cand, expect):
    tr = translation()
    f = fn(tr, '.add')
    c = F.parse_candidate(cand)
    call = F.build_call(tr['call_template'], f['name'], [b['val'] for b in c['binders']])
    path = tmp_path / 'stmt.lean'
    path.write_text(F.scratch_text(tr, 'stmt_test', c, F.assemble(c['binders'], c['pre'], c['post'], call)))
    ok, log = F.run_lean(tr['lean_root'], path)
    assert ok is expect, log
