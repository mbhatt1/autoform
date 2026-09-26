"""Describe stage: batching, validation and fallback, without calling the model."""
from __future__ import annotations

import json
import os
import re
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'src'))

from autoform.nl import describe, llm, schema  # noqa: E402

FIXTURES = ROOT / 'tests' / 'fixtures' / 'nl'


def fn(name, source='', params=('a', 'b'), sort='int', **kw):
    info = dict(name=f'm.py:<module>.{name}', source_name=name, file='m.py', line=1,
                params=[dict(name=p, sort=sort, integer_type='') for p in params], returns='int',
                hole_free=True, holes=[], call_closed=True, needs_init=False,
                source=source or f'def {name}({", ".join(params)}):\n    return a + b\n', doc='',
                tests=[], callers=[])
    info.update(kw)
    return info


def translation(functions, language='python'):
    return dict(module='M', language=language, lean_root='', source_root='', source_revision='',
                ast='', program_const='', init_const=None, call_template='', fuel=10,
                functions=functions)


def good_entry(key, name='f'):
    return dict(key=key, summary=f'{name} adds.', properties=[
        dict(id='p1', text=f'For all integers a and b, {name}(a, b) returns a + b.', kind='postcondition',
             evidence=['name']),
        dict(id='p2', text=f'{name}(2, 3) returns 5.', kind='example', evidence=['implementation'])])


class FakeModel:
    """Stands in for llm.ask: answers every key in the prompt with a canned entry."""

    def __init__(self, override=None):
        self.prompts = []
        self.override = override or {}

    def __call__(self, prompt, cwd='.', **kw):
        self.prompts.append(prompt)
        listed = json.loads(prompt.split('Functions (JSON):\n', 1)[1].split('\n\nThe answer object', 1)[0])
        entries = [self.override.get(item['call_as'], good_entry(item['key'], item['call_as']))
                   for item in listed]
        for e, item in zip(entries, listed):
            if e is not None:
                e.setdefault('key', item['key'])
        return '<json>' + json.dumps({'functions': [e for e in entries if e is not None]}) + '</json>', 0.01


@pytest.fixture
def fake(monkeypatch, tmp_path):
    monkeypatch.setenv('AUTOFORM_LLM_CACHE', str(tmp_path / 'cache'))
    model = FakeModel()
    monkeypatch.setattr(llm, 'ask', model)
    return model


def test_batches_split_and_answers_are_matched_by_key(fake, tmp_path):
    fns = [fn(f'f{i}') for i in range(10)]
    specs = describe.describe(translation(fns), tmp_path, batch_size=4, parallel=2, use_model=True)
    assert len(fake.prompts) == 3
    sizes = sorted(len(re.findall(r'"key": "f\d+"', p)) for p in fake.prompts)
    assert sizes == [2, 4, 4]
    assert [s.function for s in specs] == [f['name'] for f in fns]
    assert all(s.model != 'fallback' for s in specs)
    # Each spec is about its own function, not a neighbour in the batch.
    assert all(f" {f['source_name']}(a, b)" in s.properties[0].text for s, f in zip(specs, fns))
    written = schema.load(tmp_path / 'english.json')
    assert [w['function'] for w in written] == [f['name'] for f in fns]
    meta = schema.load(tmp_path / 'english.meta.json')
    assert meta['batches'] == 3 and meta['cost_usd'] == pytest.approx(0.03)


def test_prompt_carries_sorts_evidence_and_rules(fake, tmp_path):
    f = fn('quotient', source='def quotient(a, b):\n    return a // b\n', sort='any',
           tests=[dict(location='tests/test_m.py:3', text='assert quotient(7, 2) == 3')],
           doc='Integer quotient.', callers=['m.py:<module>.g'])
    describe.describe(translation([f]), tmp_path, use_model=True)
    p = fake.prompts[0]
    for needle in ('"sort": "any"', 'tests/test_m.py:3', 'Integer quotient.', 'm.py:<module>.g',
                   '["implementation"]', 'exceptional path', 'performance'):
        assert needle in p


def test_ineligible_functions_are_skipped_with_reason(fake, tmp_path):
    fns = [fn('ok'), fn('holey', hole_free=False, holes=['h1']), fn('open', call_closed=False)]
    specs = describe.describe(translation(fns), tmp_path, functions=['ok', 'holey', 'open', 'ghost'],
                              use_model=True)
    assert [s.function for s in specs] == ['m.py:<module>.ok']
    reasons = {s['function']: s['reason'] for s in schema.load(tmp_path / 'english.meta.json')['skipped']}
    assert reasons['m.py:<module>.holey'].startswith('not hole_free')
    assert reasons['m.py:<module>.open'] == 'not call_closed'
    assert reasons['ghost'] == 'not in translation'


def test_validation_drops_invalid_items(fake, tmp_path):
    props = [
        dict(id='p1', text='For all integers a and b, g(a, b) returns a + b.', kind='postcondition',
             evidence=[]),
        dict(id='p1', text='Duplicate id.', kind='example', evidence=['name']),
        dict(id='p2', text='g raises.', kind='bogus', evidence=['name']),
        dict(id='p3', text='   ', kind='example', evidence=['name']),
        dict(id='p4', text='g(a, b) returns the correct value.', kind='postcondition', evidence=['name']),
        dict(id='p5', text='g(a, b) runs in constant time.', kind='invariant', evidence=['name']),
        'not an object',
        dict(id='p6', text='If b is 0, g(a, b) raises ZeroDivisionError.', kind='exception',
             evidence='docstring'),
    ]
    fake.override = {'g': dict(summary='g.', properties=props)}
    [spec] = describe.describe(translation([fn('g')]), tmp_path, use_model=True)
    assert [p.id for p in spec.properties] == ['p1', 'p6']
    assert spec.properties[0].evidence == ['implementation']   # defaulted
    assert spec.properties[1].evidence == ['docstring']        # string coerced to list
    [issue] = schema.load(tmp_path / 'english.meta.json')['issues']
    text = ' | '.join(issue['problems'])
    for needle in ('duplicate id p1', "kind 'bogus'", 'p3: empty text', 'vague', 'performance',
                   'not an object'):
        assert needle in text


def test_validation_caps_at_six_and_flags_too_few():
    many = [dict(id=f'p{i}', text=f'h({i}) returns {i}.', kind='example', evidence=['name']) for i in range(9)]
    spec, problems = describe.validate(fn('h'), dict(summary='s', properties=many), 'm')
    assert len(spec.properties) == 6 and any('kept the first 6' in p for p in problems)
    spec, problems = describe.validate(fn('h'), dict(summary='s', properties=many[:1]), 'm')
    assert len(spec.properties) == 1 and any('only 1 valid' in p for p in problems)
    spec, problems = describe.validate(fn('h'), dict(summary='s', properties=[]), 'm')
    assert spec is None


def test_missing_or_invalid_answers_fall_back(fake, tmp_path):
    fake.override = {'lost': None, 'bad': dict(summary='x', properties='nope')}
    specs = describe.describe(translation([fn('fine'), fn('lost'), fn('bad')]), tmp_path, use_model=True)
    assert [s.model for s in specs] == ['claude-code', 'fallback', 'fallback']
    issues = {i['function']: i['problems'] for i in schema.load(tmp_path / 'english.meta.json')['issues']}
    assert 'no answer from the model' in issues['m.py:<module>.lost']
    assert 'used deterministic fallback' in issues['m.py:<module>.bad']


def test_model_error_falls_back_for_the_batch(monkeypatch, tmp_path):
    def boom(*a, **k):
        raise llm.LLMError('claude CLI not found on PATH')
    monkeypatch.setattr(llm, 'ask', boom)
    specs = describe.describe(translation([fn('a1'), fn('a2')]), tmp_path, use_model=True)
    assert all(s.model == 'fallback' for s in specs)
    assert schema.load(tmp_path / 'english.meta.json')['errors'] == ['claude CLI not found on PATH']


def test_unavailable_cli_uses_fallback_without_calling(monkeypatch, tmp_path):
    monkeypatch.setattr(llm, 'available', lambda: False)
    monkeypatch.setattr(llm, 'ask', lambda *a, **k: pytest.fail('model called'))
    specs = describe.describe(schema.load(FIXTURES / 'translation-PipelinePython.json'), tmp_path)
    assert all(s.model == 'fallback' for s in specs)
    add = specs[0]
    assert add.properties[0].text == 'For all integers a and b, add(a, b) returns a + b.'
    assert schema.load(tmp_path / 'english.meta.json')['model'] == 'fallback'


def test_fallback_templates():
    src = ('def safe_div(a, b):\n    """Divide a by b.  Refuses zero."""\n    if b == 0:\n'
           '        raise ValueError("zero")\n    x = a\n    return x // b\n')
    spec = describe.fallback(fn('safe_div', source=src, doc='Divide a by b.  Refuses zero.',
                                tests=[dict(location='t.py:4', text='assert safe_div(7, 2) == 3')]))
    texts = [p.text for p in spec.properties]
    assert spec.model == 'fallback' and spec.summary == 'Divide a by b.'
    assert 'If b == 0, safe_div(a, b) raises ValueError.' in texts
    assert 'If b is 0, safe_div(a, b) raises ZeroDivisionError.' in texts
    assert 'safe_div(7, 2) returns 3.' in texts
    assert 2 <= len(spec.properties) <= 6
    assert all(p.kind in describe.KINDS and p.evidence for p in spec.properties)
    ids = [p.id for p in spec.properties]
    assert len(ids) == len(set(ids))


def test_fallback_on_c_fixture_mentions_c_semantics():
    tr = schema.load(FIXTURES / 'translation-PipelineC.json')
    add = next(f for f in tr['functions'] if f['name'] == 'add')
    spec = describe.fallback(add, 'c')
    assert 'C expression `a + b`' in spec.properties[0].text
    assert len(spec.properties) >= 2
