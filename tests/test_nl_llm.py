"""The model backends of the autoformalizer (autoform.nl.llm) and the per-run budget.

No network and no real key: the api backend is exercised through a fake transport under
the real SDK (skipped when `anthropic` is not installed) and through a duck-typed fake
client that needs no SDK. Nothing here was run against the live Messages API.
"""
import json
import os
import re
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))

from autoform.nl import describe, llm, pipeline  # noqa: E402
from autoform.nl.schema import FILES  # noqa: E402

PRICE = llm.PRICES['claude-opus-5-5']


def _usage(inp=0, out=0, write=0, read=0):
    return {'input_tokens': inp, 'output_tokens': out, 'cache_creation_input_tokens': write,
            'cache_read_input_tokens': read}


@pytest.fixture
def api_env(monkeypatch, tmp_path):
    monkeypatch.setenv('AUTOFORM_CLAUDE_AUTH', 'api')
    monkeypatch.setenv('ANTHROPIC_API_KEY', 'sk-ant-test-not-a-real-key')
    monkeypatch.delenv('AUTOFORM_LLM_MODEL', raising=False)
    monkeypatch.setattr(llm, 'CACHE', tmp_path / 'llm-cache')
    monkeypatch.setattr(llm, '_API_CLIENT', None)
    return tmp_path


# --- a fake transport under the real SDK --------------------------------------------------

def _sdk_client(handler):
    """An `anthropic.Anthropic` whose HTTP layer is `handler(request) -> httpx2.Response`."""
    anthropic = pytest.importorskip('anthropic')
    httpx2 = pytest.importorskip('httpx2')
    return anthropic.Anthropic(api_key='sk-ant-test-not-a-real-key', max_retries=0,
                               http_client=anthropic.DefaultHttpxClient(transport=httpx2.MockTransport(handler)))


def _message(text, usage, model='claude-opus-5-5', stop='end_turn'):
    return {'id': 'msg_fake', 'type': 'message', 'role': 'assistant', 'model': model,
            'content': [{'type': 'text', 'text': text}], 'stop_reason': stop, 'stop_sequence': None,
            'usage': usage}


def test_api_backend_prices_usage_and_caches(api_env, monkeypatch):
    httpx2 = pytest.importorskip('httpx2')
    seen = []

    def handler(request):
        body = json.loads(request.content)
        seen.append(body)
        assert request.url.path == '/v1/messages' and request.headers['x-api-key'] == 'sk-ant-test-not-a-real-key'
        return httpx2.Response(200, json=_message('<json>{"a": 1}</json>', _usage(1200, 300, 100, 1000),
                                                  model=body['model']))

    monkeypatch.setattr(llm, '_API_CLIENT', _sdk_client(handler))
    text, cost = llm.ask('hello', api_env)
    assert text == '<json>{"a": 1}</json>'
    assert cost == pytest.approx((1200 * PRICE[0] + 300 * PRICE[1] + 100 * PRICE[2] + 1000 * PRICE[3]) / 1e6)
    assert seen[0]['model'] == llm.DEFAULT_API_MODEL == 'claude-opus-5-5'
    assert seen[0]['messages'] == [{'role': 'user', 'content': 'hello'}] and seen[0]['max_tokens'] == llm.API_MAX_TOKENS
    assert 'tools' not in seen[0] and 'thinking' not in seen[0]
    # The same prompt is a cache hit: no request, no spend.
    assert llm.ask('hello', api_env) == (text, 0.0) and len(seen) == 1
    # ask_json validates keys and sums the cost of the repair round.
    data, cost2 = llm.ask_json('question', ['a'])
    assert data == {'a': 1} and cost2 == pytest.approx(cost) and len(seen) == 2
    # AUTOFORM_LLM_MODEL picks the model; a model without a price row is refused before any call.
    monkeypatch.setenv('AUTOFORM_LLM_MODEL', 'claude-sonnet-5-5')
    _, c = llm.ask('other', api_env)
    assert seen[-1]['model'] == 'claude-sonnet-5-5' and c == pytest.approx(
        (1200 * 2 + 300 * 10 + 100 * 2.5 + 1000 * 0.20) / 1e6)
    monkeypatch.setenv('AUTOFORM_LLM_MODEL', 'claude-unpriced-9')
    with pytest.raises(llm.LLMError, match='no price for model'):
        llm.ask('third', api_env)
    assert len(seen) == 3


def test_api_backend_errors_are_llm_errors(api_env, monkeypatch):
    httpx2 = pytest.importorskip('httpx2')
    calls = []

    def handler(request):
        calls.append(1)
        if len(calls) == 1:
            return httpx2.Response(500, json={'type': 'error', 'error': {'type': 'api_error', 'message': 'boom'}})
        return httpx2.Response(200, json=_message('', _usage(10, 0), stop='refusal'))

    monkeypatch.setattr(llm, '_API_CLIENT', _sdk_client(handler))
    with pytest.raises(llm.LLMError, match=r'model error \(InternalServerError\)'):
        llm.ask('p1', api_env)
    with pytest.raises(llm.LLMError, match='refused'):
        llm.ask('p2', api_env)
    # A tool-using call cannot be served by the Messages API backend: refused, not faked.
    with pytest.raises(llm.LLMError, match='runs no tools'):
        llm.ask('p3', api_env, tools=llm.TOOLS_LEAN)
    assert len(calls) == 2
    assert not (api_env / 'llm-cache').exists()   # a failed call is never cached


def test_api_backend_needs_key_and_sdk(api_env, monkeypatch):
    monkeypatch.delenv('ANTHROPIC_API_KEY')
    assert llm.available() is False
    with pytest.raises(llm.LLMError, match='ANTHROPIC_API_KEY is not set'):
        llm.ask('p', api_env)
    monkeypatch.setenv('ANTHROPIC_API_KEY', 'x')
    monkeypatch.setitem(sys.modules, 'anthropic', None)   # import anthropic -> ImportError
    monkeypatch.setattr(llm, 'sdk_available', lambda: False)
    assert llm.available() is False
    with pytest.raises(llm.LLMError, match='pip install "anthropic'):
        llm.ask('p', api_env)
    errors, warnings = pipeline.preflight(ROOT, needs_model=True)
    assert any('anthropic SDK is not installed' in e for e in errors)
    monkeypatch.setattr(pipeline.shutil, 'which', lambda name: None)
    _, warnings = pipeline.preflight(ROOT, needs_model=True)
    assert any('prove and refine agents need the CLI' in w for w in warnings)


def test_auth_modes(monkeypatch):
    monkeypatch.setenv('ANTHROPIC_API_KEY', 'k')
    monkeypatch.setenv('AUTOFORM_CLAUDE_AUTH', 'login')
    assert 'ANTHROPIC_API_KEY' not in llm.claude_env()
    for mode in ('api-key', 'api'):
        monkeypatch.setenv('AUTOFORM_CLAUDE_AUTH', mode)
        assert llm.claude_env()['ANTHROPIC_API_KEY'] == 'k' and llm.claude_auth() == mode
    monkeypatch.setenv('AUTOFORM_CLAUDE_AUTH', 'bogus')
    with pytest.raises(llm.LLMError, match='login, api-key, api'):
        llm.claude_auth()


def test_price_table_is_dated_and_complete():
    assert re.fullmatch(r'\d{4}-\d{2}-\d{2}', llm.PRICES_DATE)
    assert llm.DEFAULT_API_MODEL in llm.PRICES
    for model, row in llm.PRICES.items():
        assert len(row) == 4 and all(p > 0 for p in row), model
        assert row[2] == pytest.approx(row[0] * 1.25) and row[3] < row[0], model
    assert llm.api_cost_usd('claude-opus-5-5', _usage(1_000_000)) == pytest.approx(4.0)
    assert llm.api_cost_usd('claude-opus-5-5', SimpleNamespace(**_usage(0, 1_000_000))) == pytest.approx(20.0)


def test_budget_rule_and_skip_records(tmp_path):
    assert not llm.over_budget(4.0, None, 100.0)
    assert not llm.over_budget(2.0, 5.0, 2.0)          # 4 <= 5: the next call fits
    assert llm.over_budget(4.0, 5.0, 2.0)              # 6 > 5: it would cross
    assert llm.over_budget(5.0, 5.0) and not llm.over_budget(4.99, 5.0)
    sk = llm.budget_skip('m.py:<module>.f', 4.0, 5.0, 2.0, property='p1')
    assert sk['function'] == 'm.py:<module>.f' and sk['property'] == 'p1' and sk['spent_usd'] == 4.0
    assert sk['reason'].startswith('budget: $4.00 of $5.00 spent; the next call (about $2.00) would cross it')
    llm.record_skips(tmp_path, 'describe', [sk])
    llm.record_skips(tmp_path, 'formalize', [dict(function='g', reason='r')])
    llm.record_skips(tmp_path, 'describe', [dict(function='h', reason='again')])   # replaces its own stage
    data = json.loads((tmp_path / FILES['budget']).read_text())
    assert [(s['stage'], s['function']) for s in data['skipped']] == [('formalize', 'g'), ('describe', 'h')]
    llm.record_skips(tmp_path / 'none', 'model', [])                               # nothing to record, no file
    assert not (tmp_path / 'none' / FILES['budget']).exists()


# --- a run with --budget-usd stops at the budget and the report names the skips -------------

class FakeClient:
    """Duck-typed stand-in for anthropic.Anthropic: every answer costs `usage` at list price."""

    def __init__(self, usage):
        self.usage, self.prompts, self.options = usage, [], []
        self.messages = SimpleNamespace(create=self._create)

    def with_options(self, **kw):
        self.options.append(kw)
        return self

    def _create(self, *, model, max_tokens, messages):
        prompt = messages[0]['content']
        self.prompts.append(prompt)
        keys = re.findall(r'"key": "(f\d+)"', prompt)
        answer = {'functions': [{'key': k, 'summary': f'Function {k}.',
                                 'properties': [{'id': 'p1', 'text': f'{k} returns an integer.',
                                                 'kind': 'postcondition', 'evidence': ['implementation']}]}
                                for k in keys]}
        return SimpleNamespace(model=model, stop_reason='end_turn', stop_details=None,
                               content=[SimpleNamespace(type='text', text='<json>' + json.dumps(answer) + '</json>')],
                               usage=SimpleNamespace(**self.usage))


def test_run_with_budget_stops_at_the_budget_and_reports_spend(api_env, monkeypatch, capsys):
    from test_nl_prove_pipeline import Stubs, _src
    client = FakeClient(_usage(500_000))               # $2.00 per call at the opus-5-5 input price
    monkeypatch.setattr(llm, '_API_CLIENT', client)
    stubs = Stubs()
    real_describe = describe.describe

    def impl(name):
        if name == 'describe':   # one function per call, so the stage can stop between functions
            return lambda t, out, **kw: real_describe(t, out, batch_size=1, parallel=1, **kw)
        return stubs.impl(name)

    monkeypatch.setattr(pipeline, '_impl', impl)
    src, out = _src(api_env), api_env / 'run'
    argv = [str(src), 'PipelinePython', '--deep', '--no-prove', '--judge', 'none', '--skip-preflight',
            '--lean-root', str(ROOT), '--out', str(out), '--budget-usd', '5']
    rc = pipeline.main(argv)
    stdout = capsys.readouterr().out
    assert rc in (0, 1)
    run = json.loads((out / 'run.json').read_text())
    # add ($2) and fraction ($2) were described; quotient would have crossed $5 and was not started.
    assert len(client.prompts) == 2 and run['stages']['describe']['cost_usd'] == 4.0 and run['cost_usd'] == 4.0
    assert run['budget_usd'] == 5.0 and run['stages']['describe']['status'] == 'ok'
    english = json.loads((out / FILES['english']).read_text())
    assert [e['function'].split('.')[-1] for e in english] == ['add', 'fraction']
    budget = json.loads((out / FILES['budget']).read_text())
    assert budget['skipped'] == [{'function': 'numbers.py:<module>.quotient', 'stage': 'describe',
                                  'reason': 'budget: $4.00 of $5.00 spent; the next call (about $2.00) would cross it',
                                  'spent_usd': 4.0, 'budget_usd': 5.0, 'estimate_usd': 2.0}]
    meta = json.loads((out / 'english.meta.json').read_text())
    assert meta['skipped'][0]['function'].endswith('quotient') and meta['cost_usd'] == 4.0
    # The pipeline went on to the report, which shows the spend and names the skip.
    rep = json.loads((out / FILES['report']).read_text())
    assert rep['run']['stages']['report']['status'] == 'ok' and rep['run']['stages']['check']['status'] == 'ok'
    assert rep['budget']['budget_usd'] == 5.0 and rep['budget']['spent_usd'] == 4.0
    assert rep['budget']['by_stage']['describe'] == 4.0
    assert [s['function'] for s in rep['budget']['skipped']['describe']] == ['numbers.py:<module>.quotient']
    quotient = next(f for f in rep['functions'] if f['name'].endswith('quotient'))
    assert quotient['budget_skips'][0]['stage'] == 'describe'
    md = (out / 'report.md').read_text()
    assert '## Spent vs budget' in md and '- budget: $5.00; spent: $4.00' in md
    assert re.search(r'- skipped at describe: 1 — numbers\.py:<module>\.quotient', md)
    assert re.search(r'describe\s+ok\s+\S+s\s+\$4\.0', stdout)
    # A bigger budget reruns describe (its inputs include the budget); the two described
    # functions are cache hits and only quotient is paid for.
    rc = pipeline.main(argv[:-1] + ['10'])
    run = json.loads((out / 'run.json').read_text())
    assert len(client.prompts) == 3 and run['stages']['describe']['cost_usd'] == 2.0
    assert [e['function'].split('.')[-1] for e in json.loads((out / FILES['english']).read_text())] == \
        ['add', 'fraction', 'quotient']
    assert json.loads((out / FILES['budget']).read_text())['skipped'] == []
    assert json.loads((out / FILES['report']).read_text())['budget']['skipped'] == {}


def test_describe_without_a_budget_is_unchanged(api_env, monkeypatch):
    from test_nl_prove_pipeline import fixture
    client = FakeClient(_usage(500_000))
    monkeypatch.setattr(llm, '_API_CLIENT', client)
    specs = describe.describe(fixture(), api_env / 'd', batch_size=1, parallel=2)
    assert len(specs) == 3 and len(client.prompts) == 3
    assert not (api_env / 'd' / FILES['budget']).exists()
    meta = json.loads((api_env / 'd' / 'english.meta.json').read_text())
    assert meta['cost_usd'] == 6.0 and meta['model'] == 'claude-code'


def test_formalize_stops_at_a_function_under_budget(tmp_path, monkeypatch):
    from autoform.nl import formalize as fz
    from test_nl_prove_pipeline import fixture
    calls = []

    def one(translation, fn, spec, prop, scratch, repairs=3, ask=None):
        calls.append(fn['name'])
        from autoform.nl.schema import Statement
        sid = fz.statement_id(fn['name'], prop['id'])
        return (Statement(sid, fn['name'], prop['id'], prop['text'], 'True', [], 'true', 'true', elaborates=True),
                {'id': sid, 'elaborates': True, 'attempts': 1, 'cost_usd': 1.5, 'seconds': 0.0})

    monkeypatch.setattr(fz, 'formalize_one', one)
    t = fixture()
    english = [{'function': f['name'], 'summary': '', 'properties': [
        {'id': 'p1', 'text': 'x', 'kind': 'postcondition', 'evidence': []},
        {'id': 'p2', 'text': 'y', 'kind': 'postcondition', 'evidence': []}]} for f in t['functions']]
    out = tmp_path / 'f'
    stmts = fz.formalize(t, english, out, parallel=2, budget_usd=5.0)
    # add costs $3 (two properties); fraction would make $6 > $5, so it and quotient are skipped by name.
    assert len(stmts) == 2 and set(calls) == {'numbers.py:<module>.add'}
    budget = json.loads((out / FILES['budget']).read_text())
    assert [(s['function'].split('.')[-1], s['property'], s['spent_usd']) for s in budget['skipped']] == \
        [('fraction', 'p1', 3.0), ('fraction', 'p2', 3.0), ('quotient', 'p1', 3.0), ('quotient', 'p2', 3.0)]
    stats = json.loads((out / 'formalize-stats.json').read_text())
    assert stats['cost_usd'] == 3.0 and len(stats['skipped']) == 4
    # Without a budget every property is formalized and nothing is recorded.
    calls.clear()
    stmts = fz.formalize(t, english, tmp_path / 'g', parallel=2)
    assert len(stmts) == 6 and not (tmp_path / 'g' / FILES['budget']).exists()


def test_requirements_name_the_optional_sdk():
    # The SDK is an extra, not a hard requirement: the default backend is the CLI, and
    # CI's `pip install -r requirements.txt` must not pull a package no gate uses.
    text = (ROOT / 'requirements.txt').read_text()
    assert not re.search(r'^anthropic', text, re.M) and "'.[llm]'" in text
    assert 'llm = ["anthropic>=1,<2"]' in (ROOT / 'pyproject.toml').read_text()
    assert 'AUTOFORM_CLAUDE_AUTH=api' in (ROOT / 'docs/autoformalize.md').read_text()
