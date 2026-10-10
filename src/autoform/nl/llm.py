"""One language-model backend for every stage, behind `ask` / `ask_json`.

`ask(prompt, cwd)` returns the model's final text. `ask_json(prompt, keys)` asks for a
JSON object between <json></json> tags and validates the listed top-level keys, retrying
once with the parse error. Results are cached on disk by prompt hash so reruns are free,
whichever backend produced them.

Backends (`AUTOFORM_CLAUDE_AUTH`):

  login    (default) headless Claude Code on the logged-in plan; `ANTHROPIC_API_KEY` is
           removed from the child environment (a set key would take precedence over it).
  api-key  headless Claude Code billing `ANTHROPIC_API_KEY` (e.g. in CI).
  api      the Anthropic Messages API through the `anthropic` Python SDK with
           `ANTHROPIC_API_KEY`; model `AUTOFORM_LLM_MODEL` or `DEFAULT_API_MODEL`. The
           spend is computed from the response usage and `PRICES` (one table, dated). This
           backend runs no tools: a tool-using call (`tools != ''`) is refused, and the
           proving agents (`autoform.harness.prover.ClaudeCodeAgent`) still need the CLI.

Spend is reported per call as `(text, cost_usd)`; the CLI reports its own cost, the api
backend prices its usage. The per-run budget (`--budget-usd`) is enforced by the stages
with `over_budget` / `record_skips` here: a stage starts no new function once the spend
plus the estimate for the next call would cross the limit, and names what it skipped in
`budget.json` with the amount spent at that point.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import re
import shutil
import signal
import subprocess
from pathlib import Path

CACHE = Path(os.environ.get('AUTOFORM_LLM_CACHE', Path.home() / '.cache/autoform/llm'))
TOOLS_NONE = ''            # pure text answer
TOOLS_LEAN = 'Bash(./check.sh:*),Read,Edit,Write,Grep,Glob'
AUTH_MODES = ('login', 'api-key', 'api')

DEFAULT_API_MODEL = 'claude-opus-5-5'
API_MAX_TOKENS = 16000     # non-streaming ceiling that stays under the SDK's HTTP timeout
# Anthropic first-party API list prices, USD per million tokens, as published on PRICES_DATE:
# (input, output, cache write, cache read). Cache write is 1.25x input (5-minute cache);
# cache read is the published figure where one exists, else 0.1x input. Add a row before
# using a model: `ask` refuses a model it cannot price.
PRICES_DATE = '2026-10-06'
PRICES = {
    'claude-opus-5-5':   (4.00, 20.00, 5.00, 0.20),
    'claude-opus-5':     (5.00, 25.00, 6.25, 0.50),
    'claude-sonnet-5-5': (2.00, 10.00, 2.50, 0.20),
    'claude-sonnet-5':   (2.00, 10.00, 2.50, 0.20),
    'claude-haiku-5-5':  (0.10, 0.50, 0.125, 0.01),
    'claude-fable-5-1':  (10.00, 50.00, 12.50, 0.25),
}


class LLMError(RuntimeError):
    pass


def claude_auth() -> str:
    mode = os.environ.get('AUTOFORM_CLAUDE_AUTH', 'login').strip().lower()
    if mode not in AUTH_MODES:
        raise LLMError(f'AUTOFORM_CLAUDE_AUTH must be one of {", ".join(AUTH_MODES)}, not {mode!r}')
    return mode


def sdk_available() -> bool:
    return importlib.util.find_spec('anthropic') is not None


def available() -> bool:
    """Whether the configured backend can answer at all (no call is made)."""
    if os.environ.get('AUTOFORM_CLAUDE_AUTH', 'login').strip().lower() == 'api':
        return bool(os.environ.get('ANTHROPIC_API_KEY')) and sdk_available()
    return shutil.which('claude') is not None


def claude_env() -> dict:
    """The environment for a `claude` child process under the chosen authentication."""
    if claude_auth() in ('api-key', 'api'):
        return dict(os.environ)
    return {k: v for k, v in os.environ.items() if k != 'ANTHROPIC_API_KEY'}


def api_model(model: str | None = None) -> str:
    return model or os.environ.get('AUTOFORM_LLM_MODEL') or DEFAULT_API_MODEL


def api_cost_usd(model: str, usage) -> float:
    """USD for one Messages API response from its `usage` (an SDK object or a dict)."""
    if model not in PRICES:
        raise LLMError(f'no price for model {model!r} in autoform.nl.llm.PRICES (dated {PRICES_DATE}); add a row')
    get = (usage.get if isinstance(usage, dict) else lambda k: getattr(usage, k, None))
    tokens = [float(get(k) or 0) for k in ('input_tokens', 'output_tokens', 'cache_creation_input_tokens',
                                           'cache_read_input_tokens')]
    return sum(n * price for n, price in zip(tokens, PRICES[model])) / 1e6


_API_CLIENT = None


def api_client():
    """The SDK client (built once). Tests replace this with a client over a fake transport."""
    global _API_CLIENT
    if _API_CLIENT is None:
        try:
            import anthropic
        except ImportError:
            raise LLMError('AUTOFORM_CLAUDE_AUTH=api needs the anthropic SDK: pip install "anthropic>=1,<2" '
                           '(requirements.txt lists it as optional)')
        key = os.environ.get('ANTHROPIC_API_KEY')
        if not key:
            raise LLMError('AUTOFORM_CLAUDE_AUTH=api but ANTHROPIC_API_KEY is not set')
        _API_CLIENT = anthropic.Anthropic(api_key=key)
    return _API_CLIENT


def _api_errors() -> tuple:
    try:
        import anthropic
    except ImportError:   # a fake client in tests; nothing to translate
        return ()
    return (anthropic.APIError,)


def ask_api(prompt: str, *, model: str | None = None, timeout: int = 1800) -> tuple[str, float]:
    """One Messages API call; (text, cost_usd) with the cost priced from the response usage."""
    model = api_model(model)
    if model not in PRICES:
        raise LLMError(f'no price for model {model!r} in autoform.nl.llm.PRICES (dated {PRICES_DATE}); add a row')
    client = api_client()
    try:
        resp = client.with_options(timeout=float(timeout)).messages.create(
            model=model, max_tokens=API_MAX_TOKENS, messages=[{'role': 'user', 'content': prompt}])
    except _api_errors() as exc:   # the SDK's APIError family: status, connection and timeout errors
        raise LLMError(f'model error ({type(exc).__name__}): {str(exc)[:500]}')
    cost = api_cost_usd(model, resp.usage)
    text = ''.join(b.text for b in resp.content if getattr(b, 'type', '') == 'text')
    if resp.stop_reason == 'refusal':
        details = getattr(resp, 'stop_details', None)
        raise LLMError(f'model refused ({getattr(details, "category", None)}) after ${cost:.4f}')
    # stop_reason 'max_tokens': the text is truncated; ask_json's repair round deals with it
    return text, cost


def ask(prompt: str, cwd: Path | str = '.', *, tools: str = TOOLS_NONE, max_turns: int = 1,
        timeout: int = 1800, model: str | None = None, cache: bool = True) -> tuple[str, float]:
    """Return (text, cost_usd). Tool-using calls (tools != '') are never cached."""
    key = hashlib.sha256(json.dumps([prompt, tools, max_turns, model]).encode()).hexdigest()
    hit = CACHE / (key + '.json')
    if cache and not tools and hit.is_file():
        data = json.loads(hit.read_text())
        return data['text'], 0.0
    if claude_auth() == 'api':
        if tools:
            raise LLMError('the api backend runs no tools; AUTOFORM_CLAUDE_AUTH=login or api-key for a call with '
                           f'tools={tools!r}')
        text, cost = ask_api(prompt, model=model, timeout=timeout)
    else:
        text, cost = ask_cli(prompt, cwd, tools=tools, max_turns=max_turns, timeout=timeout, model=model)
    if cache and not tools and text:
        CACHE.mkdir(parents=True, exist_ok=True)
        hit.write_text(json.dumps({'text': text}))
    return text, cost


def ask_cli(prompt: str, cwd: Path | str = '.', *, tools: str = TOOLS_NONE, max_turns: int = 1,
            timeout: int = 1800, model: str | None = None) -> tuple[str, float]:
    """Headless Claude Code (`claude -p`); the cost is the CLI's own `total_cost_usd`."""
    if shutil.which('claude') is None:
        raise LLMError('claude CLI not found on PATH')
    cmd = ['claude', '-p', prompt, '--output-format', 'json', '--max-turns', str(max_turns)]
    if tools:
        cmd += ['--allowedTools', tools, '--permission-mode', 'acceptEdits']
    else:
        # `--allowedTools ''` alone does not stop the model from *attempting* a tool call, which
        # ends a one-turn session with error_max_turns and no text; `--tools ''` removes them.
        cmd += ['--allowedTools', '', '--tools', '']
    if model or os.environ.get('AUTOFORM_LLM_MODEL'):
        cmd += ['--model', model or os.environ['AUTOFORM_LLM_MODEL']]
    env = claude_env()
    proc = subprocess.Popen(cmd, cwd=str(cwd), env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            text=True, start_new_session=True)
    try:
        out, err = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)   # the agent may have spawned lean processes
        except (ProcessLookupError, PermissionError):  # exited; macOS says EPERM
            pass
        proc.communicate()
        raise LLMError(f'model call timed out after {timeout}s')
    try:
        data = json.loads(out)
    except ValueError:
        raise LLMError('unparseable CLI output: ' + (out or err)[-500:])
    if data.get('is_error'):
        raise LLMError('model error: ' + str(data.get('result') or [data.get('subtype'), data.get('errors')])[:500])
    return data.get('result') or '', float(data.get('total_cost_usd') or 0)


def extract(tag: str, text: str) -> str | None:
    found = re.findall(rf'<{tag}>\s*(.*?)\s*</{tag}>', text, re.S)
    return found[-1] if found else None


def ask_json(prompt: str, keys: list, **kw) -> tuple[dict, float]:
    """Ask for <json>{...}</json>; validate top-level keys; one repair round."""
    suffix = ('\n\nAnswer with a single JSON object between <json> and </json> tags, with keys: '
              + ', '.join(keys) + '.')
    text, cost = ask(prompt + suffix, **kw)
    for attempt in range(2):
        body = extract('json', text) or text
        try:
            data = json.loads(body)
            missing = [k for k in keys if k not in data]
            if not missing:
                return data, cost
            problem = f'missing keys {missing}'
        except ValueError as exc:
            problem = f'invalid JSON: {exc}'
        if attempt == 0:
            text, c = ask(prompt + suffix + f'\n\nYour previous answer was rejected ({problem}). '
                          'Reply again with only the corrected <json> object.', **dict(kw, cache=False))
            cost += c
    raise LLMError('no valid JSON after repair: ' + problem)


# --- per-run budget ---------------------------------------------------------------------

def over_budget(spent: float, budget_usd: float | None, estimate: float = 0.0) -> bool:
    """True when no further call may start: the spend has reached the budget, or the next
    call (estimated from what the stage has measured so far) would cross it."""
    if budget_usd is None:
        return False
    return spent >= budget_usd - 1e-9 or spent + max(float(estimate or 0), 0.0) > budget_usd + 1e-9


def budget_skip(function: str, spent: float, budget_usd: float, estimate: float = 0.0, **extra) -> dict:
    """A budget.json record: the skipped function by name and the amount spent at that point."""
    reason = f'budget: ${spent:.2f} of ${budget_usd:.2f} spent'
    if estimate:
        reason += f'; the next call (about ${estimate:.2f}) would cross it'
    return dict(function=function, reason=reason, spent_usd=round(spent, 4), budget_usd=budget_usd,
                estimate_usd=round(float(estimate or 0), 4), **extra)


def record_skips(out, stage: str, items: list):
    """Replace `stage`'s budget/cap skips in budget.json (the report's "Spent vs budget"
    section). Each item names a function (and optionally a property) with its reason."""
    from .schema import FILES
    f = Path(out) / FILES['budget']
    if not items and not f.is_file():
        return
    data = json.loads(f.read_text()) if f.is_file() else {'skipped': []}
    data['skipped'] = [s for s in data['skipped'] if s.get('stage') != stage] + [dict(s, stage=stage) for s in items]
    f.write_text(json.dumps(data, indent=1, ensure_ascii=False))
