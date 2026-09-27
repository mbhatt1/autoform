"""One language-model backend for every stage: headless Claude Code on the logged-in plan.

`ask(prompt, cwd)` returns the model's final text. `ask_json(prompt, keys)` asks for a
JSON object between <json></json> tags and validates the listed top-level keys, retrying
once with the parse error. Results are cached on disk by prompt hash so reruns are free.
Authentication is `AUTOFORM_CLAUDE_AUTH`: `login` (default) removes `ANTHROPIC_API_KEY`
from the child environment so calls use the logged-in Claude account (a set key would
take precedence over it); `api-key` keeps the key and bills it (e.g. in CI).
"""
from __future__ import annotations

import hashlib
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


class LLMError(RuntimeError):
    pass


def available() -> bool:
    return shutil.which('claude') is not None


def claude_auth() -> str:
    mode = os.environ.get('AUTOFORM_CLAUDE_AUTH', 'login').strip().lower()
    if mode not in ('login', 'api-key'):
        raise LLMError(f'AUTOFORM_CLAUDE_AUTH must be login or api-key, not {mode!r}')
    return mode


def claude_env() -> dict:
    """The environment for a `claude` child process under the chosen authentication."""
    if claude_auth() == 'api-key':
        return dict(os.environ)
    return {k: v for k, v in os.environ.items() if k != 'ANTHROPIC_API_KEY'}


def ask(prompt: str, cwd: Path | str = '.', *, tools: str = TOOLS_NONE, max_turns: int = 1,
        timeout: int = 1800, model: str | None = None, cache: bool = True) -> tuple[str, float]:
    """Return (text, cost_usd). Tool-using calls (tools != '') are never cached."""
    key = hashlib.sha256(json.dumps([prompt, tools, max_turns, model]).encode()).hexdigest()
    hit = CACHE / (key + '.json')
    if cache and not tools and hit.is_file():
        data = json.loads(hit.read_text())
        return data['text'], 0.0
    if not available():
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
        os.killpg(proc.pid, signal.SIGKILL)   # the agent may have spawned lean processes
        proc.communicate()
        raise LLMError(f'model call timed out after {timeout}s')
    try:
        data = json.loads(out)
    except ValueError:
        raise LLMError('unparseable CLI output: ' + (out or err)[-500:])
    if data.get('is_error'):
        raise LLMError('model error: ' + str(data.get('result') or [data.get('subtype'), data.get('errors')])[:500])
    text, cost = data.get('result') or '', float(data.get('total_cost_usd') or 0)
    if cache and not tools:
        CACHE.mkdir(parents=True, exist_ok=True)
        hit.write_text(json.dumps({'text': text}))
    return text, cost


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
