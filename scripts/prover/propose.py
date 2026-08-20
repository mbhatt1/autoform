#!/usr/bin/env python3
"""Local neural whole-proof proposer for the Autoform portfolio (STRATEGY.md §5, tier 3).

Reads a pretty-printed Lean 4 goal on stdin, asks a *locally running* model for
candidate tactic scripts, and prints one candidate per line (tactics separated by
`;`). Nothing here is trusted: every candidate is re-elaborated by Lean, must close
the goal, and the resulting term is screened for `sorryAx`, metavariables and
non-standard axioms before it counts. A hallucinated proof simply fails to
elaborate; the worst case is wasted time.

Backends, selected by AUTOFORM_NEURAL_BACKEND:
  "ollama" (default) — a locally running model. No API key, no egress beyond localhost.
  "openai"           — the OpenAI API. Requires OPENAI_API_KEY *in the environment*.

The key is never read from a file and never written to one. Do not add it to the repo:
this project is public, and a committed key is a credential leak, not a configuration
detail.

Disabled unless AUTOFORM_NEURAL=1, because a build should not silently depend on a model
being reachable — and with the openai backend, should not silently spend money or send
source-derived goals to a third party. That second point is the important one: goals
contain fragments of the user's code. Enabling this backend exports them.
"""
import json
import os
import sys
import urllib.error
import urllib.request

if os.environ.get("AUTOFORM_NEURAL") != "1":
    print("# disabled: set AUTOFORM_NEURAL=1 to enable the local proposer")
    sys.exit(0)

goal = (open(sys.argv[1]).read() if len(sys.argv) > 1 else sys.stdin.read()).strip()
backend = os.environ.get("AUTOFORM_NEURAL_BACKEND", "ollama").lower()

PROMPT = """You are proving a theorem in Lean 4 (core + Batteries only; Mathlib and aesop are NOT available).
Goal:
{goal}

Reply with up to 6 candidate tactic scripts, one per line, no commentary, no backticks.
Separate tactics within a line by ';'. Use only core tactics such as: intro, intros, rfl,
simp, simp_all, decide, omega, constructor, exact, apply, cases, rcases-free `cases`,
induction, split, unfold, funext, bv_decide.
"""

def ask_ollama(prompt: str) -> str:
    model = os.environ.get("AUTOFORM_NEURAL_MODEL", "qwen2.5:7b")
    host = os.environ.get("OLLAMA_HOST", "http://127.0.0.1:11434")
    if not host.startswith("http"):
        host = "http://" + host
    req = urllib.request.Request(
        host.rstrip("/") + "/api/generate",
        data=json.dumps({"model": model, "prompt": prompt, "stream": False,
                         "options": {"temperature": 0.6, "num_predict": 400}}).encode(),
        headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=120) as r:
        return json.loads(r.read().decode()).get("response", "")


def ask_openai(prompt: str) -> str:
    key = os.environ.get("OPENAI_API_KEY")
    if not key:
        raise RuntimeError("OPENAI_API_KEY is not set in the environment")
    model = os.environ.get("AUTOFORM_NEURAL_MODEL", "gpt-4o-mini")
    req = urllib.request.Request(
        os.environ.get("OPENAI_BASE", "https://api.openai.com/v1") + "/chat/completions",
        data=json.dumps({"model": model,
                         "messages": [{"role": "user", "content": prompt}],
                         "temperature": 0.6}).encode(),
        headers={"Content-Type": "application/json",
                 "Authorization": "Bearer " + key})
    try:
        with urllib.request.urlopen(req, timeout=120) as r:
            body = json.loads(r.read().decode())
    except urllib.error.HTTPError as e:
        # A bare "HTTP Error 429" is ambiguous: OpenAI returns it both for rate
        # limiting (retry later) and for an exhausted balance (retrying never helps).
        # Surfacing which one it is saves the next person the diagnosis.
        try:
            err = json.loads(e.read().decode()).get("error", {})
            code, msg = err.get("code") or err.get("type"), err.get("message", "")
        except Exception:
            code, msg = None, ""
        if code in ("credit_balance_exhausted", "insufficient_quota"):
            raise RuntimeError("account has no API credits — %s" % msg) from None
        if e.code == 429:
            raise RuntimeError("rate limited (retry later): %s" % msg) from None
        if e.code == 401:
            raise RuntimeError("OPENAI_API_KEY rejected: %s" % msg) from None
        raise RuntimeError("HTTP %s: %s" % (e.code, msg or e.reason)) from None
    return body["choices"][0]["message"]["content"]


try:
    prompt = PROMPT.format(goal=goal)
    text = ask_openai(prompt) if backend == "openai" else ask_ollama(prompt)
except Exception as e:
    # Never fail the build on a proposer outage; the portfolio treats an empty
    # candidate list as "tier 3 produced nothing", which is the honest report.
    print("# unavailable (%s): %s" % (backend, e))
    sys.exit(0)

seen = []
for line in text.splitlines():
    line = line.strip().strip("`").strip()
    if not line or line.startswith("#") or line.startswith("--"):
        continue
    if line.startswith("by "):
        line = line[3:]
    if any(c in line for c in "{}\n") or len(line) > 200:
        continue
    if line not in seen:
        seen.append(line)
print("\n".join(seen[:6]))
