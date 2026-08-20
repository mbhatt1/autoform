#!/usr/bin/env python3
"""Local neural whole-proof proposer for the Autoform portfolio (STRATEGY.md §5, tier 3).

Reads a pretty-printed Lean 4 goal on stdin, asks a *locally running* model for
candidate tactic scripts, and prints one candidate per line (tactics separated by
`;`). Nothing here is trusted: every candidate is re-elaborated by Lean, must close
the goal, and the resulting term is screened for `sorryAx`, metavariables and
non-standard axioms before it counts. A hallucinated proof simply fails to
elaborate; the worst case is wasted time.

Backend: `ollama` on localhost. No API key, no network egress beyond localhost.
Disabled unless AUTOFORM_NEURAL=1, because a build should not silently depend on a
model being installed. Model via AUTOFORM_NEURAL_MODEL (default qwen2.5:7b).
"""
import json
import os
import sys
import urllib.request

if os.environ.get("AUTOFORM_NEURAL") != "1":
    print("# disabled: set AUTOFORM_NEURAL=1 to enable the local proposer")
    sys.exit(0)

goal = (open(sys.argv[1]).read() if len(sys.argv) > 1 else sys.stdin.read()).strip()
model = os.environ.get("AUTOFORM_NEURAL_MODEL", "qwen2.5:7b")
host = os.environ.get("OLLAMA_HOST", "http://127.0.0.1:11434")
if not host.startswith("http"):
    host = "http://" + host

PROMPT = """You are proving a theorem in Lean 4 (core + Batteries only; Mathlib and aesop are NOT available).
Goal:
{goal}

Reply with up to 6 candidate tactic scripts, one per line, no commentary, no backticks.
Separate tactics within a line by ';'. Use only core tactics such as: intro, intros, rfl,
simp, simp_all, decide, omega, constructor, exact, apply, cases, rcases-free `cases`,
induction, split, unfold, funext, bv_decide.
"""

try:
    req = urllib.request.Request(
        host.rstrip("/") + "/api/generate",
        data=json.dumps({"model": model, "prompt": PROMPT.format(goal=goal),
                         "stream": False, "options": {"temperature": 0.6, "num_predict": 400}}).encode(),
        headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=120) as r:
        text = json.loads(r.read().decode()).get("response", "")
except Exception as e:
    print("# unavailable: %s" % e)
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
