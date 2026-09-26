"""An autonomous proving agent in a loop with Lean (Gauss-style), outside the trusted base.

A job is one theorem: the file text up to it (imports, definitions, helper lemmas), its
statement, and a natural-language blueprint. An agent (headless Claude Code) works on a
private copy with a Lean runtime, running `lake env lean` itself until the file checks.
It returns a proof; the agent's report is never trusted.

Acceptance is independent of the agent:
  * the proof is spliced under the ORIGINAL statement, recovered from the job, so an agent
    that edited the statement proves nothing;
  * the file is re-elaborated from scratch;
  * `#print axioms` must list only propext / Classical.choice / Quot.sound
    (no sorryAx, no Lean.ofReduceBool from native_decide, no new axiom).
"""
from __future__ import annotations

import concurrent.futures as futures
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
FORBIDDEN = re.compile(r'\b(sorry|admit|native_decide|axiom|implemented_by|extern)\b')

PROMPT = """You are a Lean 4 proof engineer working autonomously. Prove ONE theorem.

File (already contains the theorem, with `sorry` as its proof): {path}
Theorem: `{name}`
Lean project root (run all Lean commands there): {root}
Check your work with:  cd {root} && lake env lean {path}
(The environment is Lean {toolchain} with this project's library; it may take ~10-60 s.)

Blueprint (what the statement means and why it should hold):
{blueprint}

Rules:
- Replace only the `sorry` of `{name}`. Do not change its statement, its name, or any
  other declaration's statement. You MAY add helper lemmas immediately before it.
- Forbidden anywhere: sorry, admit, native_decide, axiom, implemented_by, extern.
- The kernel must accept it: finish only when `lake env lean {path}` reports no errors
  for `{name}` and `#print axioms {name}` (append it temporarily if useful) lists at most
  propext, Classical.choice, Quot.sound.
- Useful tactics here: `simp [...]`, `decide`, `omega`, `rfl`, `with_unfolding_all rfl`,
  `split`, `cases`, `induction`; the file may define `af_eval`, which head-normalizes
  interpreter applications (`runFunc ...`) by unfolding and iota-reduction.
- Work for as long as needed; try several strategies if one fails.

When done, print the final helper lemmas (if any) and the proof as:
<helpers>
...lean declarations or empty...
</helpers>
<proof>
by
  ...
</proof>
If you cannot prove it, print <proof>FAILED</proof> and a one-paragraph reason in <reason></reason>.
"""


@dataclass
class Job:
    name: str                 # theorem name as written in the file (unqualified)
    prefix: str               # file text before the theorem
    statement: str            # `theorem name ... :` up to `:=` (exclusive)
    blueprint: str = ''
    suffix: str = ''          # text after the theorem (usually empty)

    def file_text(self, proof: str, helpers: str = '') -> str:
        body = self.prefix.rstrip() + '\n\n'
        if helpers.strip():
            body += helpers.strip() + '\n\n'
        return body + self.statement.rstrip() + ' :=\n' + proof.strip() + '\n' + self.suffix


@dataclass
class Result:
    name: str
    status: str               # PROVED | FAILED | REJECTED | TIMEOUT | ERROR
    proof: str = ''
    helpers: str = ''
    reason: str = ''
    axioms: list = field(default_factory=list)
    seconds: float = 0.0
    cost_usd: float = 0.0
    certificate: str | None = None
    certificate_sha256: str | None = None


def lean_check(root: Path, path: Path, name: str, timeout: int = 1800) -> tuple[bool, list, str]:
    """Elaborate `path` and read `#print axioms name`; True iff clean and standard-only."""
    text = path.read_text()
    probe = path.with_suffix('.check.lean')
    probe.write_text(text + f'\n#print axioms {name}\n')
    env = dict(os.environ, PATH=str(Path.home() / '.elan/bin') + os.pathsep + os.environ.get('PATH', ''))
    try:
        proc = subprocess.run(['lake', 'env', 'lean', str(probe)], cwd=root, env=env, capture_output=True,
                              text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return False, [], 'lean timeout'
    out = proc.stdout + proc.stderr
    m = re.search(rf"'[^']*{re.escape(name)}' depends on axioms: \[([^\]]*)\]", out)
    axioms = [a.strip() for a in m.group(1).split(',')] if m else []
    if re.search(rf"'[^']*{re.escape(name)}' does not depend on any axioms", out):
        axioms, m = [], True
    errors = [l for l in out.splitlines() if ': error' in l]
    ok = proc.returncode == 0 and not errors and bool(m) and set(axioms) <= ALLOWED_AXIOMS
    return ok, axioms, '\n'.join(errors[:20]) or out[-2000:]


def _extract(tag: str, text: str) -> str | None:
    found = re.findall(rf'<{tag}>\s*(.*?)\s*</{tag}>', text, re.S)
    return found[-1] if found else None


class ClaudeCodeAgent:
    """Headless Claude Code with Lean access, confined to a scratch directory."""
    name = 'claude-code'

    def __init__(self, model: str | None = None, max_turns: int = 60, timeout: int = 3600):
        self.model, self.max_turns, self.timeout = model, max_turns, timeout
        if not shutil.which('claude'):
            raise RuntimeError('claude CLI not found on PATH')

    def run(self, prompt: str, cwd: Path) -> tuple[str, float]:
        cmd = ['claude', '-p', prompt, '--output-format', 'json', '--max-turns', str(self.max_turns),
               '--allowedTools', 'Bash(lake env lean:*),Bash(cd:*),Read,Edit,Write,Grep,Glob',
               '--permission-mode', 'acceptEdits']
        if self.model:
            cmd += ['--model', self.model]
        env = {k: v for k, v in os.environ.items() if k != 'ANTHROPIC_API_KEY'}  # use the logged-in plan
        proc = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, timeout=self.timeout)
        try:
            data = json.loads(proc.stdout)
            return data.get('result') or '', float(data.get('total_cost_usd') or 0)
        except ValueError:
            return proc.stdout + proc.stderr, 0.0


def prove(job: Job, root: Path, workdir: Path, agent=None, attempts: int = 2) -> Result:
    root, workdir = Path(root).resolve(), Path(workdir).resolve()
    workdir.mkdir(parents=True, exist_ok=True)
    agent = agent or ClaudeCodeAgent()
    toolchain = (root / 'lean-toolchain').read_text().strip() if (root / 'lean-toolchain').exists() else '?'
    started, cost, reason = time.time(), 0.0, ''
    for attempt in range(1, attempts + 1):
        scratch = workdir / f'{job.name}.attempt{attempt}.lean'
        scratch.write_text(job.file_text('by\n  sorry'))
        prompt = PROMPT.format(path=scratch, name=job.name, root=root, toolchain=toolchain,
                               blueprint=job.blueprint or '(none supplied)')
        if reason:
            prompt += f'\n\nA previous attempt failed independent checking:\n{reason[:3000]}\n'
        try:
            reply, c = agent.run(prompt, workdir)
        except subprocess.TimeoutExpired:
            reason = 'agent timed out'
            continue
        cost += c
        proof = _extract('proof', reply)
        helpers = _extract('helpers', reply) or ''
        if not proof or proof.strip() == 'FAILED':
            reason = _extract('reason', reply) or 'agent reported failure'
            continue
        if FORBIDDEN.search(proof) or FORBIDDEN.search(helpers):
            reason = 'proof or helpers contain a forbidden construct'
            continue
        # Independent acceptance: original statement, fresh file, kernel + axiom check.
        final = workdir / f'{job.name}.final.lean'
        final.write_text(job.file_text(proof, helpers))
        ok, axioms, detail = lean_check(root, final, job.name)
        if ok:
            return Result(job.name, 'PROVED', proof, helpers, axioms=axioms, seconds=round(time.time() - started, 1),
                          cost_usd=round(cost, 4), certificate=str(final),
                          certificate_sha256=hashlib.sha256(final.read_bytes()).hexdigest())
        reason = 'independent check failed:\n' + detail
    return Result(job.name, 'FAILED', reason=reason, seconds=round(time.time() - started, 1), cost_usd=round(cost, 4))


def prove_many(jobs: list, root: Path, workdir: Path, parallel: int = 3, **kw) -> list:
    """Bounded concurrency: every agent runs its own Lean processes (a few GB each)."""
    with futures.ThreadPoolExecutor(max_workers=parallel) as pool:
        return list(pool.map(lambda j: prove(j, root, Path(workdir) / j.name, **kw), jobs))


# --- turning `sorry`s in a Lean file into jobs ------------------------------------------

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma)\s+(\S+)', re.M)


def jobs_from_file(path: Path, names: list | None = None) -> list:
    """Every theorem in `path` whose proof is `sorry` (or named explicitly), as a job whose
    prefix is the file up to that theorem. Helper lemmas added by one agent stay private
    to its job."""
    text = Path(path).read_text()
    starts = [(m.start(), m.group(2)) for m in DECL.finditer(text)]
    jobs = []
    for i, (start, name) in enumerate(starts):
        end = starts[i + 1][0] if i + 1 < len(starts) else len(text)
        chunk = text[start:end]
        if ':=' not in chunk:
            continue
        stmt, proof = chunk.split(':=', 1)
        wanted = (names and name in names) or (not names and re.fullmatch(r'\s*(by\s+)?sorry\s*', proof.split('\n\n')[0]))
        if not wanted:
            continue
        doc = re.findall(r'/--(.*?)-/\s*$', text[:start], re.S)
        jobs.append(Job(name=name, prefix=text[:start], statement=stmt, blueprint=(doc[-1].strip() if doc else '')))
    return jobs
