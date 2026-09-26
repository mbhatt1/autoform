"""Prove stage, pipeline (resume / degradation), report, and prover-agent hardening.

Stage implementations are replaced by thin local stubs; the Lean-backed tests run with
AUTOFORM_TEST_LEAN=1 and use this checkout as the Lean root.
"""
import json
import os
import subprocess
import sys
import time
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))

from autoform.harness import prover  # noqa: E402
from autoform.nl import pipeline, report as nl_report  # noqa: E402
from autoform.nl import prove as nl_prove  # noqa: E402
from autoform.nl.schema import (CheckResult, EnglishProperty, EnglishSpec, FILES,  # noqa: E402
                                Statement, dump)

FIXTURE = ROOT / 'tests/fixtures/nl/translation-PipelinePython.json'
LEAN = pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_LEAN') != '1', reason='set AUTOFORM_TEST_LEAN=1')
ADD = 'numbers.py:<module>.add'
CALL = 'runFunc Autoform.Generated.PipelinePython.program 1000 "numbers.py:<module>.add" [.int a, .int b]'
BINDERS = [{'name': 'a', 'type': 'Int', 'val': '.int a'}, {'name': 'b', 'type': 'Int', 'val': '.int b'}]
ADD_PROP = f'∀ (a b : Int), match {CALL} with | .val (.int r) => r = a + b | _ => False'


def fixture():
    t = json.loads(FIXTURE.read_text())
    t['lean_root'] = str(ROOT)
    return t


# --- stub stages -------------------------------------------------------------------------

class Stubs:
    def __init__(self, fail=()):
        self.calls, self.fail = [], set(fail)

    def impl(self, name):
        def run(*a, **k):
            self.calls.append(name)
            if name in self.fail:
                raise RuntimeError(f'{name} exploded')
            return getattr(self, name)(*a, **k)
        return run

    def translate(self, source, module, lean_root, out, **kw):
        t = fixture()
        dump(t, Path(out) / FILES['translation'])
        return t

    def describe(self, translation, out, functions=None, **kw):
        return [EnglishSpec(ADD, 'Adds two numbers.', [
            EnglishProperty('p1', 'add returns the sum of its arguments.', 'postcondition', ['docstring']),
            EnglishProperty('p2', 'add returns its first argument.', 'postcondition', ['implementation']),
            EnglishProperty('p3', 'add is never negative.', 'postcondition', ['tests/test_numbers.py:3']),
            EnglishProperty('p4', 'add is below 100.', 'postcondition', ['docstring'])])]

    def formalize(self, translation, english, out, **kw):
        mk = lambda p, post: Statement(f'add__{p}', ADD, p, f'english {p}', ADD_PROP, list(BINDERS), 'true',  # noqa
                                       post, elaborates=True)
        return [mk('p1', 'r == a + b'), mk('p2', 'r == a'), mk('p3', 'r >= 0'), mk('p4', 'r < 100')]

    def check(self, translation, statements, out, domain_size=64, runtime=True):
        ce = lambda m, rt: {'inputs': {'a': -1, 'b': 0}, 'model': m, 'runtime': rt}  # noqa
        return [CheckResult('add__p1', 'BOUNDED_HOLDS', 64, runtime_agrees=True, kernel_bounded_proof=True),
                CheckResult('add__p2', 'REFUTED_MODEL', 64, counterexample=ce('.val (.int 1)', '1')),
                CheckResult('add__p3', 'REFUTED_MODEL', 64, counterexample=ce('.val (.int -1)', '-1')),
                CheckResult('add__p4', 'REFUTED_RUNTIME', 64, counterexample=ce('.val (.int 5)', '100'))]

    def prove(self, translation, statements, checks, out, budget_usd=None, **kw):
        from autoform.nl.schema import ProofResult
        return [ProofResult(s['id'], 'PROVED' if s['id'] == 'add__p1' else 'SKIPPED', cost_usd=0.5,
                            certificate='x.lean' if s['id'] == 'add__p1' else None) for s in statements]


def _src(tmp_path):
    src = tmp_path / 'src'
    src.mkdir(exist_ok=True)
    (src / 'numbers.py').write_text('def add(a, b):\n    return a + b\n')
    return src


def test_pipeline_runs_every_stage_and_resumes(tmp_path, monkeypatch):
    stubs = Stubs()
    monkeypatch.setattr(pipeline, '_impl', stubs.impl)
    src, out = _src(tmp_path), tmp_path / 'run'
    res = pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT, deep=True)
    assert stubs.calls == list(pipeline.DEEP_STAGES)
    run = json.loads((out / 'run.json').read_text())
    assert run['mode'] == 'deep' and all(run['stages'][s]['status'] == 'ok' for s in pipeline.DEEP_STAGES)
    assert run['stages']['prove']['cost_usd'] == 2.0 and run['cost_usd'] == 2.0
    assert res['totals']['proved'] == 1 and res['potential_bugs'] == 1
    for k, f in FILES.items():
        if k not in ('models', 'deep_translation', 'refine'):
            assert (out / f).is_file(), f
    # Unchanged inputs: nothing reruns.
    stubs.calls.clear()
    pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT, deep=True)
    assert stubs.calls == []
    assert json.loads((out / 'run.json').read_text())['stages']['check']['status'] == 'resumed'
    # A changed option reruns only the stages whose inputs changed.
    pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT, runtime=False, deep=True)
    assert stubs.calls == ['check']
    stubs.calls.clear()
    pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT, runtime=False, functions=['add'], deep=True)
    assert stubs.calls == ['describe']        # same English out -> formalize and later resume
    stubs.calls.clear()
    # A changed source file reruns the translation.
    time.sleep(0.01)
    (src / 'numbers.py').write_text('def add(a, b):\n    return b + a\n')
    pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT, runtime=False, functions=['add'], deep=True)
    assert stubs.calls == ['translate']
    stubs.calls.clear()
    pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT, runtime=False, functions=['add'],
                 resume=False, deep=True)
    assert stubs.calls == list(pipeline.DEEP_STAGES)


def test_pipeline_degrades_gracefully(tmp_path, monkeypatch):
    stubs = Stubs(fail={'describe'})
    monkeypatch.setattr(pipeline, '_impl', stubs.impl)
    out, src = tmp_path / 'run', _src(tmp_path)
    res = pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT, deep=True)
    st = res['run']['stages']
    assert st['translate']['status'] == 'ok' and st['describe']['status'] == 'failed'
    assert 'describe exploded' in st['describe']['error'] and 'Traceback' in st['describe']['traceback']
    assert [st[s]['status'] for s in ('formalize', 'check', 'prove')] == ['blocked'] * 3
    assert st['report']['status'] == 'ok'
    rep = json.loads((out / 'report.json').read_text())
    assert rep['totals']['functions_translated'] == 3 and rep['totals']['statements'] == 0
    assert 'describe' in (out / 'report.md').read_text()
    # The failed stage reruns next time (and its successors run on its output).
    stubs.fail.clear()
    stubs.calls.clear()
    pipeline.run(src, module='PipelinePython', out=out, lean_root=ROOT, deep=True)
    assert stubs.calls == ['describe', 'formalize', 'check', 'prove']


def test_pipeline_check_failure_still_reports_statements_and_no_prove(tmp_path, monkeypatch):
    stubs = Stubs(fail={'check'})
    monkeypatch.setattr(pipeline, '_impl', stubs.impl)
    res = pipeline.run(_src(tmp_path), module='PipelinePython', out=tmp_path / 'run', lean_root=ROOT, prove=False,
                       deep=True)
    st = res['run']['stages']
    assert st['check']['status'] == 'failed' and st['prove']['status'] == 'disabled'
    assert 'prove' not in stubs.calls
    assert res['totals']['statements'] == 4 and res['totals']['bounded_holds'] == 0


def test_report_content_findings_first(tmp_path):
    s = Stubs()
    t = fixture()
    english = s.describe(t, tmp_path)
    stmts = s.formalize(t, english, tmp_path)
    checks = s.check(t, stmts, tmp_path)
    proofs = s.prove(t, [x.__dict__ for x in stmts], checks, tmp_path)
    t['functions'][1]['hole_free'] = False
    rep = nl_report.report(tmp_path, translation=t, english=english, statements=stmts, checks=checks,
                           proofs=proofs)
    tot = rep['totals']
    assert (tot['functions_translated'], tot['functions_eligible']) == (3, 2)
    assert tot['functions_skipped'] == {'untranslated constructs (holes)': 1}
    assert (tot['statements_elaborated'], tot['bounded_holds'], tot['refuted_by_model'],
            tot['refuted_by_runtime'], tot['proved']) == (4, 1, 2, 1, 1)
    bugs = rep['findings']['potential_bugs']
    assert [b['id'] for b in bugs] == ['add__p3'] and bugs[0]['counterexample']['runtime'] == '-1'
    assert [b['id'] for b in rep['findings']['refuted_implementation_only']] == ['add__p2']
    # REFUTED_RUNTIME only: the model and the real code disagree -> a model defect, not a bug.
    assert [b['id'] for b in rep['findings']['model_defects']] == ['add__p4'] and tot['model_defects'] == 1
    first = rep['functions'][0]
    assert first['level'] == 'deep' and {p['trust'] for p in first['properties']} == {'deep'}
    add = rep['functions'][0]
    assert add['summary'] == 'Adds two numbers.' and add['properties'][0]['proof']['status'] == 'PROVED'
    assert add['properties'][0]['lean'] == ADD_PROP
    md = (tmp_path / 'report.md').read_text()
    assert 'untrusted' in rep['trust'] and 'Lean kernel' in rep['trust'] and 'translated program' in rep['trust']
    assert md.index('Potential bugs') < md.index('Model defects') < md.index('## Functions')
    assert 'CPython: `-1`' in md and 'certificate `x.lean`' in md
    assert json.loads((tmp_path / 'report.json').read_text())['totals'] == tot


# --- prover hardening ---------------------------------------------------------------------

class Scripted:
    name = 'scripted'

    def __init__(self, reply, cost=0.0, action=None):
        self.reply, self.cost, self.action, self.calls = reply, cost, action, 0

    def run(self, prompt, cwd):
        self.calls += 1
        if self.action:
            self.action(Path(cwd))
        return self.reply, self.cost


class Refuse:
    name = 'refuse'

    def run(self, prompt, cwd):
        raise AssertionError('agent must not be called')


def _fake_lean(monkeypatch):
    """Kernel stand-in: a file checks iff its proof says GOOD."""
    def check(root, path, name, timeout=0):
        ok = 'GOOD' in path.read_text()
        return ok, (['propext'] if ok else []), '' if ok else 'error: nope'
    monkeypatch.setattr(prover, 'lean_check', check)


def _job(name='t', statement=None):
    return prover.Job(name=name, prefix='import Autoform.Lang.Core.Semantics\n',
                      statement=statement or f'theorem {name} (a b : Nat) : a + b = b + a')


def _git_root(tmp_path):
    root = tmp_path / 'lean'
    root.mkdir()
    for f, text in [('lean-toolchain', 'leanprover/lean4:v0\n'), ('Lib.lean', 'def x := 1\n'),
                    ('Other.lean', 'def y := 2\n'), ('Dirty.lean', 'def z := 3\n')]:
        (root / f).write_text(text)
    git = lambda *a: subprocess.run(['git', '-c', 'user.email=t@t', '-c', 'user.name=t', *a], cwd=root,  # noqa
                                    check=True, capture_output=True)
    git('init', '-q')
    git('add', '.')
    git('commit', '-qm', 'init')
    (root / 'Dirty.lean').write_text('def z := 4 -- work in progress\n')
    return root


def test_prover_restores_tracked_files_the_agent_modified(tmp_path, monkeypatch):
    _fake_lean(monkeypatch)
    root = _git_root(tmp_path)

    def vandal(cwd):
        (root / 'Lib.lean').write_text('axiom cheat : False\n')
        (root / 'Other.lean').unlink()
        (root / 'Dirty.lean').write_text('oops\n')
        (root / 'New.lean').write_text('x\n')
    r = prover.prove(_job(), root, tmp_path / 'w', agent=Scripted('<proof>by GOOD</proof>', action=vandal),
                     attempts=1)
    assert r.status == 'FAILED' and 'restored' in r.reason
    assert r.restored == ['Dirty.lean', 'Lib.lean', 'Other.lean'] and r.untracked == ['New.lean']
    assert (root / 'Lib.lean').read_text() == 'def x := 1\n' and (root / 'Other.lean').is_file()
    assert (root / 'Dirty.lean').read_text() == 'def z := 4 -- work in progress\n'   # pre-existing edit kept
    tr = json.loads(Path(r.transcripts[0]).read_text())
    assert tr['reply'] == '<proof>by GOOD</proof>' and tr['restored'] == r.restored


def test_split_decl_handles_assignments_inside_statements():
    chunk = ('theorem t (h : ∀ s : S, s = { x := 1 }) (f : Nat → Nat := fun n => n) :\n'
             '    let y := 2; have k : y = 2 := rfl; y = 2 -- a := in a comment\n'
             '    ∧ "a := b" = "a := b" := by\n  sorry\n')
    stmt, proof = prover.split_decl(chunk)
    assert stmt.rstrip().endswith('"a := b" = "a := b"') and proof.strip() == 'by\n  sorry'
    assert prover.split_decl('theorem u : True') is None


def test_jobs_from_file_with_assignment_in_statement(tmp_path):
    f = tmp_path / 'x.lean'
    f.write_text('import Std\ntheorem a : let n := 1; n = 1 := by\n  sorry\n\n'
                 'theorem b (s : Nat := 3) : s = s := rfl\n')
    [job] = prover.jobs_from_file(f)
    assert job.name == 'a' and job.statement.rstrip().endswith('n = 1')


def test_forbidden_screen_ignores_comments_and_strings():
    assert prover.forbidden('by\n  -- no sorry needed here\n  /- nor native_decide /- nested -/ -/\n  simp') is None
    assert prover.forbidden('by\n  have : "sorry" ≠ "" := by decide\n  simp') is None
    assert prover.forbidden('by\n  sorry') == 'sorry'
    assert prover.forbidden('by\n  exact h.sorry_free') is None
    for bad in ('by native_decide', '#eval 1', 'set_option debug.skipKernelTC true in\nby rfl',
                'run_tac pure ()', '@[extern "f"] def g := 1', 'unsafe def g := 1'):
        assert prover.forbidden(bad), bad


def test_comment_mentioning_sorry_is_accepted(tmp_path, monkeypatch):
    _fake_lean(monkeypatch)
    r = prover.prove(_job(), tmp_path, tmp_path / 'w', attempts=1,
                     agent=Scripted('<proof>by\n  -- no sorry: GOOD\n  omega</proof>'))
    assert r.status == 'PROVED'


def test_cache_hit_is_rechecked_not_trusted(tmp_path, monkeypatch):
    _fake_lean(monkeypatch)
    cache = tmp_path / 'cache'
    first = prover.prove(_job(), tmp_path, tmp_path / 'a', agent=Scripted('<proof>by GOOD</proof>'), cache_dir=cache)
    assert first.status == 'PROVED' and not first.cached and len(list(cache.iterdir())) == 1
    hit = prover.prove(_job(), tmp_path, tmp_path / 'b', agent=Refuse(), cache_dir=cache)
    assert hit.status == 'PROVED' and hit.cached and hit.cost_usd == 0
    # A different statement is a different key.
    other = prover.prove(_job(statement='theorem t : 1 = 1'), tmp_path, tmp_path / 'c', attempts=1,
                         agent=Scripted('<proof>FAILED</proof>'), cache_dir=cache)
    assert other.status == 'FAILED'
    # A cached proof that no longer checks falls through to the agent.
    [entry] = [e for e in cache.iterdir()]
    entry.write_text(json.dumps({'proof': 'by bad', 'helpers': ''}))
    agent = Scripted('<proof>by GOOD again</proof>')
    again = prover.prove(_job(), tmp_path, tmp_path / 'd', agent=agent, cache_dir=cache)
    assert again.status == 'PROVED' and not again.cached and agent.calls == 1


def test_budget_stops_agent_runs(tmp_path, monkeypatch):
    _fake_lean(monkeypatch)
    agent = Scripted('<proof>FAILED</proof>', cost=1.0)
    jobs = [_job(n) for n in ('a', 'b', 'c')]
    res = prover.prove_many(jobs, tmp_path, tmp_path / 'w', parallel=1, budget_usd=1.5, agent=agent, attempts=1)
    assert [r.status for r in res] == ['FAILED', 'FAILED', 'BUDGET'] and agent.calls == 2
    assert 'budget' in res[2].reason


def test_timeout_kills_the_process_group(tmp_path):
    pidf = tmp_path / 'pid'
    t0 = time.time()
    with pytest.raises(subprocess.TimeoutExpired):
        prover.run_group(['sh', '-c', f'sleep 60 & echo $! > {pidf}; wait'], tmp_path, timeout=1)
    assert time.time() - t0 < 20
    pid = int(pidf.read_text())
    time.sleep(0.2)
    with pytest.raises(ProcessLookupError):
        os.kill(pid, 0)


def test_agent_timeout_is_reported(tmp_path, monkeypatch):
    _fake_lean(monkeypatch)

    class Slow:
        name = 'slow'

        def run(self, prompt, cwd):
            raise subprocess.TimeoutExpired('claude', 1)
    r = prover.prove(_job(), tmp_path, tmp_path / 'w', agent=Slow(), attempts=1)
    assert r.status == 'TIMEOUT'


def test_check_sh_confines_the_agent(tmp_path):
    work = tmp_path / 'job'
    work.mkdir()
    sh = prover.write_check_sh(work.resolve(), tmp_path)
    outside = tmp_path / 'outside.lean'
    outside.write_text('theorem x : True := trivial\n')
    evil = work / 'evil.lean'
    evil.write_text('#eval IO.Process.run {cmd := "rm"}\n')
    for arg in (str(outside), '../outside.lean', 'evil.lean', 'missing.lean'):
        p = subprocess.run(['./check.sh', arg], cwd=work, capture_output=True, text=True)
        assert p.returncode == 2, (arg, p.stdout, p.stderr)
    assert 'Bash(./check.sh:*)' == prover.ALLOWED_TOOLS.split(',')[0] and 'lake' not in prover.ALLOWED_TOOLS
    assert sh.stat().st_mode & 0o100


# --- nl prove stage ------------------------------------------------------------------------

def _stmts():
    ok = Statement('add__p1', ADD, 'p1', 'add returns the sum', ADD_PROP, [], 'true', 'r == a + b', elaborates=True)
    bad = Statement('add__p2', ADD, 'p2', 'add returns a', ADD_PROP.replace('a + b', 'a'), [], 'true', 'r == a',
                    elaborates=True)
    noel = Statement('add__p3', ADD, 'p3', 'nonsense', 'garbage', [], 'true', 'true', elaborates=False)
    unchecked = Statement('add__p4', ADD, 'p4', 'x', ADD_PROP, [], 'true', 'true', elaborates=True)
    checks = [CheckResult('add__p1', 'BOUNDED_HOLDS', 64, runtime_agrees=True),
              CheckResult('add__p2', 'REFUTED_MODEL', 64, counterexample={'inputs': {'a': 0, 'b': 1}}),
              CheckResult('add__p3', 'UNCHECKABLE')]
    return [ok, bad, noel, unchecked], checks


def test_nl_prove_selects_bounded_statements(tmp_path, monkeypatch):
    _fake_lean(monkeypatch)
    stmts, checks = _stmts()
    agent = Scripted('<proof>by GOOD</proof>', cost=0.25)
    res = nl_prove.prove(fixture(), stmts, checks, tmp_path, agent=agent, cache_dir=None)
    assert [r.status for r in res] == ['PROVED', 'SKIPPED', 'SKIPPED', 'SKIPPED'] and agent.calls == 1
    assert 'REFUTED_MODEL' in res[1].reason and 'elaborate' in res[2].reason and 'no check' in res[3].reason
    saved = json.loads((tmp_path / FILES['proofs']).read_text())
    assert saved[0]['status'] == 'PROVED' and saved[0]['cost_usd'] == 0.25
    job_dir = tmp_path / 'prover' / 'add__p1'
    text = (job_dir / 'add__p1.final.lean').read_text()
    assert 'import Autoform.Generated.PipelinePython' in text and 'af_eval' in text
    assert f'theorem add__p1 : {ADD_PROP} :=' in text
    assert (job_dir / 'check.sh').is_file()
    prompt = json.loads((job_dir / 'add__p1.attempt1.transcript.json').read_text())['prompt']
    assert 'add returns the sum' in prompt and 'return a + b' in prompt and 'BOUNDED_HOLDS' in prompt
    assert nl_prove.theorem_name('numbers.py:<module>.add__p1') == 'numbers_py__module__add__p1'


def test_nl_prove_budget_zero_fails_without_calling_agent(tmp_path, monkeypatch):
    _fake_lean(monkeypatch)
    stmts, checks = _stmts()
    res = nl_prove.prove(fixture(), stmts, checks, tmp_path, agent=Refuse(), budget_usd=0, cache_dir=None)
    assert res[0].status == 'FAILED' and 'budget' in res[0].reason


@LEAN
def test_nl_prove_kernel_checks_scripted_proof(tmp_path):
    stmts, checks = _stmts()
    cache = tmp_path / 'cache'
    reply = '<proof>by\n  -- af_eval computes the call; no sorry needed\n  intro a b\n  af_eval\n  simp</proof>'
    res = nl_prove.prove(fixture(), stmts, checks, tmp_path / 'run', agent=Scripted(reply), cache_dir=cache)
    assert res[0].status == 'PROVED', res[0].reason
    assert set(res[0].axioms) <= prover.ALLOWED_AXIOMS and Path(res[0].certificate).is_file()
    # A wrong proof is rejected by the kernel.
    wrong = nl_prove.prove(fixture(), stmts, checks, tmp_path / 'wrong', agent=Scripted('<proof>by\n  rfl</proof>'),
                           attempts=1, cache_dir=None)
    assert wrong[0].status == 'FAILED' and 'independent check failed' in wrong[0].reason
    # Cache hit: re-checked by the kernel, the agent is not called.
    again = nl_prove.prove(fixture(), stmts, checks, tmp_path / 'again', agent=Refuse(), cache_dir=cache)
    assert again[0].status == 'PROVED' and 'cached' in again[0].reason


@LEAN
def test_prover_statement_with_assignment_is_kernel_checked(tmp_path):
    job = prover.Job(name='t', prefix='import Autoform.Lang.Core.Semantics\n',
                     statement='theorem t : let n : Nat := 2; n + n = 4')
    r = prover.prove(job, ROOT, tmp_path, agent=Scripted('<proof>by\n  -- sorry-free\n  decide</proof>'), attempts=1)
    assert r.status == 'PROVED', r.reason
