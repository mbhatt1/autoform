"""Split specification modules (roadmap 3.1) and the AST-digest cache (3.2).

One Lean process retains every by-computation proof term it elaborates, so
`scripts/synth_specs.py` now measures each theorem in its budget probe and, when the
predicted single-process peak exceeds `--split-gb`, emits `<M>/Base.lean` +
`<M>/PartN.lean` + an umbrella. These tests pin the plan, the emitted shape (the CI
invariants: every theorem gated in its own part, the obligations declared once), the
helpers other gates use to see all files of a split module, and the cache's semantics
(a cached "proved" is only a hint; a cached refutation is a verdict)."""
import os
import shutil
import subprocess
from pathlib import Path

import pytest

from conftest import ROOT, SCRIPTS, load


def cand(synth, cid, cost_kb=None, fuel_mono=True):
    case = '{ case := { heap := [], self := none, args := [.int 1] }, expected := .val (.int 1) }'
    c = synth.Cand(cid, 'conform', 'native test', 'subj_' + cid, 'f_' + cid,
                   'lawConform C FUEL f_' + cid, [case], dom_kind='obs')
    c.extra.update(fuel_mono=fuel_mono, proof_fuel=4)
    if cost_kb is not None:
        c.extra['probe_peak_kb'] = cost_kb
    return c


@pytest.fixture
def synth(monkeypatch):
    monkeypatch.setenv('AUTOFORM_NO_REEXEC', '1')
    return load(str(Path(SCRIPTS) / 'synth_specs.py'), 'af_split_specs')


GB = 1048576


def test_plan_keeps_one_file_under_the_threshold(synth):
    cands = [cand(synth, 'a', 1 * GB + 500000), cand(synth, 'b', 1 * GB + 400000)]
    assert synth.plan_parts(cands, 1 * GB, 4 * GB) is None


def test_plan_packs_next_fit_under_the_threshold(synth):
    base = 1 * GB
    costs = [1.5, 1.5, 1.5, 0.5, 2.5, 0.5]        # GB above base, in emission order
    cands = [cand(synth, 'c%d' % i, int(base + k * GB)) for i, k in enumerate(costs)]
    plan = synth.plan_parts(cands, base, 4 * GB)
    assert plan is not None and plan['oversize'] == []
    assert [p['ids'] for p in plan['parts']] == [['c0', 'c1'], ['c2', 'c3'], ['c4', 'c5']]
    for p in plan['parts']:
        assert p['predicted_kb'] <= 4 * GB
    assert plan['parts'][0]['predicted_kb'] == base + 3 * GB
    assert plan['total_kb'] == int(base + sum(costs) * GB)


def test_plan_names_a_theorem_no_split_can_bound(synth):
    cands = [cand(synth, 'small', 2 * GB), cand(synth, 'huge', 9 * GB), cand(synth, 'tail', 2 * GB)]
    plan = synth.plan_parts(cands, 1 * GB, 4 * GB)
    assert plan['oversize'] == ['huge']
    assert ['huge'] in [p['ids'] for p in plan['parts']]


def test_plan_refuses_without_a_measurement(synth, capsys):
    cands = [cand(synth, 'measured', 5 * GB), cand(synth, 'unmeasured')]
    assert synth.plan_parts(cands, 1 * GB, 4 * GB) is None
    assert 'no memory measurement' in capsys.readouterr().out


def test_split_emission_partitions_the_theorems_and_gates_each_part(synth):
    cands = [cand(synth, 'c%d' % i, 3 * GB) for i in range(5)]
    cands[2].extra['fuel_mono'] = False           # leaves an open obligation
    plan = synth.plan_parts(cands, 1 * GB, 4 * GB)
    assert len(plan['parts']) == 5
    files, thms, obs = synth.emit_split(cands, 'Mod', [], plan)
    whole, whole_thms, whole_obs = synth.emit(cands, 'Mod', [])
    assert [t for t, _ in thms] == [t for t, _ in whole_thms] == ['c%d' % i for i in range(5)]
    assert obs == whole_obs and len(obs) == 1
    assert set(files) == {'Mod.lean', 'Mod/Base.lean'} | {'Mod/Part%d.lean' % n for n in range(1, 6)}
    base = files['Mod/Base.lean']
    assert 'namespace Autoform.SpecsGen.Mod' in base and '\ntheorem ' not in base
    assert all('def dom_c%d ' % i in base for i in range(5))
    for n in range(1, 6):
        part = files['Mod/Part%d.lean' % n]
        assert 'import Autoform.SpecsGen.Mod.Base' in part
        assert 'namespace Autoform.SpecsGen.Mod\n' in part
        assert part.count('\ntheorem ') == 1 and 'def dom_' not in part
        # the CI anti-vacuity invariant, per part: theorems == #audit_depends lines
        theorems = [l.split()[1] for l in part.splitlines() if l.startswith('theorem ')]
        gated = [l.split()[1] for l in part.splitlines() if l.startswith('#audit_depends ')]
        assert theorems == gated == ['c%d' % (n - 1)]
        assert '#audit_axioms c%d' % (n - 1) in part
        assert 'def obligations' not in part
    umbrella = files['Mod.lean']
    assert umbrella.startswith('import Autoform.SpecsGen.Mod.Base\nimport Autoform.SpecsGen.Mod.Part1\n')
    assert 'def obligations : List OpenObligation :=' in umbrella
    assert 'ob_c2' in umbrella and '\ntheorem ' not in umbrella
    assert 'split into' not in whole and '#audit_depends c4 on f_c4' in whole


def test_write_split_removes_stale_parts_and_unsplit_removes_the_directory(synth, tmp_path):
    files = {'Mod.lean': 'umbrella', 'Mod/Base.lean': 'base', 'Mod/Part1.lean': 'p1'}
    (tmp_path / 'Mod').mkdir()
    (tmp_path / 'Mod' / 'Part7.lean').write_text('stale')
    (tmp_path / 'Mod' / 'notes.txt').write_text('kept')
    synth.write_split(files, 'Mod', str(tmp_path))
    assert sorted(p.name for p in (tmp_path / 'Mod').iterdir()) == ['Base.lean', 'Part1.lean', 'notes.txt']
    synth.unsplit('Mod', str(tmp_path))
    assert sorted(p.name for p in (tmp_path / 'Mod').iterdir()) == ['notes.txt']
    assert (tmp_path / 'Mod.lean').read_text() == 'umbrella'


def test_spec_files_follow_the_umbrella_imports(tmp_path):
    gm = load(str(Path(SCRIPTS) / 'generated_module.py'), 'af_generated_module_split')
    spec_dir = tmp_path / 'Autoform' / 'SpecsGen'
    (spec_dir / 'Mod').mkdir(parents=True)
    umbrella = spec_dir / 'Mod.lean'
    umbrella.write_text('import Autoform.SpecsGen.Mod.Base\nimport Autoform.SpecsGen.Mod.Part1\n'
                        'import Autoform.SpecsGen.Mod.Part2\n\nnamespace X\nend X\n')
    for name in ('Base', 'Part1', 'Part2', 'Part3'):
        (spec_dir / 'Mod' / (name + '.lean')).write_text('-- ' + name)
    files = gm.spec_files(umbrella)
    assert [p.name for p in files] == ['Mod.lean', 'Base.lean', 'Part1.lean', 'Part2.lean']
    assert gm.is_split_spec(umbrella)
    before = gm.spec_digest(umbrella)
    (spec_dir / 'Mod' / 'Part2.lean').write_text('-- changed')
    assert gm.spec_digest(umbrella) != before
    plain = spec_dir / 'Plain.lean'
    plain.write_text('theorem t : True := trivial\n')
    assert gm.spec_files(plain) == [plain] and not gm.is_split_spec(plain)
    import hashlib
    assert gm.spec_digest(plain) == hashlib.sha256(plain.read_bytes()).hexdigest()


def test_error_attribution_reads_lean_and_lake_formats(synth):
    path = os.path.join(synth.REPO, 'Autoform', 'SpecsGen', 'Mod', 'Part3.lean')
    lean_style = path + ':92:4: error: unsolved goals\n' + path + ':7:0: warning: unused\n'
    lake_style = ('✖ [61/61] Building Autoform.SpecsGen.Mod.Part3 (964ms)\n'
                  'error: Autoform/SpecsGen/Mod/Part3.lean:8:2: Tactic `rfl` failed\n'
                  'error: Autoform/SpecsGen/Mod/Part4.lean:9:2: elsewhere\n'
                  'error: Lean exited with code 1\n')
    assert synth._errors_in(lean_style, path) == [7, 92]
    assert synth._errors_in(lake_style, path) == [8]


def test_cache_store_round_trip_and_disable(tmp_path, monkeypatch):
    monkeypatch.setenv('AUTOFORM_CACHE_DIR', str(tmp_path / 'cache'))
    monkeypatch.delenv('AUTOFORM_NO_CACHE', raising=False)
    wc = load(str(Path(SCRIPTS) / 'work_cache.py'), 'af_work_cache_test')
    store = wc.Store('synth', wc.environment_key(model='m', lean='l'))
    digest = wc.function_digest({'name': 'f', 'body': {'k': 'skip'}})
    assert store.get(digest, 'k1') is None
    store.put(digest, 'k1', {'status': 'refuted'})
    store.put_many(digest, {'k2': {'status': 'proved'}, 'k3': {'status': 'unproved'}})
    assert store.get(digest, 'k1') == {'status': 'refuted'}
    assert sorted(store.load(digest)) == ['k1', 'k2', 'k3']
    assert store.path(digest).parent.name == digest and (tmp_path / 'cache' / digest).is_dir()
    other = wc.Store('synth', wc.environment_key(model='m2', lean='l'))
    assert other.get(digest, 'k1') is None            # a different environment is a miss
    assert 'hit' in store.summary()
    monkeypatch.setenv('AUTOFORM_NO_CACHE', '1')
    off = wc.Store('synth', 'x')
    assert not off.enabled and off.get(digest, 'k1') is None
    off.put(digest, 'k1', {'status': 'refuted'})
    assert 'disabled' in off.summary()


def test_replayed_proof_is_a_hint_but_a_replayed_refutation_is_a_verdict(synth, tmp_path, monkeypatch):
    monkeypatch.setenv('AUTOFORM_CACHE_DIR', str(tmp_path / 'cache'))
    monkeypatch.delenv('AUTOFORM_NO_CACHE', raising=False)
    wc = synth.work_cache
    store = wc.Store('synth', 'env')
    fn = {'conform_a': {'name': 'conform_a'}, 'conform_b': {'name': 'conform_b'}}
    digests = {'subj_a': wc.function_digest(fn['conform_a']), 'subj_b': wc.function_digest(fn['conform_b'])}
    a, b = cand(synth, 'a', 3 * GB), cand(synth, 'b', 3 * GB)
    a.status, a.proved = 'proved', True
    b.status, b.reason, b.checked = 'refuted', 'counterexample in the fuzzed domain', {'holds': False}
    for c in (a, b):
        store.put(digests[c.subject], synth.cand_key(c), synth.cand_record(c))
    a2, b2 = cand(synth, 'a'), cand(synth, 'b')
    assert synth.replay_candidate(a2, store, digests) and synth.replay_candidate(b2, store, digests)
    assert a2.status == 'candidate' and not a2.proved and a2.extra['probe_peak_kb'] == 3 * GB
    assert b2.status == 'refuted' and b2.checked == {'holds': False}
    changed = cand(synth, 'a')
    changed.dom = ['{ case := { heap := [], self := none, args := [.int 2] }, expected := .val (.int 1) }']
    assert not synth.replay_candidate(changed, store, digests)      # a new statement is a miss
    assert not synth.replay_candidate(cand(synth, 'a'), store, {})  # no subject digest: a miss


def test_split_base_elaborates(synth, tmp_path):
    env = dict(os.environ, PATH=str(Path.home() / '.elan/bin') + os.pathsep + os.environ['PATH'])
    if not shutil.which('lake', path=env['PATH']):
        if os.environ.get('AUTOFORM_REQUIRE_LEAN'):
            pytest.fail('Lean is required')
        pytest.skip('Lean is not installed')
    cands = [cand(synth, 'c%d' % i, 3 * GB) for i in range(2)]
    plan = synth.plan_parts(cands, 1 * GB, 4 * GB)
    files, _, _ = synth.emit_split(cands, 'SplitTest', [], plan)
    program = '''namespace Autoform.Generated.SplitTest
open Autoform.Core
def f_c0 : Func := { name := "subj_c0", params := ["a"], body := .ret (.name "a") }
def f_c1 : Func := { name := "subj_c1", params := ["a"], body := .ret (.name "a") }
def program : Program := { dialect := .python, funcs := [f_c0, f_c1] }
end Autoform.Generated.SplitTest
'''
    base = files['SplitTest/Base.lean'].replace('import Autoform.Generated.SplitTest\n', program)
    path = tmp_path / 'Base.lean'
    path.write_text(base)
    build = subprocess.run(['lake', 'build', 'Autoform.SpecsGen.Basis', 'Autoform.Harness.Audit'],
                           cwd=ROOT, env=env, text=True, capture_output=True, timeout=300)
    assert build.returncode == 0, build.stdout + build.stderr
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT, env=env,
                            text=True, capture_output=True, timeout=180)
    assert result.returncode == 0, result.stdout + result.stderr
