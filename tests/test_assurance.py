"""Assurance consumes scoped proof evidence and preserves missing checks."""
import json
import hashlib
import os
from pathlib import Path
import sys
import time

import pytest

from conftest import SCRIPTS, load


@pytest.mark.parametrize('parent_waits,ignore_interrupt', [(True, False), (False, False), (True, True)])
def test_stage_deadline_releases_descendant_resources(tmp_path, parent_waits, ignore_interrupt):
    import fcntl
    import signal

    assure = load(str(Path(SCRIPTS) / 'assure.py'), 'af_bounded_assurance')
    lock = tmp_path / 'worker.lock'
    ready = tmp_path / 'worker.pid'
    child = ('import fcntl,os,pathlib,sys,time\n'
             'stream=open(sys.argv[1], "w")\n'
             'fcntl.flock(stream, fcntl.LOCK_EX)\n'
             'pathlib.Path(sys.argv[2]).write_text(str(os.getpid()))\n'
             'time.sleep(60)\n')
    worker = tmp_path / 'worker.py'
    worker.write_text('import pathlib,signal,subprocess,sys,time\n'
                     + ('signal.signal(signal.SIGINT, signal.SIG_IGN)\n' if ignore_interrupt else '')
                     +
                     f'child=subprocess.Popen([sys.executable,"-c",{child!r},{str(lock)!r},{str(ready)!r}])\n'
                     f'while not pathlib.Path({str(ready)!r}).exists(): time.sleep(0.01)\n'
                     'print("worker ready", flush=True)\n'
                     + ('time.sleep(60)\n' if parent_waits else ''))
    job = assure.Assurance(tmp_path, 'Check', tmp_path, stage_timeout=3)
    try:
        start = time.monotonic()
        result = job.run('source', [sys.executable, str(worker)])
        assert time.monotonic() - start < 10
        assert result == (124 if parent_waits else 0)
        stage = json.loads((job.report / 'run.json').read_text())['stages']['source']
        assert stage['status'] == ('timed_out' if parent_waits else 'completed')
        assert stage['timed_out'] is parent_waits
        assert stage['timeout_seconds'] == 3
        assert 'worker ready' in (job.report / 'source.log').read_text()
        # A live descendant would still own the file lock; a zombie cannot fake failure.
        deadline = time.monotonic() + 3
        with lock.open('a') as stream:
            while True:
                try:
                    fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    break
                except BlockingIOError:
                    if time.monotonic() >= deadline:
                        pytest.fail('stage left a descendant holding resources')
                    time.sleep(0.02)
        assert job.finish() == 1  # No proof evidence, including when a stage succeeds.
        assert json.loads((job.report / 'guarantee.json').read_text())['status'] == 'unverified'
    finally:
        if ready.exists():
            try:
                os.kill(int(ready.read_text()), signal.SIGKILL)
            except ProcessLookupError:
                pass


@pytest.mark.parametrize('limit', [0, -1, float('inf'), float('nan'), True])
def test_stage_deadline_rejects_invalid_limits(tmp_path, limit):
    assure = load(str(Path(SCRIPTS) / 'assure.py'), 'af_invalid_deadline')
    with pytest.raises(ValueError, match='timeout'):
        assure.Assurance(tmp_path, 'Check', tmp_path, stage_timeout=limit)


@pytest.mark.parametrize('signum', ['SIGINT', 'SIGTERM'])
@pytest.mark.parametrize('mixed', [False, True])
def test_driver_cancellation_finalizes_and_releases_stage_resources(tmp_path, signum, mixed):
    import fcntl
    import signal
    import subprocess

    source = tmp_path / 'source'
    source.mkdir()
    (source / 'policy.py').write_text('def policy(): return True\n')
    if mixed:
        (source / 'Other.scala').write_text('object Other {}\n')
    lock, ready = tmp_path / 'stage.lock', tmp_path / 'stage.pid'
    worker = tmp_path / 'worker.py'
    worker.write_text('import fcntl,os,pathlib,signal,time\n'
                      'signal.signal(signal.SIGINT, signal.SIG_IGN)\n'
                      f'stream=open({str(lock)!r}, "w")\n'
                      'fcntl.flock(stream, fcntl.LOCK_EX)\n'
                      f'pathlib.Path({str(ready)!r}).write_text(str(os.getpid()))\n'
                      'time.sleep(60)\n')
    (tmp_path / 'autoform.sh').write_text('exec "$AUTOFORM_PYTHON" worker.py\n')
    driver = ('import sys\n'
              f'sys.path.insert(0, {str(SCRIPTS)!r})\n'
              'import assure\n'
              'implementation = assure.Assurance\n'
              f'assure.Assurance = lambda *args, **kwargs: implementation(*args, root={str(tmp_path)!r}, **kwargs)\n'
              f'sys.exit(assure.main([{str(source)!r}, "Check"]))\n')
    process = subprocess.Popen([sys.executable, '-c', driver], stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True)
    try:
        deadline = time.monotonic() + 10
        while not ready.exists():
            if process.poll() is not None or time.monotonic() >= deadline:
                pytest.fail('driver did not reach its source stage')
            time.sleep(0.02)
        selected = getattr(signal, signum)
        process.send_signal(selected)
        output, _ = process.communicate(timeout=10)
        assert process.returncode == 128 + selected, output
        report = tmp_path / 'artifacts/pipeline/Check'
        run = json.loads((report / 'run.json').read_text())
        assert run['execution_status'] == 'completed_with_gaps'
        assert not run['verification_complete']
        if mixed:
            assert run['stages']['python']['status'] == 'failed'
            assert run['stages']['python']['exit_code'] == 128 + selected
            assert run['children'][0]['eligible_for_current_repository'] is False
            child = json.loads((report.parent / 'CheckPython/run.json').read_text())
            source_stage = child['stages']['source']
        else:
            source_stage = run['stages']['source']
        assert source_stage['status'] == 'interrupted'
        assert source_stage['exit_code'] == 128 + selected
        assert 'interrupted' in run['issues']
        assert json.loads((report / 'guarantee.json').read_text())['status'] == 'unverified'
        assert (report / 'summary.md').is_file()
        with lock.open() as stream:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
    finally:
        if process.poll() is None:
            process.kill()
        process.communicate(timeout=10)
        if ready.exists():
            try:
                os.killpg(int(ready.read_text()), signal.SIGKILL)
            except ProcessLookupError:
                pass


@pytest.mark.parametrize('phase', ['baseline', 'mutant'])
def test_stage_deadline_restores_mutation_source(tmp_path, phase):
    import fcntl
    import signal

    assure = load(str(Path(SCRIPTS) / 'assure.py'), 'af_mutation_deadline')
    source = tmp_path / 'Check.lean'
    original = 'def value : Nat := 1\ntheorem checked : value = 1 := rfl\n'
    source.write_text(original)
    (tmp_path / 'lakefile.toml').write_text('name = "fixture"\n')
    lock, pidfile = tmp_path / 'build.lock', tmp_path / 'build.pid'
    home = tmp_path / 'home'
    lake = home / '.elan/bin/lake'
    lake.parent.mkdir(parents=True)
    lake.write_text(f'#!{sys.executable}\nimport fcntl,os,pathlib,time\n'
                    + (f'if pathlib.Path({str(source)!r}).read_text()=={original!r}: raise SystemExit(0)\n'
                       if phase == 'mutant' else '')
                    + f'stream=open({str(lock)!r},"w")\n'
                    'fcntl.flock(stream,fcntl.LOCK_EX)\n'
                    f'pathlib.Path({str(pidfile)!r}).write_text(str(os.getpid()))\n'
                    'time.sleep(60)\n')
    lake.chmod(0o755)
    job = assure.Assurance(tmp_path, 'Check', tmp_path, stage_timeout=3)
    job.env['HOME'] = str(home)
    try:
        assert job.run('mutation', [sys.executable, str(Path(SCRIPTS) / 'mutate.py'),
            str(source), 'Check', '--decls', 'value', '--max-mutants', '1', '--timeout', '60',
            '--json', str(tmp_path / 'mutation.json')]) == 124
        assert pidfile.exists(), 'mutation build never reached its blocking phase'
        assert source.read_text() == original, 'deadline stranded a mutant in the source file'
        assert not source.with_suffix('.lean.mutate-backup').exists()
        with lock.open() as stream:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
    finally:
        if pidfile.exists():
            try:
                os.killpg(int(pidfile.read_text()), signal.SIGKILL)
            except ProcessLookupError:
                pass


def case(tmp_path, audit_module, verified=True, untested=False):
    (tmp_path / "ast-Check.json").write_text(json.dumps([
        dict(name="f", body=dict(k="ret", e=dict(k="lit", v=1)))]))
    source = tmp_path/(audit_module.replace('.', '/')+'.lean')
    compiled = tmp_path/('.lake/build/lib/lean/'+audit_module.replace('.', '/')+'.olean')
    source.parent.mkdir(parents=True, exist_ok=True)
    compiled.parent.mkdir(parents=True, exist_ok=True)
    source.write_text('-- replay fixture\n')
    compiled.write_bytes(b'compiled fixture')
    artifacts=load(str(Path(SCRIPTS)/'proof_artifacts.py'), 'af_assurance_artifacts')
    files={str(p.relative_to(tmp_path)):artifacts.digest(p) for p in (source,compiled)}
    (tmp_path / "audit.json").write_text(json.dumps(dict(
        repo=str(tmp_path), artifact_snapshot=dict(status='STABLE', files=files),
        root_module=audit_module, verdict=dict(**{"pass": verified}),
        axiom_sweep=dict(status='CLEAN', declarations=100, root_theorems=1, root_axioms=[],
                         axiom_histogram={}, leaks=[]),
        lean4checker=dict(status="VERIFIED" if verified else "FAILED", mode='fresh',
                          returncode=0 if verified else 1))))
    thms = {"f": dict(killed=1, survived=0, verdict="HAS TEETH")}
    if untested:
        thms["g"] = dict(killed=0, survived=0, verdict="UNTESTED")
    (tmp_path / "mutation.json").write_text(json.dumps(dict(
        module="Autoform.Generated.Check", status='OK', restored_build=dict(exit_code=0), theorems=thms)))
    sacm = load(str(Path(SCRIPTS) / "sacm.py"), "af_sacm_test")
    result, _, _, _ = sacm.build_case("Check", str(tmp_path))
    return {c["id"]: c for c in result.claims}


def test_scoped_replayed_proofs_support_their_module(tmp_path):
    claims = case(tmp_path, "Autoform.SpecsGen.Check")
    assert claims["G5"]["status"] == "SUPPORTED"
    assert claims["G5"]["scope"]["declarations"] == 1


def test_failed_replay_defeats_proof_claim(tmp_path):
    assert case(tmp_path, "Autoform.SpecsGen.Check", verified=False)["G5"]["status"] == "DEFEATED"


def test_legacy_axioms_cannot_override_a_failed_current_audit(tmp_path):
    (tmp_path/'axioms.json').write_text(json.dumps(dict(module='Check', theorems=1, axioms=[])))
    assert case(tmp_path, 'Autoform.SpecsGen.Check', verified=False)['G5']['status'] == 'DEFEATED'


@pytest.mark.parametrize('module', ['Autoform.SpecsGen.Check', 'Autoform'])
def test_stale_audit_cannot_support_current_proofs(tmp_path, module):
    case(tmp_path, module)
    (tmp_path/(module.replace('.', '/')+'.lean')).write_text('-- source changed after replay\n')
    sacm=load(str(Path(SCRIPTS)/'sacm.py'), 'af_stale_assurance')
    result, _, _, _ = sacm.build_case('Check', str(tmp_path))
    claims={c['id']:c for c in result.claims}
    assert claims['G5']['status'] != 'SUPPORTED'
    if 'G5.1' in claims:
        assert claims['G5.1']['status'] != 'SUPPORTED'


def test_failed_repo_replay_defeats_narrowed_repository_claim(tmp_path):
    assert case(tmp_path, 'Autoform', verified=False)['G5.1']['status'] == 'DEFEATED'


def test_off_subject_audit_cannot_support_module(tmp_path):
    assert case(tmp_path, "Autoform.SpecsGen.Different")["G5"]["status"] != "SUPPORTED"


def test_untested_specification_is_not_adequacy_evidence(tmp_path):
    assert case(tmp_path, "Autoform.SpecsGen.Check", untested=True)["G4"]["status"] != "SUPPORTED"


@pytest.mark.parametrize('defect', ['wrong_module', 'restore_failed', 'incomplete', 'unattributed'])
def test_incomplete_or_unrelated_mutations_cannot_support_adequacy(tmp_path, defect):
    case(tmp_path, 'Autoform.SpecsGen.Check')
    path=tmp_path/'mutation.json'
    data=json.loads(path.read_text())
    if defect == 'wrong_module':
        data['module']='Autoform.Generated.CheckOther'
    elif defect == 'restore_failed':
        data['status']='RESTORE_FAILED'
        data['restored_build']['exit_code']=1
    elif defect == 'incomplete':
        data.pop('restored_build')
    else:
        data['inconclusive']=1
    path.write_text(json.dumps(data))
    sacm=load(str(Path(SCRIPTS)/'sacm.py'), 'af_incomplete_mutations')
    result, _, _, _ = sacm.build_case('Check', str(tmp_path))
    assert next(c for c in result.claims if c['id']=='G4')['status'] != 'SUPPORTED'


def test_contracts_do_not_relabel_cachetools_demo():
    emitter = load(str(Path(SCRIPTS) / "emit_contracts.py"), "af_contracts_test")
    assert emitter.emit("Check") == {"module": "Check", "theorems": []}


def test_runtime_coverage_does_not_claim_all_inputs(tmp_path):
    (tmp_path / "core-oracle.json").write_text(json.dumps(dict(
        module="Check", claim=dict(verifiable_core_static=1),
        result=dict(verifiable_core_executed=1, holed_on_some_input=0,
                    holed_on_a_real_input=0, inconclusive_never_exercised=0))))
    claims = case(tmp_path, "Autoform.SpecsGen.Check")
    assert claims["G3.2"]["status"] == "SUPPORTED"
    assert claims["G3.2"]["scope"]["quantifiedOver"] == "tested inputs"


@pytest.fixture
def guarantee_case(tmp_path, differential):
    rb = differential.runtime_backends
    guarantee = load(str(Path(SCRIPTS) / 'guarantee.py'), 'af_guarantee_test')
    source = tmp_path / 'source'
    source.mkdir()
    (source / 'f.c').write_text('int f(void) { return 1; }\n')
    report = tmp_path / 'artifacts/pipeline/Check'
    report.mkdir(parents=True)
    generated = tmp_path / 'Autoform/Generated/Check.lean'
    generated.parent.mkdir(parents=True)
    generated.write_text('def f := 1\n')
    proof = tmp_path / 'Autoform/SpecsGen/Check.lean'
    proof.parent.mkdir(parents=True)
    proof.write_text('-- unit fixture; replay is mocked in this test\n')
    compiled = tmp_path / '.lake/build/lib/lean/Autoform/SpecsGen/Check.olean'
    compiled.parent.mkdir(parents=True)
    compiled.write_bytes(b'compiled fixture')
    fs = [dict(name='f', file='f.c', params=[])]
    ast = report / 'ast-Check.json'
    ast.write_text(json.dumps(fs))
    conf = dict(module='Check', total=1, build_stable=True, divergences=0,
                provenance=dict(ast_sha256=rb.sha256(ast), generated_sha256=rb.sha256(generated),
                    source_sha256=rb.source_fingerprints(source, fs),
                    semantics_sha256=rb.semantics_fingerprints()),
                runtime_cases=[dict(name='f', comparison='agree')])
    (report / 'conformance.json').write_text(json.dumps(conf))
    (report / 'specs.json').write_text(json.dumps(dict(module='Check', build_clean=True,
        artifact_hashes={name:rb.sha256(path) for name,path in
                         [('model',generated),('proof',proof),('ast',ast),('conformance',report/'conformance.json')]},
        cross_runtime_evidence=True, specs=[dict(id='conform_f', subject='f', definition='f_f', domain=1,
                                                 family='conform', proved=True)])))
    (report / 'mutation.json').write_text(json.dumps(dict(status='OK',
        module='Autoform.Generated.Check', spec_module='Autoform.SpecsGen.Check',
        restored_build=dict(exit_code=0), mutants_generated=1, mutants_run=1,
        invalid=0, inconclusive=0, coarse_attributions=0,
        subject_map={'conform_f': ['f_f']}, mutants=[dict(decl='f_f', verdict={'conform_f': 'killed'})],
        theorems={'conform_f': dict(verdict='HAS TEETH', killed=1, survived=0, inconclusive=0,
                                  scope='on-subject')})))
    for name in ('core-oracle.json', 'context.json'):
        (report / name).write_text('{}')
    files = {str(path.relative_to(tmp_path)):rb.sha256(path) for path in
             [generated,proof,compiled,*[report/name for name in ('specs.json','conformance.json',
               'mutation.json','core-oracle.json','context.json','ast-Check.json')]]}
    audit = dict(root_module='Autoform.SpecsGen.Check', verdict={'pass': True},
                 lean4checker=dict(status='VERIFIED', mode='fresh', returncode=0),
                 artifact_snapshot=dict(status='STABLE',files=files),
                 axiom_sweep=dict(root_theorem_names=['Autoform.SpecsGen.Check.conform_f']))
    (report / 'audit.json').write_text(json.dumps(audit))
    stages = {name: dict(status='completed', exit_code=0) for name in
              ('source', 'core-oracle', 'mutation', 'restore-build', 'audit')}
    return guarantee, source, report, stages, audit


def test_guarantee_requires_scoped_audit_mutation_and_current_evidence(tmp_path, guarantee_case):
    guarantee, source, report, stages, audit = guarantee_case
    result = guarantee.emit(tmp_path, report, 'Check', source, stages)
    assert result['status'] == 'verified_scoped'
    assert not result['whole_program_correctness'] and not result['claims'][0]['all_inputs']
    assert result['evidence_sha256']
    audit['root_module'] = 'Autoform.SpecsGen.Other'
    (report / 'audit.json').write_text(json.dumps(audit))
    assert guarantee.emit(tmp_path, report, 'Check', source, stages)['status'] == 'unverified'
    audit['root_module'] = 'Autoform.SpecsGen.Check'
    (report / 'audit.json').write_text(json.dumps(audit))
    (source / 'f.c').write_text('int f(void) { return 2; }\n')
    result = guarantee.emit(tmp_path, report, 'Check', source, stages)
    assert result['status'] == 'unverified' and not result['claims']


@pytest.mark.parametrize('name', ['Autoform/SpecsGen/Check.lean',
    '.lake/build/lib/lean/Autoform/SpecsGen/Check.olean', 'artifacts/pipeline/Check/mutation.json',
    'artifacts/pipeline/Check/specs.json', 'artifacts/pipeline/Check/core-oracle.json'])
@pytest.mark.parametrize('delete', [False, True])
def test_changed_or_missing_replay_artifact_withholds_guarantee(tmp_path, guarantee_case, name, delete):
    guarantee, source, report, stages, _ = guarantee_case
    path = tmp_path / name
    if delete:
        path.unlink()
    else:
        path.write_text(path.read_text() + '\n')
    result = guarantee.emit(tmp_path, report, 'Check', source, stages)
    assert result['status'] == 'unverified' and not result['claims']
    assert any('artifact' in reason for reason in result['failed_checks'])


@pytest.mark.parametrize('change', ['nonfresh', 'missing_theorem', 'unstable', 'empty_snapshot', 'malformed'])
def test_replay_must_match_the_claim(tmp_path, guarantee_case, change):
    guarantee, source, report, stages, audit = guarantee_case
    if change == 'nonfresh':
        audit['lean4checker']['mode'] = 'module'
    elif change == 'missing_theorem':
        audit['axiom_sweep']['root_theorem_names'] = ['Autoform.SpecsGen.Check.unrelated']
    elif change == 'unstable':
        audit['artifact_snapshot']['status'] = 'CHANGED'
    elif change == 'empty_snapshot':
        audit['artifact_snapshot']['files'] = {}
    else:
        audit['artifact_snapshot'] = None
        audit['axiom_sweep'] = None
    (report/'audit.json').write_text(json.dumps(audit))
    result = guarantee.emit(tmp_path, report, 'Check', source, stages)
    assert result['status'] == 'unverified' and not result['claims']


def test_driver_cannot_succeed_when_certificate_is_withheld(tmp_path, monkeypatch):
    assure=load(str(Path(SCRIPTS)/'assure.py'), 'af_unverified_driver')
    job=assure.Assurance(tmp_path, 'Check', tmp_path)
    job.stages={name:dict(status='completed',exit_code=0) for name in
                ('source','core-oracle','mutation','restore-build','audit','contracts','assurance')}
    monkeypatch.setattr(assure.guarantee, 'emit', lambda *args:dict(status='unverified'))
    assert job.finish() == 1
    run=json.loads((job.report/'run.json').read_text())
    assert run['execution_status'] == 'completed_with_gaps'
    assert run['issues'] == ['guarantee']
    assert not run['verification_complete']


@pytest.mark.parametrize('security_report', [dict(proved=0, open_obligations=1), None])
def test_driver_summary_separates_requested_security_obligations(tmp_path, monkeypatch, security_report):
    assure = load(str(Path(SCRIPTS) / 'assure.py'), 'af_scoped_driver_counts')
    job = assure.Assurance(tmp_path, 'Check', tmp_path, properties=tmp_path / 'properties.json')
    (job.report / 'specs.json').write_text(json.dumps(dict(proved=1, open_obligations=0)))
    if security_report is not None:
        (job.report / 'security-claims.json').write_text(json.dumps(security_report))
    monkeypatch.setattr(assure.guarantee, 'emit',
                        lambda *args: dict(status='unverified', security=dict(status='unverified')))
    assert job.finish() == 1
    run = json.loads((job.report / 'run.json').read_text())
    assert run['proofs'] == 1 and run['open_obligations'] == 0  # Legacy conformance counters.
    assert run['proof_counts_scope'] == 'conformance'
    assert run['proof_summary']['conformance'] == dict(proofs=1, open_obligations=0)
    expected = security_report or dict(proved=None, open_obligations=None)
    assert run['proof_summary']['security'] == dict(requested=True, proofs=expected['proved'],
                                                   open_obligations=expected['open_obligations'])
    summary = (job.report / 'summary.md').read_text()
    assert 'Conformance specifications: 1 proved; 0 open obligations.' in summary
    if security_report is None:
        assert 'Independent security properties: unknown (not reported) proved; unknown (not reported) open obligations.' in summary
    else:
        assert 'Independent security properties: 0 proved; 1 open obligations.' in summary


def test_requested_security_properties_cannot_inherit_a_conformance_badge(tmp_path, guarantee_case):
    guarantee, source, report, stages, _ = guarantee_case
    result = guarantee.emit(tmp_path, report, 'Check', source, stages, security_requested=True)
    assert result['status'] == 'unverified' and not result['claims']
    assert result['security']['status'] == 'unverified'
    assert not result['security']['claims']
    assert (report / 'security.md').is_file()


def test_repository_properties_are_frozen_before_source_execution(tmp_path, monkeypatch):
    assure = load(str(Path(SCRIPTS) / 'assure.py'), 'af_discovered_properties')
    source = tmp_path / 'source'
    source.mkdir()
    manifest = source / 'autoform.properties.json'
    request = b'{"schema_version":1,"claims":[{"id":"original"}]}'
    manifest.write_bytes(request)
    job = assure.Assurance(source, 'Check', tmp_path)
    checked = []

    def run(name, command, accepted=(0,)):
        job.stages[name] = dict(status='completed', exit_code=0)
        if name == 'source':
            manifest.write_text('{"weakened":true}')
            (job.report / 'pipeline.json').write_text('{"stage":"runtime"}')
        return 0

    def check_security(ready):
        checked.append((job.report / 'properties.json').read_bytes())

    monkeypatch.setattr(job, 'run', run)
    monkeypatch.setattr(job, 'check_security', check_security)
    assert job.execute() == 1  # No proof evidence is fabricated by this fixture.
    assert checked == [request]
    report = json.loads((job.report / 'run.json').read_text())
    assert report['security_requested']
    assert report['property_selection'] == dict(mode='repository', path=str(manifest),
                                               sha256=hashlib.sha256(request).hexdigest())
    assert report['security_status'] == 'unverified'


def test_properties_discovery_stays_within_selected_source(tmp_path):
    assure = load(str(Path(SCRIPTS) / 'assure.py'), 'af_property_scope')
    source = tmp_path / 'component'
    source.mkdir()
    (tmp_path / 'autoform.properties.json').write_text('{"parent":true}')
    job = assure.Assurance(source, 'Check', tmp_path)
    assert job.snapshot_properties() == (None, None)
    assert job.properties is None
    (source / 'autoform.properties.json').write_text('{"selected":true}')
    assert job.snapshot_properties() == (b'{"selected":true}', None)
    assert job.property_selection['mode'] == 'repository'


def test_explicit_properties_override_repository_requirements(tmp_path):
    assure = load(str(Path(SCRIPTS) / 'assure.py'), 'af_property_override')
    source = tmp_path / 'component'
    source.mkdir()
    (source / 'autoform.properties.json').mkdir()  # Even an invalid discovered candidate is overridden.
    explicit = tmp_path / 'reviewer-policy.json'
    explicit.write_text('{"reviewer":true}')
    job = assure.Assurance(source, 'Check', tmp_path, properties=explicit)
    assert job.snapshot_properties() == (b'{"reviewer":true}', None)
    assert job.property_selection['mode'] == 'explicit'
    explicit.unlink()
    assert job.snapshot_properties()[1]
    assert job.properties == explicit  # Never fall back when the requested override is missing.


@pytest.mark.parametrize('defect', ['directory', 'broken_link', 'escaping_link', 'loop', 'fifo', 'unreadable'])
def test_invalid_discovered_manifest_withholds_security_and_clears_stale_evidence(tmp_path, monkeypatch, defect):
    assure = load(str(Path(SCRIPTS) / 'assure.py'), 'af_invalid_discovered_properties')
    source = tmp_path / 'source'
    source.mkdir()
    manifest = source / 'autoform.properties.json'
    if defect == 'directory':
        manifest.mkdir()
    elif defect == 'broken_link':
        manifest.symlink_to(source / 'absent.json')
    elif defect == 'escaping_link':
        outside = tmp_path / 'outside.json'
        outside.write_text('{}')
        manifest.symlink_to(outside)
    elif defect == 'loop':
        manifest.symlink_to(manifest)
    elif defect == 'fifo':
        os.mkfifo(manifest)
    else:
        manifest.write_text('{}')
        real_open = os.open

        def unreadable(path, *args, **kwargs):
            if Path(path) == manifest:
                raise PermissionError('unreadable property manifest')
            return real_open(path, *args, **kwargs)

        monkeypatch.setattr(os, 'open', unreadable)
    job = assure.Assurance(source, 'Check', tmp_path)
    (job.report / 'security.json').write_text('{"status":"verified_scoped"}')
    (job.report / 'guarantee.json').write_text('{"status":"verified_scoped"}')
    (job.report / 'specs.json').write_text('{"proved":999}')
    monkeypatch.setattr(job, 'run', lambda *args, **kwargs: pytest.fail('invalid property input executed source'))
    assert job.execute() == 1
    run = json.loads((job.report / 'run.json').read_text())
    assert run['security_requested'] and run['property_selection']['error']
    assert run['security_status'] == 'unverified'
    assert run['stages']['source']['status'] == 'blocked'
    assert json.loads((job.report / 'guarantee.json').read_text())['status'] == 'unverified'
    assert json.loads((job.report / 'security.json').read_text())['status'] == 'unverified'
    assert not (job.report / 'specs.json').exists()
