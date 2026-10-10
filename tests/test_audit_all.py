"""The source audit must fail, not just print, when its trust claim is false."""
import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from conftest import SCRIPTS, load


@pytest.mark.parametrize("directory", ["Core", "PCode"])
@pytest.mark.parametrize("source", [
    "partial def loop : Nat := loop\n",
    "unsafe def opaqueResult : Nat := 0\n",
    "axiom unchecked : False\n",
    "@[implemented_by fast] def trusted : Nat := 0\n",
    '@[extern "runtime_impl"] opaque trusted : Nat\n',
])
def test_trusted_escape_hatch_fails_verdict(tmp_path, monkeypatch, directory, source):
    audit = load(str(Path(SCRIPTS) / "audit_all.py"), "af_audit_regression")
    file = tmp_path / "Autoform" / "Lang" / directory / "Semantics.lean"
    file.parent.mkdir(parents=True)
    file.write_text(source)
    report = tmp_path / "audit.json"
    monkeypatch.setattr(audit, "REPO", tmp_path)
    monkeypatch.setattr("sys.argv", ["audit_all.py", "--skip-lean", "-o", str(report)])

    assert audit.main() == 1
    result = json.loads(report.read_text())
    assert not result["source_sweep"]["core_clean"]
    assert not result["verdict"]["pass"]
    assert any("trusted semantics" in reason for reason in result["verdict"]["failures"])


def test_documented_escape_hatches_are_not_code(tmp_path, monkeypatch):
    audit = load(str(Path(SCRIPTS) / "audit_all.py"), "af_audit_comments")
    file = tmp_path / "Autoform/Lang/PCode/Semantics.lean"
    file.parent.mkdir(parents=True)
    file.write_text('/- unsafe partial axiom sorry -/\ndef explanation := "unsafe partial"\n')
    monkeypatch.setattr(audit, "REPO", tmp_path)
    result = audit.source_sweep()
    assert result["core_clean"]
    assert result["core_findings"] == []


@pytest.mark.parametrize('change', ['source', 'compiled', 'new_part', 'evidence', 'none'])
def test_replay_rejects_changes_while_it_runs(tmp_path, monkeypatch, change):
    audit = load(str(Path(SCRIPTS)/'audit_all.py'), 'af_audit_snapshot')
    artifacts = audit.proof_artifacts
    source = tmp_path/'Autoform/Check.lean'
    source.parent.mkdir()
    source.write_text('def value : Nat := 1\n')
    compiled = tmp_path/'.lake/build/lib/lean/Autoform/Check.olean'
    compiled.parent.mkdir(parents=True)
    compiled.write_bytes(b'compiled fixture')
    evidence = tmp_path/'observations.json'
    evidence.write_text('{}')
    files = artifacts.snapshot(tmp_path, [{'name':'Autoform.Check','olean':str(compiled)}],
                               artifacts.project_sources(tmp_path), [evidence])
    monkeypatch.setattr(audit, 'REPO', tmp_path)
    monkeypatch.setattr(audit, 'prepare_replay', lambda *args:dict(status='READY', files=files))
    monkeypatch.setattr(audit, 'axiom_sweep', lambda *args:dict(status='CLEAN', declarations=1,
        declared_axioms=[], nonstandard_axioms=[], leaks=[], axiom_histogram={}))
    def replay(**kwargs):
        if change != 'none':
            target = {'source':source, 'compiled':compiled, 'evidence':evidence,
                      'new_part':Path(str(compiled)+'.private')}[change]
            target.write_text('changed')
        return dict(status='VERIFIED', mode='fresh', returncode=0, command='mocked replay', detail='fixture')
    monkeypatch.setattr(audit, 'lean4checker', replay)
    report=tmp_path/'audit.json'
    monkeypatch.setattr('sys.argv', ['audit_all.py','--module','Autoform.Check','--strict','-o',str(report)])
    assert (audit.main()==0) == (change=='none')
    data=json.loads(report.read_text())
    assert data['artifact_snapshot']['status'] == ('STABLE' if change=='none' else 'CHANGED')


def test_snapshot_refuses_source_changed_during_build(tmp_path):
    artifacts=load(str(Path(SCRIPTS)/'proof_artifacts.py'), 'af_artifact_build_race')
    source=tmp_path/'Autoform/Check.lean'
    source.parent.mkdir()
    source.write_text('def value : Nat := 1\n')
    compiled=tmp_path/'.lake/build/lib/lean/Autoform/Check.olean'
    compiled.parent.mkdir(parents=True)
    compiled.write_bytes(b'compiled fixture')
    before=artifacts.project_sources(tmp_path)
    source.write_text('def value : Nat := 2\n')
    with pytest.raises(ValueError, match='source changed during build'):
        artifacts.snapshot(tmp_path,[{'name':'Autoform.Check','olean':str(compiled)}],before)


def test_strict_audit_does_not_pass_without_replay(tmp_path, monkeypatch):
    audit=load(str(Path(SCRIPTS)/'audit_all.py'), 'af_strict_skipped')
    monkeypatch.setattr(audit,'REPO',tmp_path)
    monkeypatch.setattr('sys.argv',['audit_all.py','--strict','--skip-lean','-o',str(tmp_path/'audit.json')])
    assert audit.main()==1
    assert 'kernel replay skipped' in str(json.loads((tmp_path/'audit.json').read_text())['verdict'])


def test_failed_axiom_command_cannot_pass_by_emitting_json(tmp_path, monkeypatch):
    audit = load(str(Path(SCRIPTS)/'audit_all.py'), 'af_failed_axiom_command')
    monkeypatch.setattr(audit, 'REPO', tmp_path)
    payload = json.dumps([dict(name='x', module='Autoform.Check', kind='theorem', axioms=[])] * 100)
    output = 'sweep.lean:2:0: error: command failed\nAUTOFORM_AUDIT_BEGIN\n' + payload + '\nAUTOFORM_AUDIT_END\n'
    monkeypatch.setattr(audit.subprocess, 'run', lambda *args, **kwargs:
                        SimpleNamespace(returncode=1, stdout=output, stderr=''))
    result = audit.axiom_sweep('Autoform.Check')
    assert result['status'] == 'ERROR'
    assert 'command failed' in result['error']
    assert result['declarations'] == 0


@pytest.mark.parametrize('kind', ['declared_axioms', 'nonstandard_axioms'])
def test_project_axioms_prevent_passing_audit(tmp_path, monkeypatch, kind):
    audit = load(str(Path(SCRIPTS)/'audit_all.py'), 'af_project_axioms')
    monkeypatch.setattr(audit, 'REPO', tmp_path)
    source = tmp_path/'Autoform.lean'
    source.write_text('-- mocked build\n')
    files = {'Autoform.lean': audit.proof_artifacts.digest(source)}
    monkeypatch.setattr(audit, 'prepare_replay', lambda *args: dict(status='READY',files=files))
    sweep = dict(status='CLEAN', declarations=1, declared_axioms=[], nonstandard_axioms=[],
                 leaks=[], axiom_histogram={})
    sweep[kind] = [dict(name='Autoform.assumption', module='Autoform', axioms=['assumption'])]
    monkeypatch.setattr(audit, 'axiom_sweep', lambda *args:sweep)
    monkeypatch.setattr(audit, 'lean4checker', lambda **kwargs:
                        dict(status='VERIFIED', mode='fresh', returncode=0, detail='fixture'))
    report = tmp_path/'audit.json'
    monkeypatch.setattr('sys.argv', ['audit_all.py','--strict','-o',str(report)])
    assert audit.main() == 1
    assert 'project axioms' in str(json.loads(report.read_text())['verdict'])
