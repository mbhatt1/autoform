"""Independent properties cannot inherit a conformance badge or stale evidence."""
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess

import pytest

from conftest import ROOT, SCRIPTS, load


@pytest.fixture
def security():
    return load(str(Path(SCRIPTS) / 'security_specs.py'), 'af_security_specs_test')


def request(**updates):
    claim = dict(id='owner_only', subject='policy.py:<module>.authorize',
        statement='∀ owner caller : Int, runFunc program 32 "policy.py:<module>.authorize" '
                  '[.int owner, .int caller] = .val (.bool (owner == caller))')
    claim.update(updates)
    return dict(schema_version=1, claims=[claim])


@pytest.mark.parametrize('defect', ['unknown_field', 'duplicate_id', 'missing_subject', 'ambiguous_subject',
                                   'nonstring', 'bad_id', 'bool_version', 'empty', 'duplicate_key'])
def test_property_input_rejects_ambiguous_or_ignored_requirements(tmp_path, security, defect):
    data = request()
    functions = [dict(name='policy.py:<module>.authorize')]
    if defect == 'unknown_field':
        data['claims'][0]['precondition_typo'] = 'admin'
    elif defect == 'duplicate_id':
        data['claims'].append(copy.deepcopy(data['claims'][0]))
    elif defect == 'missing_subject':
        data['claims'][0]['subject'] = 'absent'
    elif defect == 'ambiguous_subject':
        functions *= 2
    elif defect == 'nonstring':
        data['claims'][0]['statement'] = False
    elif defect == 'bad_id':
        data['claims'][0]['id'] = 'owner\ntheorem injected'
    elif defect == 'bool_version':
        data['schema_version'] = True
    elif defect == 'empty':
        data['claims'] = []
    path = tmp_path / 'properties.json'
    text = json.dumps(data)
    if defect == 'duplicate_key':
        text = text.replace('"schema_version": 1', '"schema_version": 1, "schema_version": 1')
    path.write_text(text)
    with pytest.raises(ValueError):
        security.load_properties(path, functions)


@pytest.fixture(scope='module')
def property_lean_ready():
    env = dict(os.environ, PATH=str(Path.home() / '.elan/bin') + os.pathsep + os.environ['PATH'])
    if not shutil.which('lake', path=env['PATH']):
        if os.environ.get('AUTOFORM_REQUIRE_LEAN'):
            pytest.fail('Lean is required')
        pytest.skip('Lean is unavailable')
    build = subprocess.run(['lake', 'build', 'Autoform.Runtime'], cwd=ROOT, env=env,
                           capture_output=True, text=True, timeout=600)
    assert build.returncode == 0, build.stdout + build.stderr


@pytest.fixture
def property_model(tmp_path, security, monkeypatch, render_lean, property_lean_ready):
    source = tmp_path / 'source'
    source.mkdir()
    (source / 'policy.py').write_text('def authorize(owner, caller): return owner == caller\n')
    report = tmp_path / 'artifacts/pipeline/Check'
    report.mkdir(parents=True)
    funcs = [dict(name='policy.py:<module>.authorize', file='policy.py', params=['owner', 'caller'],
                  body=dict(k='ret', e=dict(k='binop', op='==', a=dict(k='name', v='owner'),
                                            b=dict(k='name', v='caller'))))]
    ast = report / 'ast-Check.json'
    ast.write_text(json.dumps(funcs))
    model = tmp_path / 'Autoform/Generated/Check.lean'
    model.parent.mkdir(parents=True)
    result = subprocess.run([os.sys.executable, str(Path(ROOT) / 'cartographer/render_lean.py'),
                             str(ast), str(model), 'Check'], capture_output=True, text=True)
    assert result.returncode == 0, result.stdout + result.stderr
    # Keep generated models isolated, while using the actual built Lean dependencies.
    original_header = security.header
    inline_model = model.read_text().replace('import Autoform.Lang.Core.Semantics\n', '')
    monkeypatch.setattr(security, 'header', lambda module:
        original_header(module).replace('import Autoform.Generated.Check\n',
                                        'import Autoform.Lang.Core.Semantics\n')
        .replace('set_option autoImplicit false', inline_model + '\nset_option autoImplicit false'))
    original_run = security.lean_run
    monkeypatch.setattr(security, 'lean_run', lambda root, *args: original_run(Path(ROOT), *args))
    return source, report


@pytest.mark.parametrize('kind', ['universal', 'false', 'vacuous', 'admitted', 'native_decide', 'injection'])
def test_kernel_property_attempts_distinguish_proof_from_missing_evidence(
        tmp_path, security, property_model, kind):
    source, report = property_model
    data = request()
    claim = data['claims'][0]
    if kind == 'false':
        claim.update(statement='runFunc program 32 "policy.py:<module>.authorize" '
                     '[.int 0, .int 1] = .val (.bool true)', proof='by decide +kernel')
    elif kind == 'vacuous':
        claim.update(statement='True', proof='by trivial')
    elif kind == 'admitted':
        claim['proof'] = 'by sorry'
    elif kind == 'native_decide':
        claim.update(statement='(match runFunc program 32 "policy.py:<module>.authorize" '
                     '[.int 1, .int 1] with | .val (.bool b) => b | _ => false) = true',
                     proof='by native_decide')
    elif kind == 'injection':
        claim['statement'] = 'True) := by trivial\naxiom injected : False\ntheorem other : (True'
    path = tmp_path / 'properties.json'
    path.write_text(json.dumps(data))
    if kind == 'injection':
        with pytest.raises(ValueError, match='property syntax'):
            security.generate(tmp_path, report, source, 'Check', path, timeout=90)
        assert not (report / 'security-claims.json').exists()
        return
    result = security.generate(tmp_path, report, source, 'Check', path, timeout=90)
    assert result['proved'] == (1 if kind == 'universal' else 0), (report / 'security-owner_only.log').read_text()
    assert result['open_obligations'] == (0 if kind == 'universal' else 1)
    proof = (tmp_path / 'Autoform/Security/Check.lean').read_text()
    assert ('theorem property_owner_only' in proof) == (kind == 'universal')
    if kind != 'universal':
        assert result['claims'][0]['status'] == 'unresolved'
        assert 'not a native-confirmed violation' in result['claims'][0]['reason']


@pytest.fixture
def security_certificate(tmp_path, security):
    source = tmp_path / 'source'
    source.mkdir()
    (source / 'policy.py').write_text('def authorize(owner, caller): return owner == caller\n')
    report = tmp_path / 'artifacts/pipeline/Check'
    report.mkdir(parents=True)
    module = 'Autoform.Security.Check'
    files = [tmp_path / 'Autoform/Generated/Check.lean', tmp_path / 'Autoform/Security/Check.lean',
             tmp_path / '.lake/build/lib/lean/Autoform/Security/Check.olean']
    for path in files:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text('mock replay input\n')
    ast = [dict(name='policy.py:<module>.authorize', file='policy.py')]
    security.write(report / 'ast-Check.json', ast)
    security.write(report / 'context.json', {})
    security.write(report / 'properties.json', request())
    claim = dict(request()['claims'][0], proved=True, definition='f_policy_py__module__authorize',
                 theorem=module + '.property_owner_only')
    specs = dict(module='Check', proof_module=module, claims=[claim], proved=1, open_obligations=0,
                 source_sha256=security.runtime_backends.source_fingerprints(source, ast),
                 artifact_hashes={key:security.proof_artifacts.digest(path) for key, path in
                     [('model',files[0]),('proof',files[1]),('ast',report/'ast-Check.json'),
                      ('properties',report/'properties.json')]})
    security.write(report / 'security-claims.json', specs)
    mutation = dict(status='OK', module='Autoform.Generated.Check', spec_module=module,
                    restored_build=dict(exit_code=0),
                    mutants_generated=1, mutants_run=1, invalid=0, inconclusive=0, coarse_attributions=0,
                    mutants=[dict(decl=claim['definition'], verdict={'property_owner_only': 'killed'})],
                    subject_map=dict(property_owner_only=[claim['definition']]),
                    theorems=dict(property_owner_only=dict(verdict='HAS TEETH', killed=1, survived=0,
                                                          inconclusive=0, scope='on-subject')))
    security.write(report / 'security-mutation.json', mutation)
    bound = files + [report / n for n in ('properties.json','security-claims.json','security-mutation.json',
                                         'context.json','ast-Check.json')]
    audit = dict(root_module=module, verdict={'pass':True},
                 lean4checker=dict(status='VERIFIED', mode='fresh', returncode=0),
                 axiom_sweep=dict(root_theorem_names=[claim['theorem']]),
                 artifact_snapshot=dict(status='STABLE', files={str(p.relative_to(tmp_path)):
                     security.proof_artifacts.digest(p) for p in bound}))
    security.write(report / 'security-audit.json', audit)
    stages = {key:dict(status='completed',exit_code=0) for key in
              ('security-properties','security-mutation','security-restore','security-audit')}
    return source, report, stages, audit, mutation, specs


def test_security_certificate_states_exact_property_scope(tmp_path, security, security_certificate):
    source, report, stages, *_ = security_certificate
    result = security.certify(tmp_path, report, source, 'Check', stages)
    assert result['status'] == 'verified_scoped', result
    assert result['claims'][0]['statement'].startswith('∀ owner caller')
    assert not result['native_confirmed_violations']
    assert result['native_validation']['status'] == 'not_run'


@pytest.mark.parametrize('defect', ['source', 'proof', 'request', 'missing_theorem', 'nonfresh', 'failed_stage',
                                   'mutation_subject', 'unresolved', 'changed_statement', 'malformed', 'malformed_stage'])
def test_incomplete_or_mismatched_security_evidence_withholds_guarantee(
        tmp_path, security, security_certificate, defect):
    source, report, stages, audit, mutation, specs = security_certificate
    if defect == 'source':
        (source / 'policy.py').write_text('def authorize(owner, caller): return True\n')
    elif defect == 'proof':
        (tmp_path / 'Autoform/Security/Check.lean').write_text('changed\n')
    elif defect == 'request':
        (report / 'properties.json').unlink()
    elif defect == 'missing_theorem':
        audit['axiom_sweep']['root_theorem_names'] = ['unrelated']
    elif defect == 'nonfresh':
        audit['lean4checker']['mode'] = 'module'
    elif defect == 'failed_stage':
        stages['security-properties']['exit_code'] = 1
    elif defect == 'mutation_subject':
        mutation['subject_map']['property_owner_only'] = ['f_unrelated']
    elif defect == 'unresolved':
        specs['claims'][0]['proved'] = False
    elif defect == 'changed_statement':
        specs['claims'][0]['statement'] = 'True'
    elif defect == 'malformed':
        audit.update(axiom_sweep=None, lean4checker=None, artifact_snapshot=None)
        mutation.update(theorems=None, subject_map=None, restored_build=None)
    elif defect == 'malformed_stage':
        stages['security-properties'] = None
    security.write(report / 'security-claims.json', specs)
    security.write(report / 'security-mutation.json', mutation)
    # Rebind forged metadata to exercise semantic checks separately from stale hashes.
    if isinstance(audit.get('artifact_snapshot'), dict):
        for name in ('security-claims.json', 'security-mutation.json'):
            audit['artifact_snapshot']['files'][str((report/name).relative_to(tmp_path))] = security.proof_artifacts.digest(report/name)
    security.write(report / 'security-audit.json', audit)
    result = security.certify(tmp_path, report, source, 'Check', stages)
    assert result['status'] == 'unverified' and not result['claims'], result
    assert not result['native_confirmed_violations']


def test_property_timeout_releases_descendant_resources(tmp_path, security, monkeypatch):
    import fcntl
    import sys
    home = tmp_path / 'fake-home'
    binary = home / '.elan/bin/lake'
    binary.parent.mkdir(parents=True)
    lock = tmp_path / 'child.lock'
    child = ('import fcntl,time\n'
             f'f=open({str(lock)!r}, "w")\n'
             'fcntl.flock(f,fcntl.LOCK_EX)\n'
             'time.sleep(60)\n')
    binary.write_text(f'#!{sys.executable}\nimport subprocess,sys,time\n'
                      f'subprocess.Popen([sys.executable,"-c",{child!r}])\n'
                      'time.sleep(60)\n')
    binary.chmod(0o755)
    monkeypatch.setattr(security.Path, 'home', lambda: home)
    code, output = security.lean_run(tmp_path, tmp_path, '-- timeout fixture\n', 'deadline', 2)
    assert code == 124 and 'exceeded its deadline' in output
    assert lock.exists(), 'child did not reach the resource before the deadline'
    with lock.open() as stream:
        fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
