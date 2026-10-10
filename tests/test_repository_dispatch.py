"""Repository dispatch keeps partial evidence and cannot compose a false guarantee.

Child proof jobs below are deliberately simulated. These tests establish dispatcher
bookkeeping and refusal behavior; they do not supply evidence of Lean proof validity.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import signal

import pytest

from conftest import SCRIPTS, fn, load


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def read(path):
    return json.loads(path.read_text())


@pytest.fixture
def dispatcher():
    return load(str(Path(SCRIPTS) / 'repository_assurance.py'), 'af_test_repository_dispatch')


@pytest.fixture
def assure():
    return load(str(Path(SCRIPTS) / 'assure.py'), 'af_test_dispatch_assure')


def make_run(tmp_path, dispatcher, assure, *, files=None, outcomes=None, request=None):
    source, root = tmp_path / 'source', tmp_path / 'workspace'
    source.mkdir()
    for relative, content in (files if files is not None else
                              {'F.java': 'class F {}\n', 'f.py': 'def f(): return 17\n'}).items():
        path = source / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
    if request is not None:
        write(source / 'autoform.properties.json', request)
    outcomes = outcomes or {}
    events = []

    class FakeJob(assure.Assurance):
        def __init__(self, *args, **kwargs):
            language = kwargs.get('language')
            error = outcomes.get(language, {}).get('construction_error')
            if error is not None:
                raise error
            super().__init__(*args, **kwargs)

        def result(self, *, failed=False):
            outcome = outcomes.get(self.language, {})
            status = 'unverified' if failed else outcome.get('status', 'verified_scoped')
            write(self.report / 'run.json', dict(module=self.module,
                execution_status='failed' if failed else 'completed_with_gaps',
                proofs=0 if failed else 1, comparisons=0 if failed else 5,
                property_selection={'routed_claim_ids': outcome.get('routed', [])}))
            witness = self.report / 'witness.txt'
            witness.write_text('original evidence ' + str(self.language))
            witness_hash = hashlib.sha256(witness.read_bytes()).hexdigest()
            certificate_module = outcome.get('certificate_module', self.module)
            audit = dict(verdict={'pass': True},
                lean4checker={'status': 'VERIFIED', 'mode': 'fresh', 'returncode': 0},
                artifact_snapshot={'status': 'STABLE',
                    'files': {str(witness.relative_to(self.root)): witness_hash}})
            write(self.report / 'audit.json', dict(audit, root_module='Autoform.SpecsGen.' + certificate_module))
            write(self.report / 'security-audit.json', dict(audit, root_module='Autoform.Security.' + certificate_module))
            write(self.report / 'security.json', dict(status=outcome.get('security_status', 'unverified'),
                module=certificate_module,
                claims=[{'statement': 'True', **claim} for claim in outcome.get('security_claims', [])]))
            write(self.report / 'guarantee.json', dict(status=status, module=certificate_module,
                claims=[{'theorem': 'Simulated.' + self.module}], evidence_sha256={
                    'witness.txt': witness_hash,
                    'security.json': hashlib.sha256((self.report / 'security.json').read_bytes()).hexdigest(),
                    'audit.json': hashlib.sha256((self.report / 'audit.json').read_bytes()).hexdigest(),
                    'security-audit.json': hashlib.sha256((self.report / 'security-audit.json').read_bytes()).hexdigest(),
                }))
            represented = outcome.get('files', ['F.java'] if self.language == 'java' else ['f.py'])
            write(self.report / 'source-coverage.json', {
                'files': [{'path': path, 'status': 'represented'} for path in represented],
                'source_stable': True, 'scan_complete': True, 'truncated_by_method_limit': False})
            (self.report / 'summary.md').write_text('Simulated child evidence for dispatcher test.\n')

        def execute(self):
            events.append(('execute', self.language))
            outcome = outcomes.get(self.language, {})
            if self.properties is not None:
                events.append(('properties', self.language,
                               self.frozen_properties if self.frozen_properties is not None
                               else self.properties.read_bytes()))
            error = outcome.get('error')
            if error is not None:
                raise error
            self.result()
            callback = outcome.get('after')
            if callback is not None:
                callback(self)
            return outcome.get('exit_code', 1)

        def finish(self):
            events.append(('finish', self.language))
            self.result(failed=True)
            return 1

    job = FakeJob(source, 'Repo', root=root)
    return dispatcher.RepositoryRun(job), events


def property_manifest(*claims):
    return {'schema_version': 1, 'claims': list(claims)}


def claim(ident, subject):
    return {'id': ident, 'subject': subject, 'statement': 'True'}


def test_second_language_runs_after_first_child_raises(tmp_path, dispatcher, assure):
    run, events = make_run(tmp_path, dispatcher, assure,
                          outcomes={'java': {'error': RuntimeError('frontend failed')}})

    assert run.execute() == 1

    assert [event[1] for event in events if event[0] == 'execute'] == ['java', 'python']
    result = read(run.job.report / 'run.json')
    assert [child['exit_code'] for child in result['children']] == [2, 1]
    assert result['stages']['java']['status'] == 'failed'
    assert result['children'][1]['guarantee_status'] == 'verified_scoped'
    assert result['verification_complete'] is False


def test_child_setup_failure_does_not_drop_remaining_languages(tmp_path, dispatcher, assure):
    run, events = make_run(tmp_path, dispatcher, assure,
        outcomes={'java': {'construction_error': OSError('child report directory unavailable')}})

    assert run.execute() == 1

    assert [event[1] for event in events if event[0] == 'execute'] == ['python']
    result = read(run.job.report / 'run.json')
    assert [child['language'] for child in result['children']] == ['python']
    assert result['stages']['java']['status'] == 'blocked'
    assert 'child report directory unavailable' in result['stages']['java']['reason']
    assert 'child report directory unavailable' in (run.job.report / 'summary.md').read_text()


@pytest.mark.parametrize('files', [{}, {'F.scala': 'object F {}\n'}, {'README.md': 'Docs only.\n'}])
def test_empty_or_unsupported_repository_reports_without_child_tools(tmp_path, dispatcher, assure, files):
    run, events = make_run(tmp_path, dispatcher, assure, files=files)

    assert run.execute() == 1

    assert events == []
    result = read(run.job.report / 'run.json')
    assert result['children'] == []
    assert result['proofs'] == 0 and result['comparisons'] == 0
    assert result['verification_complete'] is False
    certificate = read(run.job.report / 'guarantee.json')
    assert certificate['status'] == 'unverified'
    assert certificate['claims'] == []
    assert (run.job.report / 'source-coverage.json').is_file()


def test_successful_children_do_not_become_repository_correctness(tmp_path, dispatcher, assure):
    run, _ = make_run(tmp_path, dispatcher, assure,
                      outcomes={'java': {'exit_code': 0}, 'python': {'exit_code': 0}})

    assert run.execute() == 1

    result = read(run.job.report / 'run.json')
    assert result['proofs'] == 2 and result['comparisons'] == 10
    assert all(child['eligible_for_current_repository'] for child in result['children'])
    certificate = read(run.job.report / 'guarantee.json')
    assert certificate['status'] == 'unverified'
    assert certificate['whole_program_correctness'] is False
    assert certificate['claims'] == []
    assert result['source_coverage']['source_census_complete'] is False


def test_root_properties_are_preserved_and_each_route_retains_disposition(tmp_path, dispatcher, assure):
    request = property_manifest(claim('jvm', 'J.f'), claim('python', 'p.f'), claim('absent', 'Scala.f'))
    run, events = make_run(tmp_path, dispatcher, assure, request=request, outcomes={
        'java': {'routed': ['jvm'], 'security_status': 'verified_scoped',
                 'security_claims': [{'id': 'jvm', 'subject': 'J.f'}]},
        'python': {'routed': ['python'], 'security_status': 'unverified'},
    })
    original = (run.job.source / 'autoform.properties.json').read_bytes()

    assert run.execute() == 1

    assert (run.job.report / 'properties.json').read_bytes() == original
    assert all(event[2] == original for event in events if event[0] == 'properties')
    properties = read(run.job.report / 'run.json')['security_properties']
    assert {prop['id']: prop['status'] for prop in properties} == {
        'jvm': 'verified_scoped', 'python': 'unverified', 'absent': 'unrouted'}
    assert read(run.job.report / 'run.json')['security_open_obligations'] == 2


def test_one_runnable_language_keeps_mixed_repository_property_routing(tmp_path, dispatcher, assure):
    request = property_manifest(claim('python', 'p.f'), claim('scala', 'F.f'))
    run, events = make_run(tmp_path, dispatcher, assure,
        files={'p.py': 'def f(): return 17\n', 'F.scala': 'object F {}\n'},
        request=request, outcomes={
            'python': {'files': ['p.py'], 'routed': ['python'],
                       'security_status': 'verified_scoped',
                       'security_claims': [{'id': 'python', 'subject': 'p.f'}]},
        })

    assert run.execute() == 1

    assert run.delegate is False
    assert [event[1] for event in events if event[0] == 'execute'] == ['python']
    result = read(run.job.report / 'run.json')
    assert result['mode'] == 'repository'
    assert [(child['language'], child['module']) for child in result['children']] == [('python', 'RepoPython')]
    assert result['children'][0]['eligible_for_current_repository'] is True
    assert {prop['id']: prop['status'] for prop in result['security_properties']} == {
        'python': 'verified_scoped', 'scala': 'unrouted'}
    assert result['security_open_obligations'] == 1
    assert result['source_coverage']['counts']['unsupported'] == 1
    assert {row['path']: row['status'] for row in result['source_coverage']['files']} == {
        'p.py': 'represented', 'F.scala': 'unsupported', 'autoform.properties.json': 'auxiliary'}
    certificate = read(run.job.report / 'guarantee.json')
    assert certificate['status'] == 'unverified'
    assert certificate['whole_program_correctness'] is False
    assert certificate['claims'] == []


def test_python_only_repository_still_delegates_to_original_module(tmp_path, dispatcher, assure):
    run, events = make_run(tmp_path, dispatcher, assure,
                          files={'p.py': 'def f(): return 17\n'}, outcomes={'python': {'files': ['p.py']}})

    assert run.execute() == 1

    assert run.delegate is True
    assert run.job.language == 'python'
    assert run.job.module == 'Repo'
    assert run.children == []
    assert [event[1] for event in events if event[0] == 'execute'] == ['python']
    assert read(run.job.report / 'run.json')['module'] == 'Repo'
    assert not (run.job.report / 'repository-summary.json').exists()
    assert not (run.job.report.parent / 'RepoPython').exists()


def test_property_routed_to_multiple_children_is_ambiguous(tmp_path, dispatcher, assure):
    request = property_manifest(claim('shared', 'same.name'))
    outcome = {'routed': ['shared'], 'security_status': 'verified_scoped',
               'security_claims': [{'id': 'shared', 'subject': 'same.name'}]}
    run, _ = make_run(tmp_path, dispatcher, assure, request=request,
                      outcomes={'java': outcome, 'python': outcome})

    assert run.execute() == 1

    prop = read(run.job.report / 'run.json')['security_properties'][0]
    assert prop['status'] == 'ambiguous'
    assert len(prop['routes']) == 2


def test_unsupported_subject_still_has_an_open_property_record(tmp_path, dispatcher, assure):
    run, events = make_run(tmp_path, dispatcher, assure,
        files={'F.scala': 'object F {}\n'}, request=property_manifest(claim('scala', 'F.f')))

    assert run.execute() == 1

    assert events == []
    result = read(run.job.report / 'run.json')
    assert result['security_properties'][0]['status'] == 'unrouted'
    assert result['security_open_obligations'] == 1


def test_changed_configuration_invalidates_all_child_eligibility(tmp_path, dispatcher, assure):
    def change_config(child):
        (child.source / 'pom.xml').write_text('<project>changed</project>\n')

    run, _ = make_run(tmp_path, dispatcher, assure,
        files={'F.java': 'class F {}\n', 'f.py': 'pass\n', 'pom.xml': '<project/>\n'},
        outcomes={'python': {'after': change_config}})

    assert run.execute() == 1

    result = read(run.job.report / 'run.json')
    assert result['source_coverage']['source_stable'] is False
    assert {change['path'] for change in result['source_coverage']['source_changes']} == {'pom.xml'}
    assert not any(child['eligible_for_current_repository'] for child in result['children'])


def test_changed_prior_child_evidence_invalidates_its_eligibility(tmp_path, dispatcher, assure):
    def change_earlier_witness(child):
        (child.report.parent / 'RepoJava/witness.txt').write_text('changed after certification\n')

    run, _ = make_run(tmp_path, dispatcher, assure,
                      outcomes={'python': {'after': change_earlier_witness}})

    assert run.execute() == 1

    children = read(run.job.report / 'run.json')['children']
    assert children[0]['eligible_for_current_repository'] is False
    assert children[1]['eligible_for_current_repository'] is True


def test_consistent_certificate_for_another_module_cannot_be_relabeled(tmp_path, dispatcher, assure):
    run, _ = make_run(tmp_path, dispatcher, assure,
                      outcomes={'java': {'certificate_module': 'AnotherModule'}})

    assert run.execute() == 1

    children = read(run.job.report / 'run.json')['children']
    assert children[0]['module'] == 'RepoJava'
    assert children[0]['eligible_for_current_repository'] is False
    assert children[1]['eligible_for_current_repository'] is True


@pytest.mark.parametrize('change', [{'subject': 'another.subject'}, {'statement': 'False'}])
def test_security_route_cannot_credit_a_changed_subject_or_statement(tmp_path, dispatcher, assure, change):
    request = property_manifest(claim('policy', 'expected.subject'))
    run, _ = make_run(tmp_path, dispatcher, assure, request=request, outcomes={
        'java': {'routed': ['policy'], 'security_status': 'verified_scoped',
                 'security_claims': [{'id': 'policy', 'subject': 'expected.subject', **change}]},
    })

    assert run.execute() == 1

    assert read(run.job.report / 'run.json')['security_properties'][0]['status'] == 'unverified'


def test_changed_parent_request_does_not_change_child_input_or_gain_credit(tmp_path, dispatcher, assure):
    request = property_manifest(claim('policy', 'J.f'))

    def replace_parent_request(child):
        write(child.report.parent / 'Repo/properties.json',
              property_manifest(dict(claim('policy', 'J.f'), statement='False')))

    run, events = make_run(tmp_path, dispatcher, assure, request=request, outcomes={
        'java': {'after': replace_parent_request, 'routed': ['policy'],
                 'security_status': 'verified_scoped',
                 'security_claims': [{'id': 'policy', 'subject': 'J.f'}]},
    })
    original = (run.job.source / 'autoform.properties.json').read_bytes()

    assert run.execute() == 1

    assert all(event[2] == original for event in events if event[0] == 'properties')
    result = read(run.job.report / 'run.json')
    assert result['security_properties'][0]['status'] == 'unverified'
    assert result['security_properties'][0]['subject'] == 'J.f'


def test_cancellation_preserves_signal_and_does_not_start_next_child(tmp_path, dispatcher, assure):
    run, events = make_run(tmp_path, dispatcher, assure,
                          outcomes={'java': {'error': assure.SignalInterrupt(signal.SIGTERM)}})

    with pytest.raises(KeyboardInterrupt):
        run.execute()
    run.stages['interrupted'] = {'status': 'failed', 'reason': 'SIGTERM'}
    assert run.finish() == 1

    assert [event[1] for event in events if event[0] == 'execute'] == ['java']
    child = read(run.job.report / 'run.json')['children'][0]
    assert child['exit_code'] == 128 + signal.SIGTERM
    assert child['eligible_for_current_repository'] is False


def test_property_routing_uses_preexecution_snapshot(assure, tmp_path):
    source, root = tmp_path / 'source', tmp_path / 'workspace'
    source.mkdir()
    properties = tmp_path / 'request.json'
    original = property_manifest(claim('policy', 'f'))
    modified = property_manifest(dict(claim('policy', 'f'), statement='False'))
    write(properties, original)
    captured = []

    class CapturingJob(assure.Assurance):
        def run(self, name, command, **kwargs):
            self.stages[name] = {'status': 'failed', 'exit_code': 1}
            if name == 'source':
                write(self.report / 'pipeline.json', {'stage': 'runtime'})
                write(self.report / ('ast-' + self.module + '.json'), [fn(name='f', file='f.py')])
                write(properties, modified)
            return 1

        def check_security(self, conformance_ready):
            captured.append(read(self.report / 'properties.json'))

        def finish(self):
            return 1

    job = CapturingJob(source, 'Frozen', root=root, properties=properties, route_properties=True)

    assert job.execute() == 1

    assert read(properties) == modified
    assert captured == [original]
    assert job.property_selection['routed_claim_ids'] == ['policy']
