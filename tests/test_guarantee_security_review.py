"""Malformed or misattributed proof summaries must not become certificates."""
import copy
import json

import pytest

from test_assurance import guarantee_case
from test_security_specs import security, security_certificate


def rewrite_bound(root, report, audit, name, value, digest):
    path = report / name
    path.write_text(json.dumps(value))
    audit['artifact_snapshot']['files'][str(path.relative_to(root))] = digest(path)


MUTATION_DEFECTS = (
    'negative_killed', 'boolean_killed', 'string_killed', 'missing_survived',
    'boolean_survived', 'negative_inconclusive', 'wrong_scope', 'wrong_subject',
    'missing_records', 'wrong_record_subject', 'record_survived', 'record_inconclusive',
    'record_count', 'invalid_count', 'boolean_global_count', 'record_timeout',
    'boolean_restore_exit', 'restore_timeout',
)


def damage_mutation(mutation, theorem, defect):
    result = mutation['theorems'][theorem]
    if defect == 'negative_killed':
        result['killed'] = -1
    elif defect == 'boolean_killed':
        result['killed'] = True
    elif defect == 'string_killed':
        result['killed'] = '1'
    elif defect == 'missing_survived':
        del result['survived']
    elif defect == 'boolean_survived':
        result['survived'] = False
    elif defect == 'negative_inconclusive':
        result['inconclusive'] = -1
    elif defect == 'wrong_scope':
        result['scope'] = 'all-mutants'
    elif defect == 'wrong_subject':
        mutation['subject_map'][theorem] = ['f_unrelated']
    elif defect == 'missing_records':
        del mutation['mutants']
    elif defect == 'wrong_record_subject':
        mutation['mutants'][0]['decl'] = 'f_unrelated'
    elif defect == 'record_survived':
        mutation['mutants'][0]['verdict'][theorem] = 'survived'
    elif defect == 'record_inconclusive':
        mutation['mutants'][0]['verdict'] = 'inconclusive'
    elif defect == 'record_count':
        mutation['mutants_run'] = 2
    elif defect == 'invalid_count':
        mutation['invalid'] = 1
    elif defect == 'boolean_global_count':
        mutation['inconclusive'] = False
    elif defect == 'record_timeout':
        mutation['mutants'][0]['timeout'] = True
    elif defect == 'boolean_restore_exit':
        mutation['restored_build']['exit_code'] = False
    elif defect == 'restore_timeout':
        mutation['restored_build']['timeout'] = True


@pytest.mark.parametrize('defect', MUTATION_DEFECTS)
def test_conformance_certificate_rejects_inconsistent_mutation_evidence(tmp_path, guarantee_case, defect):
    guarantee, source, report, stages, audit = guarantee_case
    mutation = guarantee.read(report / 'mutation.json')
    damage_mutation(mutation, 'conform_f', defect)
    rewrite_bound(tmp_path, report, audit, 'mutation.json', mutation, guarantee.proof_artifacts.digest)
    (report / 'audit.json').write_text(json.dumps(audit))
    result = guarantee.emit(tmp_path, report, 'Check', source, stages)
    assert result['status'] == 'unverified' and result['claims'] == []
    assert any('mutation' in failure or 'adequacy' in failure for failure in result['failed_checks'])
    assert not any('artifact changed' in failure for failure in result['failed_checks'])


@pytest.mark.parametrize('defect', MUTATION_DEFECTS)
def test_security_certificate_rejects_inconsistent_mutation_evidence(
        tmp_path, security, security_certificate, defect):
    source, report, stages, audit, mutation, _ = security_certificate
    damage_mutation(mutation, 'property_owner_only', defect)
    rewrite_bound(tmp_path, report, audit, 'security-mutation.json', mutation, security.proof_artifacts.digest)
    security.write(report / 'security-audit.json', audit)
    result = security.certify(tmp_path, report, source, 'Check', stages)
    assert result['status'] == 'unverified' and result['claims'] == []
    assert any('mutation' in failure for failure in result['failed_checks'])
    assert 'security replay artifacts are missing or changed' not in result['failed_checks']


@pytest.mark.parametrize('stages', [None, [], {'source': None}, {'source': []},
                                  {'source': {'status': 'completed', 'exit_code': False}},
                                  {'source': {'status': 'completed', 'exit_code': 0, 'timed_out': True}}])
def test_malformed_stage_evidence_withholds_conformance_without_crashing(tmp_path, guarantee_case, stages):
    guarantee, source, report, _, _ = guarantee_case
    result = guarantee.emit(tmp_path, report, 'Check', source, stages)
    assert result['status'] == 'unverified' and 'source' in result['failed_checks']


@pytest.mark.parametrize('field,value', [('proved', 0), ('proved', True), ('proved', None),
                                        ('open_obligations', 17), ('open_obligations', False),
                                        ('open_obligations', -1), ('open_obligations', '0')])
def test_security_counts_must_match_the_exact_claim_inventory(
        tmp_path, security, security_certificate, field, value):
    source, report, stages, audit, _, specs = security_certificate
    specs[field] = value
    rewrite_bound(tmp_path, report, audit, 'security-claims.json', specs, security.proof_artifacts.digest)
    security.write(report / 'security-audit.json', audit)
    result = security.certify(tmp_path, report, source, 'Check', stages)
    assert result['status'] == 'unverified' and result['claims'] == []
    assert 'independent property counts disagree with the claim inventory' in result['failed_checks']


@pytest.mark.parametrize('defect', ['duplicate', 'wrong_definition', 'overstated_cases'])
def test_conformance_claim_inventory_cannot_be_duplicated_or_misattributed(tmp_path, guarantee_case, defect):
    guarantee, source, report, stages, audit = guarantee_case
    specs = guarantee.read(report / 'specs.json')
    if defect == 'duplicate':
        specs['specs'].append(copy.deepcopy(specs['specs'][0]))
    elif defect == 'wrong_definition':
        specs['specs'][0]['definition'] = 'f_unrelated'
    else:
        specs['specs'][0]['domain'] = 2
    rewrite_bound(tmp_path, report, audit, 'specs.json', specs, guarantee.proof_artifacts.digest)
    (report / 'audit.json').write_text(json.dumps(audit))
    result = guarantee.emit(tmp_path, report, 'Check', source, stages)
    assert result['status'] == 'unverified' and result['claims'] == []


def test_boolean_conformance_replay_exit_code_is_not_success(tmp_path, guarantee_case):
    guarantee, source, report, stages, audit = guarantee_case
    audit['lean4checker']['returncode'] = False
    (report / 'audit.json').write_text(json.dumps(audit))
    result = guarantee.emit(tmp_path, report, 'Check', source, stages)
    assert result['status'] == 'unverified'


def test_boolean_security_replay_exit_code_is_not_success(tmp_path, security, security_certificate):
    source, report, stages, audit, *_ = security_certificate
    audit['lean4checker']['returncode'] = False
    security.write(report / 'security-audit.json', audit)
    result = security.certify(tmp_path, report, source, 'Check', stages)
    assert result['status'] == 'unverified'


def test_missing_requested_security_claim_cannot_be_hidden_by_consistent_counts(
        tmp_path, security, security_certificate):
    source, report, stages, audit, _, specs = security_certificate
    requested = security.read(report / 'properties.json')
    second = dict(requested['claims'][0], id='second', statement='False')
    requested['claims'].append(second)
    rewrite_bound(tmp_path, report, audit, 'properties.json', requested, security.proof_artifacts.digest)
    specs['artifact_hashes']['properties'] = security.proof_artifacts.digest(report / 'properties.json')
    rewrite_bound(tmp_path, report, audit, 'security-claims.json', specs, security.proof_artifacts.digest)
    security.write(report / 'security-audit.json', audit)
    result = security.certify(tmp_path, report, source, 'Check', stages)
    assert result['status'] == 'unverified' and result['claims'] == []
    assert any('inventory differs' in failure for failure in result['failed_checks'])
