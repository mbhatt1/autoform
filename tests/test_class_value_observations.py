"""Only exact, recovered class identities can enter callable-valued proofs."""
from pathlib import Path

import pytest

from conftest import SCRIPTS, load


@pytest.fixture
def synth(monkeypatch):
    monkeypatch.setenv('AUTOFORM_NO_REEXEC', '1')
    return load(str(Path(SCRIPTS) / 'synth_specs.py'), 'af_synth_class_values')


def test_exact_class_outcomes_are_provable_without_admitting_functions(synth, tmp_path):
    first = 'first.py:<module>.Same'
    second = 'second.py:<module>.Same'
    funcs = [{'classDeclarations': [{'name': first}, {'name': second}]}]
    report = {'runtime': 'cpython',
              'measurement_basis': 'python-class-slots-v6+class-values-v1+trace-returns-v1'}
    admitted = synth.conformance_class_values(funcs, tmp_path, report)
    assert admitted == {first + '<meta>', second + '<meta>'}
    for name in admitted:
        outcome = ['val', ['fn', name]]
        assert not synth.outcome_has_callable(outcome, admitted)
        assert synth.outcome_has_callable(outcome)
        assert not synth.outcome_has_callable(['val', ['tuple', [outcome[1]]]], admitted)
        assert not synth.outcome_has_callable(
            ['val', ['dict', [[['str', 'owner'], outcome[1]]]]], admitted)
    for name in ['Same<meta>', 'unknown.py:<module>.Same<meta>', 'first.py:<module>.callback']:
        assert synth.outcome_has_callable(['val', ['fn', name]], admitted)
    assert synth.outcome_has_callable(
        ['val', ['tuple', [['fn', first + '<meta>'], ['fn', 'callback']]]], admitted)


def test_old_or_other_runtime_evidence_does_not_gain_class_proofs(synth, tmp_path):
    funcs = [{'classDeclarations': [{'name': 'first.py:<module>.Same'}]}]
    for report in [
        {'runtime': 'cpython', 'measurement_basis': 'python-class-slots-v6+trace-returns-v1'},
        {'runtime': 'node', 'measurement_basis': 'class-values-v1'},
        {'runtime': 'cpython', 'measurement_basis': 'not-class-values-v1'},
        {},
    ]:
        assert not synth.conformance_class_values(funcs, tmp_path, report)


def test_ambiguous_class_identity_remains_unprovable(synth, tmp_path):
    row = {'name': 'first.py:<module>.Same'}
    report = {'runtime': 'cpython', 'measurement_basis': 'class-values-v1'}
    assert not synth.conformance_class_values([{'classDeclarations': [row, row]}], tmp_path, report)
    assert not synth.conformance_class_values([{'name': 'legacy'}], tmp_path, report)
