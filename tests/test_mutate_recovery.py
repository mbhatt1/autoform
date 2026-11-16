"""Recovery paths of scripts/mutate.py, and the audit's line-number helper.

A mutation run owns its module through a `<file>.mutate-backup` marker. Until the
changes these tests pin, only Ctrl-C ran the restore path: a `kill` or a CI cancel left
the mutant on disk with the marker set, the next run refused to start, and there was
no command that put the tree back. Separately, a restore build that merely timed out
was reported with the same `RESTORE_FAILED` status as one whose restored source does
not compile, which are different findings with different remedies.
"""
from __future__ import annotations

import json
import os
import random
import signal
from pathlib import Path

import pytest

from conftest import SCRIPTS, load


# ---------------------------------------------------------------------------
# --recover
# ---------------------------------------------------------------------------

ORIGINAL = 'def value : Nat := 1\ntheorem checked : value = 1 := rfl\n'
MUTATED = 'def value : Nat := 2\ntheorem checked : value = 1 := rfl\n'


def _stranded(tmp_path, current=MUTATED, backup=ORIGINAL):
    source = tmp_path / 'Check.lean'
    source.write_text(current)
    marker = tmp_path / 'Check.lean.mutate-backup'
    if backup is not None:
        marker.write_text(backup)
    (tmp_path / 'lakefile.toml').write_text('name = "test"\n')
    return source, marker


class TestRecover:
    def test_recover_function_restores_differing_backup(self, tmp_path, mutate):
        source, marker = _stranded(tmp_path)
        done = mutate.recover([str(source)])
        assert done == [(str(source), 'restored')]
        assert source.read_text() == ORIGINAL
        assert not marker.exists()

    def test_recover_function_removes_stale_marker_when_identical(self, tmp_path, mutate):
        source, marker = _stranded(tmp_path, current=ORIGINAL, backup=ORIGINAL)
        assert mutate.recover([str(source)]) == [(str(source), 'marker-removed')]
        assert source.read_text() == ORIGINAL
        assert not marker.exists()

    def test_recover_function_reports_nothing_without_backup(self, tmp_path, mutate):
        source, marker = _stranded(tmp_path, current=ORIGINAL, backup=None)
        assert mutate.recover([str(source)]) == []
        assert source.read_text() == ORIGINAL

    def test_recover_function_restores_a_file_that_was_deleted(self, tmp_path, mutate):
        # The marker is the only copy left; recovery must not require the file to exist.
        source, marker = _stranded(tmp_path)
        source.unlink()
        assert mutate.recover([str(source)]) == [(str(source), 'restored')]
        assert source.read_text() == ORIGINAL
        assert not marker.exists()

    def test_recover_flag_exit_0_and_names_restored_file(self, tmp_path, monkeypatch, mutate, capsys):
        source, marker = _stranded(tmp_path)
        monkeypatch.setattr('sys.argv', ['mutate.py', str(source), '--recover'])
        assert mutate.main() == 0
        out = capsys.readouterr().out
        assert str(source) in out and 'restored' in out
        assert 'lake build' in out, 'the operator must be told the .olean files are suspect'
        assert source.read_text() == ORIGINAL
        assert not marker.exists()

    def test_recover_flag_exit_1_when_nothing_to_recover(self, tmp_path, monkeypatch, mutate, capsys):
        source, _ = _stranded(tmp_path, current=ORIGINAL, backup=None)
        monkeypatch.setattr('sys.argv', ['mutate.py', str(source), '--recover'])
        assert mutate.main() == 1
        assert 'nothing to recover' in capsys.readouterr().out
        assert source.read_text() == ORIGINAL

    def test_recover_flag_does_not_need_a_module_name(self, tmp_path, monkeypatch, mutate):
        source, _ = _stranded(tmp_path)
        monkeypatch.setattr('sys.argv', ['mutate.py', str(source), '--recover'])
        assert mutate.main() == 0

    def test_module_name_still_required_without_recover(self, tmp_path, monkeypatch, mutate):
        source, _ = _stranded(tmp_path, current=ORIGINAL, backup=None)
        monkeypatch.setattr('sys.argv', ['mutate.py', str(source)])
        with pytest.raises(SystemExit) as exc:
            mutate.main()
        assert exc.value.code == 2

    def test_recover_does_not_run_a_build(self, tmp_path, monkeypatch, mutate):
        source, _ = _stranded(tmp_path)
        monkeypatch.setattr(mutate, 'run_build',
                            lambda *a, **k: pytest.fail('--recover must not invoke lake'))
        monkeypatch.setattr('sys.argv', ['mutate.py', str(source), '--recover'])
        assert mutate.main() == 0


# ---------------------------------------------------------------------------
# signals: SIGTERM/SIGHUP take the same restore path as Ctrl-C
# ---------------------------------------------------------------------------

@pytest.mark.skipif(os.name != 'posix', reason='signals are POSIX')
class TestSignals:
    def test_handlers_installed_and_restored(self, mutate):
        before = {s: signal.getsignal(getattr(signal, s)) for s in mutate.INTERRUPT_SIGNALS}
        previous = mutate.install_signal_handlers()
        try:
            for name in mutate.INTERRUPT_SIGNALS:
                assert signal.getsignal(getattr(signal, name)) is mutate._interrupt_on
        finally:
            mutate.restore_signal_handlers(previous)
        for name in mutate.INTERRUPT_SIGNALS:
            assert signal.getsignal(getattr(signal, name)) == before[name]

    def test_sigterm_becomes_keyboard_interrupt_naming_the_signal(self, mutate):
        previous = mutate.install_signal_handlers()
        try:
            if signal.getsignal(signal.SIGTERM) is not mutate._interrupt_on:
                pytest.skip('not the main thread: handlers cannot be installed here')
            with pytest.raises(KeyboardInterrupt) as exc:
                os.kill(os.getpid(), signal.SIGTERM)
                # The handler runs at the next bytecode boundary; give it one.
                for _ in range(1000):
                    pass
            assert exc.value.args == ('SIGTERM',)
        finally:
            mutate.restore_signal_handlers(previous)

    def test_sigterm_mid_mutant_restores_source_and_removes_marker(self, tmp_path, monkeypatch, mutate):
        source, _ = _stranded(tmp_path, current=ORIGINAL, backup=None)
        marker = tmp_path / 'Check.lean.mutate-backup'
        report = tmp_path / 'mutation.json'
        calls = []

        def build(root, module, timeout):
            calls.append(source.read_text())
            if len(calls) == 1:
                return 0, '', False          # baseline
            # A CI cancel arrives while the mutant is on disk and lake is running.
            assert marker.exists(), 'the marker must be set while a mutant is live'
            if signal.getsignal(signal.SIGTERM) is not mutate._interrupt_on:
                pytest.skip('not the main thread: handlers cannot be installed here')
            os.kill(os.getpid(), signal.SIGTERM)
            for _ in range(1000):
                pass
            pytest.fail('SIGTERM did not interrupt the build')

        monkeypatch.setattr(mutate, 'run_build', build)
        monkeypatch.setattr('sys.argv', ['mutate.py', str(source), 'Check', '--decls', 'value',
                                       '--subject', 'checked=value', '--max-mutants', '1',
                                       '--json', str(report)])
        with pytest.raises(KeyboardInterrupt):
            mutate.main()
        assert calls[1] != ORIGINAL, 'the second build must have seen the mutant'
        assert source.read_text() == ORIGINAL
        assert not marker.exists()
        assert not report.exists(), 'an interrupted run writes no report'
        # main() put the process's own handlers back on the way out.
        assert signal.getsignal(signal.SIGTERM) is not mutate._interrupt_on


# ---------------------------------------------------------------------------
# RESTORE_TIMEOUT vs RESTORE_FAILED
# ---------------------------------------------------------------------------

class TestRestoreStatus:
    @pytest.mark.parametrize('exit_code,timed_out,inconclusive,expected', [
        (0, False, 0, 'OK'),
        (0, False, 2, 'INCONCLUSIVE'),
        (1, False, 0, 'RESTORE_FAILED'),
        (1, False, 2, 'RESTORE_FAILED'),
        (1, True, 0, 'RESTORE_TIMEOUT'),
        (1, True, 2, 'RESTORE_TIMEOUT'),
        # run_build reports 1 on a timeout, but the classification must read the flag,
        # not infer it from the exit code.
        (0, True, 0, 'RESTORE_TIMEOUT'),
    ])
    def test_restore_status(self, mutate, exit_code, timed_out, inconclusive, expected):
        assert mutate.restore_status(exit_code, timed_out, inconclusive) == expected

    def _gate(self, tmp_path, monkeypatch, mutate, restore_result, extra_argv=()):
        source = tmp_path / 'Check.lean'
        source.write_text(ORIGINAL)
        (tmp_path / 'lakefile.toml').write_text('name = "test"\n')
        report = tmp_path / 'mutation.json'
        timeouts = []
        results = iter([(0, '', False), (1, 'Check.lean:2:0: error: goal failed', False),
                        restore_result])

        def build(root, module, timeout):
            timeouts.append(timeout)
            return next(results)

        monkeypatch.setattr(mutate, 'run_build', build)
        monkeypatch.setattr('sys.argv', ['mutate.py', str(source), 'Check', '--decls', 'value',
                                       '--subject', 'checked=value', '--max-mutants', '1',
                                       '--json', str(report), *extra_argv])
        code = mutate.main()
        return code, json.loads(report.read_text()), timeouts

    def test_timed_out_restore_is_not_reported_as_failed(self, tmp_path, monkeypatch, mutate, capsys):
        code, data, _ = self._gate(tmp_path, monkeypatch, mutate, (1, '', True))
        assert data['status'] == 'RESTORE_TIMEOUT'
        assert data['restored_build']['timeout'] is True
        assert data['restored_build']['status'] == 'RESTORE_TIMEOUT'
        # The verdicts stand: the theorem did kill its mutant.
        assert data['theorems']['checked']['verdict'] == 'HAS TEETH'
        assert data['mutants'][0]['verdict'] == {'checked': 'killed'}
        # ...but the tree's build state is unverified, so the gate does not pass.
        assert code != 0
        out = capsys.readouterr().out
        assert 'RESTORE TIMED OUT' in out and 'lake build Check' in out
        assert 'RESTORE FAILED' not in out

    def test_failed_restore_without_timeout_stays_restore_failed(self, tmp_path, monkeypatch, mutate):
        code, data, _ = self._gate(tmp_path, monkeypatch, mutate, (1, 'restored build failed', False))
        assert code != 0
        assert data['status'] == 'RESTORE_FAILED'
        assert data['restored_build']['status'] == 'RESTORE_FAILED'
        assert data['restored_build']['timeout'] is False

    def test_report_keeps_the_fields_downstream_readers_use(self, tmp_path, monkeypatch, mutate):
        # scripts/sacm.py, guarantee.py and security_specs.py read these; adding fields
        # is fine, renaming or dropping them is not.
        _, data, _ = self._gate(tmp_path, monkeypatch, mutate, (0, '', False))
        assert data['status'] == 'OK'
        assert data['restored_build']['exit_code'] == 0
        assert data['restored_build']['timeout'] is False
        assert data['restored_build']['status'] == 'OK'
        assert set(data['restored_build']) >= {'exit_code', 'timeout', 'build_tail', 'timeout_s'}

    def test_restore_timeout_defaults_to_three_times_timeout(self, tmp_path, monkeypatch, mutate):
        _, data, timeouts = self._gate(tmp_path, monkeypatch, mutate, (0, '', False),
                                       extra_argv=['--timeout', '7'])
        assert timeouts == [7, 7, 21], '(baseline, mutant, restore)'
        assert data['restored_build']['timeout_s'] == 21

    def test_restore_timeout_flag_is_honoured(self, tmp_path, monkeypatch, mutate):
        _, data, timeouts = self._gate(tmp_path, monkeypatch, mutate, (0, '', False),
                                       extra_argv=['--timeout', '7', '--restore-timeout', '5'])
        assert timeouts == [7, 7, 5]
        assert data['restored_build']['timeout_s'] == 5


# ---------------------------------------------------------------------------
# the KILLED/SURVIVED log mark is gated by subject whenever a subject map exists
# ---------------------------------------------------------------------------

def test_log_mark_follows_the_subject_map_in_default_mode(tmp_path, monkeypatch, mutate, capsys):
    # Two theorems, two subjects. A mutant of `a` is killed by `ta` and (as expected)
    # survives `tb`, which is not about `a`. Before the fix the mark read SURVIVED in
    # default mode because `tb`'s survival was counted against the mutant.
    source = tmp_path / 'Check.lean'
    original = ('def a : Nat := 1\ndef b : Nat := 2\n'
                'theorem ta : a = 1 := rfl\ntheorem tb : b = 2 := rfl\n')
    source.write_text(original)
    (tmp_path / 'lakefile.toml').write_text('name = "test"\n')
    report = tmp_path / 'mutation.json'
    monkeypatch.setattr(mutate, 'run_build', lambda *args:
                        (0, '', False) if source.read_text() == original else
                        (1, 'Check.lean:3:0: error: goal failed', False))
    monkeypatch.setattr('sys.argv', ['mutate.py', str(source), 'Check', '--decls', 'a',
                                   '--subject', 'ta=a;tb=b', '--max-mutants', '1',
                                   '--json', str(report)])
    mutate.main()
    data = json.loads(report.read_text())
    assert data['mutants'][0]['verdict'] == {'ta': 'killed', 'tb': 'survived'}
    marks = [l for l in capsys.readouterr().out.splitlines() if l.startswith('[1/1]')]
    assert len(marks) == 1 and 'KILLED' in marks[0], marks


# ---------------------------------------------------------------------------
# audit_all: line numbers from a newline table
# ---------------------------------------------------------------------------

class TestAuditLineNumbers:
    def test_matches_count_based_definition(self):
        audit = load(str(Path(SCRIPTS) / 'audit_all.py'), 'af_audit_lines')
        rng = random.Random(20261113)
        for _ in range(50):
            text = ''.join(rng.choice('ab\n\n ') for _ in range(rng.randint(0, 200)))
            offsets = audit.newline_offsets(text)
            for pos in range(len(text) + 1):
                assert audit.line_of(offsets, pos) == text.count('\n', 0, pos) + 1, (text, pos)

    def test_edge_cases(self):
        audit = load(str(Path(SCRIPTS) / 'audit_all.py'), 'af_audit_lines')
        assert audit.newline_offsets('') == []
        assert audit.line_of([], 0) == 1
        assert audit.line_of([], 17) == 1
        offsets = audit.newline_offsets('x\ny\n')
        assert offsets == [1, 3]
        assert audit.line_of(offsets, 0) == 1
        assert audit.line_of(offsets, 1) == 1   # the newline itself ends line 1
        assert audit.line_of(offsets, 2) == 2
        assert audit.line_of(offsets, 4) == 3   # one past the final newline

    def test_source_sweep_reports_the_right_line(self, tmp_path, monkeypatch):
        audit = load(str(Path(SCRIPTS) / 'audit_all.py'), 'af_audit_lines')
        file = tmp_path / 'Autoform' / 'Lang' / 'Core' / 'Semantics.lean'
        file.parent.mkdir(parents=True)
        file.write_text('import Foo\n\n/- a comment\n   over lines -/\npartial def loop : Nat := loop\n')
        monkeypatch.setattr(audit, 'REPO', tmp_path)
        findings = audit.source_sweep()['findings']
        assert [(f['kind'], f['line'], f['text']) for f in findings] == \
            [('partial', 5, 'partial def loop : Nat := loop')]


def test_skip_lean_verdict_names_what_was_skipped(tmp_path, monkeypatch, capsys):
    audit = load(str(Path(SCRIPTS) / 'audit_all.py'), 'af_audit_verdict')
    (tmp_path / 'Autoform' / 'Lang' / 'Core').mkdir(parents=True)
    (tmp_path / 'Autoform' / 'Lang' / 'Core' / 'Clean.lean').write_text('def ok : Nat := 0\n')
    report = tmp_path / 'audit.json'
    monkeypatch.setattr(audit, 'REPO', tmp_path)
    monkeypatch.setattr('sys.argv', ['audit_all.py', '--skip-lean', '-o', str(report)])
    assert audit.main() == 0
    out = capsys.readouterr().out
    verdict = [l for l in out.splitlines() if l.startswith('VERDICT:')]
    assert verdict == ['VERDICT: PASS (source sweep only; axiom sweep and kernel replay SKIPPED)']
    assert 'no trusted-code leak' not in out
    data = json.loads(report.read_text())
    assert data['axiom_sweep']['status'] == 'SKIPPED'
    assert data['lean4checker']['status'] == 'SKIPPED'
