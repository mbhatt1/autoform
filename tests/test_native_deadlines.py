"""Harness deadlines must interrupt sampling without becoming native observations."""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import threading
import time

import pytest

from conftest import ROOT


@pytest.mark.skipif(not hasattr(signal, 'setitimer'), reason='POSIX signal deadlines')
def test_deadline_interrupts_and_restores_signal_handler(differential):
    original = signal.getsignal(signal.SIGALRM)
    with pytest.raises(differential.Timeout):
        with differential.time_limit(0.03):
            time.sleep(2)
    assert signal.getsignal(signal.SIGALRM) == original
    assert signal.getitimer(signal.ITIMER_REAL) == (0.0, 0.0)


def test_worker_thread_refuses_before_executing_native_code(differential):
    observations = []

    def worker():
        try:
            with differential.time_limit(0.03):
                observations.append('unguarded execution')
        except differential.DeadlineUnavailable:
            observations.append('refused')

    thread = threading.Thread(target=worker)
    thread.start()
    thread.join(timeout=2)
    assert not thread.is_alive()
    assert observations == ['refused']


@pytest.mark.skipif(not hasattr(signal, 'setitimer'), reason='POSIX signal deadlines')
def test_cli_deadline_handles_deep_ast_without_reporting_source_exception(tmp_path):
    source = tmp_path / 'source'
    source.mkdir()
    (source / 'probe.py').write_text('def blocked(value):\n    while True:\n        pass\n')
    # Far deeper than Python's ordinary recursion limit. Native sampling must still
    # run on the main thread; deep source syntax no longer justifies a worker thread.
    body = ('{"k":"seq","ss":[{"k":"skip"},' * 3000
            + '{"k":"ret","e":{"k":"int","v":0}}' + ']}' * 3000)
    ast = tmp_path / 'ast.json'
    ast.write_text('[{"name":"probe.py:<module>.blocked","file":"probe.py",'
                   '"params":["value"],"body":' + body + '}]')
    result = subprocess.run([sys.executable, str(Path(ROOT) / 'scripts/differential.py'),
                             str(ast), str(source), 'DeadlineProbe', '1'],
                            cwd=tmp_path, env=dict(os.environ, PYTHONHASHSEED='0'),
                            text=True, capture_output=True, timeout=12)
    assert result.returncode == 2, result.stdout + result.stderr
    report = json.loads((tmp_path / 'conformance.json').read_text())
    assert report['total'] == 0
    assert report['agree'] == report['divergences'] == 0
    assert report['cases'] == 0
    assert report['skipped']['skip_native_timeout'] == 1
    assert report['native_deadline_detail'][0]['function'] == 'probe.py:<module>.blocked'
    # A synthetic AST without `classDeclarations` is a legacy model: compared by result
    # only, so no `heap-graph-v1` basis is claimed for it.
    assert report['measurement_basis'] == 'python-deadlines-v4+trace-returns-v1'
    assert report['native_call_deadline']['seconds'] == 2.0
    assert report['status'] == 'INCONCLUSIVE: no runtime comparisons'
