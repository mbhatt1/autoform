"""Real native faults must not terminate or stall the assurance driver."""
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

import pytest

from conftest import SCRIPTS


@pytest.fixture
def native(differential):
    if not shutil.which('cc'):
        pytest.skip('C compiler unavailable')
    import native_c
    return native_c


def function(name, file='native.c', args=(), result='i32'):
    return dict(name=name, sourceName=name, file=file,
                params=['a%d' % i for i in range(len(args))],
                paramIntegerTypes=list(args), returnIntegerType=result)


def test_worker_descriptor_failure_is_reported(native, monkeypatch):
    def unavailable():
        raise OSError('file descriptor limit reached')
    monkeypatch.setattr(native.os, 'pipe', unavailable)
    assert native.worker({}) == dict(status='launch_error', detail='file descriptor limit reached')


def test_library_initializers_and_calls_execute_outside_parent(tmp_path, native):
    source = tmp_path / 'source'
    source.mkdir()
    (source / 'native.c').write_text('''
#include <unistd.h>
static int initialized_by;
__attribute__((constructor)) static void initialize(void) { initialized_by = getpid(); }
int owner(void) { return initialized_by; }
''')
    f = function('owner')
    library = native.compile_sources(source, [f], tmp_path / 'work')
    assert library(f)() != os.getpid(), 'constructor or function ran in the driver'


def test_native_results_preserve_width_state_and_output_channel(tmp_path, native):
    source = tmp_path / 'source'
    source.mkdir()
    (source / 'native.c').write_text('''
#include <stdio.h>
static int n;
int next(void) { printf("noise, not a result\\n"); fprintf(stderr, "diagnostic\\n"); return ++n; }
unsigned long long wide(void) { return 18446744073709551615ULL; }
long long echo(long long a) { return a; }
''')
    fs = [function('next'), function('wide', result='u64'), function('echo', args=['i64'], result='i64')]
    library = native.compile_sources(source, fs, tmp_path / 'work')
    assert library(fs[0]).observe([], repeat=2) == dict(status='ok', values=[1, 2])
    assert library(fs[0]).observe([]) == dict(status='ok', values=[1])
    assert library(fs[1])() == 18446744073709551615
    assert library(fs[2])(-9223372036854775808) == -9223372036854775808


def test_parent_deadline_and_crash_results(tmp_path, native, differential):
    source = tmp_path / 'source'
    source.mkdir()
    (source / 'native.c').write_text('''
#include <signal.h>
#include <unistd.h>
int spin(void) { signal(SIGALRM, SIG_IGN); alarm(0); for (;;) {} }
int crash(void) { raise(SIGSEGV); return 0; }
int no_result(void) { _exit(0); }
int healthy(void) { return 17; }
''')
    fs = [function(n) for n in ('spin', 'crash', 'no_result', 'healthy')]
    library = native.compile_sources(source, fs, tmp_path / 'work')
    assert library(fs[0]).observe([], timeout=0.3)['status'] == 'timeout'
    failed = library(fs[1]).observe([])
    assert failed['status'] == 'signal' and failed['signal'] > 0
    assert library(fs[2]).observe([])['status'] == 'protocol_error'
    assert library(fs[3])() == 17
    values, repeated, execution = differential.observe_c_plan(library, [(fs[2], []), (fs[3], [])])
    assert values == {1: 17} and repeated == {}
    assert execution['outcomes'] == {'protocol_error': 1, 'ok': 1}
    assert execution['failures'][0]['function'] == 'no_result'
    assert execution['failures'][0]['args'] == []


def test_native_descendant_cannot_keep_result_pipe_or_resources(tmp_path, native):
    import fcntl
    source = tmp_path / 'source'
    source.mkdir()
    lock = tmp_path / 'descendant.lock'
    (source / 'native.c').write_text('''
#include <sys/file.h>
#include <fcntl.h>
#include <unistd.h>
int spawn(void) {
    int ready[2];
    if (pipe(ready)) return -1;
    int child = fork();
    if (child == 0) {
        close(ready[0]);
        int fd = open(LOCK_PATH, O_CREAT | O_RDWR, 0600);
        if (fd < 0 || flock(fd, LOCK_EX)) _exit(1);
        write(ready[1], "x", 1);
        for (;;) pause();
    }
    close(ready[1]);
    char c;
    if (read(ready[0], &c, 1) != 1) return -1;
    close(ready[0]);
    return child;
}
'''.replace('LOCK_PATH', json.dumps(str(lock))))
    f = function('spawn')
    library = native.compile_sources(source, [f], tmp_path / 'work')
    result = library(f).observe([], timeout=1)
    assert result['status'] == 'ok' and result['values'][0] > 0
    # A killed process releases its file locks even if the system has not yet
    # reaped its zombie. PID existence alone would be a flaky liveness check.
    deadline = time.monotonic() + 2
    with lock.open('r+') as handle:
        while True:
            try:
                fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                if time.monotonic() >= deadline:
                    pytest.fail('native descendant retained its file lock')
                time.sleep(0.01)


def test_constructor_exit_cannot_kill_driver_and_other_units_survive(tmp_path, native):
    source = tmp_path / 'source'
    source.mkdir()
    (source / 'bad.c').write_text('''
#include <unistd.h>
__attribute__((constructor)) static void initialize(void) { _exit(23); }
int bad(void) { return 1; }
''')
    (source / 'good.c').write_text('int good(void) { return 7; }')
    fs = [function('bad', 'bad.c'), function('good', 'good.c')]
    # Running the driver in a separate process also makes this a safe regression
    # test of the old implementation, whose dlopen invoked _exit in its parent.
    driver = '''import json,sys
sys.path.insert(0, sys.argv[1])
import native_c
fs=json.loads(sys.argv[3])
lib=native_c.compile_sources(sys.argv[2],fs,sys.argv[4])
print(json.dumps({'good':lib(fs[1])(), 'bad_available':lib(fs[0]) is not None, 'info':lib.info}))
'''
    proc = subprocess.run([sys.executable, '-c', driver, SCRIPTS, str(source), json.dumps(fs),
                           str(tmp_path / 'work')], capture_output=True, text=True, timeout=30)
    assert proc.returncode == 0, proc.stdout + proc.stderr
    result = json.loads(proc.stdout)
    assert result['good'] == 7 and not result['bad_available']
    failure = result['info']['combined_build']['load_result']
    assert failure['status'] == 'exit' and failure['exit_code'] == 23


def test_constructor_timeout_is_reported(tmp_path, native, monkeypatch):
    monkeypatch.setattr(native, 'DEFAULT_TIMEOUT', 0.3)
    source = tmp_path / 'source'
    source.mkdir()
    (source / 'native.c').write_text('''
__attribute__((constructor)) static void initialize(void) { for (;;) {} }
int never(void) { return 1; }
''')
    f = function('never')
    library = native.compile_sources(source, [f], tmp_path / 'work')
    assert library(f) is None
    assert library.info['combined_build']['load_result']['status'] == 'timeout'
    assert library.info['units'][0]['load_result']['status'] == 'timeout'


def test_legacy_runtime_uses_the_same_worker(tmp_path, differential):
    (tmp_path / 'native.c').write_text('''
#include <unistd.h>
int owner(void) { return getpid(); }
''')
    f = function('owner')
    library = differential.c_runtime(str(tmp_path))
    assert library(f)() != os.getpid()
