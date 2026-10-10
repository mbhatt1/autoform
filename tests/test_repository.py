"""Git URL acquisition uses a pinned, isolated checkout and reports failures."""
import json
from pathlib import Path
import subprocess
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from autoform import repository


def git(path, *args):
    return subprocess.check_output(['git', '-C', str(path), *args], text=True).strip()


def make_remote(tmp_path):
    remote = tmp_path / 'remote'
    remote.mkdir()
    subprocess.run(['git', 'init', '-q', str(remote)], check=True)
    git(remote, 'config', 'user.name', 'Autoform Test')
    git(remote, 'config', 'user.email', 'test@example.invalid')
    source = remote / 'lib'
    source.mkdir()
    headers = remote / 'tools/testing'
    headers.mkdir(parents=True)
    (headers / 'shared.h').write_text('#define FIXTURE 7\n')
    (source / 'f.c').write_text('int f(void) { return 7; }\n')
    git(remote, 'add', '.')
    git(remote, 'commit', '-qm', 'fixture')
    git(remote, 'tag', '-a', 'tested', '-m', 'annotated release fixture')
    return remote


def test_url_checkout_pins_requested_revision_and_subdirectory(tmp_path):
    remote = make_remote(tmp_path)
    commit = git(remote, 'rev-parse', 'HEAD')
    (remote / 'lib/f.c').write_text('int f(void) { return 9; }\n')
    git(remote, 'commit', '-qam', 'next')
    workspace = tmp_path / 'workspace'
    source, record = repository.resolve_source(remote.as_uri(), workspace, 'Check',
                                               ref='tested', subdir='lib')
    assert record['commit'] == commit
    assert 'return 7' in (source / 'f.c').read_text()
    assert 'return 9' in (remote / 'lib/f.c').read_text()
    assert source.is_relative_to(workspace)
    assert (source.parent / 'tools/testing/shared.h').is_file()
    assert record['status'] == 'ready'


@pytest.mark.parametrize('subdir', ['../outside', '/tmp', 'missing'])
def test_checkout_scope_cannot_escape_or_silently_fall_back(tmp_path, subdir):
    source = tmp_path / 'source'
    source.mkdir()
    workspace = tmp_path / 'workspace'
    with pytest.raises(ValueError, match='subdir'):
        repository.resolve_source(str(source), workspace, 'Check', subdir=subdir)
    report = json.loads((workspace / 'artifacts/pipeline/Check/repository.json').read_text())
    assert report['status'] == 'failed'


def test_failed_clone_leaves_a_failure_record(tmp_path):
    workspace = tmp_path / 'workspace'
    with pytest.raises(ValueError, match='Git checkout failed'):
        repository.resolve_source((tmp_path / 'absent').as_uri(), workspace, 'Check')
    report = json.loads((workspace / 'artifacts/pipeline/Check/repository.json').read_text())
    assert report['status'] == 'failed' and 'commit' not in report


def test_url_detection_preserves_scp_and_local_paths():
    assert repository.is_git_url('git@example.com:owner/project.git')
    assert repository.is_git_url('https://example.com/owner/project.git')
    assert not repository.is_git_url('/path/with spaces/source')
    assert not repository.is_git_url('ext::sh command')
    assert repository.display_url('https://secret@example.com/p.git?token=secret') == 'https://example.com/p.git'


def test_concurrent_cli_run_preserves_existing_evidence(tmp_path, capsys):
    import fcntl
    from autoform import cli
    workspace = cli.prepare_workspace(tmp_path / 'workspace')
    report = workspace / 'artifacts/pipeline/Busy'
    report.mkdir(parents=True)
    verdict = report / 'guarantee.json'
    verdict.write_text('{"existing": true}')
    with (report / '.run.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        assert cli.main(['--workspace', str(workspace), 'assure', str(tmp_path), 'Busy']) == 2
    assert 'already in progress' in capsys.readouterr().err
    assert json.loads(verdict.read_text()) == {'existing': True}


def test_workspace_lock_rejects_different_module_before_evidence_changes(tmp_path, monkeypatch, capsys):
    import fcntl
    from autoform import cli

    workspace = cli.prepare_workspace(tmp_path / 'workspace')
    reports = workspace / 'artifacts/pipeline'
    original = {}
    for module in ('Busy', 'Different'):
        report = reports / module
        report.mkdir(parents=True)
        for name in ('guarantee.json', 'inventory.json', 'inventory-after.json',
                     'source-coverage.json', 'selection.json', 'repository-summary.json'):
            path = report / name
            original[path] = json.dumps({'existing': module, 'artifact': name}).encode()
            path.write_bytes(original[path])

    def acquisition_must_not_start(*args, **kwargs):
        pytest.fail('source acquisition began while another module held the workspace lock')

    monkeypatch.setattr(cli, 'resolve_source', acquisition_must_not_start)
    with (workspace / '.autoform-run.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        assert cli.main(['--workspace', str(workspace), 'assure', str(tmp_path), 'Different']) == 2
    assert 'a run in this workspace is already in progress' in capsys.readouterr().err
    assert {path: path.read_bytes() for path in original} == original
    assert set(path for path in reports.rglob('*') if path.is_file()) == set(original)


@pytest.mark.parametrize('source_kind', ['missing_remote', 'malformed_url'])
def test_failed_acquisition_removes_prior_repository_scope_evidence(tmp_path, source_kind):
    from autoform import cli

    workspace = cli.prepare_workspace(tmp_path / 'workspace')
    report = workspace / 'artifacts/pipeline/Check'
    report.mkdir(parents=True)
    stale = ('inventory.json', 'inventory-after.json', 'source-coverage.json',
             'selection.json', 'repository-summary.json')
    for name in stale:
        (report / name).write_text('{"prior_run": true}')
    (report / 'guarantee.json').write_text('{"status":"verified_scoped","claims":["old"]}')
    source = (tmp_path / 'absent.git').as_uri() if source_kind == 'missing_remote' else 'https://[invalid'
    assert cli.main(['--workspace', str(workspace), source, 'Check']) == 2
    assert not any((report / name).exists() for name in stale)
    assert json.loads((report / 'run.json').read_text())['execution_status'] == 'acquisition_failed'
    assert json.loads((report / 'repository.json').read_text())['status'] == 'failed'
    guarantee = json.loads((report / 'guarantee.json').read_text())
    assert guarantee['status'] == 'unverified' and guarantee['claims'] == []


@pytest.mark.parametrize('signum', ['SIGINT', 'SIGTERM'])
def test_outer_cli_cancellation_waits_for_assurance_cleanup(tmp_path, signum):
    import fcntl
    import io
    import os
    import signal
    import time
    import zipfile
    from autoform import cli

    source, workspace = tmp_path / 'source', tmp_path / 'workspace'
    source.mkdir()
    ready, cleanup, resource = source / 'ready.json', source / 'cleanup', source / 'resource.lock'
    (source / 'worker.py').write_text(
        'import fcntl,json,os,pathlib,signal,time\n'
        f'cleanup=pathlib.Path({str(cleanup)!r})\n'
        'def interrupted(signum, frame):\n'
        '    cleanup.write_text("restoring")\n'
        '    time.sleep(0.7)\n'
        '    raise SystemExit(130)\n'
        'signal.signal(signal.SIGINT, interrupted)\n'
        f'stream=open({str(resource)!r}, "w")\n'
        'fcntl.flock(stream, fcntl.LOCK_EX)\n'
        f'pathlib.Path({str(ready)!r}).write_text(json.dumps(dict(pid=os.getpid(), parent=os.getppid())))\n'
        'time.sleep(60)\n')
    payload = tmp_path / 'runtime.zip'
    with zipfile.ZipFile(io.BytesIO(cli.runtime_payload())) as original, zipfile.ZipFile(payload, 'w') as archive:
        for name in original.namelist():
            content = (b'exec "$AUTOFORM_PYTHON" "$1/worker.py"\n'
                       if name == 'autoform.sh' else original.read(name))
            archive.writestr(name, content)
    driver = ('import sys\nfrom pathlib import Path\n'
              f'sys.path.insert(0, {str(Path(__file__).resolve().parents[1] / "src")!r})\n'
              'from autoform import cli\n'
              f'cli.runtime_payload=lambda: Path({str(payload)!r}).read_bytes()\n'
              f'sys.exit(cli.main(["--workspace", {str(workspace)!r}, "assure", {str(source)!r}, "Check"]))\n')
    with (tmp_path / 'outer-cli.log').open('w') as log:
        process = subprocess.Popen([sys.executable, '-c', driver], stdout=log,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            deadline = time.monotonic() + 10
            while not ready.exists():
                assert process.poll() is None, 'outer CLI exited before starting the source stage'
                assert time.monotonic() < deadline, 'source stage did not start'
                time.sleep(0.02)
            selected = getattr(signal, signum)
            process.send_signal(selected)  # Target only the outer CLI PID.
            deadline = time.monotonic() + 5
            while not cleanup.exists():
                assert process.poll() is None, 'outer CLI exited before forwarding cancellation'
                assert time.monotonic() < deadline, 'cancellation did not reach the source stage'
                time.sleep(0.01)
            report = workspace / 'artifacts/pipeline/Check'
            # Keep exclusion until the child restores its source and finalizes evidence.
            with (report / '.run.lock').open('a') as lock:
                with pytest.raises(BlockingIOError):
                    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            process.send_signal(selected)  # Repeated cancellation must preserve restoration.
            assert process.wait(timeout=10) == 128 + selected
            run = json.loads((report / 'run.json').read_text())
            assert run['execution_status'] == 'completed_with_gaps'
            assert run['stages']['source']['status'] == 'interrupted'
            assert run['stages']['source']['exit_code'] == 128 + selected
            assert json.loads((report / 'guarantee.json').read_text())['status'] == 'unverified'
            assert (report / 'summary.md').is_file()
            for path in (report / '.run.lock', resource):
                with path.open() as lock:
                    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        finally:
            if ready.exists():
                ids = json.loads(ready.read_text())
                for pid, group in ((ids['pid'], True), (ids['parent'], False)):
                    try:
                        (os.killpg if group else os.kill)(pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait(timeout=10)


def test_outer_cli_cleanup_deadline_kills_unresponsive_child_group(tmp_path):
    import fcntl
    import os
    import signal
    import time

    ready, resource = tmp_path / 'ready.json', tmp_path / 'resource.lock'
    descendant = ('import fcntl,json,os,pathlib,time\n'
                  f'stream=open({str(resource)!r}, "w")\n'
                  'fcntl.flock(stream, fcntl.LOCK_EX)\n'
                  f'pathlib.Path({str(ready)!r}).write_text(json.dumps(dict(pid=os.getpid(), parent=os.getppid())))\n'
                  'time.sleep(60)\n')
    worker = tmp_path / 'worker.py'
    worker.write_text('import signal,subprocess,sys,time\n'
                      'signal.signal(signal.SIGINT, signal.SIG_IGN)\n'
                      'signal.signal(signal.SIGTERM, signal.SIG_IGN)\n'
                      f'subprocess.Popen([sys.executable, "-c", {descendant!r}])\n'
                      'time.sleep(60)\n')
    driver = ('import os,sys\n'
              f'sys.path.insert(0, {str(Path(__file__).resolve().parents[1] / "src")!r})\n'
              'from autoform import cli\n'
              f'sys.exit(cli._run_command([sys.executable, {str(worker)!r}], env=os.environ, cleanup_timeout=0.3))\n')
    with (tmp_path / 'outer-cli.log').open('w') as log:
        process = subprocess.Popen([sys.executable, '-c', driver], stdout=log,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            deadline = time.monotonic() + 10
            while not ready.exists():
                assert process.poll() is None, 'child runner exited before starting the descendant'
                assert time.monotonic() < deadline, 'descendant did not start'
                time.sleep(0.02)
            started = time.monotonic()
            process.send_signal(signal.SIGTERM)
            assert process.wait(timeout=3) == 143
            assert time.monotonic() - started < 3
            with resource.open() as lock:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        finally:
            if ready.exists():
                try:
                    os.killpg(json.loads(ready.read_text())['parent'], signal.SIGKILL)
                except ProcessLookupError:
                    pass
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait(timeout=10)


@pytest.mark.parametrize('exists', [False, True])
def test_interrupted_workspace_initialization_can_be_retried(tmp_path, monkeypatch, exists):
    from autoform import cli
    workspace = tmp_path / 'workspace'
    if exists:
        workspace.mkdir()
    original = Path.write_bytes
    calls = []

    def fail_midway(path, content):
        calls.append(path)
        if len(calls) == 3:
            raise OSError('simulated full disk')
        return original(path, content)

    with monkeypatch.context() as patch:
        patch.setattr(Path, 'write_bytes', fail_midway)
        with pytest.raises(OSError, match='full disk'):
            cli.prepare_workspace(workspace)
    assert not workspace.exists() or not list(workspace.iterdir())
    assert not list(tmp_path.glob('.autoform-init-*'))
    assert cli.prepare_workspace(workspace) == workspace
    assert cli.prepare_workspace(workspace) == workspace


def test_concurrent_initialization_is_refused_before_writing(tmp_path):
    import fcntl
    from autoform import cli
    workspace = tmp_path / 'workspace'
    with (tmp_path / '.workspace.autoform-init.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        with pytest.raises(ValueError, match='initialization is already in progress'):
            cli.prepare_workspace(workspace)
    assert not workspace.exists()


@pytest.mark.parametrize('name', ['../escape', '/absolute', 'a/../b', 'a//b', '.autoform-package.json'])
def test_invalid_archive_is_rejected_before_any_extraction(tmp_path, monkeypatch, name):
    import io
    import zipfile
    from autoform import cli
    data = io.BytesIO()
    with zipfile.ZipFile(data, 'w') as archive:
        archive.writestr('first.txt', 'valid')
        archive.writestr(name, 'invalid')
    monkeypatch.setattr(cli, 'runtime_payload', lambda: data.getvalue())
    with pytest.raises(ValueError, match='invalid package resource'):
        cli.prepare_workspace(tmp_path / 'workspace')
    assert not list(tmp_path.iterdir())


def test_cli_preserves_property_input_before_invalidating_old_evidence(tmp_path, monkeypatch):
    from autoform import cli
    workspace = cli.prepare_workspace(tmp_path / 'workspace')
    report = workspace / 'artifacts/pipeline/Check'
    report.mkdir(parents=True)
    properties = report / 'properties.json'
    request = '{"schema_version":1,"claims":[{"id":"rule"}]}'
    properties.write_text(request)
    (report / 'security.json').write_text('{"status":"verified_scoped"}')
    monkeypatch.setattr(cli, 'resolve_source', lambda *args, **kwargs: (tmp_path, None))
    commands = []
    monkeypatch.setattr(cli, '_run_command', lambda command, **kwargs: commands.append(command) or 0)
    assert cli.main(['--workspace', str(workspace), 'assure', str(tmp_path), 'Check',
                     '--properties', str(properties)]) == 0
    command = commands[0]
    copied = Path(command[command.index('--properties') + 1])
    assert copied.read_text() == request
    assert not (report / 'security.json').exists()


def test_git_url_cli_forwards_stage_deadline(tmp_path, monkeypatch):
    from autoform import cli
    commands = []
    monkeypatch.setattr(cli, 'resolve_source', lambda *args, **kwargs: (tmp_path, None))
    monkeypatch.setattr(cli, '_run_command', lambda command, **kwargs: commands.append(command) or 0)
    assert cli.main(['--workspace', str(tmp_path / 'workspace'),
                     'https://example.invalid/project.git', 'Check', '--stage-timeout', '17']) == 0
    command = commands[0]
    assert command[command.index('--stage-timeout') + 1] == '17.0'
    assert Path(command[1]).name == 'assure.sh'


@pytest.mark.parametrize('value', ['0', '-1', 'nan', 'inf'])
def test_invalid_stage_deadline_fails_before_checkout(tmp_path, value):
    from autoform import cli
    workspace = tmp_path / 'workspace'
    with pytest.raises(SystemExit) as error:
        cli.main(['--workspace', str(workspace), 'https://example.invalid/project.git',
                  '--stage-timeout=' + value])
    assert error.value.code == 2
    assert not workspace.exists()


@pytest.mark.parametrize('kind', ['missing', 'directory', 'fifo', 'loop'])
def test_missing_property_input_invalidates_previous_guarantee(tmp_path, monkeypatch, kind):
    import os
    from autoform import cli
    workspace = cli.prepare_workspace(tmp_path / 'workspace')
    report = workspace / 'artifacts/pipeline/Check'
    report.mkdir(parents=True)
    (report / 'guarantee.json').write_text('{"status":"verified_scoped"}')
    properties = tmp_path / 'invalid.json'
    if kind == 'directory':
        properties.mkdir()
    elif kind == 'fifo':
        os.mkfifo(properties)
    elif kind == 'loop':
        properties.symlink_to(properties)
    assert cli.main(['--workspace', str(workspace), 'assure', str(tmp_path), 'Check',
                     '--properties', str(properties)]) == 2
    assert json.loads((report / 'guarantee.json').read_text())['status'] == 'unverified'
    assert json.loads((report / 'run.json').read_text())['execution_status'] == 'property_input_failed'


@pytest.mark.parametrize('value', ['https://[invalid', 'https:///missing-host',
                                  'ssh://git@example.invalid:invalid/repo.git'])
def test_malformed_git_url_invalidates_prior_run_without_traceback(tmp_path, capsys, value):
    from autoform import cli
    workspace = cli.prepare_workspace(tmp_path / 'workspace')
    report = workspace / 'artifacts/pipeline/Check'
    report.mkdir(parents=True)
    (report / 'guarantee.json').write_text('{"status":"verified_scoped"}')
    assert cli.main(['--workspace', str(workspace), value, 'Check']) == 2
    assert json.loads((report / 'guarantee.json').read_text())['status'] == 'unverified'
    assert json.loads((report / 'repository.json').read_text())['status'] == 'failed'
    assert json.loads((report / 'run.json').read_text())['execution_status'] == 'acquisition_failed'
    assert 'Traceback' not in capsys.readouterr().err


@pytest.mark.parametrize('timed_out', [False, True])
def test_git_diagnostics_do_not_publish_url_credentials(tmp_path, monkeypatch, capsys, timed_out):
    source = 'https://root-token@example.invalid/project.git?access=root-query'
    diagnostic = ('fatal: unable to access https://root-token@example.invalid/project.git/\n'
                  'submodule ssh://git:child-secret@example.invalid/child.git?token=child-query\n')

    def failed_git(command, **kwargs):
        if timed_out:
            raise subprocess.TimeoutExpired(command, 900, output=diagnostic)
        return subprocess.CompletedProcess(command, 128, stdout=diagnostic)

    monkeypatch.setattr(repository.subprocess, 'run', failed_git)
    workspace = tmp_path / 'workspace'
    with pytest.raises(ValueError, match='Git checkout') as error:
        repository.resolve_source(source, workspace, 'Check')
    report = workspace / 'artifacts/pipeline/Check'
    recorded = str(error.value) + ''.join(path.read_text() for path in report.iterdir())
    recorded += capsys.readouterr().out
    for secret in ('root-token', 'root-query', 'child-secret', 'child-query'):
        assert secret not in recorded


@pytest.mark.parametrize('name', ['.autoform-package.json', 'lakefile.toml', 'scripts'])
def test_workspace_rejects_matching_content_behind_symlinks(tmp_path, name):
    from autoform import cli
    workspace = cli.prepare_workspace(tmp_path / 'workspace')
    resource = workspace / name
    outside = tmp_path / 'moved-resource'
    resource.rename(outside)
    resource.symlink_to(outside, target_is_directory=outside.is_dir())
    with pytest.raises(ValueError, match='workspace (manifest|resource)'):
        cli.prepare_workspace(workspace)


@pytest.mark.parametrize('kind', ['symlink', 'directory', 'parent-conflict'])
def test_special_archive_members_are_rejected_before_extraction(tmp_path, monkeypatch, kind):
    import io
    import stat
    import zipfile
    from autoform import cli
    data = io.BytesIO()
    with zipfile.ZipFile(data, 'w') as archive:
        member = zipfile.ZipInfo('member')
        if kind == 'symlink':
            member.external_attr = (stat.S_IFLNK | 0o777) << 16
        elif kind == 'directory':
            member.external_attr = (stat.S_IFDIR | 0o755) << 16
        archive.writestr(member, 'target')
        if kind == 'parent-conflict':
            archive.writestr('member/child', 'content')
    monkeypatch.setattr(cli, 'runtime_payload', lambda: data.getvalue())
    with pytest.raises(ValueError, match='invalid package resource'):
        cli.prepare_workspace(tmp_path / 'workspace')
    assert not list(tmp_path.iterdir())


@pytest.mark.parametrize('kind', ['fifo', 'symlink'])
def test_workspace_lock_refuses_nonregular_files_without_blocking(tmp_path, kind):
    import os
    from autoform import cli
    lock = tmp_path / 'lock'
    if kind == 'fifo':
        os.mkfifo(lock)
    else:
        target = tmp_path / 'target'
        target.write_text('preserve this')
        lock.symlink_to(target)
    with pytest.raises((OSError, ValueError)):
        cli._open_workspace_lock(lock)
    if kind == 'symlink':
        assert target.read_text() == 'preserve this'


def test_workspace_manifest_fifo_is_rejected_before_read(tmp_path, monkeypatch):
    import os
    from autoform import cli
    workspace = cli.prepare_workspace(tmp_path / 'workspace')
    marker = workspace / '.autoform-package.json'
    marker.unlink()
    os.mkfifo(marker)
    original = Path.read_text

    def prevent_blocking_read(path, *args, **kwargs):
        assert path != marker, 'workspace validation attempted to read a FIFO'
        return original(path, *args, **kwargs)

    monkeypatch.setattr(Path, 'read_text', prevent_blocking_read)
    with pytest.raises(ValueError, match='manifest is not a regular file'):
        cli.prepare_workspace(workspace)


def test_source_symlink_loop_has_a_failed_acquisition_record(tmp_path):
    source = tmp_path / 'source'
    source.symlink_to(source)
    workspace = tmp_path / 'workspace'
    with pytest.raises(ValueError):
        repository.resolve_source(str(source), workspace, 'Check')
    record = json.loads((workspace / 'artifacts/pipeline/Check/repository.json').read_text())
    assert record['status'] == 'failed'
