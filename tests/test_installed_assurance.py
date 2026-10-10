"""Release acceptance for the installed Git URL command and independent properties."""
import json
import os
from pathlib import Path
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.skipif(os.environ.get('AUTOFORM_TEST_INSTALLED_E2E') != '1',
                    reason='set AUTOFORM_TEST_INSTALLED_E2E=1 with the candidate wheel and toolchains installed')
def test_installed_git_url_proves_policy_and_withholds_false_property(tmp_path):
    cli = shutil.which('autoform')
    assert cli, 'candidate CLI must be installed'
    remote = tmp_path / 'remote'
    remote.mkdir()
    for name in ('policy.py', 'autoform.properties.json'):
        shutil.copyfile(ROOT / 'examples/security' / name, remote / name)

    def git(*args):
        return subprocess.check_output(['git', '-C', str(remote), *args], text=True).strip()

    git('init', '-q')
    git('config', 'user.name', 'Autoform release acceptance')
    git('config', 'user.email', 'validation@example.invalid')
    git('add', '.')
    git('commit', '-qm', 'Independent ownership property')
    workspace = tmp_path / 'proofs'
    caller = tmp_path / 'outside checkout'
    caller.mkdir()
    for module, expected in [('ReleasePolicy', 'verified_scoped'), ('ReleaseFalse', 'unverified')]:
        if module == 'ReleaseFalse':
            path = remote / 'autoform.properties.json'
            properties = json.loads(path.read_text())
            properties['claims'][0]['statement'] = 'False'
            path.write_text(json.dumps(properties))
            git('commit', '-qam', 'Deliberately impossible property')
        revision = git('rev-parse', 'HEAD')
        result = subprocess.run([cli, '--workspace', str(workspace), remote.as_uri(),
                                 module, '--ref', revision], cwd=caller,
                                capture_output=True, text=True, timeout=1800)
        report = workspace / 'artifacts/pipeline' / module
        assert result.returncode in (0, 1), result.stdout + result.stderr
        run = json.loads((report / 'run.json').read_text())
        assert run['repository']['commit'] == revision
        assert run['property_selection']['mode'] == 'repository'
        assert json.loads((report / 'security.json').read_text())['status'] == expected
        assert json.loads((report / 'guarantee.json').read_text())['status'] == expected
        if expected == 'verified_scoped':
            for name in ('audit.json', 'security-audit.json'):
                audit = json.loads((report / name).read_text())
                assert audit['verdict']['pass']
                assert audit['artifact_snapshot']['status'] == 'STABLE'
                assert audit['lean4checker']['mode'] == 'fresh'
        else:
            assert result.returncode == 1
            assert not run['verification_complete']
