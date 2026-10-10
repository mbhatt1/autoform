"""Install the actual distribution and use it outside the checkout."""
import base64
import csv
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import zipfile

import pytest


@pytest.fixture
def distribution_checker():
    import importlib.util
    root = Path(__file__).resolve().parents[1]
    spec = importlib.util.spec_from_file_location('check_distribution', root / 'scripts/check_distribution.py')
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    return checker


@pytest.fixture
def distribution_pair():
    wheel = os.environ.get('AUTOFORM_TEST_WHEEL')
    if not wheel:
        pytest.skip('set AUTOFORM_TEST_WHEEL to check actual distribution integrity')
    wheel = Path(wheel).resolve()
    sdists = list(wheel.parent.glob('*.tar.gz'))
    assert len(sdists) == 1
    return wheel, sdists[0]


def test_installed_distribution(tmp_path):
    wheel = os.environ.get("AUTOFORM_TEST_WHEEL")
    if not wheel:
        pytest.skip("set AUTOFORM_TEST_WHEEL to test an actual built wheel")
    wheel = Path(wheel).resolve()
    with zipfile.ZipFile(wheel) as archive:
        payload = archive.read("autoform/runtime.zip")
        # the subpackages behind `autoform formalize` and `autoform autoformalize`
        for module in ("autoform/harness/cli.py", "autoform/harness/prover.py", "autoform/harness/semif_worker.py",
                       "autoform/nl/pipeline.py", "autoform/nl/model.py", "autoform/nl/judge.py"):
            assert module in archive.namelist(), module
    with zipfile.ZipFile(io.BytesIO(payload)) as archive:
        names = archive.namelist()
        assert "cartographer/export_ast.sc" in names
        assert "cartographer/compiler/SourceCompiler.scala" in names
        assert "cartographer/ast_tools.py" in names
        assert "scripts/compiler_sources.py" in names
        assert "scripts/native_c_worker.py" in names
        assert "scripts/proof_artifacts.py" in names
        assert "scripts/deep_json.py" in names
        assert "scripts/security_specs.py" in names
        assert "examples/security/autoform.properties.json" in names
        for name in ('LICENSE', 'NOTICE', 'THIRD_PARTY.md', 'SUPPORT.md', 'SECURITY.md',
                     'licenses/cachetools-MIT.txt', 'docs/packaging.md'):
            assert name in names
        assert "Autoform/Lang/Core/TypedNumeric.lean" in names
        assert "Autoform/Lang/PCode/Properties.lean" in names
        assert not any(".lake/" in name or "Pipeline" in name or "__pycache__" in name for name in names)
    venv = tmp_path / "venv"
    subprocess.run([sys.executable, "-m", "venv", str(venv)], check=True, capture_output=True)
    python = venv / "bin/python"
    subprocess.run([python, "-m", "pip", "install", "--no-deps", "--no-index",
                    "--disable-pip-version-check", str(wheel)],
                   check=True, capture_output=True)
    cli = venv / "bin/autoform"
    work = tmp_path / "outside checkout"
    work.mkdir()
    workspace = work / "proof project"

    def invoke(*args):
        return subprocess.run([str(cli), "--workspace", str(workspace), *args],
                              cwd=work, text=True, capture_output=True, timeout=60)

    assert invoke("--version").returncode == 0
    result = invoke("init")
    assert result.returncode == 0, result.stderr
    assert invoke("init").returncode == 0
    assert (workspace / "scripts/synth_specs.py").is_file()
    # Import the actual bundled passes and resolve the modular exporter outside
    # the checkout; neither source imports nor using-file directives may rely on it.
    probe = subprocess.run([python, "-c", """
import sys
from pathlib import Path
root = Path(sys.argv[1])
sys.path[:0] = [str(root / 'cartographer'), str(root / 'scripts')]
from compiler_sources import source_files
from generator_lowering import lower_generators
from python_truth_values import lower_truth_values
from python_truth_lowering import lower_truth_conditions
sources = source_files(root / 'cartographer/export_ast.sc')
assert any(path.name == 'SourceCompiler.scala' for path in sources)
assert all(path.is_file() and path.is_relative_to(root) for path in sources)
functions = [{'name': 'probe', 'body': {'k': 'skip'}}]
assert lower_truth_conditions(lower_truth_values(lower_generators(functions))) == functions
""", str(workspace)], cwd=work, text=True, capture_output=True, timeout=30)
    assert probe.returncode == 0, probe.stderr
    assert invoke("source", "--help").returncode == 0
    help_result = invoke("assure", "--help")
    assert help_result.returncode == 0 and '--properties' in help_result.stdout
    assert '--stage-timeout' in help_result.stdout
    assert invoke("machine", "--help").returncode == 0
    # A failed repeat invalidates previously passing evidence even after installation.
    corpus = work / "corpus"
    corpus.mkdir()
    (corpus / "f.py").write_text("def add(a, b): return a + b\n")
    # Output names must not overwrite the library's own generated dependencies.
    reserved = invoke("source", str(corpus), "Cachetools")
    assert reserved.returncode != 0
    assert "bundled with the library" in reserved.stderr
    assert invoke("init").returncode == 0
    report = workspace / "artifacts/pipeline/Installed"
    report.mkdir(parents=True)
    (report / "conformance.json").write_text('{"agree":999}')
    env = dict(os.environ, JOERN_HOME=str(work / "missing-joern"))
    failed = subprocess.run([cli, "--workspace", workspace, "source", corpus, "Installed"],
                            cwd=work, env=env, text=True, capture_output=True, timeout=30)
    assert failed.returncode != 0
    assert not (report / "conformance.json").exists()
    assert json.loads((report / "pipeline.json").read_text())["status"] == "failed"
    # The URL shorthand acquires source and records a failed acquisition without
    # retaining a previous proof or guarantee for that output module.
    (report / 'guarantee.json').write_text('{"status":"verified_scoped"}')
    (report / 'specs.json').write_text('{"proved":999}')
    missing = invoke((work / 'missing-remote').as_uri(), 'Installed')
    assert missing.returncode != 0
    assert json.loads((report / 'run.json').read_text())['execution_status'] == 'acquisition_failed'
    assert json.loads((report / 'guarantee.json').read_text())['status'] == 'unverified'
    assert not (report / 'specs.json').exists()
    # Discovery is packaged and fails closed before running repository code.
    (corpus / 'autoform.properties.json').mkdir()
    (report / 'security.json').write_text('{"status":"verified_scoped"}')
    invalid = invoke('assure', str(corpus), 'Installed')
    assert invalid.returncode != 0
    run = json.loads((report / 'run.json').read_text())
    assert run['security_requested'] and run['property_selection']['mode'] == 'repository'
    assert run['stages']['source']['status'] == 'blocked'
    assert json.loads((report / 'security.json').read_text())['status'] == 'unverified'
    # Generated evidence is allowed; edits to bundled semantics require a new workspace.
    (workspace / "Autoform/Lang/Core/Semantics.lean").write_text("modified\n")
    assert "workspace resource changed" in invoke("init").stderr


def test_distribution_rejects_builder_omission_of_transitive_compiler_unit(
        tmp_path, monkeypatch, distribution_checker):
    folder = tmp_path / 'cartographer/compiler'
    folder.mkdir(parents=True)
    entry = folder.parent / 'export_ast.sc'
    child, leaf = folder / 'SourceCompiler.scala', folder / 'Json.scala'
    entry.write_text('//> using file compiler/SourceCompiler.scala\n')
    child.write_text('//> using file Json.scala\n')
    leaf.write_text('object Json {}\n')
    resources = {p.relative_to(tmp_path).as_posix(): p.read_bytes() for p in (entry, child)}
    monkeypatch.setattr(distribution_checker, 'runtime_files', lambda root: resources)
    # The builder and its ordinary expected-file check share runtime_files. A
    # common omission must still fail before either archive is trusted.
    with pytest.raises(ValueError, match='compiler source missing from runtime: cartographer/compiler/Json.scala'):
        distribution_checker.check(tmp_path / 'unused.whl', tmp_path / 'unused.tar.gz', tmp_path)
    resources[leaf.relative_to(tmp_path).as_posix()] = leaf.read_bytes()
    distribution_checker.check_compiler_sources(tmp_path, resources)


def test_distribution_matches_checkout_and_rejects_missing_notice(
        tmp_path, distribution_checker, distribution_pair):
    wheel, sdist = distribution_pair
    assert distribution_checker.check(wheel, sdist)['status'] == 'passed'
    broken = tmp_path / wheel.name
    with zipfile.ZipFile(wheel) as original, zipfile.ZipFile(broken, 'w') as altered:
        for name in original.namelist():
            if not name.endswith('/licenses/LICENSE'):
                altered.writestr(name, original.read(name))
    with pytest.raises((ValueError, KeyError)):
        distribution_checker.check(broken, sdist)


@pytest.mark.parametrize('mutation', ['extra-module', 'startup-hook', 'missing-entry-point',
                                     'wrong-entry-point', 'record-hash'])
def test_distribution_rejects_wheel_installation_mutations(
        tmp_path, distribution_checker, distribution_pair, mutation):
    wheel, sdist = distribution_pair
    broken = tmp_path / wheel.name
    with zipfile.ZipFile(wheel) as original, zipfile.ZipFile(broken, 'w') as altered:
        for name in original.namelist():
            content = original.read(name)
            if mutation == 'missing-entry-point' and name.endswith('/entry_points.txt'):
                continue
            if mutation == 'wrong-entry-point' and name.endswith('/entry_points.txt'):
                content = b'[console_scripts]\nautoform = autoform.cli:wrong\n'
            if mutation == 'record-hash' and name.endswith('/RECORD'):
                content = content.replace(b'sha256=', b'sha512=', 1)
            altered.writestr(name, content)
        if mutation == 'extra-module':
            altered.writestr('autoform/undeclared.py', b'raise RuntimeError("unreviewed")\n')
        if mutation == 'startup-hook':
            altered.writestr('undeclared.pth', b'import undeclared\n')
    with pytest.raises((ValueError, KeyError)):
        distribution_checker.check(broken, sdist)


@pytest.mark.parametrize('mutation', ['missing-fixtures', 'stale-readme', 'stale-test',
                                     'extra-source', 'unsafe-path'])
def test_distribution_rejects_sdist_source_mutations(
        tmp_path, distribution_checker, distribution_pair, mutation):
    wheel, sdist = distribution_pair
    broken = tmp_path / sdist.name
    with tarfile.open(sdist, 'r:gz') as original, tarfile.open(broken, 'w:gz') as altered:
        members = original.getmembers()
        prefix = members[0].name.split('/')[0] + '/'
        for member in members:
            if mutation == 'missing-fixtures' and member.name == prefix + 'tests/conftest.py':
                continue
            content = original.extractfile(member).read() if member.isfile() else None
            if ((mutation == 'stale-readme' and member.name == prefix + 'README.md') or
                    (mutation == 'stale-test' and member.name == prefix + 'tests/test_package.py')):
                content = b'stale source\n'
                member.size = len(content)
            altered.addfile(member, io.BytesIO(content) if content is not None else None)
        if mutation in ('extra-source', 'unsafe-path'):
            name = prefix + ('undeclared.py' if mutation == 'extra-source' else '../outside.py')
            entry = tarfile.TarInfo(name)
            entry.size = 1
            altered.addfile(entry, io.BytesIO(b'0'))
    with pytest.raises((ValueError, KeyError)):
        distribution_checker.check(wheel, broken)


@pytest.mark.parametrize('name', ['', '/absolute', '../outside', 'a/../outside',
                                'a//b', './a', 'a\\b', 'a\x00b'])
def test_distribution_rejects_ambiguous_archive_paths(distribution_checker, name):
    with pytest.raises(ValueError, match='unsafe archive path'):
        distribution_checker.safe_name(name)


@pytest.mark.parametrize('mutation, error', [
    ('runtime-dependency', 'Requires-Dist'),
    ('optional-marker', 'Requires-Dist'),
    ('python-version', 'Requires-Python'),
    ('extra', 'Provides-Extra'),
    ('egg-dependency', 'requires.txt'),
    ('egg-marker', 'requires.txt'),
])
def test_distribution_rejects_coherent_dependency_metadata_tampering(
        tmp_path, distribution_checker, distribution_pair, mutation, error):
    wheel, sdist = distribution_pair
    # Both PKG-INFO copies match METADATA and every changed wheel byte has a
    # freshly computed RECORD hash. Only the independent TOML contract can
    # reject these coherent dependency modifications.
    with zipfile.ZipFile(wheel) as original:
        contents = {name: original.read(name) for name in original.namelist()}
    metadata_name = next(name for name in contents if name.endswith('.dist-info/METADATA'))
    metadata = contents[metadata_name]
    if mutation == 'runtime-dependency':
        metadata = metadata.replace(b'\n\n', b'\nRequires-Dist: undeclared-package>=1\n\n', 1)
    elif mutation == 'optional-marker':
        assert b'extra == "machine"' in metadata
        metadata = metadata.replace(b'extra == "machine"', b'extra == "test"', 1)
    elif mutation == 'python-version':
        assert b'Requires-Python: >=3.10\n' in metadata
        metadata = metadata.replace(b'Requires-Python: >=3.10\n', b'Requires-Python: >=2.7\n', 1)
    elif mutation == 'extra':
        metadata = metadata.replace(b'\n\n', b'\nProvides-Extra: undeclared\n\n', 1)
    contents[metadata_name] = metadata
    record_name = metadata_name.removesuffix('METADATA') + 'RECORD'
    record = io.StringIO(newline='')
    writer = csv.writer(record)
    for name, content in contents.items():
        digest = base64.urlsafe_b64encode(hashlib.sha256(content).digest()).decode().rstrip('=')
        writer.writerow((name, '', '') if name == record_name else
                        (name, 'sha256=' + digest, str(len(content))))
    contents[record_name] = record.getvalue().encode()
    broken_wheel = tmp_path / wheel.name
    with zipfile.ZipFile(broken_wheel, 'w') as altered:
        for name, content in contents.items():
            altered.writestr(name, content)
    with zipfile.ZipFile(broken_wheel) as altered:
        distribution_checker.check_record(altered, metadata_name.removesuffix('METADATA'))
    broken_sdist = tmp_path / sdist.name
    with tarfile.open(sdist, 'r:gz') as original, tarfile.open(broken_sdist, 'w:gz') as altered:
        for member in original.getmembers():
            content = original.extractfile(member).read() if member.isfile() else None
            if member.name.endswith('/PKG-INFO'):
                content = metadata
            if member.name.endswith('.egg-info/requires.txt'):
                if mutation in ('runtime-dependency', 'egg-dependency'):
                    content = b'undeclared-package>=1\n' + content
                elif mutation == 'egg-marker':
                    assert b'[test:python_version < "3.11"]' in content
                    content = content.replace(b'[test:python_version < "3.11"]',
                                              b'[test:python_version >= "3.11"]')
                elif mutation == 'extra':
                    content += b'\n[undeclared]\n'
            if content is not None:
                member.size = len(content)
            altered.addfile(member, io.BytesIO(content) if content is not None else None)
    with pytest.raises(ValueError, match=error + ' differs from pyproject.toml'):
        distribution_checker.check(broken_wheel, broken_sdist)
