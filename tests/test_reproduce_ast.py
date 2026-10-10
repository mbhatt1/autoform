"""Failed or incomplete compiler runs must never become reproduction evidence."""
import json
from pathlib import Path
import sys
from types import SimpleNamespace

import pytest

from conftest import SCRIPTS, load


@pytest.fixture
def reproduction(tmp_path, monkeypatch):
    module = load(str(Path(SCRIPTS) / 'reproduce_ast.py'), 'af_reproduce_ast')
    root = tmp_path / 'repo'
    root.mkdir()
    source = root / 'source'
    source.mkdir()
    artifact = root / 'ast-Test.json'
    artifact.write_text('[]\n')
    exporter = root / 'export.sc'
    exporter.write_text('//> using file Compiler.scala\n')
    unit = root / 'Compiler.scala'
    unit.write_text('object Compiler {}\n')
    workspace = root / 'workspace'
    workspace.mkdir()
    sentinel = workspace / 'keep.txt'
    sentinel.write_text('unrelated work\n')
    monkeypatch.setattr(module.P, 'REPO', root)
    monkeypatch.setattr(module.P, 'PROV_DIR', root / 'provenance')
    monkeypatch.setattr(module.P, 'detect_joern', lambda: {'joern_version': 'test'})
    monkeypatch.setattr(module.P, 'pinned_joern', lambda: 'test')
    monkeypatch.setattr(module.P, 'joern_home', lambda: root / 'joern')
    monkeypatch.setattr(sys, 'argv', ['reproduce_ast.py', str(artifact), '--source', str(source),
                                    '--exporter', str(exporter)])
    calls = []

    def runner(export_status=0):
        def run(arguments, **options):
            calls.append((arguments, options))
            if Path(arguments[0]).name == 'joern-parse':
                Path(arguments[arguments.index('--output') + 1]).write_bytes(b'cpg')
                return SimpleNamespace(returncode=0, stdout='', stderr='')
            fresh = next(argument[4:] for argument in arguments if argument.startswith('out='))
            Path(fresh).write_bytes(artifact.read_bytes())
            return SimpleNamespace(returncode=export_status, stdout='', stderr='compiler diagnostics')
        monkeypatch.setattr(module.subprocess, 'run', run)

    return SimpleNamespace(module=module, root=root, artifact=artifact, exporter=exporter,
                           unit=unit, sentinel=sentinel, calls=calls, runner=runner)


def test_failed_export_cannot_report_matching_output_as_reproduced(reproduction, capsys):
    reproduction.runner(export_status=1)
    assert reproduction.module.main() == 2
    output = capsys.readouterr()
    assert 'export failed (rc=1' in output.err
    assert 'REPRODUCED' not in output.out
    assert reproduction.sentinel.read_text() == 'unrelated work\n'


def test_reproduction_runs_in_its_own_workspace(reproduction, capsys):
    reproduction.runner()
    assert reproduction.module.main() == 0
    assert 'REPRODUCED byte-for-byte' in capsys.readouterr().out
    directories = [Path(options['cwd']) for _, options in reproduction.calls]
    assert len(directories) == 2 and directories[0] == directories[1]
    assert directories[0] != reproduction.root
    assert not directories[0].exists()
    assert reproduction.sentinel.read_text() == 'unrelated work\n'
    export_command = reproduction.calls[1][0]
    assert export_command[export_command.index('--script') + 1] == str(reproduction.exporter)


def test_missing_compiler_unit_is_rejected_before_parsing(reproduction, capsys):
    reproduction.runner()
    reproduction.unit.unlink()
    assert reproduction.module.main() == 2
    assert 'cannot read exporter source dependencies' in capsys.readouterr().err
    assert not reproduction.calls


def test_explicit_exporter_takes_precedence_over_provenance(reproduction):
    records = reproduction.root / 'provenance'
    records.mkdir()
    (records / 'ast-Test.json.prov.json').write_text(json.dumps({'exporter': 'previous.sc'}))
    reproduction.runner()
    assert reproduction.module.main() == 0
