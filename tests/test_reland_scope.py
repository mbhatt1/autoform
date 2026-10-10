"""A corpus re-land may validate its own evidence without refreshing other pins."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

import pytest


ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def provenance_tree(root):
    (root / "provenance").mkdir()
    (root / "joern-version").write_text("4.0.606\n")
    exporter = root / "export.sc"
    exporter.write_text("current exporter\n")
    for name in ("Fresh", "Stale"):
        artifact = root / f"ast-{name}.json"
        artifact.write_text("[]\n")
        record = {
            "schema_version": 1,
            "artifact": artifact.name,
            "artifact_sha256": digest(artifact),
            "artifact_bytes": artifact.stat().st_size,
            "joern_version": "4.0.606",
            "cpg_schema_version": "1.7.70",
            "exporter": exporter.name,
            "exporter_sha256": digest(exporter) if name == "Fresh" else "0" * 64,
            "source_path": str(root),
            "source_revision": "tree-sha256:fixture",
            "command": f"scripts/reland_corpus.sh source {name}",
            "recorded_by": "test fixture",
        }
        (root / "provenance" / (artifact.name + ".prov.json")).write_text(json.dumps(record))


def check_provenance(root, *args):
    return subprocess.run(
        [sys.executable, ROOT / "scripts/check_provenance.py", "--root", root, *args],
        text=True, capture_output=True, timeout=30)


def test_targeted_provenance_preserves_global_failure(tmp_path):
    provenance_tree(tmp_path)
    targeted = check_provenance(tmp_path, "--strict", "--artifact", "ast-Fresh.json")
    assert targeted.returncode == 0, targeted.stderr
    assert "Repository-wide provenance was not checked" in targeted.stdout
    global_check = check_provenance(tmp_path)
    assert global_check.returncode == 1
    assert "ast-Stale.json" in global_check.stderr
    stale = check_provenance(tmp_path, "--artifact", "ast-Stale.json")
    assert stale.returncode == 1
    assert "changed since this artifact was exported" in stale.stderr


@pytest.mark.parametrize("name", ["ast-Missing.json", "../ast-Fresh.json", "export.sc"])
def test_unknown_provenance_selection_fails(tmp_path, name):
    provenance_tree(tmp_path)
    result = check_provenance(tmp_path, "--artifact", name)
    assert result.returncode == 1
    assert "absent or not recognized" in result.stderr


@pytest.fixture
def specs_checker(tmp_path, monkeypatch):
    spec = importlib.util.spec_from_file_location("reland_specs_check", ROOT / "scripts/check_specs_fresh.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    monkeypatch.setattr(module, "ROOT", str(tmp_path))
    manifest = tmp_path / "artifact-manifest.json"
    monkeypatch.setattr(module, "MANIFEST", str(manifest))
    monkeypatch.setattr(module, "SPECS", {"SpecsGen/Fresh": "Fresh", "SpecsGen/Stale": "Stale"})
    (tmp_path / "Autoform/SpecsGen").mkdir(parents=True)
    records = {}
    for name in ("Fresh", "Stale"):
        (tmp_path / f"Autoform/SpecsGen/{name}.lean").write_text("-- fixture\n")
        (tmp_path / f"ast-{name}.json").write_text("[]\n")
        records[f"SpecsGen/{name}"] = {"corpus": name, "corpus_ast_sha256": "old-" + name}
    manifest.write_text(json.dumps({"specs": records, "modules": {}}))
    return module, manifest


def test_record_only_regenerated_corpus(specs_checker, monkeypatch, capsys):
    module, manifest = specs_checker
    before = json.loads(manifest.read_text())
    monkeypatch.setattr(sys, "argv", ["check", "--record", "--corpus", "Fresh"])
    assert module.main() == 0
    after = json.loads(manifest.read_text())
    assert after["specs"]["SpecsGen/Stale"] == before["specs"]["SpecsGen/Stale"]
    assert after["specs"]["SpecsGen/Fresh"]["corpus_ast_sha256"] == digest(manifest.parent / "ast-Fresh.json")
    assert "Other specification pins are unchanged and unchecked" in capsys.readouterr().out
    monkeypatch.setattr(sys, "argv", ["check"])
    assert module.main() == 1
    assert "SpecsGen/Stale" in capsys.readouterr().err


def test_missing_selected_specs_cannot_be_recorded(specs_checker, monkeypatch):
    module, manifest = specs_checker
    before = manifest.read_bytes()
    (manifest.parent / "Autoform/SpecsGen/Fresh.lean").unlink()
    monkeypatch.setattr(sys, "argv", ["check", "--record", "--corpus", "Fresh"])
    assert module.main() == 2
    assert manifest.read_bytes() == before


def test_one_present_selection_cannot_hide_an_absent_one(specs_checker, monkeypatch):
    module, manifest = specs_checker
    before = manifest.read_bytes()
    (manifest.parent / "Autoform/SpecsGen/Stale.lean").unlink()
    monkeypatch.setattr(sys, "argv", ["check", "--record", "--corpus", "Fresh", "--corpus", "Stale"])
    assert module.main() == 2
    assert manifest.read_bytes() == before


def test_missing_selected_ast_cannot_refresh_any_pins(specs_checker, monkeypatch):
    module, manifest = specs_checker
    before = manifest.read_bytes()
    (manifest.parent / "ast-Stale.json").unlink()
    monkeypatch.setattr(module, "git_tracked", lambda _: False)
    monkeypatch.setattr(sys, "argv", ["check", "--record", "--corpus", "Fresh", "--corpus", "Stale"])
    assert module.main() == 2
    assert manifest.read_bytes() == before


def test_selected_ignored_artifact_still_requires_a_record(tmp_path):
    provenance_tree(tmp_path)
    subprocess.run(["git", "init", "-q", tmp_path], check=True, capture_output=True)
    (tmp_path / ".gitignore").write_text("ast-Local.json\n")
    (tmp_path / "ast-Local.json").write_text("[]\n")
    result = check_provenance(tmp_path, "--strict", "--artifact", "ast-Local.json")
    assert result.returncode == 1
    assert "no provenance record" in result.stderr
