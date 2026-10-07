import json
import subprocess
import sys
from pathlib import Path

import pytest

from autoform_cli.cli import main


def test_translate_dry_run_plans_pipeline(capsys):
    rc = main(["--dry-run", "--json", "translate", "/src/repo", "Service"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["kind"] == "translate"
    assert payload["dry_run"] is True
    names = [step["name"] for step in payload["steps"]]
    assert names[:4] == [
        "check Joern version pin",
        "parse source with Joern",
        "build formalization graph",
        "export neutral AST",
    ]
    assert "record AST provenance" in names
    assert any("provenance.py" in " ".join(step["command"]) for step in payload["steps"])
    assert any("render_lean.py" in " ".join(step["command"]) for step in payload["steps"])
    assert payload["metadata"]["autoform_cli_version"]
    assert payload["metadata"]["repo_root"] == str(Path(__file__).resolve().parents[1])
    assert payload["metadata"]["cpp_defines_set"] is False


def test_config_supplies_source_and_module(tmp_path, capsys):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text('[project]\nsource = "/workspace/app"\nmodule = "App"\n')
    rc = main(["--config", str(cfg), "--dry-run", "--json", "assure"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["kind"] == "assure"
    assert payload["source"] == "/workspace/app"
    assert payload["module"] == "App"
    assert any(step["name"] == "build SACM assurance case" for step in payload["steps"])


def test_init_refuses_to_overwrite(tmp_path):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text("existing")
    with pytest.raises(SystemExit):
        main(["init", "--output", str(cfg)])


def test_invalid_module_name_fails_cleanly():
    with pytest.raises(SystemExit):
        main(["--dry-run", "translate", "/src", "not-a-module"])


def test_legacy_shell_entrypoints_delegate_to_python_cli():
    root = Path(__file__).resolve().parents[1]
    autoform = (root / "autoform.sh").read_text()
    assure = (root / "assure.sh").read_text()
    assert "CMD=(python3 -m autoform_cli)" in autoform and "CMD+=(translate)" in autoform
    assert "CMD=(python3 -m autoform_cli)" in assure and "CMD+=(assure)" in assure
    assert "GLOBAL" in autoform and "POSITIONAL" in autoform

def test_named_target_translate_uses_config(tmp_path, capsys):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text('[targets.payments]\nsource = "/srv/payments"\nmodule = "Payments"\n')
    rc = main(["--config", str(cfg), "--dry-run", "--json", "translate", "--target", "payments"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["source"] == "/srv/payments"
    assert payload["module"] == "Payments"


def test_batch_dry_run_emits_single_fleet_plan(tmp_path, capsys):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text(
        '[targets.payments]\n'
        'source = "/srv/payments"\n'
        'module = "Payments"\n'
        'mode = "assure"\n\n'
        '[targets.search]\n'
        'source = "/srv/search"\n'
        'module = "Search"\n'
    )
    rc = main(["--config", str(cfg), "--dry-run", "--json", "batch"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["kind"] == "batch"
    assert payload["count"] == 2
    assert [item["target"] for item in payload["results"]] == ["payments", "search"]
    assert payload["results"][0]["kind"] == "assure"
    assert payload["results"][1]["kind"] == "translate"


def test_targets_lists_configured_entries(tmp_path, capsys):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text('[targets.api]\nsource = "/srv/api"\nmodule = "Api"\n')
    rc = main(["--config", str(cfg), "--json", "targets"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["targets"] == [
        {"mode": "translate", "module": "Api", "name": "api", "owner": None, "source": "/srv/api", "tags": [], "tier": None}
    ]


def test_batch_run_id_is_scoped_per_target(tmp_path, capsys):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text('[targets.api]\nsource = "/srv/api"\nmodule = "Api"\n')
    rc = main(["--config", str(cfg), "--dry-run", "--json", "--run-id", "fleet42", "batch"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["results"][0]["run_id"] == "fleet42-api"
    assert payload["results"][0]["manifest"].endswith(".autoform-runs/fleet42-api/run.json")


def test_pipeline_manifest_records_manifest_path(tmp_path):
    from autoform_cli.pipeline import PipelineRunner

    runner = PipelineRunner(dry_run=False, artifact_dir=tmp_path / "run")
    result = runner.result("translate", "/src", "Module", 0)
    assert result.manifest == str((tmp_path / "run" / "run.json"))
    saved = json.loads((tmp_path / "run" / "run.json").read_text())
    assert saved["manifest"] == result.manifest
    assert saved["metadata"]["autoform_cli_version"]
    assert saved["metadata"]["python_executable"]


def test_validate_reports_bad_target_config(tmp_path, capsys):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text(
        '[targets.bad]\n'
        'source = "/srv/missing"\n'
        'module = "bad-module"\n'
        'mode = "invent"\n'
    )
    rc = main(["--config", str(cfg), "--json", "validate"])
    assert rc == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["kind"] == "validate"
    assert payload["ok"] is False
    paths = {item["path"] for item in payload["violations"]}
    assert "targets.bad.module" in paths
    assert "targets.bad.mode" in paths


def test_validate_rejects_non_string_test_metadata(tmp_path, capsys):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text(
        '[targets.api]\n'
        'source = "/srv/api"\n'
        'module = "Api"\n'
        'test_command = ["pytest"]\n'
    )
    rc = main(["--config", str(cfg), "--json", "validate"])
    assert rc == 1
    payload = json.loads(capsys.readouterr().out)
    assert {item["path"] for item in payload["violations"]} == {"targets.api.test_command"}

def test_validate_can_require_existing_sources(tmp_path, capsys):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text('[targets.api]\nsource = "/definitely/not/here"\nmodule = "Api"\n')
    rc = main(["--config", str(cfg), "--json", "validate", "--require-existing-source"])
    assert rc == 1
    payload = json.loads(capsys.readouterr().out)
    assert any(item["path"] == "targets.api.source" for item in payload["violations"])


def test_schema_outputs_run_manifest_schema(capsys):
    rc = main(["--json", "schema", "run-manifest"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["title"] == "Autoform run manifest"
    assert "steps" in payload["properties"]





def test_spec_plan_turns_tests_into_behavior_contract_plan(capsys):
    rc = main([
        "--json",
        "spec-plan",
        "/srv/service",
        "Service",
        "--test-command",
        "pytest tests",
        "--test-framework",
        "pytest",
    ])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["kind"] == "spec-plan"
    assert payload["strategy"] == "test-first-autoformalization"
    assert payload["source"] == "/srv/service"
    assert payload["module"] == "Service"
    assert payload["test_command"] == "pytest tests"
    phases = [phase["name"] for phase in payload["phases"]]
    assert phases == [
        "seed-characterization-tests",
        "discover-tests",
        "trace-runtime-behavior",
        "translate-source",
        "emit-lean-behavior-specs",
        "check-conformance",
        "anti-vacuity",
    ]
    assert "/srv/service/tests/test_autoform_characterization.py" in payload["artifacts"]
    seed_phase = next(phase for phase in payload["phases"] if phase["name"] == "seed-characterization-tests")
    assert seed_phase["command"] == "autoform seed-python-tests /srv/service Service --output /srv/service/tests/test_autoform_characterization.py"
    assert "Autoform/Specs/ServiceBehaviorSpec.lean" in payload["artifacts"]
    trace_phase = next(phase for phase in payload["phases"] if phase["name"] == "trace-runtime-behavior")
    assert trace_phase["command"].startswith("autoform trace-python-tests /srv/service Service --test-command 'pytest tests'")
    emit_phase = next(phase for phase in payload["phases"] if phase["name"] == "emit-lean-behavior-specs")
    assert emit_phase["command"].startswith("autoform spec-from-trace ")
    assert emit_phase["command"].endswith("/.autoform-runs/Service/behavior-trace.jsonl Service --output Autoform/Specs/ServiceBehaviorSpec.lean")
    assert any("tautological" in reject for phase in payload["phases"] for reject in phase.get("rejects", []))


def test_spec_plan_uses_configured_target_metadata(tmp_path, capsys):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text(
        '[targets.api]\n'
        'source = "/srv/api"\n'
        'module = "Api"\n'
        'test_command = "pytest tests/api"\n'
        'test_framework = "pytest"\n'
    )
    rc = main(["--config", str(cfg), "--json", "spec-plan", "--target", "api"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["target"] == "api"
    assert payload["source"] == "/srv/api"
    assert payload["module"] == "Api"
    assert payload["test_command"] == "pytest tests/api"
    assert payload["test_framework"] == "pytest"

def test_schema_outputs_spec_plan_schema(capsys):
    rc = main(["--json", "schema", "spec-plan"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["title"] == "Autoform test-first specification plan"
    assert payload["properties"]["strategy"]["const"] == "test-first-autoformalization"


def test_spec_from_trace_writes_lean_behavior_inventory(tmp_path, capsys):
    trace = tmp_path / "trace.jsonl"
    trace.write_text(
        json.dumps({
            "function": "pkg.mod.normalize",
            "source_test": "tests/test_mod.py::test_normalize",
            "args": [" A "],
            "kwargs": {"lower": True},
            "receiver_state": {"cache": []},
            "result": "a",
            "side_effects": {"writes": []},
            "coverage": ["pkg/mod.py:12"],
        }) + "\n" +
        json.dumps({
            "id": "obs-skip",
            "function": "pkg.mod.external",
            "args": [],
            "kwargs": {},
            "skip_reason": "unencodable socket side effect",
        }) + "\n"
    )
    output = tmp_path / "ServiceBehaviorSpec.lean"
    rc = main(["--json", "spec-from-trace", str(trace), "Service", "--output", str(output)])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["kind"] == "spec-from-trace"
    assert payload["observations"] == 2
    assert payload["usable_observations"] == 1
    assert payload["skipped_observations"] == 1
    assert payload["imports_generated_module"] is True
    lean = output.read_text()
    assert "import Autoform.Generated.Service" in lean
    assert "namespace Autoform.Specs.Trace.Service" in lean
    assert 'functionName := "pkg.mod.normalize"' in lean
    assert 'sourceTest := some "tests/test_mod.py::test_normalize"' in lean
    assert 'argsJson := "[\\" A \\"]"' in lean
    assert 'receiverStateJson := some "{\\"cache\\":[]}"' in lean
    assert 'sideEffectsJson := some "{\\"writes\\":[]}"' in lean
    assert "theorem observationCount_eq : observationCount = 2 := by decide" in lean
    assert "theorem usableObservationCount_eq : usableObservationCount = 1 := by decide" in lean
    assert "Skipped observations are visible evidence gaps" in lean


def test_spec_from_trace_refuses_empty_trace(tmp_path):
    trace = tmp_path / "trace.jsonl"
    trace.write_text("\n")
    with pytest.raises(SystemExit, match="zero behavior observations"):
        main(["spec-from-trace", str(trace), "Service", "--output", str(tmp_path / "Spec.lean")])


def test_trace_python_tests_runs_pytest_and_emits_spec(tmp_path, capsys):
    src = tmp_path / "pkg"
    tests_dir = src / "tests"
    tests_dir.mkdir(parents=True)
    (src / "mathy.py").write_text(
        "def add(x, y):\n"
        "    total = x + y\n"
        "    return total\n"
    )
    (tests_dir / "test_mathy.py").write_text(
        "from mathy import add\n\n"
        "def test_add():\n"
        "    assert add(2, 3) == 5\n"
    )
    trace = tmp_path / "trace.jsonl"
    spec = tmp_path / "MathyBehaviorSpec.lean"
    rc = main([
        "--json",
        "trace-python-tests",
        str(src),
        "Mathy",
        "--test-command",
        f"{sys.executable} -m pytest -q",
        "--trace-output",
        str(trace),
        "--spec-output",
        str(spec),
        "--no-generated-import",
    ])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["kind"] == "trace-python-tests"
    assert payload["returncode"] == 0
    assert payload["observations"] >= 1
    assert payload["usable_observations"] >= 1
    observations = [json.loads(line) for line in trace.read_text().splitlines()]
    assert any(obs["function"] == "mathy.add" and obs["result"] == 5 for obs in observations)
    lean = spec.read_text()
    assert "namespace Autoform.Specs.Trace.Mathy" in lean
    assert 'functionName := "mathy.add"' in lean
    assert "theorem usableObservationCount_eq" in lean


def test_trace_python_tests_rejects_zero_observations(tmp_path, capsys):
    src = tmp_path / "pkg"
    tests_dir = src / "tests"
    tests_dir.mkdir(parents=True)
    (tests_dir / "test_smoke.py").write_text("def test_smoke():\n    assert True\n")
    rc = main([
        "--json",
        "trace-python-tests",
        str(src),
        "Smoke",
        "--test-command",
        f"{sys.executable} -m pytest -q",
        "--trace-output",
        str(tmp_path / "trace.jsonl"),
        "--trace-only",
    ])
    assert rc == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["test_returncode"] == 0
    assert payload["returncode"] == 1
    assert payload["observations"] == 0
    assert payload["violations"][0]["message"] == "test command passed but no project function observations were recorded"


def test_seed_python_tests_writes_runnable_characterization_tests(tmp_path, capsys):
    src = tmp_path / "pkg"
    src.mkdir()
    (src / "mathy.py").write_text(
        "def add(x, y):\n"
        "    return x + y\n\n"
        "def hello():\n"
        "    return 'hi'\n\n"
        "def needs_input(value):\n"
        "    return value\n"
    )
    samples = tmp_path / "samples.json"
    samples.write_text(json.dumps({"mathy.add": [{"args": [2, 3], "kwargs": {}}]}))
    output = src / "tests" / "test_autoform_characterization.py"
    rc = main([
        "--json",
        "seed-python-tests",
        str(src),
        "Mathy",
        "--sample-cases",
        str(samples),
        "--output",
        str(output),
    ])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["kind"] == "seed-python-tests"
    assert payload["written_cases"] == 2
    assert payload["pending_functions"] == 1
    generated = output.read_text()
    assert "mathy.add#1" in generated
    assert "mathy.hello#1" in generated
    assert "mathy.needs_input" in generated
    run = subprocess.run([sys.executable, "-m", "pytest", "-q", str(output)], cwd=src, text=True, capture_output=True, check=False)
    assert run.returncode == 0, run.stdout + run.stderr
    assert "2 passed" in run.stdout
    assert "1 skipped" in run.stdout


def test_seed_python_tests_requires_runnable_cases(tmp_path, capsys):
    src = tmp_path / "pkg"
    src.mkdir()
    (src / "mathy.py").write_text("def needs_input(value):\n    return value\n")
    rc = main(["--json", "seed-python-tests", str(src), "Mathy", "--output", str(src / "tests" / "test_autoform.py")])
    assert rc == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["written_cases"] == 0
    assert payload["pending_functions"] == 1
    assert "no runnable characterization cases" in payload["violations"][0]["message"]


def test_seed_python_tests_pending_for_unencodable_return(tmp_path, capsys):
    src = tmp_path / "pkg"
    src.mkdir()
    (src / "handles.py").write_text(
        "def open_handle():\n"
        "    return object()\n"
    )
    output = src / "tests" / "test_autoform.py"
    rc = main([
        "--json",
        "seed-python-tests",
        str(src),
        "Handles",
        "--output",
        str(output),
        "--allow-empty",
    ])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["written_cases"] == 0
    assert payload["pending_functions"] == 1
    generated = output.read_text()
    assert "not JSON-serializable" in generated


def test_schema_outputs_behavior_trace_observation_schema(capsys):
    rc = main(["--json", "schema", "behavior-trace-observation"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["title"] == "Autoform behavior trace observation"
    assert payload["required"] == ["function"]
    assert "skip_reason" in payload["properties"]


def test_schema_outputs_config_schema(capsys):
    rc = main(["--json", "schema", "config"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["title"] == "Autoform CLI configuration"
    assert "targets" in payload["properties"]
    assert "test_command" in payload["properties"]["project"]["properties"]
    target_schema = payload["properties"]["targets"]["additionalProperties"]
    assert target_schema["required"] == ["source", "module"]
    assert "test_command" in target_schema["properties"]


def test_gate_fails_required_step(tmp_path, capsys):
    manifest = tmp_path / "run.json"
    manifest.write_text(json.dumps({
        "kind": "translate",
        "module": "Api",
        "source": "/srv/api",
        "run_id": "run1",
        "dry_run": False,
        "returncode": 0,
        "artifacts": [],
        "steps": [
            {
                "name": "type-check generated Lean",
                "command": ["lake", "build"],
                "returncode": 1,
                "required": True,
                "allow_failure": False,
            }
        ],
    }))
    rc = main(["--json", "gate", "--manifest", str(manifest)])
    assert rc == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["ok"] is False
    assert payload["violations"][0]["path"] == "steps[0].returncode"


def test_gate_can_require_artifacts(tmp_path, capsys):
    manifest = tmp_path / "run.json"
    manifest.write_text(json.dumps({
        "kind": "translate",
        "module": "Api",
        "source": "/srv/api",
        "run_id": "run1",
        "dry_run": False,
        "returncode": 0,
        "artifacts": ["missing.json"],
        "steps": [],
    }))
    rc = main([
        "--json",
        "gate",
        "--manifest",
        str(manifest),
        "--require-artifacts",
        "--root",
        str(tmp_path),
    ])
    assert rc == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["violations"][0]["path"] == "artifacts[0]"


def test_repo_root_flag_controls_pipeline_paths(capsys):
    root = Path(__file__).resolve().parents[1]
    rc = main(["--repo-root", str(root), "--dry-run", "--json", "translate", "/src/repo", "Service"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    commands = [" ".join(step["command"]) for step in payload["steps"]]
    assert any(str(root / "scripts" / "provenance.py") in command for command in commands)
    assert any(str(root / "cartographer" / "export_ast.sc") in command for command in commands)


def test_repo_root_rejects_non_autoform_dir(tmp_path):
    with pytest.raises(SystemExit):
        main(["--repo-root", str(tmp_path), "doctor"])


def test_bundle_packages_manifest_and_artifacts(tmp_path, capsys):
    artifact = tmp_path / "artifact.txt"
    artifact.write_text("evidence")
    manifest = tmp_path / "run.json"
    manifest.write_text(json.dumps({
        "kind": "translate",
        "module": "Api",
        "source": "/srv/api",
        "run_id": "run1",
        "dry_run": False,
        "returncode": 0,
        "artifacts": ["artifact.txt"],
        "steps": [],
    }))
    output = tmp_path / "bundle.tar.gz"
    rc = main([
        "--json",
        "bundle",
        "--manifest",
        str(manifest),
        "--output",
        str(output),
        "--root",
        str(tmp_path),
    ])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["ok"] is True
    assert output.exists()
    import tarfile
    with tarfile.open(output, "r:gz") as tar:
        assert sorted(tar.getnames()) == ["artifact.txt", "run.json"]


def test_bundle_fails_missing_artifact(tmp_path, capsys):
    manifest = tmp_path / "run.json"
    manifest.write_text(json.dumps({
        "kind": "translate",
        "module": "Api",
        "source": "/srv/api",
        "run_id": "run1",
        "dry_run": False,
        "returncode": 0,
        "artifacts": ["missing.txt"],
        "steps": [],
    }))
    rc = main([
        "--json",
        "bundle",
        "--manifest",
        str(manifest),
        "--output",
        str(tmp_path / "bundle.tar.gz"),
        "--root",
        str(tmp_path),
    ])
    assert rc == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["ok"] is False
    assert payload["missing"] == ["missing.txt"]


def test_check_writes_junit_report(tmp_path, capsys):
    report = tmp_path / "check.xml"
    rc = main(["--dry-run", "--json", "check", "--junit", str(report)])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["junit"] == str(report)
    assert report.exists()
    text = report.read_text()
    assert 'testsuite name="autoform-check"' in text
    assert 'testcase name="render-integrity check"' in text


def test_report_writes_markdown_evidence(tmp_path, capsys):
    artifact = tmp_path / "ledger-Api.json"
    artifact.write_text("{}")
    manifest = tmp_path / "run.json"
    manifest.write_text(json.dumps({
        "kind": "assure",
        "module": "Api",
        "source": "/srv/api",
        "run_id": "run1",
        "dry_run": False,
        "returncode": 1,
        "artifacts": ["ledger-Api.json", "missing.json"],
        "steps": [
            {
                "name": "type-check generated Lean",
                "command": ["lake", "build", "Autoform.Generated.Api"],
                "returncode": 1,
                "required": True,
                "allow_failure": False,
                "stderr_tail": "unknown declaration",
            }
        ],
    }))
    output = tmp_path / "report.md"
    rc = main([
        "--json",
        "report",
        "--manifest",
        str(manifest),
        "--output",
        str(output),
        "--root",
        str(tmp_path),
    ])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["kind"] == "report"
    assert payload["output"] == str(output)
    body = output.read_text()
    assert "# Autoform Evidence Report: Api" in body
    assert "Result: **failed**" in body
    assert "type-check generated Lean" in body
    assert "unknown declaration" in body
    assert "`ledger-Api.json` | true" in body
    assert "`missing.json` | false" in body


def test_lake_path_from_config_is_used_in_dry_run(tmp_path, capsys):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text('[runtime]\nlake = "/opt/lean/bin/lake"\n')
    rc = main(["--config", str(cfg), "--dry-run", "--json", "translate", "/src/repo", "Service"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    commands = {step["name"]: step["command"] for step in payload["steps"]}
    assert commands["type-check generated Lean"][:2] == ["/opt/lean/bin/lake", "build"]
    assert commands["emit trust ledger"][:3] == ["/opt/lean/bin/lake", "env", "lean"]
    assert payload["metadata"]["lake"] == "/opt/lean/bin/lake"


def test_runner_records_missing_executable_as_step_failure(tmp_path):
    from autoform_cli.pipeline import PipelineRunner

    runner = PipelineRunner(root=Path(__file__).resolve().parents[1], capture=True, artifact_dir=tmp_path / "run")
    missing = tmp_path / "definitely-missing-tool"
    with pytest.raises(SystemExit) as exc:
        runner.run("missing tool", [missing, "--version"])
    assert exc.value.code == 127
    assert runner.steps[0].returncode == 127
    assert "definitely-missing-tool" in (runner.steps[0].stderr_tail or "")
    result = runner.result("translate", "/src", "Service", runner.required_failure_rc())
    assert result.returncode == 127
    saved = json.loads((tmp_path / "run" / "run.json").read_text())
    assert saved["steps"][0]["returncode"] == 127


def test_check_writes_sarif_report(tmp_path, capsys):
    report = tmp_path / "check.sarif"
    rc = main(["--dry-run", "--json", "check", "--sarif", str(report)])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["sarif"] == str(report)
    data = json.loads(report.read_text())
    assert data["version"] == "2.1.0"
    assert data["runs"][0]["tool"]["driver"]["name"] == "autoform"
    assert data["runs"][0]["results"] == []


def test_targets_filter_by_metadata(tmp_path, capsys):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text(
        '[targets.payments]\n'
        'source = "/srv/payments"\n'
        'module = "Payments"\n'
        'owner = "payments"\n'
        'tier = "critical"\n'
        'tags = ["pci", "nightly"]\n\n'
        '[targets.search]\n'
        'source = "/srv/search"\n'
        'module = "Search"\n'
        'owner = "search"\n'
        'tier = "standard"\n'
        'tags = ["nightly"]\n'
    )
    rc = main(["--config", str(cfg), "--json", "targets", "--tag", "pci", "--owner", "payments", "--tier", "critical"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["count"] == 1
    assert payload["targets"][0]["name"] == "payments"
    assert payload["targets"][0]["tags"] == ["pci", "nightly"]


def test_batch_filters_targets_by_metadata(tmp_path, capsys):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text(
        '[targets.payments]\n'
        'source = "/srv/payments"\n'
        'module = "Payments"\n'
        'owner = "payments"\n'
        'tier = "critical"\n'
        'tags = ["nightly", "pci"]\n\n'
        '[targets.search]\n'
        'source = "/srv/search"\n'
        'module = "Search"\n'
        'owner = "search"\n'
        'tier = "standard"\n'
        'tags = ["nightly"]\n'
    )
    rc = main(["--config", str(cfg), "--dry-run", "--json", "batch", "--tag", "nightly", "--tier", "critical"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["count"] == 1
    assert payload["results"][0]["target"] == "payments"
    assert payload["results"][0]["owner"] == "payments"
    assert payload["results"][0]["tier"] == "critical"


def test_validate_rejects_bad_target_metadata(tmp_path, capsys):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text('[targets.api]\nsource = "/srv/api"\nmodule = "Api"\ntags = "nightly"\nowner = ["team"]\n')
    rc = main(["--config", str(cfg), "--json", "validate"])
    assert rc == 1
    payload = json.loads(capsys.readouterr().out)
    paths = {item["path"] for item in payload["violations"]}
    assert "targets.api.tags" in paths
    assert "targets.api.owner" in paths


def test_index_summarizes_multiple_manifests(tmp_path, capsys):
    good = tmp_path / "good.json"
    bad = tmp_path / "bad.json"
    good.write_text(json.dumps({
        "kind": "translate",
        "module": "Good",
        "source": "/srv/good",
        "run_id": "good",
        "dry_run": False,
        "returncode": 0,
        "artifacts": [],
        "steps": [],
    }))
    bad.write_text(json.dumps({
        "kind": "assure",
        "module": "Bad",
        "source": "/srv/bad",
        "run_id": "bad",
        "dry_run": False,
        "returncode": 1,
        "artifacts": [],
        "steps": [{"name": "type-check", "returncode": 1}],
    }))
    output = tmp_path / "index.json"
    rc = main(["--json", "index", str(good), str(bad), "--output", str(output)])
    assert rc == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["kind"] == "manifest-index"
    assert payload["count"] == 2
    assert payload["entries"][0]["ok"] is True
    assert payload["entries"][1]["failed_steps"] == 1
    assert output.exists()
    saved = json.loads(output.read_text())
    assert saved["output"] == str(output)


def test_index_can_require_artifacts(tmp_path, capsys):
    manifest = tmp_path / "run.json"
    manifest.write_text(json.dumps({
        "kind": "translate",
        "module": "Api",
        "source": "/srv/api",
        "run_id": "api",
        "dry_run": False,
        "returncode": 0,
        "artifacts": ["missing.txt"],
        "steps": [],
    }))
    rc = main(["--json", "index", str(manifest), "--root", str(tmp_path), "--require-artifacts"])
    assert rc == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["entries"][0]["missing_artifacts"] == ["missing.txt"]


def test_gate_accepts_passing_manifest_index(tmp_path, capsys):
    index = tmp_path / "fleet-index.json"
    index.write_text(json.dumps({
        "kind": "manifest-index",
        "count": 1,
        "returncode": 0,
        "ok": True,
        "require_artifacts": False,
        "entries": [
            {
                "manifest": "run.json",
                "kind": "translate",
                "module": "Api",
                "source": "/srv/api",
                "run_id": "api",
                "returncode": 0,
                "ok": True,
                "failed_steps": 0,
                "missing_artifacts": [],
            }
        ],
        "violations": [],
    }))
    rc = main(["--json", "gate", "--manifest", str(index)])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["ok"] is True


def test_gate_fails_manifest_index_entry_failures(tmp_path, capsys):
    index = tmp_path / "fleet-index.json"
    index.write_text(json.dumps({
        "kind": "manifest-index",
        "count": 1,
        "returncode": 1,
        "ok": False,
        "require_artifacts": True,
        "entries": [
            {
                "manifest": "run.json",
                "kind": "translate",
                "module": "Api",
                "source": "/srv/api",
                "run_id": "api",
                "returncode": 1,
                "ok": False,
                "failed_steps": 1,
                "missing_artifacts": ["ledger-Api.json"],
            }
        ],
        "violations": [],
    }))
    rc = main(["--json", "gate", "--manifest", str(index), "--require-artifacts"])
    assert rc == 1
    payload = json.loads(capsys.readouterr().out)
    paths = {item["path"] for item in payload["violations"]}
    assert "returncode" in paths
    assert "entries[0].returncode" in paths
    assert "entries[0].missing_artifacts" in paths


def test_schema_outputs_manifest_index_schema(capsys):
    rc = main(["--json", "schema", "manifest-index"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["title"] == "Autoform manifest index"
    assert payload["properties"]["kind"]["const"] == "manifest-index"
    assert "entries" in payload["properties"]


def test_report_writes_manifest_index_markdown(tmp_path, capsys):
    index = tmp_path / "fleet-index.json"
    index.write_text(json.dumps({
        "kind": "manifest-index",
        "count": 2,
        "returncode": 1,
        "ok": False,
        "require_artifacts": True,
        "entries": [
            {
                "manifest": "good/run.json",
                "kind": "translate",
                "module": "Good",
                "source": "/srv/good",
                "run_id": "good",
                "returncode": 0,
                "ok": True,
                "failed_steps": 0,
                "missing_artifacts": [],
            },
            {
                "manifest": "bad/run.json",
                "kind": "assure",
                "module": "Bad",
                "source": "/srv/bad",
                "run_id": "bad",
                "returncode": 1,
                "ok": False,
                "failed_steps": 1,
                "missing_artifacts": ["ledger-Bad.json"],
            },
        ],
        "violations": [{"path": "entries[1].returncode", "message": "entry failed"}],
    }))
    output = tmp_path / "fleet-report.md"
    rc = main(["--json", "report", "--manifest", str(index), "--output", str(output)])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["output"] == str(output)
    body = output.read_text()
    assert "# Autoform Fleet Evidence Report" in body
    assert "Result: **failed**" in body
    assert "Good" in body and "Bad" in body
    assert "ledger-Bad.json" in body
    assert "Index violations" in body


def test_plan_writes_filtered_fleet_plan(tmp_path, capsys):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text(
        '[targets.payments]\n'
        'source = "/srv/payments"\n'
        'module = "Payments"\n'
        'mode = "assure"\n'
        'owner = "payments"\n'
        'tier = "critical"\n'
        'tags = ["nightly", "pci"]\n\n'
        '[targets.search]\n'
        'source = "/srv/search"\n'
        'module = "Search"\n'
        'mode = "translate"\n'
        'owner = "search"\n'
        'tier = "standard"\n'
        'tags = ["nightly"]\n'
    )
    output = tmp_path / "plan.json"
    artifact_dir = tmp_path / "runs"
    rc = main([
        "--config", str(cfg),
        "--json",
        "--run-id", "nightly",
        "--artifact-dir", str(artifact_dir),
        "plan",
        "--tag", "nightly",
        "--tier", "critical",
        "--output", str(output),
    ])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["kind"] == "fleet-plan"
    assert payload["count"] == 1
    entry = payload["entries"][0]
    assert entry["target"] == "payments"
    assert entry["mode"] == "assure"
    assert entry["run_id"] == "nightly-payments"
    assert entry["artifact_dir"] == str(artifact_dir / "payments")
    assert entry["manifest"] == str(artifact_dir / "payments" / "run.json")
    assert output.exists()


def test_schema_outputs_fleet_plan_schema(capsys):
    rc = main(["--json", "schema", "fleet-plan"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["title"] == "Autoform fleet plan"
    assert payload["properties"]["kind"]["const"] == "fleet-plan"
    assert "entries" in payload["properties"]


def test_batch_can_apply_reviewed_plan(tmp_path, capsys):
    plan = tmp_path / "plan.json"
    artifact_dir = tmp_path / "runs" / "payments"
    plan.write_text(json.dumps({
        "kind": "fleet-plan",
        "count": 1,
        "run_id": "nightly",
        "artifact_dir": str(tmp_path / "runs"),
        "filters": {"tags": ["nightly"], "owner": None, "tier": None},
        "entries": [
            {
                "target": "payments",
                "mode": "translate",
                "source": "/srv/payments",
                "module": "Payments",
                "run_id": "nightly-payments",
                "artifact_dir": str(artifact_dir),
                "manifest": str(artifact_dir / "run.json"),
                "owner": "payments",
                "tier": "critical",
                "tags": ["nightly", "pci"],
                "conformance_cases": 7,
            }
        ],
    }))
    rc = main(["--dry-run", "--json", "batch", "--plan", str(plan)])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["plan"] == str(plan)
    assert payload["count"] == 1
    result = payload["results"][0]
    assert result["target"] == "payments"
    assert result["run_id"] == "nightly-payments"
    assert result["manifest"] == str(artifact_dir / "run.json")
    assert result["tags"] == ["nightly", "pci"]


def test_batch_plan_rejects_filters(tmp_path):
    plan = tmp_path / "plan.json"
    plan.write_text(json.dumps({"kind": "fleet-plan", "count": 0, "run_id": "r", "filters": {}, "entries": []}))
    with pytest.raises(SystemExit):
        main(["--dry-run", "batch", "--plan", str(plan), "--tag", "nightly"])


def test_verify_plan_passes_for_current_config(tmp_path, capsys):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text(
        '[targets.api]\n'
        'source = "/srv/api"\n'
        'module = "Api"\n'
        'mode = "translate"\n'
        'owner = "platform"\n'
        'tier = "critical"\n'
        'tags = ["nightly"]\n'
    )
    plan = tmp_path / "plan.json"
    rc = main(["--config", str(cfg), "--json", "--run-id", "nightly", "plan", "--tag", "nightly", "--output", str(plan)])
    assert rc == 0
    capsys.readouterr()
    rc = main(["--config", str(cfg), "--json", "verify-plan", "--plan", str(plan)])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["ok"] is True
    assert payload["violations"] == []


def test_verify_plan_detects_config_drift(tmp_path, capsys):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text(
        '[targets.api]\n'
        'source = "/srv/api"\n'
        'module = "Api"\n'
        'mode = "translate"\n'
        'tags = ["nightly"]\n'
    )
    plan = tmp_path / "plan.json"
    assert main(["--config", str(cfg), "--json", "--run-id", "nightly", "plan", "--tag", "nightly", "--output", str(plan)]) == 0
    capsys.readouterr()
    cfg.write_text(
        '[targets.api]\n'
        'source = "/srv/api-v2"\n'
        'module = "Api"\n'
        'mode = "translate"\n'
        'tags = ["nightly"]\n'
    )
    rc = main(["--config", str(cfg), "--json", "verify-plan", "--plan", str(plan), "--include-expected"])
    assert rc == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["ok"] is False
    assert any(item["path"] == "entries.api.source" for item in payload["violations"])
    assert payload["expected"]["entries"][0]["source"] == "/srv/api-v2"


def test_verify_plan_honors_explicit_target_subset(tmp_path, capsys):
    cfg = tmp_path / "autoform.toml"
    cfg.write_text(
        '[targets.api]\n'
        'source = "/srv/api"\n'
        'module = "Api"\n'
        'tags = ["nightly"]\n\n'
        '[targets.worker]\n'
        'source = "/srv/worker"\n'
        'module = "Worker"\n'
        'tags = ["nightly"]\n'
    )
    plan = tmp_path / "plan.json"
    rc = main(["--config", str(cfg), "--json", "--run-id", "nightly", "plan", "api", "--tag", "nightly", "--output", str(plan)])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["requested_targets"] == ["api"]
    assert [entry["target"] for entry in payload["entries"]] == ["api"]
    rc = main(["--config", str(cfg), "--json", "verify-plan", "--plan", str(plan), "--include-expected"])
    assert rc == 0
    verified = json.loads(capsys.readouterr().out)
    assert verified["ok"] is True
    assert [entry["target"] for entry in verified["expected"]["entries"]] == ["api"]
