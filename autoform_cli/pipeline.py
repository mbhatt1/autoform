"""Shared Autoform pipeline orchestration.

This module is the single execution path for the enterprise CLI and the legacy shell
entry points. It keeps the proof-producing tools unchanged, but moves orchestration into
Python so CI systems can inspect plans, capture run metadata, and avoid shell drift.
"""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
import uuid
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Mapping, Sequence

from . import __version__


ROOT = Path(__file__).resolve().parents[1]


@dataclass
class Step:
    name: str
    command: list[str]
    returncode: int | None = None
    required: bool = True
    allow_failure: bool = False
    elapsed_seconds: float | None = None
    stdout_tail: str | None = None
    stderr_tail: str | None = None

    def as_dict(self) -> dict[str, object]:
        return {
            "name": self.name,
            "command": self.command,
            "returncode": self.returncode,
            "required": self.required,
            "allow_failure": self.allow_failure,
            "elapsed_seconds": self.elapsed_seconds,
            "stdout_tail": self.stdout_tail,
            "stderr_tail": self.stderr_tail,
        }


@dataclass
class PipelineResult:
    kind: str
    module: str
    source: str | None
    run_id: str
    dry_run: bool
    returncode: int
    steps: list[Step] = field(default_factory=list)
    artifacts: list[str] = field(default_factory=list)
    manifest: str | None = None
    metadata: dict[str, object] = field(default_factory=dict)

    def as_dict(self) -> dict[str, object]:
        return {
            "kind": self.kind,
            "module": self.module,
            "source": self.source,
            "run_id": self.run_id,
            "dry_run": self.dry_run,
            "returncode": self.returncode,
            "steps": [s.as_dict() for s in self.steps],
            "artifacts": self.artifacts,
            "manifest": self.manifest,
            "metadata": self.metadata,
        }


class PipelineRunner:
    def __init__(
        self,
        *,
        root: Path = ROOT,
        env: Mapping[str, str] | None = None,
        dry_run: bool = False,
        capture: bool = False,
        run_id: str | None = None,
        artifact_dir: Path | None = None,
        keep_work: bool = False,
        metadata: Mapping[str, Any] | None = None,
    ) -> None:
        self.root = root
        self.env = dict(env or os.environ)
        self.dry_run = dry_run
        self.capture = capture
        self.run_id = run_id or time.strftime("%Y%m%d-%H%M%S-") + uuid.uuid4().hex[:8]
        self.artifact_dir = artifact_dir or (root / ".autoform-runs" / self.run_id)
        self.keep_work = keep_work
        self.lake = self.env.get("AUTOFORM_LAKE", "lake")
        self.metadata = dict(metadata or {})
        self.steps: list[Step] = []
        self.artifacts: list[str] = []


    def _git_output(self, *args: str) -> str | None:
        try:
            cp = subprocess.run(
                ["git", *args],
                cwd=self.root,
                text=True,
                capture_output=True,
                check=False,
                timeout=5,
            )
        except (OSError, subprocess.SubprocessError):
            return None
        if cp.returncode != 0:
            return None
        return cp.stdout.strip()

    def _run_metadata(self) -> dict[str, object]:
        status = self._git_output("status", "--short")
        metadata: dict[str, object] = {
            "autoform_cli_version": __version__,
            "repo_root": str(self.root),
            "git_commit": self._git_output("rev-parse", "HEAD"),
            "git_dirty": None if status is None else bool(status),
            "python_version": sys.version.split()[0],
            "python_executable": sys.executable,
            "lake": self.lake,
            "joern_home": self.env.get("JOERN_HOME", str(Path.home() / "joern")),
            "cpp_defines_set": bool(self.env.get("CPP_DEFINES")),
        }
        metadata.update(self.metadata)
        return metadata

    def _cmd(self, command: Sequence[object]) -> list[str]:
        return [str(part) for part in command]

    def add_plan(self, name: str, command: Sequence[object], *, required: bool = True, allow_failure: bool = False) -> Step:
        step = Step(name=name, command=self._cmd(command), required=required, allow_failure=allow_failure)
        self.steps.append(step)
        return step

    def run(
        self,
        name: str,
        command: Sequence[object],
        *,
        required: bool = True,
        allow_failure: bool = False,
        check_output: bool = False,
    ) -> subprocess.CompletedProcess[str] | None:
        step = self.add_plan(name, command, required=required, allow_failure=allow_failure)
        if self.dry_run:
            step.returncode = 0
            return None
        start = time.monotonic()
        try:
            if self.capture or check_output:
                cp = subprocess.run(
                    step.command,
                    cwd=self.root,
                    env=self.env,
                    text=True,
                    capture_output=True,
                    check=False,
                )
                step.stdout_tail = (cp.stdout or "")[-4000:]
                step.stderr_tail = (cp.stderr or "")[-4000:]
            else:
                cp = subprocess.run(step.command, cwd=self.root, env=self.env, text=True, check=False)
        except FileNotFoundError as exc:
            step.elapsed_seconds = round(time.monotonic() - start, 3)
            step.returncode = 127
            step.stderr_tail = str(exc)
            if required and not allow_failure:
                raise SystemExit(127) from exc
            return None
        step.elapsed_seconds = round(time.monotonic() - start, 3)
        step.returncode = int(cp.returncode)
        if cp.returncode != 0 and required and not allow_failure:
            raise SystemExit(cp.returncode)
        return cp

    def header(self, text: str) -> None:
        if not self.capture and not self.dry_run:
            print(f"\n\033[1m=== {text} ===\033[0m")

    def _record_artifact(self, path: Path) -> None:
        if path.exists():
            try:
                self.artifacts.append(str(path.relative_to(self.root)))
            except ValueError:
                self.artifacts.append(str(path))

    def _manifest_path(self) -> str:
        manifest = self.artifact_dir / "run.json"
        try:
            return str(manifest.relative_to(self.root))
        except ValueError:
            return str(manifest)

    def _write_manifest(self, result: PipelineResult) -> None:
        result.manifest = self._manifest_path()
        if self.dry_run:
            return
        self.artifact_dir.mkdir(parents=True, exist_ok=True)
        manifest = self.artifact_dir / "run.json"
        manifest.write_text(json.dumps(result.as_dict(), indent=2, sort_keys=True) + "\n")


    def required_failure_rc(self) -> int:
        for step in self.steps:
            if step.required and not step.allow_failure and step.returncode not in (None, 0):
                return int(step.returncode or 1)
        return 0

    def result(self, kind: str, source: str | None, module: str, returncode: int) -> PipelineResult:
        result = PipelineResult(
            kind=kind,
            module=module,
            source=source,
            run_id=self.run_id,
            dry_run=self.dry_run,
            returncode=returncode,
            steps=self.steps,
            artifacts=self.artifacts,
            metadata=self._run_metadata(),
        )
        self._write_manifest(result)
        return result

    def translate(self, source: Path, module: str, *, conformance_cases: int = 5) -> PipelineResult:
        source = source.expanduser()
        joern = Path(self.env.get("JOERN_HOME", str(Path.home() / "joern"))) / "joern-cli"
        cpp_defines = self.env.get("CPP_DEFINES", "")
        frontend_args: list[str] = []
        export_args: list[str] = []
        if cpp_defines:
            frontend_args.append("--frontend-args")
            for define in [d for d in cpp_defines.split(",") if d]:
                frontend_args.extend(["--define", define])
            export_args.extend(["--param", f"cppDefines={cpp_defines}"])

        work_path = Path("<work>") if self.dry_run else Path(tempfile.mkdtemp(prefix="autoform_"))
        cpg = work_path / "cpg.bin"
        ast = work_path / "ast.json"
        lean = self.root / "Autoform" / "Generated" / f"{module}.lean"
        tracked_ast = self.root / f"ast-{module}.json"
        workspace = self.root / "workspace"
        parse_command = [joern / "joern-parse", source, "--output", cpg, *frontend_args]
        export_command = [joern / "joern", "--script", self.root / "cartographer" / "export_ast.sc", "--param", f"cpgPath={cpg}", "--param", f"out={ast}", *export_args]
        provenance_command = (
            f"{' '.join(self._cmd(parse_command)).replace(str(cpg), '<cpg>')} && "
            f"{' '.join(self._cmd(export_command)).replace(str(cpg), '<cpg>').replace(str(ast), str(tracked_ast))}"
        )
        try:
            self.header("1/7 front-end pin")
            self.run(
                "check Joern version pin",
                [sys.executable, self.root / "scripts" / "provenance.py", "joern-version", "--check"],
            )

            self.header("2/7 parse")
            self.run("parse source with Joern", parse_command)

            self.header("3/7 formalization graph")
            self.run(
                "build formalization graph",
                [joern / "joern", "--script", self.root / "cartographer" / "formalization_graph.sc", "--param", f"cpgPath={cpg}", "--param", f"out={self.root / 'formalization-graph.json'}"],
                allow_failure=True,
                required=False,
            )

            self.header("4/7 export neutral AST")
            export_cp = self.run("export neutral AST", export_command, check_output=True)
            if export_cp is not None and (export_cp.returncode != 0 or "exported" not in (export_cp.stdout or "")):
                sys.stderr.write(export_cp.stdout or "")
                sys.stderr.write(export_cp.stderr or "")
                raise SystemExit(export_cp.returncode or 1)
            if not self.dry_run:
                shutil.copyfile(ast, tracked_ast)
                self._record_artifact(tracked_ast)

            self.run(
                "record AST provenance",
                [
                    sys.executable,
                    self.root / "scripts" / "provenance.py",
                    "record",
                    "--artifact",
                    tracked_ast,
                    "--source",
                    source,
                    "--exporter",
                    "cartographer/export_ast.sc",
                    "--command",
                    provenance_command,
                ],
            )
            self._record_artifact(self.root / "provenance" / f"{tracked_ast.name}.prov.json")

            self.header("5/7 render Lean")
            self.run(
                "render Lean module",
                [sys.executable, self.root / "cartographer" / "render_lean.py", ast, lean, module],
            )
            self._record_artifact(lean)

            self.header("6/7 build generated Lean")
            self.run("type-check generated Lean", [self.lake, "build", f"Autoform.Generated.{module}"])

            self.header("7/7 differential conformance")
            self.run(
                "differential conformance",
                [sys.executable, self.root / "scripts" / "differential.py", ast, source, module, str(conformance_cases)],
                required=False,
                allow_failure=True,
            )
            self._record_artifact(self.root / "conformance.json")

            ledger = work_path / "Ledger.lean"
            if self.dry_run:
                self.add_plan("render trust ledger harness", ["template", "scripts/ledger.lean.tmpl", "--module", module, "--out", ledger])
            else:
                template = (self.root / "scripts" / "ledger.lean.tmpl").read_text()
                ledger.write_text(template.replace("@MODULE@", module))
            self.run("emit trust ledger", [self.lake, "env", "lean", ledger])
            self._record_artifact(self.root / f"ledger-{module}.json")
            result = self.result("translate", str(source), module, self.required_failure_rc())
            return result
        except SystemExit as exc:
            rc = int(exc.code or self.required_failure_rc() or 1)
            return self.result("translate", str(source), module, rc)
        finally:
            if not self.dry_run and not self.keep_work:
                shutil.rmtree(work_path, ignore_errors=True)
                shutil.rmtree(workspace, ignore_errors=True)

    def assure(self, source: Path, module: str) -> PipelineResult:
        source = source.expanduser()
        self.header("1/5 translate")
        translate_result = self.translate(source, module)
        translate_rc = int(translate_result.returncode)
        if translate_rc and not self.dry_run and not self.capture:
            print("  translate: FAILED")

        self.header("2/5 conformance vs real runtime")
        self.run(
            "conformance vs real runtime",
            [sys.executable, self.root / "scripts" / "differential.py", self.root / f"ast-{module}.json", source, module, "5"],
            required=False,
            allow_failure=True,
        )
        self._record_artifact(self.root / "conformance.json")

        self.header("3/5 axiom + escape-hatch audit")
        self.run("build whole library for audit", [self.lake, "build"], required=False, allow_failure=True)
        audit_flags = self.env.get("AUTOFORM_AUDIT_FLAGS", "--skip-kernel").split()
        self.run(
            "trust audit",
            [sys.executable, self.root / "scripts" / "audit_all.py", *audit_flags],
            required=False,
            allow_failure=True,
        )
        self._record_artifact(self.root / "audit.json")

        self.header("4/5 specification teeth")
        spec = self.root / "Autoform" / "Specs" / f"{module}Spec.lean"
        if spec.exists() or self.dry_run:
            self.run(
                "mutation gate",
                [sys.executable, self.root / "scripts" / "mutate.py", self.root / "Autoform" / "Generated" / f"{module}.lean", f"Autoform.Generated.{module}", "--max-mutants", "8"],
                required=False,
                allow_failure=True,
            )
            self._record_artifact(self.root / "mutation.json")
        else:
            if not self.capture and not self.dry_run:
                print(f"  no Autoform/Specs/{module}Spec.lean — G4 will be UNDEVELOPED for {module} (correct)")

        self.header("5/5 assurance case")
        self.run("render-integrity check", [sys.executable, self.root / "scripts" / "check_render.py"], required=False, allow_failure=True)
        self.run("documentation consistency check", [sys.executable, self.root / "scripts" / "check_docs.py"], required=False, allow_failure=True)
        self.run("emit contracts", [sys.executable, self.root / "scripts" / "emit_contracts.py", module])
        self._record_artifact(self.root / f"contracts-{module}.json")
        self.run("build SACM assurance case", [sys.executable, self.root / "scripts" / "sacm.py", "--module", module])
        self._record_artifact(self.root / f"sacm-{module}.json")

        artifacts = [
            "formalization-graph.json",
            f"ast-{module}.json",
            f"ledger-{module}.json",
            "conformance.json",
            "audit.json",
            "mutation.json",
            f"sacm-{module}.json",
        ]
        if not self.capture and not self.dry_run:
            print("\n\033[1m=== artifacts ===\033[0m")
            for artifact in artifacts:
                if (self.root / artifact).exists():
                    print(artifact)
        for artifact in artifacts:
            self._record_artifact(self.root / artifact)

        rc = translate_rc
        for step in self.steps:
            if step.required and not step.allow_failure and step.returncode not in (None, 0):
                rc = rc or int(step.returncode or 1)
        return self.result("assure", str(source), module, rc)
