"""Enterprise-oriented command line entry point for Autoform.

The CLI is intentionally a thin orchestration layer over the existing, reviewed shell and
Python tools. It adds stable command names, configuration loading, dry-run support,
machine-readable output, and preflight checks without changing the proof-producing path.
"""
from __future__ import annotations

import argparse
import glob as glob_mod
import json
import os
import shutil
import subprocess
import sys
import tarfile
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

from . import __version__
from . import pipeline as pipeline_mod
from .pipeline import PipelineRunner


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CONFIG_NAMES = ("autoform.toml", ".autoform.toml")


def _repo_root_from(raw: str | None) -> Path:
    value = raw or os.environ.get("AUTOFORM_ROOT")
    path = Path(value).expanduser().resolve() if value else ROOT
    required = [path / "cartographer" / "render_lean.py", path / "scripts" / "provenance.py"]
    missing = [str(item) for item in required if not item.exists()]
    if missing:
        raise SystemExit(f"{path} is not an Autoform repo root; missing {', '.join(missing)}")
    return path


def _set_repo_root(path: Path) -> None:
    global ROOT
    ROOT = path
    pipeline_mod.ROOT = path


@dataclass(frozen=True)
class CommandResult:
    command: list[str]
    cwd: str
    returncode: int
    dry_run: bool = False


RUN_MANIFEST_SCHEMA: dict[str, Any] = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "$id": "https://autoform.local/schemas/run-manifest.json",
    "title": "Autoform run manifest",
    "type": "object",
    "required": ["kind", "module", "run_id", "dry_run", "returncode", "steps", "artifacts"],
    "properties": {
        "kind": {"type": "string", "enum": ["translate", "assure"]},
        "module": {"type": "string"},
        "source": {"type": ["string", "null"]},
        "run_id": {"type": "string"},
        "dry_run": {"type": "boolean"},
        "returncode": {"type": "integer"},
        "manifest": {"type": ["string", "null"]},
        "metadata": {
            "type": "object",
            "properties": {
                "autoform_cli_version": {"type": "string"},
                "repo_root": {"type": "string"},
                "config": {"type": ["string", "null"]},
                "git_commit": {"type": ["string", "null"]},
                "git_dirty": {"type": ["boolean", "null"]},
                "python_version": {"type": "string"},
                "python_executable": {"type": "string"},
                "lake": {"type": "string"},
                "joern_home": {"type": "string"},
                "cpp_defines_set": {"type": "boolean"},
            },
            "additionalProperties": True,
        },
        "artifacts": {"type": "array", "items": {"type": "string"}},
        "steps": {
            "type": "array",
            "items": {
                "type": "object",
                "required": ["name", "command", "returncode", "required", "allow_failure"],
                "properties": {
                    "name": {"type": "string"},
                    "command": {"type": "array", "items": {"type": "string"}},
                    "returncode": {"type": ["integer", "null"]},
                    "required": {"type": "boolean"},
                    "allow_failure": {"type": "boolean"},
                    "elapsed_seconds": {"type": ["number", "null"]},
                    "stdout_tail": {"type": ["string", "null"]},
                    "stderr_tail": {"type": ["string", "null"]},
                },
                "additionalProperties": True,
            },
        },
    },
    "additionalProperties": True,
}


MANIFEST_INDEX_SCHEMA: dict[str, Any] = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "$id": "https://autoform.local/schemas/manifest-index.json",
    "title": "Autoform manifest index",
    "type": "object",
    "required": ["kind", "count", "returncode", "ok", "entries", "violations"],
    "properties": {
        "kind": {"type": "string", "const": "manifest-index"},
        "count": {"type": "integer"},
        "returncode": {"type": "integer"},
        "ok": {"type": "boolean"},
        "require_artifacts": {"type": "boolean"},
        "output": {"type": "string"},
        "entries": {
            "type": "array",
            "items": {
                "type": "object",
                "required": ["manifest", "returncode", "ok"],
                "properties": {
                    "manifest": {"type": "string"},
                    "kind": {"type": ["string", "null"]},
                    "module": {"type": ["string", "null"]},
                    "source": {"type": ["string", "null"]},
                    "run_id": {"type": ["string", "null"]},
                    "returncode": {"type": "integer"},
                    "ok": {"type": "boolean"},
                    "steps": {"type": ["integer", "null"]},
                    "failed_steps": {"type": "integer"},
                    "artifacts": {"type": ["integer", "null"]},
                    "missing_artifacts": {"type": "array", "items": {"type": "string"}},
                },
                "additionalProperties": True,
            },
        },
        "violations": {
            "type": "array",
            "items": {
                "type": "object",
                "required": ["path", "message"],
                "properties": {
                    "path": {"type": "string"},
                    "message": {"type": "string"},
                },
                "additionalProperties": True,
            },
        },
    },
    "additionalProperties": True,
}


FLEET_PLAN_SCHEMA: dict[str, Any] = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "$id": "https://autoform.local/schemas/fleet-plan.json",
    "title": "Autoform fleet plan",
    "type": "object",
    "required": ["kind", "count", "run_id", "filters", "entries"],
    "properties": {
        "kind": {"type": "string", "const": "fleet-plan"},
        "count": {"type": "integer"},
        "run_id": {"type": "string"},
        "artifact_dir": {"type": ["string", "null"]},
        "requested_targets": {"type": "array", "items": {"type": "string"}},
        "mode": {"type": ["string", "null"], "enum": ["translate", "assure", None]},
        "conformance_cases": {"type": "integer"},
        "filters": {"type": "object"},
        "entries": {
            "type": "array",
            "items": {
                "type": "object",
                "required": ["target", "mode", "source", "module", "run_id", "manifest"],
                "properties": {
                    "target": {"type": "string"},
                    "mode": {"type": "string", "enum": ["translate", "assure"]},
                    "source": {"type": "string"},
                    "module": {"type": "string"},
                    "run_id": {"type": "string"},
                    "artifact_dir": {"type": "string"},
                    "manifest": {"type": "string"},
                    "owner": {"type": ["string", "null"]},
                    "tier": {"type": ["string", "null"]},
                    "tags": {"type": "array", "items": {"type": "string"}},
                    "conformance_cases": {"type": "integer"},
                },
                "additionalProperties": True,
            },
        },
    },
    "additionalProperties": True,
}


SPEC_PLAN_SCHEMA: dict[str, Any] = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "$id": "https://autoform.local/schemas/spec-plan.json",
    "title": "Autoform test-first specification plan",
    "type": "object",
    "required": ["kind", "source", "module", "strategy", "phases", "artifacts"],
    "properties": {
        "kind": {"type": "string", "const": "spec-plan"},
        "source": {"type": "string"},
        "module": {"type": "string"},
        "strategy": {"type": "string", "const": "test-first-autoformalization"},
        "test_command": {"type": ["string", "null"]},
        "test_framework": {"type": ["string", "null"]},
        "trace_format": {"type": "string"},
        "phases": {
            "type": "array",
            "items": {
                "type": "object",
                "required": ["name", "purpose", "outputs"],
                "properties": {
                    "name": {"type": "string"},
                    "purpose": {"type": "string"},
                    "command": {"type": ["string", "null"]},
                    "outputs": {"type": "array", "items": {"type": "string"}},
                    "rejects": {"type": "array", "items": {"type": "string"}},
                },
                "additionalProperties": True,
            },
        },
        "artifacts": {"type": "array", "items": {"type": "string"}},
        "anti_vacuity": {"type": "array", "items": {"type": "string"}},
    },
    "additionalProperties": True,
}

CONFIG_SCHEMA: dict[str, Any] = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "$id": "https://autoform.local/schemas/autoform-config.json",
    "title": "Autoform CLI configuration",
    "type": "object",
    "properties": {
        "project": {
            "type": "object",
            "properties": {
                "source": {"type": "string"},
                "module": {"type": "string", "pattern": "^[A-Za-z][A-Za-z0-9_]*$"},
                "ast": {"type": "string"},
                "lean_output": {"type": "string"},
                "test_command": {"type": "string"},
                "test_framework": {"type": "string"},
            },
            "additionalProperties": True,
        },
        "runtime": {
            "type": "object",
            "properties": {
                "joern_home": {"type": "string"},
                "lake": {"type": "string"},
                "cpp_defines": {
                    "oneOf": [
                        {"type": "string"},
                        {"type": "array", "items": {"type": "string"}},
                    ]
                },
            },
            "additionalProperties": True,
        },
        "targets": {
            "type": "object",
            "additionalProperties": {
                "type": "object",
                "required": ["source", "module"],
                "properties": {
                    "source": {"type": "string"},
                    "module": {"type": "string", "pattern": "^[A-Za-z][A-Za-z0-9_]*$"},
                    "mode": {"type": "string", "enum": ["translate", "assure"]},
                    "owner": {"type": "string"},
                    "tier": {"type": "string"},
                    "tags": {"type": "array", "items": {"type": "string"}},
                    "test_command": {"type": "string"},
                    "test_framework": {"type": "string"},
                    "joern_home": {"type": "string"},
                    "lake": {"type": "string"},
                    "cpp_defines": {
                        "oneOf": [
                            {"type": "string"},
                            {"type": "array", "items": {"type": "string"}},
                        ]
                    },
                },
                "additionalProperties": True,
            },
        },
    },
    "additionalProperties": True,
}


def _is_valid_module_name(value: str | None) -> bool:
    if not value:
        return False
    return value.replace("_", "").isalnum() and value[0].isalpha()


def _mode(value: Any) -> str:
    return str(value or "translate")


def _validate_config(config: Mapping[str, Any], *, require_existing_source: bool = False) -> list[dict[str, str]]:
    violations: list[dict[str, str]] = []

    def add(path: str, message: str) -> None:
        violations.append({"path": path, "message": message})

    project = _section(config, "project")
    if project:
        module = project.get("module")
        if module is not None and not _is_valid_module_name(str(module)):
            add("project.module", "module must start with a letter and contain only letters, digits or underscores")
        source = project.get("source")
        if require_existing_source and source and not Path(str(source)).expanduser().exists():
            add("project.source", "source path does not exist")

    runtime = _section(config, "runtime")
    if "cpp_defines" in runtime and not isinstance(runtime["cpp_defines"], (str, list)):
        add("runtime.cpp_defines", "cpp_defines must be a string or an array of strings")
    if isinstance(runtime.get("cpp_defines"), list) and not all(isinstance(x, str) for x in runtime["cpp_defines"]):
        add("runtime.cpp_defines", "cpp_defines array must contain only strings")
    if "joern_home" in runtime and not isinstance(runtime["joern_home"], str):
        add("runtime.joern_home", "joern_home must be a string")
    if "lake" in runtime and not isinstance(runtime["lake"], str):
        add("runtime.lake", "lake must be a string")
    for key in ("test_command", "test_framework"):
        if key in project and not isinstance(project[key], str):
            add(f"project.{key}", f"{key} must be a string")

    targets = _target_map(config)
    for raw_name, raw_target in targets.items():
        name = str(raw_name)
        path = f"targets.{name}"
        if not name.replace("_", "").replace("-", "").isalnum():
            add(path, "target name should contain only letters, digits, underscores or hyphens")
        if not isinstance(raw_target, Mapping):
            add(path, "target must be a table")
            continue
        source = raw_target.get("source")
        if not source:
            add(f"{path}.source", "source is required")
        elif require_existing_source and not Path(str(source)).expanduser().exists():
            add(f"{path}.source", "source path does not exist")
        module = raw_target.get("module")
        if not _is_valid_module_name(str(module) if module is not None else None):
            add(f"{path}.module", "module is required and must start with a letter")
        mode = _mode(raw_target.get("mode"))
        if mode not in ("translate", "assure"):
            add(f"{path}.mode", "mode must be 'translate' or 'assure'")
        cpp_defines = raw_target.get("cpp_defines")
        if cpp_defines is not None and not isinstance(cpp_defines, (str, list)):
            add(f"{path}.cpp_defines", "cpp_defines must be a string or an array of strings")
        if isinstance(cpp_defines, list) and not all(isinstance(x, str) for x in cpp_defines):
            add(f"{path}.cpp_defines", "cpp_defines array must contain only strings")
        joern_home = raw_target.get("joern_home")
        if joern_home is not None and not isinstance(joern_home, str):
            add(f"{path}.joern_home", "joern_home must be a string")
        for key in ("test_command", "test_framework"):
            if key in raw_target and not isinstance(raw_target[key], str):
                add(f"{path}.{key}", f"{key} must be a string")
        lake = raw_target.get("lake")
        if lake is not None and not isinstance(lake, str):
            add(f"{path}.lake", "lake must be a string")
        owner = raw_target.get("owner")
        if owner is not None and not isinstance(owner, str):
            add(f"{path}.owner", "owner must be a string")
        tier = raw_target.get("tier")
        if tier is not None and not isinstance(tier, str):
            add(f"{path}.tier", "tier must be a string")
        tags = raw_target.get("tags")
        if tags is not None and not (isinstance(tags, list) and all(isinstance(x, str) for x in tags)):
            add(f"{path}.tags", "tags must be an array of strings")
    return violations


def _load_manifest(path: Path) -> tuple[dict[str, Any] | None, list[dict[str, str]]]:
    if not path.exists():
        return None, [{"path": str(path), "message": "manifest file does not exist"}]
    try:
        data = json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        return None, [{"path": str(path), "message": f"manifest is not valid JSON: {exc.msg}"}]
    if not isinstance(data, dict):
        return None, [{"path": str(path), "message": "manifest root must be an object"}]
    return data, []


def _load_plan(path: Path) -> tuple[dict[str, Any] | None, list[dict[str, str]]]:
    data, violations = _load_manifest(path)
    if data is None:
        return None, violations
    if data.get("kind") != "fleet-plan":
        return None, [{"path": str(path), "message": "plan file must have kind='fleet-plan'"}]
    entries = data.get("entries")
    if not isinstance(entries, list):
        return None, [{"path": "entries", "message": "fleet plan entries must be an array"}]
    required = ("target", "mode", "source", "module", "run_id", "artifact_dir", "manifest")
    plan_violations: list[dict[str, str]] = []
    for index, raw in enumerate(entries):
        if not isinstance(raw, Mapping):
            plan_violations.append({"path": f"entries[{index}]", "message": "entry must be an object"})
            continue
        for key in required:
            if key not in raw:
                plan_violations.append({"path": f"entries[{index}].{key}", "message": "required field is missing"})
        mode = raw.get("mode")
        if mode not in ("translate", "assure"):
            plan_violations.append({"path": f"entries[{index}].mode", "message": "mode must be 'translate' or 'assure'"})
    if plan_violations:
        return None, plan_violations
    return data, []


def _index_gate_violations(data: Mapping[str, Any], *, require_artifacts: bool) -> list[dict[str, str]]:
    violations: list[dict[str, str]] = []

    def add(path: str, message: str) -> None:
        violations.append({"path": path, "message": message})

    if data.get("returncode") != 0:
        add("returncode", f"fleet index returned {data.get('returncode')!r}")
    if data.get("ok") is not True:
        add("ok", "fleet index is not ok")
    entries = data.get("entries")
    if not isinstance(entries, list):
        add("entries", "entries must be an array")
        return violations
    for index, raw in enumerate(entries):
        path = f"entries[{index}]"
        if not isinstance(raw, Mapping):
            add(path, "entry must be an object")
            continue
        if raw.get("returncode") != 0:
            add(f"{path}.returncode", f"entry {raw.get('module') or raw.get('manifest') or index!r} returned {raw.get('returncode')!r}")
        if raw.get("ok") is not True:
            add(f"{path}.ok", f"entry {raw.get('module') or raw.get('manifest') or index!r} is not ok")
        missing = raw.get("missing_artifacts", [])
        if require_artifacts and missing:
            if not isinstance(missing, list):
                add(f"{path}.missing_artifacts", "missing_artifacts must be an array")
            else:
                for artifact in missing:
                    add(f"{path}.missing_artifacts", f"artifact does not exist: {artifact}")
    return violations


def _manifest_gate_violations(data: Mapping[str, Any], *, require_artifacts: bool, root: Path) -> list[dict[str, str]]:
    if data.get("kind") == "manifest-index":
        return _index_gate_violations(data, require_artifacts=require_artifacts)

    violations: list[dict[str, str]] = []

    def add(path: str, message: str) -> None:
        violations.append({"path": path, "message": message})

    if data.get("returncode") != 0:
        add("returncode", f"pipeline returned {data.get('returncode')!r}")
    steps = data.get("steps")
    if not isinstance(steps, list):
        add("steps", "steps must be an array")
    else:
        for index, raw in enumerate(steps):
            path = f"steps[{index}]"
            if not isinstance(raw, Mapping):
                add(path, "step must be an object")
                continue
            required = bool(raw.get("required", True))
            allow_failure = bool(raw.get("allow_failure", False))
            rc = raw.get("returncode")
            if required and not allow_failure and rc != 0:
                name = raw.get("name", f"step {index}")
                add(f"{path}.returncode", f"required step {name!r} returned {rc!r}")
    artifacts = data.get("artifacts", [])
    if require_artifacts:
        if not isinstance(artifacts, list):
            add("artifacts", "artifacts must be an array")
        else:
            for index, artifact in enumerate(artifacts):
                if not isinstance(artifact, str):
                    add(f"artifacts[{index}]", "artifact path must be a string")
                    continue
                candidate = Path(artifact).expanduser()
                if not candidate.is_absolute():
                    candidate = root / candidate
                if not candidate.exists():
                    add(f"artifacts[{index}]", f"artifact does not exist: {artifact}")
    return violations


def _parse_simple_toml(text: str, path: Path) -> dict[str, Any]:
    """Parse the small config subset Autoform needs when tomllib/tomli is unavailable.

    Supported syntax is intentionally narrow: section headers, string values and arrays of
    strings. That keeps Python 3.9 usable without making this a general TOML parser.
    """
    data: dict[str, Any] = {}
    current: dict[str, Any] = data
    for lineno, raw in enumerate(text.splitlines(), 1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        if line.startswith("[") and line.endswith("]"):
            name = line[1:-1].strip()
            if not name:
                raise SystemExit(f"{path}:{lineno}: empty section name")
            current = data
            for part in name.split("."):
                part = part.strip()
                if not part:
                    raise SystemExit(f"{path}:{lineno}: empty section path component")
                current = current.setdefault(part, {})
                if not isinstance(current, dict):
                    raise SystemExit(f"{path}:{lineno}: section conflicts with scalar value")
            continue
        if "=" not in line:
            raise SystemExit(f"{path}:{lineno}: unsupported TOML syntax")
        key, value = [part.strip() for part in line.split("=", 1)]
        if value.startswith('"') and value.endswith('"'):
            current[key] = value[1:-1]
        elif value.startswith("[") and value.endswith("]"):
            items = []
            body = value[1:-1].strip()
            if body:
                for item in body.split(","):
                    item = item.strip()
                    if not (item.startswith('"') and item.endswith('"')):
                        raise SystemExit(f"{path}:{lineno}: only string arrays are supported")
                    items.append(item[1:-1])
            current[key] = items
        else:
            raise SystemExit(f"{path}:{lineno}: only quoted strings and string arrays are supported")
    return data


def _load_toml(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    try:
        import tomllib  # Python 3.11+
    except ModuleNotFoundError:  # pragma: no cover - exercised only on old Python
        try:
            import tomli as tomllib  # type: ignore
        except ModuleNotFoundError:
            return _parse_simple_toml(path.read_text(), path)
    with path.open("rb") as f:
        data = tomllib.load(f)
    if not isinstance(data, dict):
        raise SystemExit(f"{path}: expected a TOML table at the root")
    return data


def _find_config(explicit: str | None, cwd: Path, repo_root: Path | None = None) -> tuple[Path | None, dict[str, Any]]:
    if explicit:
        path = Path(explicit).expanduser().resolve()
        return path, _load_toml(path)
    search_dirs = [cwd]
    if repo_root is not None and repo_root != cwd:
        search_dirs.append(repo_root)
    for directory in search_dirs:
        for name in DEFAULT_CONFIG_NAMES:
            path = directory / name
            if path.exists():
                return path, _load_toml(path)
    return None, {}


def _section(config: Mapping[str, Any], name: str) -> Mapping[str, Any]:
    value = config.get(name, {})
    if value is None:
        return {}
    if not isinstance(value, Mapping):
        raise SystemExit(f"config section [{name}] must be a table")
    return value


def _cfg(config: Mapping[str, Any], section: str, key: str, default: Any = None) -> Any:
    sec = _section(config, section)
    return sec.get(key, default)


def _module_name(raw: str | None, default: str = "Translated") -> str:
    value = raw or default
    if not value.replace("_", "").isalnum() or not value[0].isalpha():
        raise SystemExit(
            f"invalid module name {value!r}: use a Lean-style alphanumeric name starting with a letter"
        )
    return value


def _target_map(config: Mapping[str, Any]) -> Mapping[str, Any]:
    targets = config.get("targets", {})
    if targets is None:
        return {}
    if not isinstance(targets, Mapping):
        raise SystemExit("config section [targets] must contain target tables")
    return targets


def _target_config(config: Mapping[str, Any], name: str | None) -> Mapping[str, Any]:
    if not name:
        return {}
    targets = _target_map(config)
    value = targets.get(name)
    if value is None:
        raise SystemExit(f"unknown target {name!r}; run `autoform targets` to list configured targets")
    if not isinstance(value, Mapping):
        raise SystemExit(f"config target {name!r} must be a table")
    return value


def _target_names(config: Mapping[str, Any]) -> list[str]:
    return sorted(str(name) for name, value in _target_map(config).items() if isinstance(value, Mapping))


def _target_tags(target: Mapping[str, Any]) -> list[str]:
    raw = target.get("tags", [])
    if isinstance(raw, list):
        return [str(tag) for tag in raw]
    return []


def _target_payload(name: str, target: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "name": name,
        "source": target.get("source"),
        "module": target.get("module"),
        "mode": target.get("mode", "translate"),
        "owner": target.get("owner"),
        "tier": target.get("tier"),
        "tags": _target_tags(target),
    }


def _target_matches(target: Mapping[str, Any], *, tags: Sequence[str] = (), owner: str | None = None, tier: str | None = None) -> bool:
    target_tags = set(_target_tags(target))
    if tags and not set(tags).issubset(target_tags):
        return False
    if owner and str(target.get("owner", "")) != owner:
        return False
    if tier and str(target.get("tier", "")) != tier:
        return False
    return True


def _select_target_names(config: Mapping[str, Any], names: Sequence[str] = (), *, tags: Sequence[str] = (), owner: str | None = None, tier: str | None = None) -> list[str]:
    selected = list(names) if names else _target_names(config)
    out: list[str] = []
    for name in selected:
        target = _target_config(config, name)
        if _target_matches(target, tags=tags, owner=owner, tier=tier):
            out.append(str(name))
    return out


def _resolve_project(config: Mapping[str, Any], target: str | None) -> Mapping[str, Any]:
    merged: dict[str, Any] = dict(_section(config, "project"))
    merged.update(dict(_target_config(config, target)))
    return merged


def _env_from_args(args: argparse.Namespace, config: Mapping[str, Any], target_config: Mapping[str, Any] | None = None) -> dict[str, str]:
    env = os.environ.copy()
    runtime = _section(config, "runtime")
    target_config = target_config or {}
    joern_home = args.joern_home or target_config.get("joern_home") or runtime.get("joern_home")
    if joern_home:
        env["JOERN_HOME"] = str(Path(str(joern_home)).expanduser())
    lake = args.lake or target_config.get("lake") or runtime.get("lake")
    if lake:
        env["AUTOFORM_LAKE"] = str(Path(str(lake)).expanduser()) if os.sep in str(lake) else str(lake)
    cpp_defines = args.cpp_defines or target_config.get("cpp_defines") or runtime.get("cpp_defines")
    if isinstance(cpp_defines, list):
        cpp_defines = ",".join(str(x) for x in cpp_defines)
    if cpp_defines:
        env["CPP_DEFINES"] = str(cpp_defines)
    env.setdefault("LANG", "C.UTF-8")
    env.setdefault("LC_ALL", "C.UTF-8")
    java_opts = env.get("JAVA_TOOL_OPTIONS", "")
    if "-Dfile.encoding" not in java_opts:
        env["JAVA_TOOL_OPTIONS"] = (java_opts + " -Dfile.encoding=UTF-8").strip()
    return env


def _write_junit(path: Path, suite_name: str, cases: Sequence[Mapping[str, Any]]) -> None:
    tests = len(cases)
    failures = sum(1 for case in cases if int(case.get("returncode") or 0) != 0)
    suite = ET.Element("testsuite", {
        "name": suite_name,
        "tests": str(tests),
        "failures": str(failures),
    })
    for case in cases:
        name = str(case.get("name", "check"))
        testcase = ET.SubElement(suite, "testcase", {"name": name})
        rc = int(case.get("returncode") or 0)
        stdout = str(case.get("stdout_tail") or "")
        stderr = str(case.get("stderr_tail") or "")
        if rc != 0:
            failure = ET.SubElement(testcase, "failure", {
                "message": f"{name} exited {rc}",
                "type": "AutoformCheckFailure",
            })
            failure.text = (stderr or stdout or f"returncode={rc}")[-4000:]
        if stdout:
            ET.SubElement(testcase, "system-out").text = stdout
        if stderr:
            ET.SubElement(testcase, "system-err").text = stderr
    path.parent.mkdir(parents=True, exist_ok=True)
    ET.ElementTree(suite).write(path, encoding="utf-8", xml_declaration=True)


def _write_sarif(path: Path, cases: Sequence[Mapping[str, Any]]) -> None:
    rules = []
    results = []
    seen: set[str] = set()
    for case in cases:
        name = str(case.get("name", "check"))
        rule_id = "autoform." + "".join(ch.lower() if ch.isalnum() else "-" for ch in name).strip("-")
        if rule_id not in seen:
            seen.add(rule_id)
            rules.append({
                "id": rule_id,
                "name": name,
                "shortDescription": {"text": name},
                "helpUri": "https://github.com/mbhatt1/autoform",
            })
        rc = int(case.get("returncode") or 0)
        if rc == 0:
            continue
        command = case.get("command")
        uri = ""
        if isinstance(command, list) and len(command) > 1:
            uri = str(command[1])
        message = str(case.get("stderr_tail") or case.get("stdout_tail") or f"{name} exited {rc}")[-4000:]
        results.append({
            "ruleId": rule_id,
            "level": "error",
            "message": {"text": message},
            "locations": [{"physicalLocation": {"artifactLocation": {"uri": uri}}}],
        })
    payload = {
        "version": "2.1.0",
        "$schema": "https://json.schemastore.org/sarif-2.1.0.json",
        "runs": [{
            "tool": {"driver": {"name": "autoform", "version": __version__, "rules": rules}},
            "results": results,
        }],
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def _print_payload(args: argparse.Namespace, payload: Mapping[str, Any]) -> None:
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        kind = payload.get("kind", "autoform")
        print(f"{kind}:")
        for key, value in payload.items():
            if key == "kind":
                continue
            print(f"  {key}: {value}")


def _run(
    cmd: Sequence[str],
    *,
    args: argparse.Namespace,
    env: Mapping[str, str] | None = None,
    check: bool = False,
) -> CommandResult:
    expanded = [str(x) for x in cmd]
    if args.dry_run:
        payload = {"kind": "dry-run", "cwd": str(ROOT), "command": expanded}
        _print_payload(args, payload)
        return CommandResult(expanded, str(ROOT), 0, dry_run=True)
    completed = subprocess.run(expanded, cwd=ROOT, env=dict(env) if env else None, check=False)
    if check and completed.returncode != 0:
        raise SystemExit(completed.returncode)
    return CommandResult(expanded, str(ROOT), int(completed.returncode))


def _pipeline_runner(args: argparse.Namespace, env: Mapping[str, str]) -> PipelineRunner:
    artifact_dir = Path(args.artifact_dir).expanduser() if getattr(args, "artifact_dir", None) else None
    return PipelineRunner(
        root=ROOT,
        env=env,
        dry_run=args.dry_run,
        capture=args.json or args.dry_run,
        run_id=getattr(args, "run_id", None),
        artifact_dir=artifact_dir,
        keep_work=getattr(args, "keep_work", False),
        metadata={"config": str(args.config_path) if getattr(args, "config_path", None) else None},
    )


def _emit_pipeline_result(args: argparse.Namespace, result) -> None:
    if args.json or args.dry_run:
        print(json.dumps(result.as_dict(), indent=2, sort_keys=True))


def _tool_status(executable: str, version_args: Sequence[str] = ("--version",)) -> dict[str, Any]:
    explicit_path = Path(executable).expanduser() if os.sep in executable else None
    path = str(explicit_path) if explicit_path and explicit_path.exists() else shutil.which(executable)
    result: dict[str, Any] = {"tool": executable, "found": bool(path), "path": path}
    if not path:
        return result
    try:
        cp = subprocess.run(
            [path, *version_args], capture_output=True, text=True, timeout=10, check=False
        )
        result.update(
            {
                "returncode": cp.returncode,
                "version": (cp.stdout or cp.stderr).strip().splitlines()[:2],
            }
        )
    except Exception as exc:  # pragma: no cover - defensive for unusual local tools
        result.update({"returncode": None, "error": str(exc)})
    return result


def cmd_doctor(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    runtime = _section(config, "runtime")
    joern_home = args.joern_home or runtime.get("joern_home") or os.environ.get("JOERN_HOME")
    lake = args.lake or runtime.get("lake") or os.environ.get("AUTOFORM_LAKE") or "lake"
    joern_cli = Path(str(joern_home or Path.home() / "joern")) / "joern-cli"
    checks = [
        _tool_status("python3"),
        _tool_status(str(lake)),
        _tool_status("lean"),
        _tool_status("git"),
        {
            "tool": "joern-parse",
            "found": (joern_cli / "joern-parse").exists(),
            "path": str(joern_cli / "joern-parse"),
        },
        {
            "tool": "joern",
            "found": (joern_cli / "joern").exists(),
            "path": str(joern_cli / "joern"),
        },
    ]
    payload = {
        "kind": "doctor",
        "repo": str(ROOT),
        "config": str(args.config_path) if getattr(args, "config_path", None) else None,
        "checks": checks,
        "ok": all(c.get("found") for c in checks),
    }
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print("Autoform doctor")
        print(f"repo: {ROOT}")
        for check in checks:
            status = "ok" if check.get("found") else "missing"
            print(f"  {check['tool']}: {status} ({check.get('path') or 'not on PATH'})")
            if check.get("version"):
                print(f"    {check['version'][0]}")
    return 0 if payload["ok"] else 1


def _source_module_from_args(args: argparse.Namespace, config: Mapping[str, Any]) -> tuple[Path, str, Mapping[str, Any]]:
    target = getattr(args, "target", None)
    project = _resolve_project(config, target)
    raw_source = args.source or project.get("source", "")
    if not raw_source:
        subject = f" target {target!r}" if target else ""
        raise SystemExit(f"source is required for{subject}; pass <source> or configure source in autoform.toml")
    source = Path(str(raw_source)).expanduser()
    module = _module_name(args.module or project.get("module"), "Translated")
    return source, module, project


def _target_args(base: argparse.Namespace, target: str, mode: str | None = None) -> argparse.Namespace:
    clone = argparse.Namespace(**vars(base))
    clone.target = target
    clone.source = None
    clone.module = None
    if base.run_id:
        clone.run_id = f"{base.run_id}-{target}"
    if base.artifact_dir:
        clone.artifact_dir = str(Path(base.artifact_dir).expanduser() / target)
    if mode is not None:
        clone.mode = mode
    return clone


def _run_id_for_target(base: argparse.Namespace, target: str) -> str:
    if getattr(base, "run_id", None):
        return f"{base.run_id}-{target}"
    return target


def _artifact_dir_for_target(base: argparse.Namespace, target: str, run_id: str) -> Path:
    if getattr(base, "artifact_dir", None):
        return Path(base.artifact_dir).expanduser() / target
    return ROOT / ".autoform-runs" / run_id


def _manifest_path_for_artifact_dir(path: Path) -> str:
    manifest = path / "run.json"
    try:
        return str(manifest.relative_to(ROOT))
    except ValueError:
        return str(manifest)


def cmd_plan(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    names = _select_target_names(
        config,
        list(args.targets or []),
        tags=getattr(args, "tag", []) or [],
        owner=getattr(args, "owner", None),
        tier=getattr(args, "tier", None),
    )
    if not names:
        raise SystemExit("plan requires matching target names or configured [targets.<name>] entries")
    entries: list[dict[str, Any]] = []
    for name in names:
        target = _target_config(config, name)
        mode = args.mode or str(target.get("mode", "translate"))
        if mode not in ("translate", "assure"):
            raise SystemExit(f"target {name!r}: mode must be 'translate' or 'assure', got {mode!r}")
        source = str(target.get("source", ""))
        module = _module_name(str(target.get("module", "")) if target.get("module") is not None else None, "Translated")
        run_id = _run_id_for_target(args, name)
        artifact_dir = _artifact_dir_for_target(args, name, run_id)
        entries.append({
            "target": name,
            "mode": mode,
            "source": source,
            "module": module,
            "run_id": run_id,
            "artifact_dir": str(artifact_dir),
            "manifest": _manifest_path_for_artifact_dir(artifact_dir),
            "owner": target.get("owner"),
            "tier": target.get("tier"),
            "tags": _target_tags(target),
            "conformance_cases": args.conformance_cases,
        })
    payload = {
        "kind": "fleet-plan",
        "count": len(entries),
        "run_id": args.run_id or "",
        "artifact_dir": args.artifact_dir,
        "requested_targets": list(args.targets or []),
        "mode": args.mode,
        "conformance_cases": args.conformance_cases,
        "filters": {"tags": getattr(args, "tag", []) or [], "owner": getattr(args, "owner", None), "tier": getattr(args, "tier", None)},
        "entries": entries,
    }
    if args.output:
        output = Path(args.output).expanduser()
        payload["output"] = str(output)
        if not args.dry_run:
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    if args.json or args.dry_run or not args.output:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"Autoform fleet plan wrote {args.output} ({len(entries)} target(s))")
    return 0



def cmd_spec_plan(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    source, module, project = _source_module_from_args(args, config)
    test_command = args.test_command or project.get("test_command") or None
    test_framework = args.test_framework or project.get("test_framework") or None
    default_trace_dir = _artifact_dir_for_target(args, getattr(args, "target", None) or module, args.run_id or module)
    trace_output = args.trace_output or str(default_trace_dir / "behavior-trace.jsonl")
    spec_output = args.spec_output or f"Autoform/Specs/{module}BehaviorSpec.lean"
    ast_output = f"ast-{module}.json"
    generated_output = f"Autoform/Generated/{module}.lean"
    phases: list[dict[str, Any]] = [
        {
            "name": "discover-tests",
            "purpose": "Find the tests that describe the codebase's public behavior before trusting a source-only translation.",
            "command": test_command,
            "outputs": ["test inventory", "entry points", "runtime dependencies"],
            "rejects": ["no tests discovered", "tests that cannot run on the real runtime"],
        },
        {
            "name": "trace-runtime-behavior",
            "purpose": "Run the real tests and record concrete inputs, outputs, exceptions, receiver state and covered call paths.",
            "command": test_command,
            "outputs": [trace_output],
            "rejects": ["tests pass without exercising translated functions", "unserializable observations without a named skip reason"],
        },
        {
            "name": "translate-source",
            "purpose": "Translate the same source tree through Joern and render the neutral AST into Lean.",
            "command": f"autoform translate {source} {module}",
            "outputs": [ast_output, generated_output, f"provenance/{ast_output}.prov.json"],
            "rejects": ["unattributed AST", "generated Lean not rendered from the recorded AST"],
        },
        {
            "name": "emit-lean-behavior-specs",
            "purpose": "Turn runtime observations into Lean examples and contracts over Autoform.eval rather than copying test syntax blindly.",
            "command": None,
            "outputs": [spec_output],
            "rejects": ["tautological specs", "tests that only assert determinism or implementation echoes"],
        },
        {
            "name": "check-conformance",
            "purpose": "Compare Lean execution against the recorded real-runtime behavior and keep every mismatch or skip reason explicit.",
            "command": f"python3 scripts/differential.py {ast_output} {source} {module}",
            "outputs": ["conformance.json"],
            "rejects": ["zero compared cases", "silent skip", "stale .olean answer"],
        },
        {
            "name": "anti-vacuity",
            "purpose": "Mutate the source and specs so behavior constraints must fail when the implementation changes in relevant ways.",
            "command": f"python3 scripts/mutate.py {generated_output} Autoform.Generated.{module}",
            "outputs": ["mutation.json"],
            "rejects": ["all mutants survive", "coverage-free examples", "specs proved only by rfl after erasing behavior"],
        },
    ]
    payload: dict[str, Any] = {
        "kind": "spec-plan",
        "strategy": "test-first-autoformalization",
        "source": str(source),
        "module": module,
        "target": getattr(args, "target", None),
        "test_command": test_command,
        "test_framework": test_framework,
        "trace_format": "jsonl: function, args, kwargs, receiver_state, result|exception, side_effects, coverage",
        "phases": phases,
        "artifacts": [trace_output, ast_output, generated_output, spec_output, "conformance.json", "mutation.json"],
        "anti_vacuity": [
            "Reject suites with zero runtime observations for translated functions.",
            "Reject Lean specs that only restate reflexive facts such as f(x) = f(x).",
            "Require mutation or counterexample evidence before treating generated tests as specifications.",
            "Keep unencodable values and unsupported side effects as named skip reasons, never as passes.",
        ],
    }
    if args.output:
        output = Path(args.output).expanduser()
        payload["output"] = str(output)
        if not args.dry_run:
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    if args.json or args.dry_run or not args.output:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"Autoform spec plan wrote {args.output} ({len(phases)} phase(s))")
    return 0

def _plan_entry_key(entry: Mapping[str, Any]) -> str:
    return str(entry.get("target", ""))


def _plan_comparable_entry(entry: Mapping[str, Any]) -> dict[str, Any]:
    keys = ["target", "mode", "source", "module", "run_id", "artifact_dir", "manifest", "owner", "tier", "tags", "conformance_cases"]
    return {key: entry.get(key) for key in keys}


def _expected_plan_from_loaded_plan(plan: Mapping[str, Any], config: Mapping[str, Any]) -> tuple[dict[str, Any], list[dict[str, str]]]:
    filters = plan.get("filters", {}) if isinstance(plan.get("filters"), Mapping) else {}
    tags = filters.get("tags", []) if isinstance(filters.get("tags", []), list) else []
    owner = filters.get("owner") if isinstance(filters.get("owner"), (str, type(None))) else None
    tier = filters.get("tier") if isinstance(filters.get("tier"), (str, type(None))) else None
    run_id = str(plan.get("run_id") or "")
    artifact_dir = plan.get("artifact_dir")
    mode = plan.get("mode")
    conformance_cases = int(plan.get("conformance_cases") or 5)
    requested_targets = plan.get("requested_targets", [])
    if isinstance(requested_targets, list):
        requested = [str(item) for item in requested_targets]
    else:
        requested = []
    if not requested and isinstance(plan.get("entries"), list):
        requested = [str(entry.get("target")) for entry in plan["entries"] if isinstance(entry, Mapping) and entry.get("target")]
    names = _select_target_names(config, requested, tags=tags, owner=owner, tier=tier)
    entries: list[dict[str, Any]] = []
    violations: list[dict[str, str]] = []
    shim = argparse.Namespace(run_id=run_id or None, artifact_dir=artifact_dir, mode=mode, conformance_cases=conformance_cases)
    for name in names:
        target = _target_config(config, name)
        entry_mode = str(mode or target.get("mode", "translate"))
        if entry_mode not in ("translate", "assure"):
            violations.append({"path": f"targets.{name}.mode", "message": "mode must be 'translate' or 'assure'"})
            continue
        try:
            module = _module_name(str(target.get("module", "")) if target.get("module") is not None else None, "Translated")
        except SystemExit as exc:
            violations.append({"path": f"targets.{name}.module", "message": str(exc)})
            continue
        entry_run_id = _run_id_for_target(shim, name)
        entry_artifact_dir = _artifact_dir_for_target(shim, name, entry_run_id)
        entries.append({
            "target": name,
            "mode": entry_mode,
            "source": str(target.get("source", "")),
            "module": module,
            "run_id": entry_run_id,
            "artifact_dir": str(entry_artifact_dir),
            "manifest": _manifest_path_for_artifact_dir(entry_artifact_dir),
            "owner": target.get("owner"),
            "tier": target.get("tier"),
            "tags": _target_tags(target),
            "conformance_cases": conformance_cases,
        })
    return {
        "kind": "fleet-plan",
        "count": len(entries),
        "run_id": run_id,
        "artifact_dir": artifact_dir,
        "requested_targets": requested,
        "mode": mode,
        "conformance_cases": conformance_cases,
        "filters": {"tags": tags, "owner": owner, "tier": tier},
        "entries": entries,
    }, violations


def _plan_drift(plan: Mapping[str, Any], expected: Mapping[str, Any]) -> list[dict[str, str]]:
    violations: list[dict[str, str]] = []
    planned_entries = plan.get("entries", []) if isinstance(plan.get("entries"), list) else []
    expected_entries = expected.get("entries", []) if isinstance(expected.get("entries"), list) else []
    planned_by_target = {_plan_entry_key(entry): entry for entry in planned_entries if isinstance(entry, Mapping)}
    expected_by_target = {_plan_entry_key(entry): entry for entry in expected_entries if isinstance(entry, Mapping)}
    for target in sorted(set(planned_by_target) - set(expected_by_target)):
        violations.append({"path": f"entries.{target}", "message": "target is in plan but no longer selected by config"})
    for target in sorted(set(expected_by_target) - set(planned_by_target)):
        violations.append({"path": f"entries.{target}", "message": "target is selected by config but missing from plan"})
    for target in sorted(set(planned_by_target) & set(expected_by_target)):
        planned = _plan_comparable_entry(planned_by_target[target])
        expected_entry = _plan_comparable_entry(expected_by_target[target])
        for key, expected_value in expected_entry.items():
            if planned.get(key) != expected_value:
                violations.append({"path": f"entries.{target}.{key}", "message": f"plan has {planned.get(key)!r}, config resolves to {expected_value!r}"})
    return violations


def cmd_verify_plan(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    plan_path = Path(args.plan).expanduser()
    plan, violations = _load_plan(plan_path)
    expected: dict[str, Any] | None = None
    if plan is not None:
        expected, expected_violations = _expected_plan_from_loaded_plan(plan, config)
        violations.extend(expected_violations)
        if not expected_violations:
            violations.extend(_plan_drift(plan, expected))
    payload = {
        "kind": "verify-plan",
        "plan": str(plan_path),
        "ok": not violations,
        "violations": violations,
    }
    if expected is not None and args.include_expected:
        payload["expected"] = expected
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        if violations:
            print("Autoform plan verification failed:")
            for item in violations:
                print(f"  {item['path']}: {item['message']}")
        else:
            print("Autoform plan verification passed.")
    return 0 if not violations else 1


def cmd_translate(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    source, module, project = _source_module_from_args(args, config)
    env = _env_from_args(args, config, project)
    result = _pipeline_runner(args, env).translate(source, module, conformance_cases=args.conformance_cases)
    _emit_pipeline_result(args, result)
    return result.returncode


def cmd_assure(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    source, module, project = _source_module_from_args(args, config)
    env = _env_from_args(args, config, project)
    result = _pipeline_runner(args, env).assure(source, module)
    _emit_pipeline_result(args, result)
    return result.returncode


def cmd_targets(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    names = _select_target_names(
        config,
        tags=getattr(args, "tag", []) or [],
        owner=getattr(args, "owner", None),
        tier=getattr(args, "tier", None),
    )
    targets = [_target_payload(name, _target_config(config, name)) for name in names]
    payload = {"kind": "targets", "count": len(targets), "filters": {"tags": getattr(args, "tag", []) or [], "owner": getattr(args, "owner", None), "tier": getattr(args, "tier", None)}, "targets": targets}
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        if not targets:
            print("No [targets.<name>] entries configured.")
        for target in targets:
            print(f"{target['name']}: {target.get('mode')} {target.get('source')} -> {target.get('module')}")
    return 0


def _config_for_plan_entry(config: Mapping[str, Any], target_name: str) -> Mapping[str, Any]:
    targets = _target_map(config)
    value = targets.get(target_name)
    return value if isinstance(value, Mapping) else {}


def _run_batch_entry(args: argparse.Namespace, config: Mapping[str, Any], entry: Mapping[str, Any]):
    name = str(entry["target"])
    mode = str(entry["mode"])
    entry_args = argparse.Namespace(**vars(args))
    entry_args.target = name
    entry_args.source = str(entry["source"])
    entry_args.module = str(entry["module"])
    entry_args.run_id = str(entry["run_id"])
    entry_args.artifact_dir = str(Path(str(entry["artifact_dir"])).expanduser())
    project = _config_for_plan_entry(config, name)
    env = _env_from_args(entry_args, config, project)
    runner = _pipeline_runner(entry_args, env)
    cases = int(entry.get("conformance_cases") or getattr(args, "conformance_cases", 5))
    source = Path(entry_args.source).expanduser()
    result = runner.assure(source, entry_args.module) if mode == "assure" else runner.translate(source, entry_args.module, conformance_cases=cases)
    item = result.as_dict()
    item["target"] = name
    item["mode"] = mode
    item["owner"] = entry.get("owner")
    item["tier"] = entry.get("tier")
    item["tags"] = list(entry.get("tags", [])) if isinstance(entry.get("tags", []), list) else []
    return item, int(result.returncode)


def cmd_batch(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    plan_path = Path(args.plan).expanduser() if getattr(args, "plan", None) else None
    results = []
    worst = 0
    if plan_path:
        if args.targets or args.tag or args.owner or args.tier or args.mode:
            raise SystemExit("batch --plan cannot be combined with target names, --mode, --tag, --owner or --tier")
        plan, violations = _load_plan(plan_path)
        if plan is None:
            payload = {"kind": "batch", "plan": str(plan_path), "dry_run": args.dry_run, "returncode": 1, "count": 0, "violations": violations, "results": []}
            if args.json or args.dry_run:
                print(json.dumps(payload, indent=2, sort_keys=True))
            else:
                for item in violations:
                    print(f"{item['path']}: {item['message']}")
            return 1
        for entry in plan.get("entries", []):
            item, rc = _run_batch_entry(args, config, entry)
            results.append(item)
            worst = worst or rc
            if worst and args.fail_fast:
                break
        payload = {"kind": "batch", "plan": str(plan_path), "dry_run": args.dry_run, "returncode": worst, "count": len(results), "results": results}
        if args.json or args.dry_run:
            print(json.dumps(payload, indent=2, sort_keys=True))
        return worst

    names = _select_target_names(
        config,
        list(args.targets or []),
        tags=getattr(args, "tag", []) or [],
        owner=getattr(args, "owner", None),
        tier=getattr(args, "tier", None),
    )
    if not names:
        raise SystemExit("batch requires matching target names or configured [targets.<name>] entries")
    for name in names:
        target = _target_config(config, name)
        mode = args.mode or str(target.get("mode", "translate"))
        if mode not in ("translate", "assure"):
            raise SystemExit(f"target {name!r}: mode must be 'translate' or 'assure', got {mode!r}")
        target_args = _target_args(args, name, mode)
        source, module, project = _source_module_from_args(target_args, config)
        env = _env_from_args(target_args, config, project)
        runner = _pipeline_runner(target_args, env)
        result = runner.assure(source, module) if mode == "assure" else runner.translate(source, module, conformance_cases=args.conformance_cases)
        item = result.as_dict()
        item["target"] = name
        item["mode"] = mode
        item["owner"] = target.get("owner")
        item["tier"] = target.get("tier")
        item["tags"] = _target_tags(target)
        results.append(item)
        worst = worst or int(result.returncode)
        if worst and args.fail_fast:
            break
    payload = {"kind": "batch", "dry_run": args.dry_run, "returncode": worst, "count": len(results), "filters": {"tags": getattr(args, "tag", []) or [], "owner": getattr(args, "owner", None), "tier": getattr(args, "tier", None)}, "results": results}
    if args.json or args.dry_run:
        print(json.dumps(payload, indent=2, sort_keys=True))
    return worst


def cmd_validate(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    violations = _validate_config(config, require_existing_source=args.require_existing_source)
    payload = {
        "kind": "validate",
        "config": str(args.config_path) if getattr(args, "config_path", None) else None,
        "ok": not violations,
        "violations": violations,
    }
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        if violations:
            print("Autoform config validation failed:")
            for item in violations:
                print(f"  {item['path']}: {item['message']}")
        else:
            print("Autoform config validation passed.")
    return 0 if not violations else 1


def cmd_schema(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    schemas = {"run-manifest": RUN_MANIFEST_SCHEMA, "manifest-index": MANIFEST_INDEX_SCHEMA, "fleet-plan": FLEET_PLAN_SCHEMA, "spec-plan": SPEC_PLAN_SCHEMA, "config": CONFIG_SCHEMA}
    schema = schemas[args.name]
    if args.json:
        print(json.dumps(schema, indent=2, sort_keys=True))
    else:
        print(json.dumps(schema, indent=2, sort_keys=True))
    return 0


def cmd_gate(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    manifest = Path(args.manifest).expanduser()
    data, violations = _load_manifest(manifest)
    if data is not None:
        root = Path(args.root).expanduser() if args.root else ROOT
        violations.extend(_manifest_gate_violations(data, require_artifacts=args.require_artifacts, root=root))
    payload = {
        "kind": "gate",
        "manifest": str(manifest),
        "ok": not violations,
        "violations": violations,
    }
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        if violations:
            print("Autoform gate failed:")
            for item in violations:
                print(f"  {item['path']}: {item['message']}")
        else:
            print("Autoform gate passed.")
    return 0 if not violations else 1


def cmd_bundle(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    manifest = Path(args.manifest).expanduser()
    data, violations = _load_manifest(manifest)
    entries: list[tuple[Path, str]] = []
    missing: list[str] = []
    root = Path(args.root).expanduser() if args.root else ROOT
    if data is not None:
        entries.append((manifest, "run.json"))
        artifacts = data.get("artifacts", [])
        if not isinstance(artifacts, list):
            violations.append({"path": "artifacts", "message": "artifacts must be an array"})
        else:
            for index, artifact in enumerate(artifacts):
                if not isinstance(artifact, str):
                    violations.append({"path": f"artifacts[{index}]", "message": "artifact path must be a string"})
                    continue
                candidate = Path(artifact).expanduser()
                if not candidate.is_absolute():
                    candidate = root / candidate
                if candidate.exists():
                    arcname = artifact if not Path(artifact).is_absolute() else candidate.name
                    entries.append((candidate, arcname))
                else:
                    missing.append(artifact)
            if missing and not args.allow_missing:
                for artifact in missing:
                    violations.append({"path": "artifacts", "message": f"artifact does not exist: {artifact}"})
    output = Path(args.output).expanduser()
    payload = {
        "kind": "bundle",
        "manifest": str(manifest),
        "output": str(output),
        "dry_run": args.dry_run,
        "entries": [arcname for _, arcname in entries],
        "missing": missing,
        "ok": not violations,
        "violations": violations,
    }
    if violations:
        if args.json:
            print(json.dumps(payload, indent=2, sort_keys=True))
        else:
            print("Autoform bundle failed:")
            for item in violations:
                print(f"  {item['path']}: {item['message']}")
        return 1
    if not args.dry_run:
        output.parent.mkdir(parents=True, exist_ok=True)
        with tarfile.open(output, "w:gz") as tar:
            for path, arcname in entries:
                tar.add(path, arcname=arcname)
    if args.json or args.dry_run:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"Autoform bundle wrote {output} ({len(entries)} entries)")
    return 0


def _markdown_escape(value: Any) -> str:
    return str(value).replace("|", "\\|").replace("\n", " ")


def _manifest_index_report_markdown(data: Mapping[str, Any], *, manifest: Path) -> str:
    status = "passed" if data.get("ok") is True and data.get("returncode") == 0 else "failed"
    lines = [
        "# Autoform Fleet Evidence Report",
        "",
        f"- Manifest index: `{manifest}`",
        f"- Runs: `{data.get('count', 0)}`",
        f"- Result: **{status}** (`returncode={data.get('returncode')}`)",
        f"- Artifact check: `{data.get('require_artifacts', False)}`",
        "",
        "## Fleet runs",
        "",
        "| Module | Kind | Run ID | Return code | Failed steps | Missing artifacts | Manifest |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    entries = data.get("entries", [])
    if isinstance(entries, list) and entries:
        for raw in entries:
            if not isinstance(raw, Mapping):
                lines.append("| invalid entry |  |  |  |  |  |  |")
                continue
            missing = raw.get("missing_artifacts", [])
            if isinstance(missing, list):
                missing_text = ", ".join(str(item) for item in missing) or "0"
            else:
                missing_text = "invalid"
            lines.append(
                "| "
                + " | ".join([
                    _markdown_escape(raw.get("module", "")),
                    _markdown_escape(raw.get("kind", "")),
                    _markdown_escape(raw.get("run_id", "")),
                    _markdown_escape(raw.get("returncode", "")),
                    _markdown_escape(raw.get("failed_steps", "")),
                    _markdown_escape(missing_text),
                    f"`{_markdown_escape(raw.get('manifest', ''))}`",
                ])
                + " |"
            )
    else:
        lines.append("| No runs recorded |  |  |  |  |  |  |")

    violations = data.get("violations", [])
    if isinstance(violations, list) and violations:
        lines.extend(["", "## Index violations", "", "| Path | Message |", "| --- | --- |"] )
        for raw in violations:
            if isinstance(raw, Mapping):
                lines.append(f"| {_markdown_escape(raw.get('path', ''))} | {_markdown_escape(raw.get('message', ''))} |")
            else:
                lines.append(f"| invalid | {_markdown_escape(raw)} |")

    lines.extend([
        "",
        "## Reviewer notes",
        "",
        "- Use this report to triage a fleet run quickly; use each listed manifest for exact commands, logs and artifacts.",
        "- Gate the index with `autoform gate --manifest <fleet-index.json>` before promoting results.",
        "",
    ])
    return "\n".join(lines)


def _manifest_report_markdown(data: Mapping[str, Any], *, manifest: Path, root: Path) -> str:
    if data.get("kind") == "manifest-index":
        return _manifest_index_report_markdown(data, manifest=manifest)
    title = f"Autoform Evidence Report: {data.get('module', 'unknown module')}"
    status = "passed" if data.get("returncode") == 0 else "failed"
    lines = [
        f"# {title}",
        "",
        f"- Manifest: `{manifest}`",
        f"- Kind: `{data.get('kind', 'unknown')}`",
        f"- Module: `{data.get('module', 'unknown')}`",
        f"- Source: `{data.get('source', '')}`",
        f"- Run ID: `{data.get('run_id', '')}`",
        f"- Dry run: `{data.get('dry_run', False)}`",
        f"- Result: **{status}** (`returncode={data.get('returncode')}`)",
        "",
        "## Pipeline steps",
        "",
        "| Step | Required | Allows failure | Return code |",
        "| --- | --- | --- | --- |",
    ]
    steps = data.get("steps", [])
    if isinstance(steps, list) and steps:
        for index, raw in enumerate(steps, 1):
            if not isinstance(raw, Mapping):
                lines.append(f"| {index}. invalid step |  |  |  |")
                continue
            name = _markdown_escape(raw.get("name", f"step {index}"))
            required = _markdown_escape(raw.get("required", True))
            allow_failure = _markdown_escape(raw.get("allow_failure", False))
            rc = _markdown_escape(raw.get("returncode"))
            lines.append(f"| {index}. {name} | {required} | {allow_failure} | {rc} |")
    else:
        lines.append("| No steps recorded |  |  |  |")

    failed = [raw for raw in steps if isinstance(raw, Mapping) and raw.get("returncode") not in (0, None)] if isinstance(steps, list) else []
    if failed:
        lines.extend(["", "## Failed-step evidence", ""])
        for raw in failed:
            name = str(raw.get("name", "step"))
            lines.extend([f"### {name}", "", f"Return code: `{raw.get('returncode')}`", ""])
            command = raw.get("command")
            if isinstance(command, list):
                lines.extend(["Command:", "", "```sh", " ".join(str(part) for part in command), "```", ""])
            for key, label in (("stdout_tail", "stdout tail"), ("stderr_tail", "stderr tail")):
                tail = raw.get(key)
                if tail:
                    lines.extend([f"{label}:", "", "```", str(tail)[-4000:], "```", ""])

    artifacts = data.get("artifacts", [])
    lines.extend(["", "## Artifacts", "", "| Artifact | Present |", "| --- | --- |"])
    if isinstance(artifacts, list) and artifacts:
        for artifact in artifacts:
            if not isinstance(artifact, str):
                lines.append(f"| {_markdown_escape(artifact)} | invalid |")
                continue
            candidate = Path(artifact).expanduser()
            if not candidate.is_absolute():
                candidate = root / candidate
            lines.append(f"| `{_markdown_escape(artifact)}` | {str(candidate.exists()).lower()} |")
    else:
        lines.append("| No artifacts recorded |  |")
    lines.extend(["", "## Reviewer notes", "", "- Treat this report as an index. The manifest remains the source of truth for exact commands and return codes.", "- Keep the manifest and listed artifacts together when uploading CI evidence.", ""])
    return "\n".join(lines)


def cmd_report(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    manifest = Path(args.manifest).expanduser()
    data, violations = _load_manifest(manifest)
    root = Path(args.root).expanduser() if args.root else ROOT
    if data is None:
        payload = {"kind": "report", "manifest": str(manifest), "ok": False, "violations": violations}
        if args.json:
            print(json.dumps(payload, indent=2, sort_keys=True))
        else:
            print("Autoform report failed:")
            for item in violations:
                print(f"  {item['path']}: {item['message']}")
        return 1

    output = Path(args.output).expanduser()
    markdown = _manifest_report_markdown(data, manifest=manifest, root=root)
    payload = {
        "kind": "report",
        "manifest": str(manifest),
        "output": str(output),
        "dry_run": args.dry_run,
        "ok": True,
    }
    if not args.dry_run:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(markdown)
    if args.json or args.dry_run:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"Autoform report wrote {output}")
    return 0


def _expand_manifest_patterns(patterns: Sequence[str]) -> list[Path]:
    paths: list[Path] = []
    seen: set[str] = set()
    for raw in patterns:
        matches = glob_mod.glob(raw) if glob_mod.has_magic(raw) else [raw]
        for match in sorted(matches):
            resolved = str(Path(match).expanduser())
            if resolved not in seen:
                seen.add(resolved)
                paths.append(Path(resolved))
    return paths


def _artifact_missing(data: Mapping[str, Any], *, root: Path) -> list[str]:
    missing: list[str] = []
    artifacts = data.get("artifacts", [])
    if not isinstance(artifacts, list):
        return missing
    for artifact in artifacts:
        if not isinstance(artifact, str):
            continue
        candidate = Path(artifact).expanduser()
        if not candidate.is_absolute():
            candidate = root / candidate
        if not candidate.exists():
            missing.append(artifact)
    return missing


def cmd_index(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    manifests = _expand_manifest_patterns(args.manifests)
    if not manifests:
        raise SystemExit("index requires at least one manifest path or glob")
    root = Path(args.root).expanduser() if args.root else ROOT
    entries: list[dict[str, Any]] = []
    violations: list[dict[str, str]] = []
    worst = 0
    for manifest in manifests:
        data, load_violations = _load_manifest(manifest)
        if data is None:
            violations.extend(load_violations)
            worst = worst or 1
            entries.append({"manifest": str(manifest), "ok": False, "violations": load_violations})
            continue
        steps = data.get("steps", [])
        failed_steps = [step for step in steps if isinstance(step, Mapping) and step.get("returncode") not in (0, None)] if isinstance(steps, list) else []
        missing = _artifact_missing(data, root=root) if args.require_artifacts else []
        if missing:
            worst = worst or 1
            for artifact in missing:
                violations.append({"path": f"{manifest}:artifacts", "message": f"artifact does not exist: {artifact}"})
        rc = int(data.get("returncode") or 0)
        worst = worst or rc
        entries.append({
            "manifest": str(manifest),
            "kind": data.get("kind"),
            "module": data.get("module"),
            "source": data.get("source"),
            "run_id": data.get("run_id"),
            "returncode": rc,
            "ok": rc == 0 and not missing,
            "steps": len(steps) if isinstance(steps, list) else None,
            "failed_steps": len(failed_steps),
            "artifacts": len(data.get("artifacts", [])) if isinstance(data.get("artifacts", []), list) else None,
            "missing_artifacts": missing,
        })
    payload = {
        "kind": "manifest-index",
        "count": len(entries),
        "returncode": worst,
        "ok": worst == 0 and not violations,
        "require_artifacts": args.require_artifacts,
        "entries": entries,
        "violations": violations,
    }
    if args.output:
        output = Path(args.output).expanduser()
        payload["output"] = str(output)
        if not args.dry_run:
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    if args.json or args.dry_run or not args.output:
        print(json.dumps(payload, indent=2, sort_keys=True))
    elif worst or violations:
        print(f"Autoform manifest index found failures across {len(entries)} run(s)")
    else:
        print(f"Autoform manifest index wrote {args.output} ({len(entries)} run(s))")
    return 0 if payload["ok"] else 1


def cmd_render(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    ast = Path(args.ast or _cfg(config, "project", "ast", "")).expanduser()
    module = _module_name(args.module or _cfg(config, "project", "module"), "Translated")
    output = Path(args.output or _cfg(config, "project", "lean_output", f"Autoform/Generated/{module}.lean"))
    result = _run(
        [sys.executable, str(ROOT / "cartographer" / "render_lean.py"), str(ast), str(output), module],
        args=args,
    )
    return result.returncode


def cmd_audit(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    flags: list[str] = []
    if args.kernel_only:
        flags.append("--kernel-only")
    elif not args.with_kernel:
        flags.append("--skip-kernel")
    if args.strict:
        flags.append("--strict")
    result = _run([sys.executable, str(ROOT / "scripts" / "audit_all.py"), *flags], args=args)
    return result.returncode


def cmd_check(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    planned: list[tuple[str, list[str]]] = []
    if args.render:
        planned.append(("render-integrity check", [sys.executable, str(ROOT / "scripts" / "check_render.py")]))
    if args.docs:
        planned.append(("documentation consistency check", [sys.executable, str(ROOT / "scripts" / "check_docs.py")]))
    if args.provenance:
        planned.append(("provenance coverage check", [sys.executable, str(ROOT / "scripts" / "check_provenance.py")]))
    if not planned:
        planned = [
            ("render-integrity check", [sys.executable, str(ROOT / "scripts" / "check_render.py")]),
            ("documentation consistency check", [sys.executable, str(ROOT / "scripts" / "check_docs.py")]),
            ("provenance coverage check", [sys.executable, str(ROOT / "scripts" / "check_provenance.py")]),
        ]

    results: list[dict[str, Any]] = []
    worst = 0
    for name, command in planned:
        if args.dry_run:
            result = {"name": name, "command": command, "returncode": 0, "dry_run": True}
        else:
            cp = subprocess.run(command, cwd=ROOT, text=True, capture_output=(args.json or bool(args.junit) or bool(args.sarif)), check=False)
            result = {"name": name, "command": command, "returncode": int(cp.returncode), "dry_run": False}
            if args.json or args.junit or args.sarif:
                result["stdout_tail"] = (cp.stdout or "")[-4000:]
                result["stderr_tail"] = (cp.stderr or "")[-4000:]
            worst = worst or int(cp.returncode)
        results.append(result)
        if worst and args.fail_fast:
            break

    if args.junit:
        junit_path = Path(args.junit).expanduser()
        _write_junit(junit_path, "autoform-check", results)
    if args.sarif:
        sarif_path = Path(args.sarif).expanduser()
        _write_sarif(sarif_path, results)
    payload = {"kind": "check", "dry_run": args.dry_run, "returncode": worst, "steps": results}
    if args.junit:
        payload["junit"] = str(Path(args.junit).expanduser())
    if args.sarif:
        payload["sarif"] = str(Path(args.sarif).expanduser())
    if args.json or args.dry_run:
        print(json.dumps(payload, indent=2, sort_keys=True))
    return worst


def cmd_init(args: argparse.Namespace, config: Mapping[str, Any]) -> int:
    path = Path(args.output).expanduser()
    if path.exists() and not args.force:
        raise SystemExit(f"{path} already exists; pass --force to overwrite")
    template = ROOT / "autoform.toml.example"
    if template.exists():
        text = template.read_text()
    else:
        text = """# Autoform project configuration\n\n[project]\n# source = \"/path/to/source/repo\"\nmodule = \"Translated\"\n\n[runtime]\n# joern_home = \"~/joern\"\n# cpp_defines = [\"SQLITE_TEST\", \"SQLITE_API= \" ]\n"""
    if args.dry_run:
        payload = {"kind": "dry-run", "write": str(path), "content": text}
        _print_payload(args, payload)
        return 0
    path.write_text(text)
    _print_payload(args, {"kind": "init", "wrote": str(path)})
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="autoform",
        description="Enterprise CLI for translating codebases into Autoform Lean artifacts.",
    )
    parser.add_argument("--version", action="version", version=f"autoform {__version__}")
    parser.add_argument("--config", dest="config", help="Path to autoform.toml")
    parser.add_argument("--repo-root", help="Autoform checkout root; defaults to AUTOFORM_ROOT or the installed package root")
    parser.add_argument("--json", action="store_true", help="Emit machine-readable JSON where supported")
    parser.add_argument("--dry-run", action="store_true", help="Print the command without executing it")
    parser.add_argument("--joern-home", help="Joern installation root; defaults to JOERN_HOME or ~/joern")
    parser.add_argument("--lake", help="Lake executable path; defaults to AUTOFORM_LAKE or lake on PATH")
    parser.add_argument("--cpp-defines", help="Comma-separated C/C++ defines passed to Joern")
    parser.add_argument("--run-id", help="Stable run identifier for manifests and CI artifacts")
    parser.add_argument("--artifact-dir", help="Directory for the run manifest; defaults to .autoform-runs/<run-id>")
    parser.add_argument("--keep-work", action="store_true", help="Keep temporary CPG/AST work directories for debugging")

    sub = parser.add_subparsers(dest="command", required=True)

    sub.add_parser("doctor", help="Check local Autoform dependencies").set_defaults(func=cmd_doctor)

    p = sub.add_parser("targets", help="List configured enterprise targets")
    p.add_argument("--tag", action="append", default=[], help="Only include targets carrying this tag; repeat for intersection")
    p.add_argument("--owner", help="Only include targets owned by this team or person")
    p.add_argument("--tier", help="Only include targets in this service tier")
    p.set_defaults(func=cmd_targets)

    p = sub.add_parser("translate", help="Run source -> AST -> Lean -> ledger pipeline")
    p.add_argument("source", nargs="?", help="Source tree to translate")
    p.add_argument("module", nargs="?", help="Lean module name")
    p.add_argument("--target", help="Configured [targets.<name>] entry to translate")
    p.add_argument("--conformance-cases", type=int, default=5, help="Random fallback cases per function for differential testing")
    p.set_defaults(func=cmd_translate)

    p = sub.add_parser("assure", help="Run the full assurance pipeline")
    p.add_argument("source", nargs="?", help="Source tree to translate")
    p.add_argument("module", nargs="?", help="Lean module name")
    p.add_argument("--target", help="Configured [targets.<name>] entry to assure")
    p.set_defaults(func=cmd_assure)

    p = sub.add_parser("plan", help="Resolve a filtered fleet execution plan without running targets")
    p.add_argument("targets", nargs="*", help="Target names; defaults to every configured target")
    p.add_argument("--mode", choices=["translate", "assure"], help="Override each target's configured mode")
    p.add_argument("--tag", action="append", default=[], help="Only plan targets carrying this tag; repeat for intersection")
    p.add_argument("--owner", help="Only plan targets owned by this team or person")
    p.add_argument("--tier", help="Only plan targets in this service tier")
    p.add_argument("--conformance-cases", type=int, default=5, help="Random fallback cases per function for differential testing")
    p.add_argument("--output", help="Output JSON plan path")
    p.set_defaults(func=cmd_plan)

    p = sub.add_parser("spec-plan", help="Plan test-first autoformalization from runtime tests to Lean specs")
    p.add_argument("source", nargs="?", help="Source tree whose tests define the behavior to capture")
    p.add_argument("module", nargs="?", help="Lean module name")
    p.add_argument("--target", help="Configured [targets.<name>] entry to plan")
    p.add_argument("--test-command", help="Command that runs the codebase's real tests, for example 'pytest tests' or 'npm test'")
    p.add_argument("--test-framework", help="Name of the test framework or runner whose results will be traced")
    p.add_argument("--trace-output", help="Behavior trace JSONL path to produce")
    p.add_argument("--spec-output", help="Lean behavior spec module to produce")
    p.add_argument("--output", help="Write the spec plan JSON to this path")
    p.set_defaults(func=cmd_spec_plan)

    p = sub.add_parser("verify-plan", help="Check that a reviewed fleet plan still matches current config")
    p.add_argument("--plan", required=True, help="Path to autoform fleet-plan JSON")
    p.add_argument("--include-expected", action="store_true", help="Include the config-resolved expected plan in JSON output")
    p.set_defaults(func=cmd_verify_plan)

    p = sub.add_parser("batch", help="Run a filtered fleet or an explicit fleet plan")
    p.add_argument("targets", nargs="*", help="Target names; defaults to every configured target")
    p.add_argument("--plan", help="Run entries from a reviewed autoform plan JSON file")
    p.add_argument("--mode", choices=["translate", "assure"], help="Override each target's configured mode")
    p.add_argument("--tag", action="append", default=[], help="Only run targets carrying this tag; repeat for intersection")
    p.add_argument("--owner", help="Only run targets owned by this team or person")
    p.add_argument("--tier", help="Only run targets in this service tier")
    p.add_argument("--conformance-cases", type=int, default=5, help="Random fallback cases per function for differential testing")
    p.add_argument("--fail-fast", action="store_true", help="Stop after the first failing target")
    p.set_defaults(func=cmd_batch)


    p = sub.add_parser("validate", help="Validate autoform.toml for fleet use")
    p.add_argument("--require-existing-source", action="store_true", help="Fail when configured source paths are missing")
    p.set_defaults(func=cmd_validate)

    p = sub.add_parser("schema", help="Print machine-readable Autoform JSON schemas")
    p.add_argument("name", choices=["run-manifest", "manifest-index", "fleet-plan", "spec-plan", "config"])
    p.set_defaults(func=cmd_schema)

    p = sub.add_parser("gate", help="Evaluate a run manifest as a CI release gate")
    p.add_argument("--manifest", required=True, help="Path to .autoform-runs/<run-id>/run.json")
    p.add_argument("--require-artifacts", action="store_true", help="Fail when listed artifacts are missing")
    p.add_argument("--root", help="Repository root for relative artifact paths")
    p.set_defaults(func=cmd_gate)


    p = sub.add_parser("bundle", help="Package a run manifest and its artifacts for CI upload")
    p.add_argument("--manifest", required=True, help="Path to .autoform-runs/<run-id>/run.json")
    p.add_argument("--output", required=True, help="Output .tar.gz bundle path")
    p.add_argument("--root", help="Repository root for relative artifact paths")
    p.add_argument("--allow-missing", action="store_true", help="Bundle existing artifacts and report missing ones without failing")
    p.set_defaults(func=cmd_bundle)

    p = sub.add_parser("report", help="Write a Markdown evidence report from a run manifest")
    p.add_argument("--manifest", required=True, help="Path to .autoform-runs/<run-id>/run.json")
    p.add_argument("--output", required=True, help="Output Markdown report path")
    p.add_argument("--root", help="Repository root for relative artifact paths")
    p.set_defaults(func=cmd_report)

    p = sub.add_parser("index", help="Summarize many run manifests into one JSON index")
    p.add_argument("manifests", nargs="+", help="Manifest paths or shell-style globs")
    p.add_argument("--output", help="Output JSON index path; stdout when omitted")
    p.add_argument("--root", help="Repository root for relative artifact paths")
    p.add_argument("--require-artifacts", action="store_true", help="Fail when listed artifacts are missing")
    p.set_defaults(func=cmd_index)

    p = sub.add_parser("render", help="Render a neutral AST JSON file into Lean")
    p.add_argument("ast", nargs="?", help="Input ast-<Module>.json")
    p.add_argument("module", nargs="?", help="Lean module name")
    p.add_argument("--output", help="Output Lean file")
    p.set_defaults(func=cmd_render)

    p = sub.add_parser("audit", help="Run trust-boundary audits")
    group = p.add_mutually_exclusive_group()
    group.add_argument("--with-kernel", action="store_true", help="Include the slow independent kernel replay")
    group.add_argument("--kernel-only", action="store_true", help="Run only kernel replay")
    p.add_argument("--strict", action="store_true", help="Make delegated or unavailable checks fail")
    p.set_defaults(func=cmd_audit)

    p = sub.add_parser("check", help="Run repository integrity checks")
    p.add_argument("--render", action="store_true", help="Run render-integrity check")
    p.add_argument("--docs", action="store_true", help="Run documentation consistency check")
    p.add_argument("--provenance", action="store_true", help="Run provenance coverage check")
    p.add_argument("--fail-fast", action="store_true", help="Stop at the first failing check")
    p.add_argument("--junit", help="Write a JUnit XML report for CI systems")
    p.add_argument("--sarif", help="Write a SARIF 2.1.0 report for code-scanning systems")
    p.set_defaults(func=cmd_check)

    p = sub.add_parser("init", help="Create an autoform.toml template")
    p.add_argument("--output", default="autoform.toml")
    p.add_argument("--force", action="store_true")
    p.set_defaults(func=cmd_init)

    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    repo_root = _repo_root_from(args.repo_root)
    _set_repo_root(repo_root)
    config_path, config = _find_config(args.config, Path.cwd(), repo_root)
    args.config_path = config_path
    args.repo_root_path = repo_root
    return int(args.func(args, config))


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
