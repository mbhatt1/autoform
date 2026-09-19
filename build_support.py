"""Bundle the pipeline's source resources, without caches or local evidence."""
from pathlib import Path
import re
import zipfile

ROOT = Path(__file__).resolve().parent


def runtime_files(root=ROOT):
    files = {}
    pending = ["Autoform.Runtime"]
    while pending:
        module = pending.pop()
        name = module.replace(".", "/") + ".lean"
        if name in files:
            continue
        content = (root / name).read_bytes()
        files[name] = content
        pending.extend(re.findall(r"^import (Autoform(?:\.[\w]+)+)\s*$",
                                  content.decode(), re.MULTILINE))
    files["Autoform.lean"] = b"import Autoform.Runtime\n"
    for name in ("autoform.sh", "assure.sh", "lakefile.toml", "lake-manifest.json",
                 "lean-toolchain", "joern-version", "requirements.txt", "requirements-machine.txt",
                 "LICENSE", "NOTICE", "THIRD_PARTY.md", "SUPPORT.md", "SECURITY.md"):
        files[name] = (root / name).read_bytes()
    for path in sorted((root / "licenses").glob("*.txt")):
        files[path.relative_to(root).as_posix()] = path.read_bytes()
    for folder, suffixes in (("scripts", {".py", ".tmpl", ".mjs", ".sh"}),
                             ("docs", {".md"}),
                             ("cartographer", {".py", ".sc", ".sh"}),
                             ("examples", {".s", ".asm", ".py", ".c", ".cpp", ".go", ".java", ".kt", ".js", ".ts", ".json"})):
        for path in sorted((root / folder).rglob("*")):
            if path.is_file() and path.suffix in suffixes and "__pycache__" not in path.parts:
                files[path.relative_to(root).as_posix()] = path.read_bytes()
    return files


def source_files(root=ROOT):
    """Source inputs promised by the sdist, excluding backend-generated metadata.

    Keep this independent of setuptools' cached SOURCES.txt so the distribution
    check catches omissions in MANIFEST.in and stale incremental builds.
    """
    root = Path(root)
    names = set(runtime_files(root)) - {"Autoform.lean"}
    names.update(("README.md", "CONTRIBUTING.md", "pyproject.toml", "build_support.py",
                  "setup.py", "MANIFEST.in"))
    for folder, patterns in (("src/autoform", ("*.py",)),
                             ("tests", ("*.py", "*.md")),
                             ("Autoform/Lang", ("*.lean",)),
                             ("Autoform/Harness", ("*.lean",)),
                             ("Autoform/Tactics", ("*.lean",))):
        for pattern in patterns:
            names.update(path.relative_to(root).as_posix()
                         for path in (root / folder).rglob(pattern)
                         if path.is_file() and "__pycache__" not in path.parts)
    return {name: (root / name).read_bytes() for name in sorted(names)}


def __getattr__(name):
    # Editable CLI runs need only resource selection, not setuptools at runtime.
    if name != "RuntimeBuild":
        raise AttributeError(name)
    from setuptools.command.build_py import build_py
    return type("RuntimeBuild", (_RuntimeBuild, build_py), {})


class _RuntimeBuild:
    def run(self):
        super().run()
        target = Path(self.build_lib) / "autoform" / "runtime.zip"
        target.parent.mkdir(parents=True, exist_ok=True)
        with zipfile.ZipFile(target, "w", compression=zipfile.ZIP_DEFLATED) as archive:
            for name, content in sorted(runtime_files().items()):
                info = zipfile.ZipInfo(name, (2020, 1, 1, 0, 0, 0))
                info.compress_type = zipfile.ZIP_DEFLATED
                info.external_attr = 0o100644 << 16
                archive.writestr(info, content)

    def get_outputs(self, include_bytecode=1):
        return super().get_outputs(include_bytecode) + [str(Path(self.build_lib) / "autoform/runtime.zip")]
