#!/usr/bin/env python3
"""Account for repository files without claiming unsupported language coverage.

Discovery never follows repository symlinks or reads devices, sockets, or FIFOs.
Only VCS metadata and explicitly excluded paths are omitted. A failed or unstable
read remains visible in the inventory and makes ``scan_complete`` false.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
from typing import Any


# Exactly the intersection of renderer.DIALECT and differential.LANG_BY_EXT.
# This is adapter availability, not a claim of complete language semantics.
ADAPTERS = {
    "python": {"frontend": "PYTHONSRC", "extensions": (".py",)},
    "c": {"frontend": "C", "extensions": (".c", ".h", ".cpp", ".cc", ".cxx", ".hh", ".hpp")},
    "java": {"frontend": "JAVASRC", "extensions": (".java",)},
    "go": {"frontend": "GOLANG", "extensions": (".go",)},
    "js": {"frontend": "JAVASCRIPT", "extensions": (".js", ".jsx", ".mjs", ".cjs")},
    "ts": {"frontend": "JAVASCRIPT", "extensions": (".ts", ".tsx")},
    "kotlin": {"frontend": "KOTLIN", "extensions": (".kt",)},
}

_LANGUAGE_EXTENSIONS = {
    "python": (".py", ".pyi", ".pyw", ".pyx", ".pxd"),
    "c": (".c", ".h", ".cpp", ".cc", ".cxx", ".hh", ".hpp", ".hxx", ".ipp", ".tpp", ".cu", ".cuh"),
    "java": (".java",), "go": (".go",),
    "js": (".js", ".jsx", ".mjs", ".cjs"),
    "ts": (".ts", ".tsx", ".mts", ".cts"),
    "kotlin": (".kt", ".kts"), "scala": (".scala", ".sc", ".sbt"),
    "r": (".r", ".rmd"), "rust": (".rs",), "csharp": (".cs", ".csx"),
    "fsharp": (".fs", ".fsi", ".fsx"), "swift": (".swift",),
    "ruby": (".rb", ".rake", ".gemspec"), "php": (".php", ".phtml", ".php3", ".php4", ".php5"),
    "shell": (".sh", ".bash", ".zsh", ".fish", ".ksh"),
    "powershell": (".ps1", ".psm1", ".psd1"), "batch": (".bat", ".cmd"),
    "sql": (".sql",), "notebook": (".ipynb",), "lean": (".lean",),
    "haskell": (".hs", ".lhs"), "ocaml": (".ml", ".mli"),
    "elixir": (".ex", ".exs"), "erlang": (".erl", ".hrl"),
    "clojure": (".clj", ".cljs", ".cljc", ".edn"), "lua": (".lua",),
    "perl": (".pl", ".pm", ".t"), "julia": (".jl",),
    "objective_c": (".m", ".mm"), "dart": (".dart",), "elm": (".elm",),
    "fortran": (".f", ".for", ".f77", ".f90", ".f95", ".f03", ".f08"),
    "assembly": (".s", ".asm"), "verilog": (".v", ".vh", ".sv", ".svh"),
    "vhdl": (".vhd", ".vhdl"), "zig": (".zig",), "d": (".d",),
    "groovy": (".groovy", ".gradle"), "pascal": (".pas", ".pp"),
    "solidity": (".sol",), "move": (".move",), "nix": (".nix",),
    "terraform": (".tf", ".tfvars"), "cmake": (".cmake",),
    "make": (".mk",), "bazel": (".bzl", ".bazel"),
    "protobuf": (".proto",), "graphql": (".graphql", ".gql"),
    "html": (".html", ".htm", ".xhtml"), "css": (".css", ".scss", ".sass", ".less"),
    "vue": (".vue",), "svelte": (".svelte",), "webassembly": (".wat", ".wasm"),
}
_LANGUAGE_BY_EXTENSION = {ext: language for language, exts in _LANGUAGE_EXTENSIONS.items() for ext in exts}
_SOURCE_NAMES = {
    "makefile": "make", "gnumakefile": "make", "dockerfile": "dockerfile",
    "containerfile": "dockerfile", "cmakelists.txt": "cmake", "jenkinsfile": "groovy",
    "gemfile": "ruby", "rakefile": "ruby", "build": "bazel", "workspace": "bazel",
}
_AUXILIARY_EXTENSIONS = frozenset({
    ".md", ".markdown", ".rst", ".txt", ".adoc", ".org", ".pdf", ".tex", ".bib",
    ".json", ".jsonl", ".jsonc", ".yaml", ".yml", ".toml", ".ini", ".cfg", ".conf",
    ".xml", ".xsd", ".dtd", ".properties", ".env", ".lock", ".csv", ".tsv",
    ".png", ".jpg", ".jpeg", ".gif", ".webp", ".svg", ".ico", ".bmp", ".tif", ".tiff",
    ".mp3", ".wav", ".ogg", ".flac", ".mp4", ".webm", ".mov", ".avi",
    ".ttf", ".otf", ".woff", ".woff2", ".zip", ".gz", ".bz2", ".xz", ".tar", ".7z",
    ".jar", ".war", ".class", ".pyc", ".pyo", ".o", ".a", ".so", ".dylib", ".dll",
    ".exe", ".bin", ".dat", ".db", ".sqlite", ".sqlite3", ".olean", ".ilean",
    ".map", ".sum", ".mod", ".pem", ".crt", ".cer", ".key", ".patch", ".diff",
})
_AUXILIARY_NAMES = frozenset({
    "license", "licence", "copying", "notice", "authors", "contributors", "changelog",
    "readme", ".gitignore", ".gitattributes", ".gitmodules", ".editorconfig", ".dockerignore",
    ".npmrc", ".nvmrc", ".python-version", "lean-toolchain", "codeowners",
})
_VCS_NAMES = frozenset({".git", ".hg", ".svn"})
_CHUNK_BYTES = 1024 * 1024


def _classification(name: str) -> tuple[str, str | None, bool]:
    extension = PurePosixPath(name).suffix
    lowered_name = name.lower()
    language = _SOURCE_NAMES.get(lowered_name) or _LANGUAGE_BY_EXTENSION.get(extension.lower())
    if language:
        supported = extension in ADAPTERS.get(language, {}).get("extensions", ())
        return "source", language, supported
    if (extension.lower() in _AUXILIARY_EXTENSIONS or lowered_name in _AUXILIARY_NAMES
            or lowered_name.startswith(("license.", "licence.", ".env."))):
        return "auxiliary", None, False
    return "unclassified", None, False


def _identity(info: os.stat_result) -> tuple[int, ...]:
    return (info.st_dev, info.st_ino, info.st_mode, info.st_size, info.st_mtime_ns, info.st_ctime_ns)


def _canonical(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def discover(source: str | os.PathLike[str], exclude=()) -> dict[str, Any]:
    """Inventory a directory; caller exclusions are exact paths or subtrees.

    Absolute exclusions must lie inside ``source``. Relative exclusions use POSIX
    separators; globs are not interpreted. The content fingerprint intentionally
    excludes the absolute source location, so identical checkouts compare equally.
    """
    root = os.path.abspath(os.fspath(source))
    result: dict[str, Any] = {
        "schema_version": 1, "source": root, "scan_complete": True,
        "files": [], "languages": {}, "errors": [], "excluded": [], "counts": {},
    }

    def error(path: str, reason: str) -> None:
        result["errors"].append({"path": path, "reason": reason})

    exclusions: set[str] = set()
    if isinstance(exclude, (str, bytes, os.PathLike)):
        exclude = (exclude,)
    for item in exclude:
        try:
            value = os.fsdecode(os.fspath(item))
            if os.path.isabs(value):
                if os.path.commonpath((root, value)) != root:
                    raise ValueError("absolute exclusion is outside source")
                value = os.path.relpath(value, root)
            parts = PurePosixPath(value).parts
            if not parts or value == "." or ".." in parts or "\0" in value:
                raise ValueError("exclusion must identify a path inside source")
            exclusions.add(PurePosixPath(*parts).as_posix())
        except (TypeError, ValueError, OSError) as exc:
            error(".", f"invalid exclusion: {exc}")

    def exclusion(path: str, name: str) -> str | None:
        if name in _VCS_NAMES:
            return "vcs_metadata"
        if any(path == item or path.startswith(item + "/") for item in exclusions):
            return "caller_excluded"
        return None

    def visit(fd: int, prefix: str, before: os.stat_result) -> None:
        try:
            names = sorted(os.listdir(fd))
        except OSError as exc:
            error(prefix or ".", f"cannot list directory: {exc.strerror or exc}")
            return
        for name in names:
            path = f"{prefix}/{name}" if prefix else name
            reason = exclusion(path, name)
            if reason:
                result["excluded"].append({"path": path, "reason": reason})
                continue
            try:
                info = os.stat(name, dir_fd=fd, follow_symlinks=False)
            except OSError as exc:
                error(path, f"cannot stat entry: {exc.strerror or exc}")
                continue
            if stat.S_ISDIR(info.st_mode):
                child = None
                try:
                    child = os.open(name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                                    dir_fd=fd)
                    opened = os.fstat(child)
                    if _identity(opened) != _identity(info):
                        error(path, "directory changed before traversal")
                    else:
                        visit(child, path, opened)
                    if _identity(os.stat(name, dir_fd=fd, follow_symlinks=False)) != _identity(opened):
                        error(path, "directory changed during traversal")
                except OSError as exc:
                    error(path, f"cannot traverse directory: {exc.strerror or exc}")
                finally:
                    if child is not None:
                        os.close(child)
                continue
            category, language, supported = _classification(name)
            kind = "regular" if stat.S_ISREG(info.st_mode) else "symlink" if stat.S_ISLNK(info.st_mode) else "special"
            record = {"path": path, "kind": kind, "category": category, "language": language,
                      "supported": supported and kind == "regular", "sha256": None,
                      "bytes": info.st_size if kind == "regular" else None,
                      "mode": stat.S_IMODE(info.st_mode)}
            result["files"].append(record)
            if kind == "symlink":
                try:
                    record["link_target"] = os.readlink(name, dir_fd=fd)
                    if _identity(os.stat(name, dir_fd=fd, follow_symlinks=False)) != _identity(info):
                        error(path, "symlink changed while reading its target")
                except OSError as exc:
                    error(path, f"cannot read symlink target: {exc.strerror or exc}")
                continue
            if kind == "special":
                record["special_type"] = stat.S_IFMT(info.st_mode)
                continue
            stream = None
            try:
                stream = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=fd)
                opened = os.fstat(stream)
                if not stat.S_ISREG(opened.st_mode) or _identity(opened) != _identity(info):
                    error(path, "file changed before hashing")
                    record["supported"] = False
                    continue
                digest = hashlib.sha256()
                size = 0
                while True:
                    chunk = os.read(stream, _CHUNK_BYTES)
                    if not chunk:
                        break
                    digest.update(chunk)
                    size += len(chunk)
                final = os.fstat(stream)
                linked = os.stat(name, dir_fd=fd, follow_symlinks=False)
                if size != info.st_size or _identity(final) != _identity(info) or _identity(linked) != _identity(info):
                    error(path, "file changed while hashing")
                    record["supported"] = False
                else:
                    record["sha256"] = digest.hexdigest()
            except OSError as exc:
                error(path, f"cannot hash file: {exc.strerror or exc}")
                record["supported"] = False
            finally:
                if stream is not None:
                    os.close(stream)
        try:
            if _identity(os.fstat(fd)) != _identity(before):
                error(prefix or ".", "directory changed during traversal")
        except OSError as exc:
            error(prefix or ".", f"cannot verify directory: {exc.strerror or exc}")

    fd = None
    try:
        initial = os.stat(root, follow_symlinks=False)
        if not stat.S_ISDIR(initial.st_mode):
            error(".", "source is not a regular directory (symlinks are not followed)")
        elif not all(hasattr(os, flag) for flag in ("O_NOFOLLOW", "O_DIRECTORY", "O_NONBLOCK")):
            error(".", "platform lacks safe no-follow directory traversal")
        else:
            fd = os.open(root, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
            opened = os.fstat(fd)
            if _identity(opened) != _identity(initial):
                error(".", "source directory changed before traversal")
            else:
                visit(fd, "", opened)
            if _identity(os.stat(root, follow_symlinks=False)) != _identity(opened):
                error(".", "source directory changed during traversal")
    except OSError as exc:
        error(".", f"cannot scan source: {exc.strerror or exc}")
    except RecursionError:
        error(".", "directory nesting exceeds scanner traversal limit")
    finally:
        if fd is not None:
            os.close(fd)

    result["files"].sort(key=lambda item: item["path"])
    for key in ("errors", "excluded"):
        result[key] = sorted({(item["path"], item["reason"]) for item in result[key]})
        result[key] = [{"path": path, "reason": reason} for path, reason in result[key]]
    for record in result["files"]:
        language = record["language"]
        if language is None:
            continue
        adapter = ADAPTERS.get(language)
        group = result["languages"].setdefault(language, {
            "supported": True, "frontend": adapter["frontend"] if adapter else None,
            "files": [], "supported_files": [], "unsupported_files": [], "extensions": [],
        })
        group["files"].append(record["path"])
        group["supported_files" if record["supported"] else "unsupported_files"].append(record["path"])
        group["extensions"].append(PurePosixPath(record["path"]).suffix)
        group["supported"] = group["supported"] and record["supported"]
    result["languages"] = dict(sorted(result["languages"].items()))
    for group in result["languages"].values():
        group["extensions"] = sorted(set(group["extensions"]))
    files = result["files"]
    result["counts"] = {
        "files": len(files), "regular_files": sum(f["kind"] == "regular" for f in files),
        "symlinks": sum(f["kind"] == "symlink" for f in files),
        "special_files": sum(f["kind"] == "special" for f in files),
        "source_files": sum(f["category"] == "source" for f in files),
        "supported_source_files": sum(f["supported"] for f in files),
        "unsupported_source_files": sum(f["category"] == "source" and not f["supported"] for f in files),
        "auxiliary_files": sum(f["category"] == "auxiliary" for f in files),
        "unclassified_files": sum(f["category"] == "unclassified" for f in files),
        "hashed_files": sum(f["sha256"] is not None for f in files),
        "total_bytes": sum(f["bytes"] or 0 for f in files),
        "errors": len(result["errors"]), "excluded": len(result["excluded"]),
    }
    result["scan_complete"] = not result["errors"]
    result["fingerprint"] = hashlib.sha256(_canonical({k: v for k, v in result.items() if k != "source"})).hexdigest()
    return result


def changed(before: dict[str, Any], after: dict[str, Any]) -> list[dict[str, str]]:
    """Describe file and scan-evidence changes, ignoring checkout location."""
    differences = []
    first = {record["path"]: record for record in before.get("files", [])}
    second = {record["path"]: record for record in after.get("files", [])}
    for path in sorted(first.keys() | second.keys()):
        reason = "added" if path not in first else "deleted" if path not in second else "changed"
        if first.get(path) != second.get(path):
            differences.append({"path": path, "reason": reason})
    for key in ("errors", "excluded"):
        previous = {(record["path"], record["reason"]) for record in before.get(key, [])}
        current = {(record["path"], record["reason"]) for record in after.get(key, [])}
        for path, reason in sorted(previous ^ current):
            action = "added" if (path, reason) in current else "removed"
            differences.append({"path": path, "reason": f"{key} {action}: {reason}"})
    if before.get("scan_complete") != after.get("scan_complete"):
        differences.append({"path": ".", "reason": "scan completeness changed"})
    return sorted(differences, key=lambda item: (item["path"], item["reason"]))


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source")
    parser.add_argument("--exclude", action="append", default=[], metavar="PATH")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    inventory = discover(args.source, args.exclude)
    serialized = json.dumps(inventory, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(serialized, encoding="utf-8")
    else:
        print(serialized, end="")
    return 0 if inventory["scan_complete"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
