"""`.autoform-work/cache` — translations and verdicts keyed by AST digest.

A re-land (`scripts/reland_corpus.sh`) re-exports a corpus and then re-runs every stage
over every function: the oracle traces the suite and asks Lean about each recorded call,
the synthesizer refutes, guards, probes and proves each candidate. All of that is a pure
function of its inputs -- the function's AST, the rendered model, the Lean semantics and
the harness itself -- so a function whose inputs did not change has nothing new to say.
This module is the memo: every entry lives under `.autoform-work/cache/<digest>/`, where
`<digest>` is the SHA-256 of the function's AST record, and is further keyed by a digest
of everything else the stored verdict depends on (`environment_key`). A key that
over-approximates the dependencies costs a miss; one that under-approximates would replay
a verdict about a program that no longer exists, which is the staleness
`scripts/check_specs_fresh.py` was written against. The keys below therefore include the
whole rendered model and every Lean source the proof import closure can reach.

What is NOT cached: anything the kernel checks. A cached "proved" is a hint that the
emitted text will be identical; the proof itself is re-verified by `lake build`, which is
a no-op exactly when nothing it depends on changed. Set `AUTOFORM_NO_CACHE=1` to bypass
the cache entirely (every stage then runs as if the directory were empty).
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]


def root() -> Path | None:
    """The cache directory, or None when caching is disabled."""
    if os.environ.get("AUTOFORM_NO_CACHE"):
        return None
    return Path(os.environ.get("AUTOFORM_CACHE_DIR") or (REPO / ".autoform-work" / "cache"))


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def sha256_file(path) -> str | None:
    path = Path(path)
    if not path.is_file():
        return None
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for block in iter(lambda: fh.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def sha256_json(obj) -> str:
    return sha256_text(json.dumps(obj, sort_keys=True, separators=(",", ":"), default=str))


def function_digest(func: dict) -> str:
    """The digest of one exported function record, the key every entry sits under."""
    return sha256_json(func)


def tree_digest(directory, suffixes=(".py",)) -> str:
    """Digest of every file with one of `suffixes` under `directory` (name and content)."""
    directory = Path(directory)
    h = hashlib.sha256()
    if not directory.is_dir():
        return sha256_text("missing:" + str(directory))
    for path in sorted(directory.rglob("*")):
        if path.is_file() and path.suffix in suffixes and "__pycache__" not in path.parts:
            h.update(("%s\0%s\n" % (path.relative_to(directory).as_posix(),
                                     sha256_file(path))).encode())
    return h.hexdigest()


def lean_sources_digest(exclude_prefixes=("Autoform/SpecsGen/", "Autoform/Specs/",
                                          "Autoform/Generated/", "Autoform/NL/",
                                          "Autoform/NLModel/", "Autoform/Security/"),
                        include=("Autoform/SpecsGen/Basis.lean",)) -> str:
    """Digest of the Lean sources a specification proof can depend on, other than the
    rendered model (digested separately) and other specification modules (irrelevant)."""
    h = hashlib.sha256()
    paths = [REPO / "lean-toolchain", REPO / "lakefile.toml", REPO / "lake-manifest.json"]
    paths += sorted((REPO / "Autoform").rglob("*.lean"))
    for path in paths:
        if not path.is_file():
            continue
        rel = path.relative_to(REPO).as_posix()
        if rel in include or not any(rel.startswith(p) for p in exclude_prefixes):
            h.update(("%s\0%s\n" % (rel, sha256_file(path))).encode())
    return h.hexdigest()


def scripts_digest(names) -> str:
    """Digest of the harness scripts whose code decides a verdict."""
    h = hashlib.sha256()
    for name in names:
        h.update(("%s\0%s\n" % (name, sha256_file(REPO / name))).encode())
    return h.hexdigest()


def environment_key(**parts) -> str:
    """One digest over every named dependency of a stored verdict."""
    return sha256_json(parts)


class Store:
    """Entries under `<root>/<digest>/<kind>-<key16>.json`, a JSON object each."""

    def __init__(self, kind: str, env_key: str):
        self.kind = kind
        self.env_key = env_key
        self.root = root()
        self.hits = 0
        self.misses = 0
        self.writes = 0

    @property
    def enabled(self) -> bool:
        return self.root is not None

    def path(self, digest: str) -> Path:
        return self.root / digest / ("%s-%s.json" % (self.kind, self.env_key[:16]))

    def load(self, digest: str) -> dict:
        if not self.enabled:
            return {}
        p = self.path(digest)
        try:
            with p.open(encoding="utf-8") as fh:
                data = json.load(fh)
        except (OSError, ValueError):
            return {}
        return data if isinstance(data, dict) else {}

    def get(self, digest: str, key: str):
        entry = self.load(digest).get(key)
        if entry is None:
            self.misses += 1
        else:
            self.hits += 1
        return entry

    def put(self, digest: str, key: str, value) -> None:
        if not self.enabled:
            return
        p = self.path(digest)
        data = self.load(digest)
        data[key] = value
        p.parent.mkdir(parents=True, exist_ok=True)
        tmp = p.with_suffix(".json.tmp.%d" % os.getpid())
        with tmp.open("w", encoding="utf-8") as fh:
            json.dump(data, fh, sort_keys=True)
        os.replace(tmp, p)
        self.writes += 1

    def put_many(self, digest: str, values: dict) -> None:
        if not self.enabled or not values:
            return
        p = self.path(digest)
        data = self.load(digest)
        data.update(values)
        p.parent.mkdir(parents=True, exist_ok=True)
        tmp = p.with_suffix(".json.tmp.%d" % os.getpid())
        with tmp.open("w", encoding="utf-8") as fh:
            json.dump(data, fh, sort_keys=True)
        os.replace(tmp, p)
        self.writes += len(values)

    def summary(self) -> str:
        if not self.enabled:
            return "%s: cache disabled (AUTOFORM_NO_CACHE)" % self.kind
        return "%s: %d hit(s), %d miss(es), %d written under %s" % (
            self.kind, self.hits, self.misses, self.writes, self.root)
