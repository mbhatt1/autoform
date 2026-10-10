"""The files that make up a rendered module `Autoform.Generated.<M>`.

`cartographer/render_lean.py --shard-functions N` splits a large corpus into part modules
`Autoform/Generated/<M>/PartNNNN.lean` that the root `Autoform/Generated/<M>.lean` imports.
Anything that hashes, snapshots, mutates or inspects "the model" has to see all of them:
a digest of the root alone would let a part change without the evidence noticing.

The root's own import list is the authority, not a directory listing, so a stale part left
on disk is never mistaken for part of the model.
"""
from pathlib import Path
import re

GENERATED = Path("Autoform") / "Generated"


def part_names(root_lean: Path, module: str) -> list[str]:
    """`PartNNNN` names imported by the root module, in import order."""
    if not root_lean.is_file():
        return []
    pattern = re.compile(r"import Autoform\.Generated\.%s\.(Part\d+)\s*$" % re.escape(module))
    parts = []
    for line in root_lean.read_text(encoding="utf-8").splitlines():
        if not line.startswith("import "):
            if line.strip():
                break
            continue
        match = pattern.match(line)
        if match:
            parts.append(match.group(1))
    return parts


def lean_files(repo, module: str) -> list[Path]:
    """The root `.lean` followed by every part it imports."""
    root = Path(repo) / GENERATED / (module + ".lean")
    return [root] + [root.parent / module / (p + ".lean") for p in part_names(root, module)]


def build_files(repo, module: str, exts=(".olean", ".ilean")) -> list[Path]:
    """Compiled artifacts of the root and its parts under `.lake/build/lib/lean`."""
    repo = Path(repo)
    lib = repo / ".lake" / "build" / "lib" / "lean" / GENERATED
    names = [Path(module)] + [Path(module) / p for p in
                              part_names(repo / GENERATED / (module + ".lean"), module)]
    return [lib / (str(n) + ext) for n in names for ext in exts]


def is_sharded(repo, module: str) -> bool:
    return len(lean_files(repo, module)) > 1


def model_files(generated) -> list[Path]:
    """`lean_files` addressed by the root module's path instead of (repo, module)."""
    generated = Path(generated)
    module = generated.stem
    return [generated] + [generated.parent / module / (p + ".lean")
                          for p in part_names(generated, module)]


def model_digest(generated) -> str:
    """The digest evidence is bound to. Unsharded: the root file's SHA-256, exactly as
    before sharding existed, so recorded evidence stays valid. Sharded: the SHA-256 of
    each file's name and digest in import order, so changing any part changes it."""
    import hashlib
    files = model_files(generated)
    if len(files) == 1:
        return hashlib.sha256(files[0].read_bytes()).hexdigest()
    h = hashlib.sha256()
    for path in files:
        h.update(("%s/%s\0%s\n" % (path.parent.name, path.name,
                                   hashlib.sha256(path.read_bytes()).hexdigest())).encode())
    return h.hexdigest()
