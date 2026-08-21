#!/usr/bin/env python3
"""provenance.py — pin the CPG front end, and record how each artifact was produced.

`lake-manifest.json` pins every Lean dependency to a revision and `lean-toolchain` pins
the compiler, so two machines elaborate the same library.  Nothing did that for the other
half of the pipeline.  The neutral AST is a *function of Joern*: the CPG front end decides
the node vocabulary, the resolved `fullName`s, whether `IS_VARIADIC` is set, whether a
clause is elided.  Two machines with different Joern builds can produce different
`ast-*.json` from identical source and no artifact would show it.

So there is now `joern-version` beside `lean-toolchain`, and every artifact Joern produces
carries a provenance record naming the version that produced it.

Provenance records live in `provenance/<artifact>.prov.json`, a sidecar rather than a
field inside the artifact, for one reason: `cartographer/export_ast.sc` writes a bare JSON
array and every consumer (`render_lean.py`, `check_docs.py`, `differential.py`) indexes it
as one.  Wrapping the array in an envelope is a better end state and is written up as a
merge-phase change in `docs/architecture.md`; a sidecar gets the checkable property today
without breaking five readers.

WHAT A RECORD MUST MAKE POSSIBLE
    The `.cpg` files are not tracked (they are hundreds of megabytes) so a committed AST
    cannot be diffed against a re-export of its own CPG.  A record therefore names
    everything needed to *rebuild* the CPG and re-run the export:

        source_path       where the tree was
        source_revision   git commit of that tree, or, when it is not a checkout,
                          `tree-sha256:<digest>` — a content digest over the tree, which
                          is a reproducible identifier a later regeneration can re-derive
        command           the exact command line, so regeneration is not a reconstruction
        joern_version     the front end, from `joern-version`
        exporter_sha256   the Joern script that produced it

    `exporter_sha256` is the field that earns its keep without any CPG at all: change
    `export_ast.sc` and every committed AST is immediately, mechanically known to be
    out of date, by `scripts/check_provenance.py`, on a clean clone, with no Joern
    installed.  That is the "an exporter change cannot be re-verified" gap, closed from
    the side that does not need the 400 MB.

Subcommands
    joern-version   print the installed Joern version; --check compares it to the pin
    record          write a provenance record for an artifact
    show            print a record

`scripts/check_provenance.py` is the enforcement half.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
PROV_DIR = REPO / "provenance"
PIN_FILE = REPO / "joern-version"

# Artifacts whose content is decided by the Joern front end, and which are tracked.
JOERN_ARTIFACT_GLOBS = ("ast-*.json", "formalization-graph.json")

# Joern scripts an artifact can be attributed to.
EXPORTERS = {
    "cartographer/export_ast.sc": "ast-*.json",
    "cartographer/formalization_graph.sc": "formalization-graph.json",
}


# --------------------------------------------------------------------------- #
# Joern version detection
# --------------------------------------------------------------------------- #
#
# Deliberately does NOT shell out to `joern --version`: that boots a JVM and a Scala REPL
# (tens of seconds), and it is the one thing that must work in a checker that may run
# where Joern is half-installed.  The version is in the distribution's own jar names --
# `io.joern.joern-cli-4.0.606.jar` -- which is a fact about the bytes on disk rather than
# about a process starting successfully.  The macOS installer's known failure mode is
# exiting 0 having installed nothing (docs/running.md), and reading the lib directory
# catches exactly that.

_JAR_RE = re.compile(r"^io\.joern\.joern-cli-(.+)\.jar$")
_CPG_RE = re.compile(r"^io\.shiftleft\.codepropertygraph_[\d.]+-(.+)\.jar$")


class JoernAbsent(Exception):
    """Joern could not be located or its version could not be determined."""


def joern_home() -> Path:
    return Path(os.environ.get("JOERN_HOME", str(Path.home() / "joern")))


def detect_joern() -> dict:
    """Version of the installed Joern, from its jar names.

    Raises JoernAbsent with a reason.  Never returns a guess: an unknown front-end
    version recorded as some default would be the exact defect this file exists to
    prevent.
    """
    lib = joern_home() / "joern-cli" / "lib"
    if not lib.is_dir():
        raise JoernAbsent(
            f"no Joern at {lib} (JOERN_HOME={os.environ.get('JOERN_HOME', '<unset>')}, "
            f"default ~/joern). See docs/running.md; note that joern-install.sh can exit "
            f"0 having installed nothing."
        )
    names = os.listdir(lib)
    vers = [m.group(1) for m in (_JAR_RE.match(n) for n in names) if m]
    if not vers:
        raise JoernAbsent(
            f"{lib} exists but contains no io.joern.joern-cli-<version>.jar; this is not "
            f"a complete joern-cli distribution ({len(names)} files present)."
        )
    if len(set(vers)) > 1:
        raise JoernAbsent(
            f"{lib} contains {len(set(vers))} joern-cli versions ({', '.join(sorted(set(vers)))}); "
            f"which one runs is unpredictable. Remove the stale distribution."
        )
    cpg = sorted({m.group(1) for m in (_CPG_RE.match(n) for n in names) if m})
    return {
        "joern_version": vers[0],
        "cpg_schema_version": cpg[0] if len(cpg) == 1 else None,
        "joern_home": str(joern_home()),
    }


def pinned_joern() -> str:
    """The pinned version. A missing pin is a failure, not a free pass."""
    if not PIN_FILE.exists():
        raise JoernAbsent(
            f"{PIN_FILE} is missing. It is the CPG front end's `lean-toolchain`; without "
            f"it nothing constrains which Joern produced the committed ASTs."
        )
    txt = PIN_FILE.read_text().strip()
    if not txt:
        raise JoernAbsent(f"{PIN_FILE} is empty.")
    return txt


# --------------------------------------------------------------------------- #
# Digests and source revisions
# --------------------------------------------------------------------------- #

def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


SKIP_DIRS = {".git", "__pycache__", ".lake", "node_modules", ".mypy_cache"}


def tree_sha256(root: Path) -> str:
    """Content digest of a source tree: sorted (relpath, blob-sha) pairs, hashed.

    The fallback identity for a tree that is not a git checkout (the Linux corpora here
    are unpacked tarballs).  It is reproducible -- a later regeneration re-derives the
    same digest from the same bytes -- which is the whole requirement.  It is not a
    substitute for a revision when a revision exists, and `record` prefers the revision.
    """
    h = hashlib.sha256()
    files = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if d not in SKIP_DIRS)
        for fn in sorted(filenames):
            p = Path(dirpath) / fn
            if p.is_symlink() or not p.is_file():
                continue
            files.append(p)
    for p in sorted(files):
        h.update(str(p.relative_to(root)).encode())
        h.update(b"\0")
        h.update(sha256_file(p).encode())
        h.update(b"\n")
    return f"tree-sha256:{h.hexdigest()}:{len(files)}files"


def source_revision(src: Path) -> str:
    """git revision if the tree is a checkout, else a content digest. Never a guess."""
    try:
        out = subprocess.run(
            ["git", "-C", str(src), "rev-parse", "HEAD"],
            capture_output=True, text=True, timeout=30,
        )
        if out.returncode == 0 and out.stdout.strip():
            rev = out.stdout.strip()
            dirty = subprocess.run(
                ["git", "-C", str(src), "status", "--porcelain"],
                capture_output=True, text=True, timeout=60,
            ).stdout.strip()
            return f"git:{rev}" + ("+dirty" if dirty else "")
    except (OSError, subprocess.SubprocessError):
        pass
    return tree_sha256(src)


def record_path(artifact: Path) -> Path:
    return PROV_DIR / (artifact.name + ".prov.json")


def relrepo(p: Path) -> str:
    try:
        return str(Path(p).resolve().relative_to(REPO))
    except ValueError:
        return str(Path(p).resolve())


# --------------------------------------------------------------------------- #
# record
# --------------------------------------------------------------------------- #

SCHEMA_VERSION = 1

REQUIRED_FIELDS = (
    "schema_version", "artifact", "artifact_sha256", "joern_version",
    "exporter", "exporter_sha256", "source_path", "source_revision", "command",
)


def cmd_record(args) -> int:
    artifact = Path(args.artifact).resolve()
    if not artifact.is_file():
        print(f"provenance: no such artifact {artifact}", file=sys.stderr)
        return 2
    src = Path(args.source).resolve()
    if not src.exists():
        print(f"provenance: source tree {src} does not exist; a provenance record whose "
              f"source_revision is invented is worse than none.", file=sys.stderr)
        return 2
    exporter = Path(args.exporter)
    exporter_abs = exporter if exporter.is_absolute() else REPO / exporter
    if not exporter_abs.is_file():
        print(f"provenance: no such exporter script {exporter_abs}", file=sys.stderr)
        return 2
    try:
        det = detect_joern()
    except JoernAbsent as e:
        print(f"provenance: cannot record — {e}", file=sys.stderr)
        print("provenance: recording an artifact without knowing which Joern made it is "
              "the gap this tool closes; refusing.", file=sys.stderr)
        return 2

    rec = {
        "schema_version": SCHEMA_VERSION,
        "artifact": relrepo(artifact),
        "artifact_sha256": sha256_file(artifact),
        "artifact_bytes": artifact.stat().st_size,
        "joern_version": det["joern_version"],
        "cpg_schema_version": det["cpg_schema_version"],
        "exporter": relrepo(exporter_abs),
        "exporter_sha256": sha256_file(exporter_abs),
        "source_path": str(src),
        "source_revision": source_revision(src),
        "command": args.command,
        "recorded_by": "scripts/provenance.py record",
    }
    PROV_DIR.mkdir(exist_ok=True)
    out = record_path(artifact)
    out.write_text(json.dumps(rec, indent=1, sort_keys=True) + "\n")
    print(f"provenance: wrote {relrepo(out)} (joern {rec['joern_version']}, "
          f"source {rec['source_revision'][:24]}…)")
    return 0


def cmd_show(args) -> int:
    p = record_path(Path(args.artifact).resolve())
    if not p.exists():
        print(f"provenance: no record at {p}", file=sys.stderr)
        return 1
    print(p.read_text(), end="")
    return 0


def cmd_joern_version(args) -> int:
    try:
        det = detect_joern()
    except JoernAbsent as e:
        print(f"joern-version: UNKNOWN — {e}", file=sys.stderr)
        return 2
    print(det["joern_version"])
    if args.check:
        try:
            want = pinned_joern()
        except JoernAbsent as e:
            print(f"joern-version: {e}", file=sys.stderr)
            return 2
        if det["joern_version"] != want:
            print(f"joern-version: MISMATCH — installed {det['joern_version']}, "
                  f"`joern-version` pins {want}. The neutral AST is a function of the "
                  f"front end: regenerating with this build may change ast-*.json for "
                  f"reasons that have nothing to do with the source. Install the pinned "
                  f"release (docs/running.md) or change the pin deliberately and "
                  f"regenerate every artifact.", file=sys.stderr)
            return 1
        print(f"joern-version: matches pin ({want})")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)

    jv = sub.add_parser("joern-version", help="print the installed Joern version")
    jv.add_argument("--check", action="store_true", help="compare against ./joern-version")
    jv.set_defaults(fn=cmd_joern_version)

    rc = sub.add_parser("record", help="write a provenance record for an artifact")
    rc.add_argument("--artifact", required=True)
    rc.add_argument("--source", required=True, help="source tree the CPG was built from")
    rc.add_argument("--exporter", required=True, help="the .sc script that produced it")
    rc.add_argument("--command", required=True, help="the exact command line used")
    rc.set_defaults(fn=cmd_record)

    sh = sub.add_parser("show", help="print an artifact's provenance record")
    sh.add_argument("artifact")
    sh.set_defaults(fn=cmd_show)

    a = ap.parse_args()
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
