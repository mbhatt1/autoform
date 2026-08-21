#!/usr/bin/env python3
"""reproduce_ast.py — rebuild an artifact's CPG from source and re-export it.

`ast-*.json` is tracked; the `.cpg` it came from is not (they are hundreds of megabytes).
The consequence people usually notice is that an exporter change cannot be re-verified
against the committed ASTs.  The consequence people usually do NOT notice is that a
committed AST can drift arbitrarily far from the exporter that is committed beside it and
nothing complains, because the two are only ever compared through a Lean module that was
rendered at the same time as the AST and therefore agrees with it by construction.

This is the independent recomputation.  It does not read the committed AST to decide what
to expect; it goes back to the source tree, rebuilds the CPG with the pinned Joern, runs
the committed exporter, and diffs.  If the CPG does not have to be kept, this is what
makes that acceptable — provided it is actually run.

    scripts/reproduce_ast.py ast-Sample.json --source /path/to/sample
    scripts/reproduce_ast.py ast-Sample.json          # source from the provenance record

Exit: 0 reproduced byte-for-byte, 1 differs, 2 could not run (and says why).

Cost is real — a large corpus is minutes of joern-parse — which is why this is a command
rather than something wired into every build.  `scripts/check_provenance.py` is the cheap
check that runs everywhere; this is the expensive one that establishes the fact.
"""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import provenance as P  # noqa: E402


def normalized(path: Path):
    return json.dumps(json.loads(path.read_text()), indent=1, sort_keys=True).splitlines()


def summarize(committed: Path, fresh: Path) -> list[str]:
    """A short, honest description of how they differ — names first, then shape."""
    a, b = json.loads(committed.read_text()), json.loads(fresh.read_text())
    out = [f"committed has {len(a)} entries, fresh export has {len(b)}"]
    if isinstance(a, list) and isinstance(b, list) and a and isinstance(a[0], dict):
        na = {x.get("name") for x in a}
        nb = {x.get("name") for x in b}
        if nb - na:
            out.append(f"only in fresh: {sorted(nb - na)[:8]}")
        if na - nb:
            out.append(f"only in committed: {sorted(na - nb)[:8]}")
        if na == nb:
            out.append("same function set; the bodies differ")
    import difflib
    d = list(difflib.unified_diff(normalized(committed), normalized(fresh),
                                  "committed", "fresh", lineterm="", n=0))
    out.append(f"{len(d)} unified-diff lines over the normalized JSON")
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("artifact")
    ap.add_argument("--source", help="source tree (default: from the provenance record)")
    ap.add_argument("--exporter", default="cartographer/export_ast.sc")
    ap.add_argument("--keep", help="directory to leave the fresh export in")
    a = ap.parse_args()

    art = Path(a.artifact).resolve()
    if not art.is_file():
        print(f"reproduce_ast: no such artifact {art}", file=sys.stderr)
        return 2

    src = a.source
    exporter = a.exporter
    rec_path = P.record_path(art)
    if rec_path.exists():
        rec = json.loads(rec_path.read_text())
        src = src or rec.get("source_path")
        exporter = rec.get("exporter", exporter)
    if not src:
        print(f"reproduce_ast: no --source and no provenance record at "
              f"{rec_path}; there is nothing to reproduce *from*. This is the gap "
              f"scripts/provenance.py record exists to close.", file=sys.stderr)
        return 2
    srcp = Path(src)
    if not srcp.is_dir():
        print(f"reproduce_ast: source tree {srcp} is absent. Cannot reproduce; this is "
              f"UNVERIFIED, not a pass.", file=sys.stderr)
        return 2

    try:
        det = P.detect_joern()
        pin = P.pinned_joern()
    except P.JoernAbsent as e:
        print(f"reproduce_ast: {e}", file=sys.stderr)
        return 2
    if det["joern_version"] != pin:
        print(f"reproduce_ast: installed Joern {det['joern_version']} != pin {pin}. A "
              f"difference found now could be the front end rather than the exporter, so "
              f"the comparison would not mean what it looks like. Refusing.",
              file=sys.stderr)
        return 2

    cli = P.joern_home() / "joern-cli"
    work = Path(tempfile.mkdtemp(prefix="reproduce-ast-"))
    try:
        cpg = work / "cpg.bin"
        print(f"reproduce_ast: joern-parse {srcp}  (Joern {pin})")
        r = subprocess.run([str(cli / "joern-parse"), str(srcp), "--output", str(cpg)],
                           capture_output=True, text=True)
        if r.returncode != 0 or not cpg.exists():
            print(f"reproduce_ast: joern-parse failed (rc={r.returncode})\n"
                  f"{r.stdout[-2000:]}{r.stderr[-2000:]}", file=sys.stderr)
            return 2
        fresh = work / art.name
        print(f"reproduce_ast: {exporter}")
        r = subprocess.run([str(cli / "joern"), "--script", exporter,
                            "--param", f"cpgPath={cpg}", "--param", f"out={fresh}"],
                           capture_output=True, text=True, cwd=str(P.REPO))
        if not fresh.exists():
            print(f"reproduce_ast: the exporter produced nothing (rc={r.returncode})\n"
                  f"{r.stdout[-3000:]}{r.stderr[-2000:]}", file=sys.stderr)
            return 2
        for line in r.stdout.splitlines():
            if line.startswith("exported"):
                print("  " + line)

        same = art.read_bytes() == fresh.read_bytes()
        if a.keep:
            Path(a.keep).mkdir(parents=True, exist_ok=True)
            shutil.copy(fresh, Path(a.keep) / art.name)
        if same:
            print(f"reproduce_ast: {art.name} REPRODUCED byte-for-byte from {srcp} "
                  f"with Joern {pin} and {exporter}.")
            return 0
        print(f"reproduce_ast: {art.name} DIFFERS from a fresh export.", file=sys.stderr)
        for line in summarize(art, fresh):
            print(f"  {line}", file=sys.stderr)
        print("  The committed artifact does not correspond to the committed exporter. "
              "Regenerate it (./autoform.sh) and re-render the Lean module beside it, or "
              "record why the difference is expected.", file=sys.stderr)
        return 1
    finally:
        shutil.rmtree(work, ignore_errors=True)
        shutil.rmtree(P.REPO / "workspace", ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
