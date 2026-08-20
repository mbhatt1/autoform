#!/usr/bin/env python3
"""check_provenance.py — is every Joern-produced artifact traceable to what produced it?

An unchecked provenance record decays into a comment.  This is the check.

It runs from a clean clone with no Joern installed and no `.cpg` anywhere, because every
question it asks is answerable from tracked bytes:

  1. COVERAGE      every tracked `ast-*.json` (and `formalization-graph.json`, if present)
                   has a record, or is named in the unattributed baseline.  A new
                   artifact with no record fails.  An artifact that quietly appears is
                   the failure mode this catches.
  2. INTEGRITY     the record's `artifact_sha256` is the artifact's actual digest.  An
                   artifact regenerated without re-recording fails here.
  3. PIN           the record's `joern_version` equals `joern-version`.  The front end
                   decides the AST; a bump that was not propagated to the artifacts is a
                   silent change of meaning.
  4. EXPORTER      the record's `exporter_sha256` equals the current digest of the Joern
                   script named in it.  This is the check that closes "committed ASTs
                   cannot be regenerated without their CPGs": the `.cpg` files are not
                   tracked, so a committed AST cannot be diffed against a re-export --
                   but the moment `cartographer/export_ast.sc` changes, every AST that
                   predates the change is *mechanically known* to be stale, and the record
                   holds the exact command that regenerates it.
  5. FIELDS        the fields a regeneration needs are present and non-empty.
  6. ORPHANS       no record without an artifact.
  7. BASELINE      an artifact named in the unattributed baseline still has the digest it
                   had when it was baselined.  Regenerate it and the excuse expires; you
                   must record real provenance.

Two things this check deliberately does NOT claim:
  * It does not verify that the recorded command actually reproduces the artifact.  That
    needs Joern, the source tree and ~minutes per corpus; `--verify-source` re-derives
    the recorded `source_revision` when the tree is present, and says so when it is not.
    An unre-derived revision is reported as UNVERIFIED, never counted as verified.
  * A baselined artifact is reported, by name, on every run.  It is a named gap, not a
    pass.  `--strict` refuses to accept the baseline at all.

Usage:  scripts/check_provenance.py [--strict] [--verify-source] [--root .]
Exit:   0 everything attributed or explicitly baselined; 1 a violation; 2 nothing checked.
"""
from __future__ import annotations

import argparse
import glob
import json
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import provenance as P  # noqa: E402

BASELINE = "provenance/unattributed.json"


def load_json(p: Path):
    try:
        return json.loads(p.read_text())
    except (OSError, json.JSONDecodeError) as e:
        return e


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--strict", action="store_true",
                    help="treat baselined (unattributed) artifacts as failures")
    ap.add_argument("--verify-source", action="store_true",
                    help="re-derive source_revision where the source tree is present")
    a = ap.parse_args()
    root = Path(a.root).resolve()
    P.REPO = root
    P.PROV_DIR = root / "provenance"
    P.PIN_FILE = root / "joern-version"

    fail: list[str] = []
    notes: list[str] = []

    # --- the pin itself ---------------------------------------------------- #
    try:
        pin = P.pinned_joern()
    except P.JoernAbsent as e:
        print(f"FAIL  {e}", file=sys.stderr)
        print("check_provenance: without a pin there is nothing to check against.",
              file=sys.stderr)
        return 1

    # --- artifacts --------------------------------------------------------- #
    artifacts: list[Path] = []
    for g in P.JOERN_ARTIFACT_GLOBS:
        artifacts.extend(sorted(Path(p) for p in glob.glob(str(root / g))))
    if not artifacts:
        # Silence must never read as success: finding no artifacts at all means the
        # check looked in the wrong place, not that everything is attributed.
        print(f"check_provenance: found no {' / '.join(P.JOERN_ARTIFACT_GLOBS)} under "
              f"{root}. Nothing was checked; this is not a pass.", file=sys.stderr)
        return 2

    bpath = root / BASELINE
    baseline = {}
    if bpath.exists():
        b = load_json(bpath)
        if isinstance(b, Exception):
            fail.append(f"{BASELINE} is unreadable ({b}); the backlog it records cannot "
                        f"be honoured, so nothing may rely on it.")
        else:
            baseline = b.get("artifacts", {})

    prov_dir = root / "provenance"
    seen_records = set()
    attributed = 0
    baselined: list[str] = []

    for art in artifacts:
        rel = art.name
        rp = prov_dir / (rel + ".prov.json")
        actual = P.sha256_file(art)
        if not rp.exists():
            entry = baseline.get(rel)
            if entry is None:
                fail.append(
                    f"{rel}: no provenance record ({rp.relative_to(root)}) and not in "
                    f"{BASELINE}. Record one with:  scripts/provenance.py record "
                    f"--artifact {rel} --source <tree> --exporter cartographer/export_ast.sc "
                    f"--command '<exact command>'")
            elif entry.get("artifact_sha256") != actual:
                fail.append(
                    f"{rel}: listed in {BASELINE} as unattributed, but its digest changed "
                    f"({entry.get('artifact_sha256', '?')[:12]}… -> {actual[:12]}…). It was "
                    f"regenerated, so its provenance is knowable now: record it and remove "
                    f"the baseline entry. A stale excuse is not an excuse.")
            else:
                baselined.append(f"{rel}: {entry.get('reason', 'no reason recorded')}")
            continue
        seen_records.add(rp.name)
        rec = load_json(rp)
        if isinstance(rec, Exception):
            fail.append(f"{rel}: provenance record is unreadable ({rec}).")
            continue

        missing = [f for f in P.REQUIRED_FIELDS if not rec.get(f)]
        if missing:
            fail.append(f"{rel}: provenance record is missing {', '.join(missing)}; a "
                        f"regeneration from it would be a reconstruction, not a replay.")
            continue
        if rec["artifact_sha256"] != actual:
            fail.append(
                f"{rel}: record says sha256 {rec['artifact_sha256'][:12]}…, file is "
                f"{actual[:12]}…. The artifact changed after it was recorded — re-record "
                f"it, or restore the artifact the record describes.")
        if rec["joern_version"] != pin:
            fail.append(
                f"{rel}: produced by Joern {rec['joern_version']}, but `joern-version` "
                f"pins {pin}. Either the pin moved without regenerating the artifact, or "
                f"the artifact was made with an unpinned front end. The neutral AST is a "
                f"function of the front end; this difference is not cosmetic.")
        exp = root / rec["exporter"]
        if not exp.exists():
            fail.append(f"{rel}: recorded exporter {rec['exporter']} does not exist.")
        else:
            now = P.sha256_file(exp)
            if now != rec["exporter_sha256"]:
                fail.append(
                    f"{rel}: {rec['exporter']} changed since this artifact was exported "
                    f"({rec['exporter_sha256'][:12]}… -> {now[:12]}…). The .cpg is not "
                    f"tracked, so the committed AST cannot be re-verified in place; "
                    f"regenerate it with the recorded command and re-record:\n"
                    f"        {rec['command']}\n"
                    f"        source: {rec['source_path']} @ {rec['source_revision']}")
        if a.verify_source:
            src = Path(rec["source_path"])
            if not src.exists():
                notes.append(f"{rel}: source tree {src} absent — source_revision "
                             f"{rec['source_revision'][:28]}… UNVERIFIED (not re-derived).")
            else:
                got = P.source_revision(src)
                if got != rec["source_revision"]:
                    fail.append(f"{rel}: source at {src} is now {got[:36]}…, record says "
                                f"{rec['source_revision'][:36]}…. Regenerating today would "
                                f"not reproduce this artifact.")
                else:
                    notes.append(f"{rel}: source_revision re-derived and matches.")
        attributed += 1

    for rp in sorted(prov_dir.glob("*.prov.json")) if prov_dir.is_dir() else []:
        if rp.name not in seen_records:
            art = rp.name[: -len(".prov.json")]
            if not (root / art).exists():
                fail.append(f"{rp.relative_to(root)}: describes {art}, which does not "
                            f"exist. An orphan record is a claim about nothing.")

    # --- report ------------------------------------------------------------ #
    for n in notes:
        print(f"note   {n}")
    for b in baselined:
        print(f"UNATTRIBUTED  {b}", file=sys.stderr)
    for f in fail:
        print(f"FAIL   {f}", file=sys.stderr)

    total = len(artifacts)
    print(f"\ncheck_provenance: {attributed}/{total} artifacts fully attributed to "
          f"Joern {pin}; {len(baselined)} unattributed (baselined); "
          f"{len(fail)} violation(s).")
    if baselined and a.strict:
        print("check_provenance: --strict, so the baseline is not accepted.",
              file=sys.stderr)
        return 1
    if fail:
        return 1
    if baselined:
        print("check_provenance: PASS with a named gap — the artifacts above predate "
              "provenance recording and are listed, not hidden. Regenerating any of them "
              "requires recording real provenance.")
    else:
        print("check_provenance: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
