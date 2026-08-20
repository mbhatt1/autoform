#!/usr/bin/env python3
"""check_docs.py — do the numbers in the docs still match the artifacts?

This repo's whole claim is that its reported numbers are honest. A number that was true
when it was written and is false now is not a documentation nit; it is the same defect
class as a metric computed from the artifact it describes.

The drift was real: at the time this script was written `docs/languages.md` said the
`cachetools` verifiable core was 45, `docs/scale.md` said 45, `docs/contracts.md` said 74,
and `ledger-Cachetools.json` said 69 — three documents, three different numbers, none of
them current. Nothing checked, so nothing complained.

Each row below binds one documented figure to the artifact field it is supposed to quote.
A mismatch is an error with the correct value printed, not a warning.

Usage:  scripts/check_docs.py [--fix-hint] [--root .]
Exit:   0 all figures current; 1 at least one stale; 2 an artifact is missing.
"""
from __future__ import annotations
import argparse, json, os, re, sys

# (doc, regex with ONE capturing group, artifact, key, transform)
CHECKS = [
    ("docs/scale.md",
     r"\|\s*`cachetools` \(published\)\s*\|\s*(\d+)\s*\|",
     "ledger-Cachetools.json", "functions", int),
    ("docs/scale.md",
     r"\|\s*`cachetools` \(published\)\s*\|\s*\d+\s*\|\s*([\d,]+) \(\d+%\)",
     "ledger-Cachetools.json", "holeFree", int),
    ("docs/scale.md",
     r"\|\s*`cachetools` \(published\)\s*\|\s*\d+\s*\|\s*[\d,]+ \(\d+%\)\s*\|\s*([\d,]+) \(\d+%\)",
     "ledger-Cachetools.json", "verifiableCore", int),
    ("docs/contracts.md",
     r"hole-free and (\d+) are call-closed",
     "ledger-Cachetools.json", "verifiableCore", int),
    ("docs/languages.md",
     r"\|\s*Python\s*\|.*?\|\s*(\d+)\s*\|\s*\d+%",
     "ledger-Cachetools.json", "functions", int),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    a = ap.parse_args()
    stale, missing = [], []
    for doc, rx, art, key, cast in CHECKS:
        dp, ap_ = os.path.join(a.root, doc), os.path.join(a.root, art)
        if not os.path.exists(dp) or not os.path.exists(ap_):
            missing.append(f"{doc} or {art}")
            continue
        want = json.load(open(ap_)).get(key)
        m = re.search(rx, open(dp).read(), re.S)
        if not m:
            stale.append(f"{doc}: pattern for {art}:{key} no longer matches — the doc was "
                         f"restructured and this check silently stopped checking. "
                         f"Fix the pattern, do not delete the row.")
            continue
        got = cast(m.group(1).replace(",", ""))
        if got != want:
            stale.append(f"{doc}: says {key}={got}, {art} says {want}")
    for m in missing:
        print(f"MISSING  {m}", file=sys.stderr)
    for s in stale:
        print(f"STALE    {s}", file=sys.stderr)
    if missing and not stale:
        print("check_docs: artifacts missing; nothing checked", file=sys.stderr)
        return 2
    if stale:
        print(f"\ncheck_docs: {len(stale)} stale figure(s). The docs are the claim; "
              f"update them or explain the difference.", file=sys.stderr)
        return 1
    print(f"check_docs: {len(CHECKS)} documented figures all match their artifacts")
    return 0


if __name__ == "__main__":
    sys.exit(main())
