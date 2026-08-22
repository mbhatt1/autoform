#!/usr/bin/env python3
"""check_specs_fresh.py — is each specification module still about the corpus it was
generated from?

A specification is a statement about a *specific rendering* of a corpus, not about the
project in the abstract. Closing a hole changes what the translated function computes, so
improving coverage can turn a true law false or a false law true. Specs do not rot
gracefully; they invert.

That is not hypothetical. It happened three times in one day:

  * `C_tfFree` asserted the cachetools context contains no `tryFinally`. The exporter
    learned to translate `try/finally`, the assertion became FALSE, and 72 fuel-transported
    laws that rested on it had to be demoted to obligations.
  * Fifteen V8 laws were recorded as refuted. They were evaluated against a module carrying
    55 `op:shiftLeft` holes; the current export has none. Seven of the fifteen are true
    against the current corpus, and the "refutation" described a program that no longer
    existed.
  * A cost of 11 GB was quoted as a property of the fuel transport. It was a property of the
    module layout, and moved by three orders of magnitude when the layout changed.

In every case the specs were internally consistent and the build was green. Nothing tied a
spec to the corpus version it was generated against, so nothing could notice.

This binds them. `artifact-manifest.json` gains a `specs` section recording, per spec
module, the `ast_sha256` of the corpus it was generated from. A mismatch means the specs
describe a program that is no longer the one in the tree — reported as STALE, with the
instruction to re-generate rather than to re-record.

Re-recording without re-generating is the failure mode to avoid: it makes the check agree
with whatever is there, which is a rubber stamp rather than a gate. `--record` therefore
prints what it is overwriting.

Usage:  scripts/check_specs_fresh.py [--record]
Exit:   0 all specs current; 1 at least one stale; 2 nothing checkable.
"""
from __future__ import annotations
import argparse, hashlib, json, os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MANIFEST = os.path.join(ROOT, "artifact-manifest.json")

# spec module (path under Autoform/) -> corpus module it is about
SPECS = {
    "SpecsGen/V8Base": "V8Base",
    "SpecsGen/Cachetools": "Cachetools",
    "SpecsGen/LinuxLib": "LinuxLibSample",
    "SpecsGen/LinuxLibSample": "LinuxLibSample",
    "SpecsGen/V8BaseSample": "V8BaseSample",
    "Specs/V8Spec": "V8BaseSample",
    "Specs/CachetoolsSpec": "Cachetools",
}


def sha(path: str) -> str | None:
    if not os.path.exists(path):
        return None
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for blk in iter(lambda: fh.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def corpus_hash(man: dict, corpus: str) -> tuple[str | None, str]:
    """Hash of the AST the corpus module is rendered from, and where it came from."""
    ent = man.get("modules", {}).get(corpus, {})
    tracked = os.path.join(ROOT, f"ast-{corpus}.json")
    if os.path.exists(tracked):
        return sha(tracked), f"ast-{corpus}.json"
    hint = ent.get("ast_hint")
    if hint and os.path.exists(hint):
        return sha(hint), hint
    return ent.get("ast_sha256"), "artifact-manifest.json (AST absent)"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--record", action="store_true",
                    help="pin the current corpus hashes (only after re-generating)")
    a = ap.parse_args()
    man = json.load(open(MANIFEST))
    specs = man.setdefault("specs", {})
    stale, unchecked, ok = [], [], 0

    for spec, corpus in SPECS.items():
        if not os.path.exists(os.path.join(ROOT, "Autoform", spec + ".lean")) and \
           not os.path.isdir(os.path.join(ROOT, "Autoform", spec)):
            continue
        cur, src = corpus_hash(man, corpus)
        if cur is None:
            unchecked.append(f"{spec}: corpus {corpus} has no AST and no recorded hash")
            continue
        rec = specs.get(spec, {}).get("corpus_ast_sha256")
        if a.record:
            if rec and rec != cur:
                print(f"  re-pinning {spec}: {rec[:12]} -> {cur[:12]} (from {src})")
            specs[spec] = {"corpus": corpus, "corpus_ast_sha256": cur, "source": src}
            ok += 1
            continue
        if rec is None:
            unchecked.append(f"{spec}: never pinned — run --record after generating")
        elif rec != cur:
            stale.append(f"{spec}: generated against corpus {corpus} @ {rec[:12]}, "
                         f"tree now has {cur[:12]} ({src}).\n"
                         f"    The laws describe a different program. RE-GENERATE the specs; "
                         f"do not re-record the hash.")
        else:
            ok += 1

    if a.record:
        json.dump(man, open(MANIFEST, "w"), indent=1, sort_keys=True)
        print(f"check_specs_fresh: pinned {ok} spec module(s)")
        return 0
    for u in unchecked:
        print(f"UNPINNED {u}", file=sys.stderr)
    for s in stale:
        print(f"STALE    {s}", file=sys.stderr)
    if stale:
        print(f"\ncheck_specs_fresh: {len(stale)} spec module(s) describe a corpus that has "
              f"changed under them.", file=sys.stderr)
        return 1
    if not ok and unchecked:
        return 2
    print(f"check_specs_fresh: {ok} spec module(s) match the corpus they were generated from")
    return 0


if __name__ == "__main__":
    sys.exit(main())
