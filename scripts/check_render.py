#!/usr/bin/env python3
"""check_render.py -- does the AST still render to the artifact everything was measured on?

## What changed, and why

Until today `Autoform/Generated/<M>.lean` was **tracked in git** and this script compared
the tracked module against a fresh `render(ast-<M>.json)`. That check caught real bugs (a
mutation-gate mutant that survived four commits; a 238-vs-208 function drift), and the
argument for it was sound as far as it went.

But it had the causality backwards. The mutant reached git *because the module was
tracked*: a 21 MB machine-generated file is not reviewable in a diff, so a one-token
change inside it is invisible to every human gate and only a re-render can see it. The
module is a **deterministic function of the AST** -- `render_lean.py` is verified
byte-identical across runs -- so tracking it stores no information the AST does not
already determine, while opening a write channel for exactly the corruption this script
was written to detect.

So the policy is now: **the AST is the tracked source of truth; the rendered Lean module
is a build product and is not tracked.** See `docs/integrity.md` for the full argument,
including why the largest ASTs are tracked by hash rather than by bytes.

## What this script verifies under the new policy

Not tracking the module does NOT make this check a no-op -- it makes it check three
different, still-falsifiable things:

1. **AST integrity.** The AST's sha256 must equal the one recorded in
   `artifact-manifest.json`. Under the new policy the AST is the only place a mutant can
   enter, and a mutant in a 500 KB JSON is a reviewable diff, not a needle in 21 MB.
2. **Render stability.** `sha256(render(AST))` must equal the recorded render hash. This
   is what the old byte-comparison against the tracked module bought -- the identity of
   the artifact all downstream numbers describe -- minus the megabytes and minus the
   write channel. A renderer change that silently alters output is caught here.
3. **Local materialisation.** If `Autoform/Generated/<M>.lean` exists on disk (it will,
   after any build), it must be byte-identical to the fresh render. This is the original
   mutant check, still intact, now covering a working tree instead of an index.

With `--typecheck` it additionally materialises the render and runs
`lake build Autoform.Generated.<M>`, which is the claim that the AST renders to a Lean
program the kernel accepts. That is a weaker claim than "the committed module is correct"
and a stronger one than "the bytes match": it is checked against the toolchain, not
against a hash we wrote ourselves.

## Silence is not success

Every module named in the manifest must reach a verdict. A missing AST, a missing manifest
entry, a render failure -- each is reported as UNVERIFIABLE with a reason and makes the
exit code non-zero. This script must never pass by having stopped looking.

Usage:
  scripts/check_render.py [--typecheck] [Module ...]
  scripts/check_render.py --record [Module ...]     # re-record hashes after an intended change

## Not tracked by policy is a verdict, not a pass

Three corpora (`Ansible`, `LinuxCrypto`, `LinuxLib`) have an AST that is gitignored by
policy (`docs/integrity.md`): it is larger than its render, and neither its source commit
nor its exporter version was recorded, so a re-export cannot reproduce the pinned hash.
Its absence from a clone is the expected state. Reporting that as UNVERIFIABLE on every
run kept CI permanently red, which trains everyone to ignore exit 3 -- including on the
day it means something.

So `artifact-manifest.json` carries a hand-edited, reviewed allowlist,
`untracked_by_policy`. A module whose AST is absent gets the verdict **NOT-TRACKED**
(printed, counted separately, never counted as verified, does not fail the run) only if
ALL of these hold, each checked here rather than assumed:

* it has an allowlist entry with non-empty `reason` and `reviewed` fields;
* `git check-ignore` confirms `ast-<M>.json` is ignored and `git ls-files` that it is not
  tracked -- the policy is real in this tree, not merely asserted in the manifest;
* its manifest entry says `ast_tracked: false`;
* no spec module in the manifest's `specs` is pinned to it -- tracked theorems about a
  corpus no clone can produce are exactly the case STRATEGY 55 made UNVERIFIABLE.

Anything else with an absent AST is UNVERIFIABLE, as before. If the AST IS on disk the
allowlist is irrelevant and the module is fully checked. `--strict` ignores the allowlist
entirely. A run in which nothing was verified still exits 2. `--record` never writes the
allowlist.

Exit: 0 every module verified or NOT-TRACKED by reviewed policy (at least one verified);
      1 a module mismatched; 2 nothing could be checked at all;
      3 some modules verified but others were unverifiable.
"""
from __future__ import annotations
import argparse, difflib, hashlib, json, os, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RENDER = os.path.join(ROOT, "cartographer", "render_lean.py")
MANIFEST = os.path.join(ROOT, "artifact-manifest.json")
GEN = os.path.join(ROOT, "Autoform", "Generated")


def sha256(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def load_manifest() -> dict:
    if not os.path.exists(MANIFEST):
        return {"policy": "see docs/integrity.md", "modules": {}}
    with open(MANIFEST) as f:
        return json.load(f)


def ast_path(m: str, entry: dict) -> str | None:
    """Where this module's AST lives, or None if it cannot be found.

    Tracked ASTs sit at the repo root. Corpora whose AST is too large to track are
    recorded with an `ast_hint` -- an out-of-tree path from the run that produced them.
    A hint that no longer resolves is an UNVERIFIABLE, never a pass."""
    for cand in (os.path.join(ROOT, f"ast-{m}.json"), entry.get("ast_hint")):
        if cand and os.path.exists(cand):
            return cand
    return None


def render(ast: str, m: str, out: str) -> str | None:
    r = subprocess.run([sys.executable, RENDER, ast, out, m],
                       capture_output=True, text=True, timeout=3600)
    if r.returncode != 0:
        return f"render failed ({r.returncode}): {(r.stderr or r.stdout)[-500:]}"
    return None


def first_diff(a_path: str, b_path: str, a_name: str, b_name: str) -> str:
    a = open(a_path).read().splitlines()
    b = open(b_path).read().splitlines()
    body = [l for l in difflib.unified_diff(a, b, a_name, b_name, n=0, lineterm="")
            if l.startswith(("+", "-")) and not l.startswith(("+++", "---"))]
    head = "\n".join("      " + l for l in body[:12])
    more = f"\n      ... {len(body) - 12} more differing lines" if len(body) > 12 else ""
    return f"{len(body)} differing lines\n{head}{more}"


def _git(*args: str) -> subprocess.CompletedProcess | None:
    try:
        return subprocess.run(["git", "-C", ROOT, *args], capture_output=True,
                              text=True, timeout=60)
    except (OSError, subprocess.SubprocessError):
        return None


def policy_untracked(m: str, entry: dict, man: dict) -> tuple[bool, str]:
    """Is the absence of ast-<M>.json the reviewed policy, checked against this tree?

    Returns (True, reason) only if every condition in the module docstring holds;
    otherwise (False, why-not), and the caller reports UNVERIFIABLE with that text."""
    allow = (man.get("untracked_by_policy") or {}).get(m)
    if not allow:
        return False, "no untracked_by_policy entry"
    if not (isinstance(allow, dict) and str(allow.get("reason", "")).strip()
            and str(allow.get("reviewed", "")).strip()):
        return False, ("its untracked_by_policy entry lacks a non-empty 'reason' and "
                       "'reviewed' field, so it is not a reviewed exception")
    if entry.get("ast_tracked") is not False:
        return False, ("artifact-manifest.json does not record ast_tracked: false, which "
                       "contradicts the allowlist")
    name = f"ast-{m}.json"
    ign = _git("check-ignore", "-q", "--no-index", name)
    if ign is None or ign.returncode != 0:
        return False, (f"git does not confirm {name} is ignored here (not a git checkout, "
                       f"or .gitignore no longer lists it), so the policy is only asserted")
    ls = _git("ls-files", "--error-unmatch", name)
    if ls is None or ls.returncode == 0:
        return False, f"{name} is tracked in git yet absent from the working tree"
    pinned = sorted(k for k, v in (man.get("specs") or {}).items()
                    if isinstance(v, dict) and v.get("corpus") == m)
    if pinned:
        return False, (f"spec module(s) {', '.join(pinned)} are pinned to this corpus; "
                       f"theorems about an AST no clone can produce are unverifiable "
                       f"(STRATEGY 55), and no allowlist entry can change that")
    return True, str(allow["reason"]).strip()


def check(m: str, entry: dict, typecheck: bool, man: dict | None = None,
          strict: bool = False) -> tuple[str, str]:
    """Returns (verdict, detail), verdict in {OK, MISMATCH, UNVERIFIABLE, NOT-TRACKED}."""
    ast = ast_path(m, entry)
    if ast is None:
        if not strict and (man or {}).get("untracked_by_policy", {}).get(m):
            ok, why = policy_untracked(m, entry, man or {})
            if ok:
                return ("NOT-TRACKED",
                        f"AST absent and gitignored by reviewed policy -- NOT checked. "
                        f"Pinned ast_sha256 {str(entry.get('ast_sha256'))[:12]}. {why}")
            return ("UNVERIFIABLE",
                    f"AST not found, and its untracked_by_policy entry does not "
                    f"apply: {why}.")
        hint = entry.get("ast_hint") or "(no out-of-tree hint recorded)"
        return ("UNVERIFIABLE",
                f"AST not found: neither ast-{m}.json nor {hint} exists. "
                f"{entry.get('provenance', '')} Re-export it or drop the module from "
                f"artifact-manifest.json; this check cannot speak for it.")

    got = sha256(ast)
    want = entry.get("ast_sha256")
    if not want:
        return ("UNVERIFIABLE",
                f"artifact-manifest.json records no ast_sha256 for {m}; "
                f"run scripts/check_render.py --record {m} after reviewing the AST.")
    if got != want:
        return ("MISMATCH",
                f"the AST has changed since it was recorded.\n"
                f"      recorded {want}\n      on disk  {got}\n"
                f"      The AST is the tracked source of truth -- review this diff, then "
                f"re-record with scripts/check_render.py --record {m}.")

    with tempfile.TemporaryDirectory(prefix="autoform_render_") as d:
        fresh = os.path.join(d, f"{m}.lean")
        err = render(ast, m, fresh)
        if err:
            return ("UNVERIFIABLE", err)
        rh = sha256(fresh)
        if entry.get("render_sha256") and rh != entry["render_sha256"]:
            return ("MISMATCH",
                    f"the AST is unchanged but its render is not.\n"
                    f"      recorded render {entry['render_sha256']}\n"
                    f"      fresh render    {rh}\n"
                    f"      render_lean.py is supposed to be a deterministic function of "
                    f"the AST alone; something in the renderer changed the artifact every "
                    f"downstream number describes.")

        live = os.path.join(GEN, f"{m}.lean")
        notes = []
        if os.path.exists(live):
            if sha256(live) != rh:
                return ("MISMATCH",
                        f"Autoform/Generated/{m}.lean on disk is NOT the render of its AST.\n"
                        f"      " + first_diff(fresh, live, "render(AST)", "on disk") +
                        f"\n      Anything measured from it describes a program nobody wrote. "
                        f"Rebuild it: cartographer/render_lean.py "
                        f"{os.path.relpath(ast, ROOT)} Autoform/Generated/{m}.lean {m}")
            notes.append("working-tree module matches")
        else:
            notes.append("no working-tree module (build product, not tracked)")

        if typecheck:
            os.makedirs(GEN, exist_ok=True)
            with open(fresh, "rb") as s, open(live, "wb") as t:
                t.write(s.read())
            r = subprocess.run(["lake", "build", f"Autoform.Generated.{m}"],
                               cwd=ROOT, capture_output=True, text=True, timeout=7200)
            if r.returncode != 0:
                tail = (r.stdout + r.stderr).strip().splitlines()[-15:]
                return ("MISMATCH",
                        "the render of the AST does not type-check.\n" +
                        "\n".join("      " + l for l in tail))
            notes.append("render type-checks (lake build)")

        return ("OK", f"{rh[:12]} ({', '.join(notes)})")


def record(ms: list[str], man: dict) -> int:
    bad = 0
    for m in ms:
        entry = man["modules"].setdefault(m, {})
        ast = ast_path(m, entry)
        if ast is None:
            print(f"RECORD-FAILED {m}: no AST found", file=sys.stderr)
            bad = 1
            continue
        with tempfile.TemporaryDirectory(prefix="autoform_render_") as d:
            fresh = os.path.join(d, f"{m}.lean")
            err = render(ast, m, fresh)
            if err:
                print(f"RECORD-FAILED {m}: {err}", file=sys.stderr)
                bad = 1
                continue
            tracked = os.path.exists(os.path.join(ROOT, f"ast-{m}.json"))
            entry.update({
                "ast_tracked": tracked,
                "ast_bytes": os.path.getsize(ast),
                "ast_sha256": sha256(ast),
                "render_bytes": os.path.getsize(fresh),
                "render_sha256": sha256(fresh),
            })
            if not tracked:
                entry.setdefault("ast_hint", ast)
                entry.setdefault(
                    "provenance",
                    "AST too large to track; re-export with cartographer/export_ast.sc "
                    "from the corpus CPG.")
            print(f"recorded {m}: ast {entry['ast_sha256'][:12]} "
                  f"render {entry['render_sha256'][:12]} ({entry['render_bytes']} B)")
    man["policy"] = ("The AST is the tracked source of truth; Autoform/Generated/*.lean is a "
                     "build product and is not tracked. See docs/integrity.md. Hashes here "
                     "pin the identity of both halves; scripts/check_render.py verifies them.")
    with open(MANIFEST, "w") as f:
        json.dump(man, f, indent=2, sort_keys=True)
        f.write("\n")
    return bad


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("modules", nargs="*")
    ap.add_argument("--typecheck", action="store_true",
                    help="materialise the render and lake build it")
    ap.add_argument("--record", action="store_true",
                    help="re-record AST and render hashes (do this only after review)")
    ap.add_argument("--strict", action="store_true",
                    help="ignore the untracked_by_policy allowlist: an absent AST is "
                         "UNVERIFIABLE whatever the policy says")
    args = ap.parse_args()

    man = load_manifest()
    known = sorted(set(man["modules"]) |
                   {fn[4:-5] for fn in os.listdir(ROOT)
                    if fn.startswith("ast-") and fn.endswith(".json")})
    ms = args.modules or known
    if not ms:
        print("check_render: no module has an AST and artifact-manifest.json is empty. "
              "Nothing was checked -- this is a failure, not a pass.", file=sys.stderr)
        return 2

    if args.record:
        return record(ms, man)

    results = []
    for m in ms:
        entry = man["modules"].get(m)
        if entry is None:
            results.append((m, "UNVERIFIABLE",
                            f"artifact-manifest.json has no entry for {m}, so there is no "
                            f"recorded hash to check it against. If ast-{m}.json is real "
                            f"and reviewed, run: scripts/check_render.py --record {m}"))
            continue
        v, d = check(m, entry, args.typecheck, man, args.strict)
        results.append((m, v, d))

    for m, v, d in results:
        stream = sys.stdout if v == "OK" else sys.stderr
        print(f"{v} {m}: {d}", file=stream)

    ok = sum(1 for _, v, _ in results if v == "OK")
    mism = sum(1 for _, v, _ in results if v == "MISMATCH")
    unv = sum(1 for _, v, _ in results if v == "UNVERIFIABLE")
    nt = [m for m, v, _ in results if v == "NOT-TRACKED"]
    ntmsg = (f", {len(nt)} NOT checked (untracked by reviewed policy: {', '.join(nt)})"
             if nt else "")
    print(f"\ncheck_render: {ok} verified, {mism} mismatched, {unv} unverifiable"
          f"{ntmsg} (of {len(results)})", file=sys.stderr if mism or unv else sys.stdout)
    if mism:
        return 1
    if ok == 0:
        return 2
    if unv:
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())
