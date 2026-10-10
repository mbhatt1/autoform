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
import deep_json

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
    # Added after a tone pass found three documents quoting three different populations
    # for the same corpus (208, 238, 209) with only the third correct. Five checked
    # figures was too few: the ones that drifted were the ones nobody checked.
    ("docs/contracts.md", r"On `cachetools`, (\d+) of \d+ functions are",
     "ledger-Cachetools.json", "holeFree", int),
    ("docs/contracts.md", r"On `cachetools`, \d+ of (\d+) functions are",
     "ledger-Cachetools.json", "functions", int),
    ("docs/languages.md", r"the ledger's population \((\d+) for", 
     "ledger-Cachetools.json", "functions", int),
    # The Java corpus row (commons-lang3, 2026-10-10): the matrix row quotes the ledger,
    # the oracle figures come from the tracked run snapshot evidence-CommonsLang3.json
    # (conformance.json is a gitignored run product, as ledger-*.json is; CI regenerates
    # the ledger from the built module before running this script).
    ("docs/languages.md",
     r"\|\s*Java \(commons-lang3[^|]*\|.*?\|\s*(\d+)\s*\|\s*\d+ \(\d+%\)",
     "ledger-CommonsLang3.json", "functions", int),
    ("docs/languages.md",
     r"\|\s*Java \(commons-lang3[^|]*\|.*?\|\s*\d+\s*\|\s*(\d+) \(\d+%\)",
     "ledger-CommonsLang3.json", "holeFree", int),
    ("docs/languages.md",
     r"\|\s*Java \(commons-lang3[^|]*\|.*?\|\s*\d+\s*\|\s*\d+ \(\d+%\)\s*\|\s*(\d+) \(\d+%\)",
     "ledger-CommonsLang3.json", "verifiableCore", int),
    ("docs/languages.md", r"\*\*(\d+) functions compared, \d+/\d+ cases agree, \d+ divergences",
     "evidence-CommonsLang3.json", "compared_functions", int),
    ("docs/languages.md", r"\*\*\d+ functions compared, (\d+)/\d+ cases agree, \d+ divergences",
     "evidence-CommonsLang3.json", "agree", int),
    ("docs/languages.md", r"\*\*\d+ functions compared, \d+/(\d+) cases agree, \d+ divergences",
     "evidence-CommonsLang3.json", "total", int),
    ("docs/languages.md", r"\*\*\d+ functions compared, \d+/\d+ cases agree, (\d+) divergences",
     "evidence-CommonsLang3.json", "divergences", int),
    ("docs/languages.md", r"\*\*\d+ functions compared, \d+/\d+ cases agree, \d+ divergences,\s*(\d+) cases inconclusive",
     "evidence-CommonsLang3.json", "inconclusive", int),
    ("docs/languages.md", r"Ledger \(`ledger-CommonsLang3.json`\): (\d+) functions",
     "ledger-CommonsLang3.json", "functions", int),
    ("docs/languages.md", r"Ledger \(`ledger-CommonsLang3.json`\): \d+ functions, (\d+) hole-free",
     "ledger-CommonsLang3.json", "holeFree", int),
    ("docs/languages.md", r"Ledger \(`ledger-CommonsLang3.json`\): \d+ functions, \d+ hole-free \(\d+%\), (\d+) in the",
     "ledger-CommonsLang3.json", "verifiableCore", int),
    ("docs/languages.md", r"(\d+) holes in \d+ functions \(table above\)",
     "ledger-CommonsLang3.json", "holes", int),
]


# Cross-artifact consistency. Checking docs against artifacts is not enough: if the
# artifact is stale, the docs can match it perfectly and still be false. That happened
# immediately -- this script passed 5/5 while ledger-Cachetools.json said 238 functions
# and ast-Cachetools.json had 208, because the ledger had not been re-run after an
# exporter change. A checker that compares two things which drift together has only
# proved they drift together.
#
# No new provenance is needed to catch it: independent artifacts describing the same
# module must agree on the facts they share. Population is the sharpest one.
CROSS = [
    ("ledger-Cachetools.json", "functions", "ast-Cachetools.json", None,
     "function count"),
    ("ledger-CommonsLang3.json", "functions", "ast-CommonsLang3.json", None,
     "function count"),
    ("evidence-CommonsLang3.json", "population", "ast-CommonsLang3.json", None,
     "function count"),
]

# Figures whose artifact CI does not regenerate. A missing artifact in CHECKS is a
# failure (exit 2), which is right for artifacts CI builds: absence there means a stage
# was skipped. Django's ledger is not built by CI -- its export is a 4-minute, 6.6 GB
# Joern run -- so a row for it in CHECKS would make every CI run exit 2. These rows are
# checked exactly like CHECKS when the artifact is on disk, and when it is not the
# checker SAYS the figure is unbound, by name, instead of silently passing. That line is
# the point: a reader of the CI log sees which documented numbers nothing re-derived.
# (doc, regex with ONE capturing group, artifact, derive(json) -> value, transform)
OPTIONAL = [
    ("docs/GOAL-arbitrary-codebases.md",
     r"`ledger-Django\.json` is produced in.*?([\d,]+) functions, [\d,]+ holes under \d+ labels",
     "ledger-Django.json", lambda d: d.get("functions"), int),
    ("docs/GOAL-arbitrary-codebases.md",
     r"`ledger-Django\.json` is produced in.*?[\d,]+ functions, ([\d,]+) holes under \d+ labels",
     "ledger-Django.json", lambda d: d.get("holes"), int),
    ("docs/GOAL-arbitrary-codebases.md",
     r"`ledger-Django\.json` is produced in.*?holes under (\d+) labels",
     "ledger-Django.json", lambda d: len(d.get("holesByLabel", [])), int),
    ("docs/GOAL-arbitrary-codebases.md",
     r"`ledger-Django\.json` is produced in.*?labels, ([\d,]+) hole-free",
     "ledger-Django.json", lambda d: d.get("holeFree"), int),
    ("docs/GOAL-arbitrary-codebases.md",
     r"`ledger-Django\.json` is produced in.*?hole-free\s+\(\d+ %\), ([\d,]+) in the verifiable core",
     "ledger-Django.json", lambda d: d.get("verifiableCore"), int),
    ("docs/GOAL-arbitrary-codebases.md",
     r"The top hole labels:\s+`expr:BLOCK-prelude` (\d+),",
     "ledger-Django.json",
     lambda d: next((r["count"] for r in d.get("holesByLabel", [])
                     if r["label"] == "expr:BLOCK-prelude"), None), int),
]

# (doc, regex with one capturing group, artifact, counter) — figures quoted in prose
# rather than held in a JSON field.
COUNTED = [
    ("README.md", r"\|\s*(\d+) holes, all named\s*\|",
     "ast-Cachetools.json", "ast_hole_count", "hole count"),
    # The per-corpus spec figures are bound to the TRACKED spec modules, not to the
    # `.autoform-work/reland/<M>/specs.json` reports (gitignored: a clone cannot see them).
    # A theorem is counted by its `#audit_axioms` line, which the generator emits exactly
    # once per theorem it proved; the over-budget figure is the `budgetExcluded` list, and
    # a module with no such list has zero.
    ("README.md", r"requests 2\.32\.5 — [^;]*?, (\d+) specs",
     "Autoform/SpecsGen/Requests.lean", "specsgen_theorem_count", "requests spec count"),
    ("README.md", r"requests 2\.32\.5 — [^;]*?, \d+ specs, (\d+) over the proof budget",
     "Autoform/SpecsGen/Requests.lean", "specsgen_budget_excluded_count",
     "requests over-budget count"),
    ("README.md", r"click 8\.2\.1 — [^;]*?, (\d+) specs",
     "Autoform/SpecsGen/Click.lean", "specsgen_theorem_count", "click spec count"),
    ("README.md", r"click 8\.2\.1 — [^;]*?, \d+ specs, (\d+) over the proof budget",
     "Autoform/SpecsGen/Click.lean", "specsgen_budget_excluded_count",
     "click over-budget count"),
    ("README.md", r"jinja2 3\.1\.6 — [^;.]*?, (\d+) specs",
     "Autoform/SpecsGen/Jinja2.lean", "specsgen_theorem_count", "jinja2 spec count"),
    ("README.md", r"jinja2 3\.1\.6 — [^;.]*?, \d+ specs, (\d+) over the proof budget",
     "Autoform/SpecsGen/Jinja2.lean", "specsgen_budget_excluded_count",
     "jinja2 over-budget count"),
]


def ast_hole_count(path):
    """Holes in a neutral AST, counted from the label field the exporter emits."""
    return len(re.findall(r'"(?:label|hole)"\s*:\s*"[^"]+"', open(path).read()))


def specsgen_sources(path):
    """A spec module's text: the file itself, plus its `<Module>/` directory of parts when
    the generator split it (split-modules: `Base` and `PartN`)."""
    out = [open(path, encoding="utf-8").read()]
    part_dir = os.path.splitext(path)[0]
    if os.path.isdir(part_dir):
        for name in sorted(os.listdir(part_dir)):
            if name.endswith(".lean"):
                out.append(open(os.path.join(part_dir, name), encoding="utf-8").read())
    return "\n".join(out)


def specsgen_theorem_count(path):
    """Theorems a generated spec module proves: one `#audit_axioms` line each."""
    return len(re.findall(r'^#audit_axioms ', specsgen_sources(path), re.M))


def specsgen_budget_excluded_count(path):
    """Entries of the module's `budgetExcluded` list; 0 when the generator emitted none."""
    src = specsgen_sources(path)
    m = re.search(r'^def budgetExcluded : List \(String × String × String\) :=\n(.*?)\n\n',
                  src, re.S | re.M)
    return len(re.findall(r'\("', m.group(1))) if m else 0


def ast_function_count(path):
    d = deep_json.load(path)
    return len(d) if isinstance(d, list) else len(d.get("functions", []))


def check_cross(root):
    out = []
    for art, key, other, _, what in CROSS:
        ap_, op_ = os.path.join(root, art), os.path.join(root, other)
        absent = [n for n, q in ((art, ap_), (other, op_)) if not os.path.exists(q)]
        if absent:
            # Silence here would be the worst outcome: the cross-artifact check is the
            # only one that can catch a stale artifact, and skipping it quietly is the
            # "checker that stopped looking" failure this file warns about elsewhere.
            # It went quiet on a fresh clone because ast-*.json was gitignored while the
            # module rendered from it was tracked.
            out.append(f"cannot cross-check {what}: {', '.join(absent)} absent. "
                       f"This check is the only one that detects a stale artifact; "
                       f"treat its absence as a failure, not a pass.")
            continue
        a = json.load(open(ap_)).get(key)
        b = ast_function_count(op_)
        if a != b:
            out.append(f"{art} says {what}={a}, but {other} has {b}. One of them is "
                       f"stale -- re-run the pipeline stage that produces the older one "
                       f"BEFORE trusting any figure derived from it.")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    a = ap.parse_args()
    stale, missing = [], []
    stale.extend(check_cross(a.root))
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
    for doc, rx, art, fn, what in COUNTED:
        dp, ap_ = os.path.join(a.root, doc), os.path.join(a.root, art)
        if not (os.path.exists(dp) and os.path.exists(ap_)):
            missing.append(f"{doc} or {art}")
            continue
        want = globals()[fn](ap_)
        m = re.search(rx, open(dp).read())
        if not m:
            stale.append(f"{doc}: pattern for {what} no longer matches — the doc was "
                         f"restructured and this check stopped checking.")
        elif int(m.group(1)) != want:
            stale.append(f"{doc}: says {what}={m.group(1)}, {art} has {want}")

    unbound, bound = [], 0
    for doc, rx, art, derive, cast in OPTIONAL:
        dp, ap_ = os.path.join(a.root, doc), os.path.join(a.root, art)
        if not os.path.exists(dp):
            missing.append(doc)
            continue
        m = re.search(rx, open(dp).read(), re.S)
        if not m:
            stale.append(f"{doc}: pattern for {art} no longer matches — the doc was "
                         f"restructured and this check silently stopped checking. "
                         f"Fix the pattern, do not delete the row.")
            continue
        if not os.path.exists(ap_):
            unbound.append(f"{doc}: {m.group(1)} ({art} absent; not regenerated by CI)")
            continue
        want = derive(json.load(open(ap_)))
        got = cast(m.group(1).replace(",", ""))
        if got != want:
            stale.append(f"{doc}: says {got} for {art}, which says {want}")
        else:
            bound += 1

    for u in unbound:
        print(f"UNBOUND  {u}", file=sys.stderr)
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
    print(f"check_docs: {len(CHECKS)} documented figures all match their artifacts"
          + (f"; {bound} optional figure(s) checked" if bound else "")
          + (f"; {len(unbound)} figure(s) UNBOUND (artifact absent, see above)" if unbound else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
