#!/usr/bin/env python3
"""FVSpec evaluation harness — the anti-vacuity gate over the FVSpec benchmark.

STRATEGY.md §11: FVSpec (GaloisInc/fvspec) is 9,415 Lean 4 verification challenges
derived from 2,772 real-world Python property-based tests across 333 repos. The specs
were produced by a three-agent LLM pipeline and were **never mutation-validated**.

Two uses, per the plan:
  (a) it is the evaluation set for our Specifier;
  (b) running *our* anti-vacuity gate across all 9,415 specs is a genuine contribution
      back to the benchmark. This script is (b).

The gate is the static, source-level analogue of `Autoform/Harness/Audit.lean`:

  * dependency-vacuity   — `#audit_depends`. A theorem whose statement never mentions
                           the implementation cannot constrain the implementation.
                           Sound *necessary* condition for non-vacuity, cheap to check.
  * opaque-subject       — the Lean analogue of `#audit_axioms`' `sorryAx` finding at
                           the *statement* level: if the symbols under test are declared
                           `axiom` (or the impl body is `sorry`), the theorem is about
                           an uninterpreted constant, so proving it says nothing about
                           any program.
  * trivial truth        — conclusion is syntactically `True`, or a reflexive instance
                           of `=` / `↔` / `≤`, i.e. provable without the subject.
  * hypothesis satisfiability — premises that are syntactically unsatisfiable (`False`,
                           `p` together with `¬p`, `x ≠ x`, `n < 0` at `Nat`, false
                           numeric literals) make the theorem vacuously true.
  * empty quantification — binding a variable in `Empty` / `PEmpty` / `Fin 0` / `False`,
                           or membership in a literal empty list.

HONESTY CONTRACT. This is a *static* gate on spec text. It can flag; it cannot certify.
Nothing here is ever reported as "passed" or "verified" — a spec that survives every
check is reported as `clean_static`, meaning only "none of the checks that actually ran
fired on it". Every record carries `checks_run`, and the report carries an explicit
`not_checked` list naming the semantic checks (Plausible refutation, mutation gate,
real elaboration) that this script does not perform. Specs the parser could not handle
are reported `not_analyzed`, never lumped in with the clean ones.

Usage:
    scripts/fvspec.py [--path DIR_OR_JSONL] [--limit N] [--out fvspec-report.json]
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable, Iterator

# --------------------------------------------------------------------------------------
# Acquisition
# --------------------------------------------------------------------------------------

GITHUB_REPO = "https://github.com/GaloisInc/fvspec"
# NOTE (measured, not assumed): the GitHub repo contains the *generation pipeline*, the
# leaderboard and the baselines — it does NOT contain the 9,415 formalizations. Those
# live only in the Hugging Face dataset `GaloisInc/fvspec-fv` (one JSONL, `train.jsonl`,
# ~235 MB, 9,415 rows). `GaloisInc/fvspec-pbt` is the *upstream* Python-PBT corpus, not
# the Lean benchmark. So HF is the real source and the clone is a fallback/locator.
HF_DATASET = "GaloisInc/fvspec-fv"
HF_FILE = "train.jsonl"
HF_URL = f"https://huggingface.co/datasets/{HF_DATASET}/resolve/main/{HF_FILE}"

FETCH_HELP = f"""\
Could not obtain the FVSpec benchmark.

The 9,415 Lean formalizations live in the Hugging Face dataset `{HF_DATASET}`
(file `{HF_FILE}`). The GitHub repo {GITHUB_REPO} holds the generation
pipeline, not the formalizations.

To run this harness offline, obtain the data on a networked machine by ONE of:

  1. curl -L -o train.jsonl \\
       {HF_URL}

  2. python3 -c "from datasets import load_dataset; \\
       load_dataset('{HF_DATASET}', split='train').to_json('train.jsonl')"

  3. git clone https://huggingface.co/datasets/{HF_DATASET}

then re-run:  scripts/fvspec.py --path /path/to/train.jsonl

No data is fabricated when the fetch fails; the run aborts instead."""


def _looks_like_dataset(p: Path) -> bool:
    return p.is_file() and p.suffix in (".jsonl", ".json", ".ndjson")


def locate_local(path: Path) -> Path:
    """Resolve a user-supplied --path to a JSONL of benchmark rows."""
    if _looks_like_dataset(path):
        return path
    if path.is_dir():
        # Prefer an obvious train split, then any jsonl under the tree.
        for cand in (path / HF_FILE, path / "data" / HF_FILE):
            if cand.is_file():
                return cand
        hits = sorted(
            (p for p in path.rglob("*.jsonl") if ".git" not in p.parts),
            key=lambda p: -p.stat().st_size,
        )
        if hits:
            return hits[0]
    raise SystemExit(
        f"--path {path} contains no benchmark JSONL.\n\n{FETCH_HELP}"
    )


def try_clone(dest: Path) -> Path | None:
    """git clone --depth 1 the FVSpec repo. Returns the clone dir, or None."""
    if dest.exists() and any(dest.iterdir()):
        return dest
    dest.parent.mkdir(parents=True, exist_ok=True)
    try:
        r = subprocess.run(
            ["git", "clone", "--depth", "1", GITHUB_REPO, str(dest)],
            capture_output=True,
            text=True,
            timeout=600,
        )
    except (OSError, subprocess.TimeoutExpired) as e:
        print(f"[fetch] git clone failed: {e}", file=sys.stderr)
        return None
    if r.returncode != 0:
        print(f"[fetch] git clone failed: {r.stderr.strip()[:400]}", file=sys.stderr)
        return None
    return dest


def try_huggingface(cache: Path) -> Path | None:
    """Download the fvspec-fv JSONL. Returns the local path, or None."""
    cache.mkdir(parents=True, exist_ok=True)
    target = cache / HF_FILE
    if target.is_file() and target.stat().st_size > 1_000_000:
        print(f"[fetch] using cached {target}", file=sys.stderr)
        return target
    tmp = target.with_suffix(".partial")
    print(f"[fetch] downloading {HF_URL}", file=sys.stderr)
    if shutil.which("curl"):
        r = subprocess.run(
            ["curl", "-sSL", "--fail", "-o", str(tmp), HF_URL],
            capture_output=True,
            text=True,
            timeout=1800,
        )
        ok = r.returncode == 0
        if not ok:
            print(f"[fetch] curl failed: {r.stderr.strip()[:300]}", file=sys.stderr)
    else:
        import urllib.request

        try:
            urllib.request.urlretrieve(HF_URL, tmp)  # noqa: S310
            ok = True
        except Exception as e:  # pragma: no cover - network dependent
            print(f"[fetch] urllib failed: {e}", file=sys.stderr)
            ok = False
    if not ok or not tmp.exists() or tmp.stat().st_size < 1_000_000:
        tmp.unlink(missing_ok=True)
        return None
    tmp.rename(target)
    return target


def acquire(path: Path | None, cache: Path) -> tuple[Path, str]:
    """Locate the benchmark. Returns (jsonl path, provenance string)."""
    if path is not None:
        return locate_local(path), f"local:{path}"

    clone = try_clone(cache / "fvspec")
    if clone is not None:
        hits = sorted(
            (p for p in clone.rglob("*.jsonl") if ".git" not in p.parts),
            key=lambda p: -p.stat().st_size,
        )
        big = [p for p in hits if p.stat().st_size > 5_000_000]
        if big:
            return big[0], f"github-clone:{big[0]}"
        print(
            "[fetch] clone succeeded but carries no formalization JSONL "
            "(the repo ships the pipeline, not the data); falling back to HF",
            file=sys.stderr,
        )

    hf = try_huggingface(cache / "hf")
    if hf is not None:
        return hf, f"huggingface:{HF_DATASET}/{HF_FILE}"

    raise SystemExit(FETCH_HELP)


# --------------------------------------------------------------------------------------
# Normalized problem form
# --------------------------------------------------------------------------------------


@dataclass
class Problem:
    problem_id: str
    repo: str
    repo_url: str
    spec: str
    impl: str
    python: str
    pbt_name: str
    is_canonical: bool
    num_theorems_declared: int
    impl_autoform_success: float | None
    implementation_level: str
    # dataset's own self-report, used only as a cross-check of our gate
    claims_invokes_impl: bool | None


def _repo_of(row: dict) -> tuple[str, str]:
    r = row.get("pbt_repo") or {}
    if isinstance(r, dict):
        return str(r.get("name") or "?"), str(r.get("url") or "")
    return str(r), ""


def read_problems(jsonl: Path, limit: int | None) -> Iterator[Problem]:
    n = 0
    with jsonl.open("r", encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            line = line.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as e:
                print(f"[parse] line {lineno}: bad JSON ({e}); skipped", file=sys.stderr)
                continue
            spec = row.get("spec") or row.get("Spec.lean") or ""
            impl = row.get("impl") or row.get("Impl.lean") or ""
            if not spec:
                continue
            name, url = _repo_of(row)
            yield Problem(
                problem_id=str(row.get("sample_id", row.get("id", f"line{lineno}"))),
                repo=name,
                repo_url=url,
                spec=spec,
                impl=impl,
                python=row.get("pbt_code") or "",
                pbt_name=row.get("pbt_sample_name") or "",
                is_canonical=bool(row.get("is_canonical", False)),
                num_theorems_declared=int(row.get("num_theorems") or 0),
                impl_autoform_success=row.get("impl_autoform_success"),
                implementation_level=str(row.get("implementation_level") or ""),
                claims_invokes_impl=row.get("actually_invokes_given"),
            )
            n += 1
            if limit is not None and n >= limit:
                return


# --------------------------------------------------------------------------------------
# A very small Lean surface-syntax reader
#
# This is deliberately *not* a Lean parser. It reads declaration headers and splits a
# theorem into binders / hypotheses / conclusion well enough to run syntactic checks.
# Anything it cannot split is reported `not_analyzed` rather than assumed fine.
# --------------------------------------------------------------------------------------

OPEN = "([{⟨⦃"
CLOSE = ")]}⟩⦄"

DECL_START = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|nonrec\s+)*"
    r"(theorem|lemma|example|def|abbrev|axiom|opaque|instance|structure|inductive|"
    r"class|deriving|namespace|end|open|import|section|variable|#\w+|--|/-)\b",
)

NAMED_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|nonrec\s+)*"
    r"(theorem|lemma|def|abbrev|axiom|opaque|instance|structure|inductive|class)\s+"
    r"([A-Za-z_α-ω][A-Za-z0-9_'!?.₀-₉α-ω]*)",
)

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'.!?₀-₉]*")

PROOF_SEP = re.compile(r":=\s*(?:by\b|sorry\b|\bsorry\b)")


def strip_comments(text: str) -> str:
    """Remove `--` line comments and `/- -/` block comments (nesting-aware)."""
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return "".join(out)


def split_decls(text: str) -> list[tuple[str, str, str]]:
    """Split Lean source into (keyword, name, body) triples, one per top-level decl."""
    lines = text.split("\n")
    starts: list[int] = [i for i, ln in enumerate(lines) if DECL_START.match(ln)]
    decls: list[tuple[str, str, str]] = []
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else len(lines)
        chunk = "\n".join(lines[s:e])
        m = NAMED_DECL.match(chunk)
        if m:
            decls.append((m.group(1), m.group(2), chunk))
    return decls


def split_top(text: str, marker: str) -> tuple[str, str] | None:
    """Split at the first occurrence of `marker` at bracket depth 0 (not part of `:=`)."""
    depth = 0
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0 and text.startswith(marker, i):
            if marker == ":" and text.startswith(":=", i):
                i += 2
                continue
            if marker == ":" and i and text[i - 1] == ":":
                i += 1
                continue
            return text[:i], text[i + len(marker):]
        i += 1
    return None


def split_all_top(text: str, marker: str) -> list[str]:
    """Split on every depth-0 occurrence of `marker`."""
    parts, buf, depth = [], [], 0
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        if depth == 0 and text.startswith(marker, i):
            parts.append("".join(buf))
            buf = []
            i += len(marker)
            continue
        buf.append(c)
        i += 1
    parts.append("".join(buf))
    return parts


def strip_proof(body: str) -> tuple[str, bool]:
    """Drop the proof term. Returns (statement-with-header, has_sorry)."""
    has_sorry = re.search(r"\bsorry\b", body) is not None
    # The proof separator is the LAST `:= by` / `:= sorry`; earlier `:=` belong to `let`.
    last = None
    for m in PROOF_SEP.finditer(body):
        last = m
    if last is not None:
        return body[: last.start()], has_sorry
    cut = split_top(body, ":=")
    if cut is not None:
        return cut[0], has_sorry
    return body, has_sorry


BINDER_RE = re.compile(r"[(\[{⦃]")


def parse_binders(head: str) -> tuple[list[tuple[str, str]], str]:
    """Parse a theorem header `name (a : T) {b : U} : Stmt` into ([(names, type)], stmt)."""
    m = NAMED_DECL.match(head)
    rest = head[m.end():] if m else head
    sep = split_top(rest, ":")
    if sep is None:
        return [], ""
    binder_text, stmt = sep
    binders: list[tuple[str, str]] = []
    i, n = 0, len(binder_text)
    while i < n:
        c = binder_text[i]
        if c in OPEN:
            depth, j = 0, i
            while j < n:
                if binder_text[j] in OPEN:
                    depth += 1
                elif binder_text[j] in CLOSE:
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            inner = binder_text[i + 1 : j]
            bs = split_top(inner, ":")
            if bs:
                binders.append((bs[0].strip(), bs[1].strip()))
            else:
                binders.append(("", inner.strip()))
            i = j + 1
        else:
            i += 1
    return binders, stmt.strip()


FORALL_RE = re.compile(r"^\s*[∀Π]")


def peel_quantifiers(stmt: str) -> tuple[list[tuple[str, str]], str]:
    """Peel leading `∀ (x : T) ..., body`, returning extra binders and the body."""
    binders: list[tuple[str, str]] = []
    s = stmt.strip()
    guard = 0
    while FORALL_RE.match(s) and guard < 16:
        guard += 1
        cut = split_top(s, ",")
        if cut is None:
            break
        head, s = cut[0], cut[1].strip()
        head = head.lstrip("∀Π ").strip()
        bs, _ = parse_binders("theorem _ " + head + " : dummy")
        if bs:
            binders.extend(bs)
        else:
            inner = split_top(head, ":")
            if inner:
                binders.append((inner[0].strip(), inner[1].strip()))
            else:
                binders.append((head, ""))
    return binders, s


def peel_lets(body: str) -> str:
    """Drop `let x := e` prefixes / lines so the real conclusion is visible."""
    lines = [ln for ln in body.split("\n")]
    kept = []
    for ln in lines:
        t = ln.strip()
        if t.startswith("let ") or re.match(r"^have\s+\w+\s*:", t):
            continue
        kept.append(ln)
    out = "\n".join(kept).strip()
    out = re.sub(r"^;\s*", "", out)
    return out or body.strip()


def split_arrows(body: str) -> tuple[list[str], str]:
    """Split `A → B → C` into ([A, B], C) at depth 0."""
    parts = [p.strip() for p in split_all_top(body, "→") if p.strip()]
    if len(parts) <= 1:
        return [], body.strip()
    return parts[:-1], parts[-1]


# --------------------------------------------------------------------------------------
# The anti-vacuity gate
# --------------------------------------------------------------------------------------

EMPTY_TYPES = {"Empty", "PEmpty", "False", "Fin 0"}
NORM = re.compile(r"\s+")

TRIVIAL_TRUE = {"True", "trivial", "True.intro"}

REL_REFL = ["↔", "=", "≤", "≥", "⊆", "⊇", "≡"]

CHECKS_RUN = [
    "dependency_vacuity",
    "opaque_subject",
    "trivial_conclusion",
    "reflexive_conclusion",
    "unsatisfiable_hypotheses",
    "empty_quantification",
    "no_sorry_obligation",
]

CHECKS_NOT_RUN = [
    "lean_elaboration (statements are not type-checked here)",
    "plausible_refutation (semantic counterexample search — needs Lean + Plausible)",
    "mutation_gate (scripts/mutate.py equivalent — needs a compiling Lean project)",
    "axiom_basis_of_proofs (#audit_axioms — needs elaborated proof terms)",
    "semantic_hypothesis_satisfiability (SMT/decision procedure; only syntactic "
    "unsatisfiability is detected)",
]


def norm(s: str) -> str:
    return NORM.sub(" ", s).strip().strip("()").strip()


def collect_defined_names(impl: str) -> set[str]:
    names: set[str] = set()
    for kw, name, _ in split_decls(strip_comments(impl)):
        if kw in ("def", "abbrev", "opaque", "instance", "structure", "inductive", "class"):
            names.add(name.split(".")[-1])
            names.add(name)
    return names


def collect_stub_names(impl: str) -> set[str]:
    """impl-side names that are `axiom`, or whose body is `sorry` — opaque subjects."""
    stubs: set[str] = set()
    for kw, name, body in split_decls(strip_comments(impl)):
        if kw in ("axiom", "opaque"):
            stubs.add(name.split(".")[-1])
        elif kw in ("def", "abbrev") and re.search(r"\bsorry\b", body):
            stubs.add(name.split(".")[-1])
    return stubs


def idents(text: str) -> set[str]:
    out = set()
    for m in IDENT.finditer(text):
        tok = m.group(0)
        out.add(tok)
        out.add(tok.split(".")[-1])
    return out


NUM_EQ = re.compile(r"^\s*(\d+)\s*=\s*(\d+)\s*$")
NUM_NEQ = re.compile(r"^\s*(\d+)\s*≠\s*(\d+)\s*$")


def hypothesis_unsat(hyps: list[str], binder_types: dict[str, str]) -> list[str]:
    """Syntactically unsatisfiable premises -> the theorem is vacuously true."""
    found: list[str] = []
    seen = [norm(h) for h in hyps]
    for h in seen:
        if h in ("False", "False.elim"):
            found.append(f"premise is `False`: `{h}`")
        m = NUM_EQ.match(h)
        if m and m.group(1) != m.group(2):
            found.append(f"premise is a false numeric equality: `{h}`")
        m = NUM_NEQ.match(h)
        if m and m.group(1) == m.group(2):
            found.append(f"premise is a false numeric disequality: `{h}`")
        ne = split_top(h, "≠")
        if ne and norm(ne[0]) and norm(ne[0]) == norm(ne[1]):
            found.append(f"premise asserts `x ≠ x`: `{h}`")
        m = re.match(r"^\s*(\w+)\s*<\s*0\s*$", h)
        if m and binder_types.get(m.group(1), "").strip() in ("Nat", "ℕ"):
            found.append(f"premise `{h}` is unsatisfiable at `Nat`")
        m = re.match(r"^\s*(\w+)\s*≠\s*\1\b", h)
        if m:
            found.append(f"premise is irreflexive-on-itself: `{h}`")
    # p together with ¬p
    positives = {h for h in seen if not h.startswith("¬")}
    for h in seen:
        if h.startswith("¬"):
            inner = norm(h[1:])
            if inner in positives:
                found.append(f"premises contain both `{inner}` and `¬{inner}`")
    # x < c and c' < x with c' >= c on literals
    lows: dict[str, int] = {}
    highs: dict[str, int] = {}
    for h in seen:
        m = re.match(r"^\s*(\w+)\s*<\s*(\d+)\s*$", h)
        if m:
            highs[m.group(1)] = min(highs.get(m.group(1), 10**9), int(m.group(2)))
        m = re.match(r"^\s*(\d+)\s*<\s*(\w+)\s*$", h)
        if m:
            lows[m.group(2)] = max(lows.get(m.group(2), -(10**9)), int(m.group(1)))
    for v in set(lows) & set(highs):
        if lows[v] + 1 >= highs[v]:
            found.append(f"premises bound `{v}` to an empty range ({lows[v]} < {v} < {highs[v]})")
    return found


def empty_quantification(binders: list[tuple[str, str]], hyps: list[str]) -> list[str]:
    found: list[str] = []
    for names, ty in binders:
        t = norm(ty)
        if t in EMPTY_TYPES or re.match(r"^Fin\s+0$", t):
            found.append(f"binder `{names} : {t}` quantifies over an empty type")
    for h in hyps:
        hh = norm(h)
        if re.search(r"∈\s*\[\s*\]", hh) or re.search(r"∈\s*\(\s*\[\s*\]", hh):
            found.append(f"premise is membership in an empty list: `{hh}`")
        if re.match(r"^\s*\[\s*\]\s*≠\s*\[\s*\]\s*$", hh):
            found.append(f"premise is `[] ≠ []`: `{hh}`")
    return found


def trivial_conclusion(concl: str) -> list[str]:
    found: list[str] = []
    c = norm(concl)
    if c in TRIVIAL_TRUE:
        found.append("conclusion is syntactically `True`")
        return found
    if re.match(r"^True\b", c) and len(c) <= 8:
        found.append("conclusion is syntactically `True`")
    return found


def reflexive_conclusion(concl: str) -> list[str]:
    c = norm(concl)
    for rel in REL_REFL:
        cut = split_top(c, rel)
        if cut is None:
            continue
        lhs, rhs = norm(cut[0]), norm(cut[1])
        if lhs and lhs == rhs:
            return [f"conclusion is a reflexive instance of `{rel}` (`{lhs} {rel} {rhs}`)"]
        break
    return []


@dataclass
class TheoremVerdict:
    name: str
    analyzed: bool = False
    reason_not_analyzed: str = ""
    has_sorry: bool = False
    mentions_impl: bool = False
    impl_names_used: list[str] = field(default_factory=list)
    findings: list[dict] = field(default_factory=list)

    @property
    def flagged(self) -> bool:
        return bool(self.findings)

    def to_json(self) -> dict:
        return {
            "name": self.name,
            "analyzed": self.analyzed,
            "reason_not_analyzed": self.reason_not_analyzed or None,
            "has_sorry_obligation": self.has_sorry,
            "mentions_impl": self.mentions_impl,
            "impl_names_used": sorted(self.impl_names_used)[:12],
            "status": (
                "not_analyzed"
                if not self.analyzed
                else ("flagged" if self.findings else "clean_static")
            ),
            "findings": self.findings,
        }


def analyze_theorem(
    name: str,
    body: str,
    impl_names: set[str],
    impl_stubs: set[str],
    spec_axioms: set[str],
) -> TheoremVerdict:
    v = TheoremVerdict(name=name)
    stmt_src, has_sorry = strip_proof(body)
    v.has_sorry = has_sorry

    binders, stmt = parse_binders(stmt_src)
    if not stmt.strip():
        v.analyzed = False
        v.reason_not_analyzed = "could not split header from statement"
        return v
    v.analyzed = True

    qbinders, qbody = peel_quantifiers(stmt)
    binders = binders + qbinders
    qbody = peel_lets(qbody)
    arrow_hyps, concl = split_arrows(qbody)

    binder_types = {}
    hyps: list[str] = []
    for names, ty in binders:
        for nm in names.split():
            binder_types[nm] = ty
        t = norm(ty)
        if t and (
            re.search(r"[=<>≤≥∈≠∧∨¬↔]", t) or t in ("True", "False") or t.startswith("¬")
        ):
            hyps.append(ty)
    hyps.extend(arrow_hyps)

    # --- dependency vacuity (#audit_depends, statically) ------------------------------
    used = idents(stmt)
    hit = sorted(used & impl_names)
    v.impl_names_used = hit
    v.mentions_impl = bool(hit)
    if impl_names and not hit:
        v.findings.append(
            {
                "check": "dependency_vacuity",
                "severity": "high",
                "detail": (
                    "statement never mentions any name defined in Impl.lean; "
                    "it cannot constrain the implementation under test"
                ),
            }
        )

    # --- opaque subject (statement is about uninterpreted constants) -------------------
    ax_hit = sorted(used & spec_axioms)
    stub_hit = sorted(used & impl_stubs)
    if ax_hit and not hit:
        v.findings.append(
            {
                "check": "opaque_subject",
                "severity": "high",
                "detail": (
                    "the symbols under test are declared `axiom` inside the spec itself "
                    f"({', '.join(ax_hit[:6])}); proving the theorem constrains no program"
                ),
            }
        )
    elif stub_hit:
        v.findings.append(
            {
                "check": "opaque_subject",
                "severity": "medium",
                "detail": (
                    "statement is about implementation names that are `axiom`/`sorry` "
                    f"stubs in Impl.lean ({', '.join(stub_hit[:6])})"
                ),
            }
        )

    # --- trivial truth ----------------------------------------------------------------
    for d in trivial_conclusion(concl):
        v.findings.append({"check": "trivial_conclusion", "severity": "high", "detail": d})
    for d in reflexive_conclusion(concl):
        v.findings.append({"check": "reflexive_conclusion", "severity": "high", "detail": d})

    # --- hypothesis satisfiability ----------------------------------------------------
    for d in hypothesis_unsat(hyps, binder_types):
        v.findings.append(
            {"check": "unsatisfiable_hypotheses", "severity": "high", "detail": d}
        )
    for d in empty_quantification(binders, hyps):
        v.findings.append({"check": "empty_quantification", "severity": "high", "detail": d})

    # --- is there an obligation at all? -----------------------------------------------
    if not has_sorry:
        v.findings.append(
            {
                "check": "no_sorry_obligation",
                "severity": "low",
                "detail": "theorem carries no `sorry` placeholder (nothing to discharge)",
            }
        )
    return v


@dataclass
class ProblemVerdict:
    problem: Problem
    theorems: list[TheoremVerdict]
    parse_error: str = ""

    def to_json(self) -> dict:
        p = self.problem
        analyzed = [t for t in self.theorems if t.analyzed]
        flagged = [t for t in analyzed if t.flagged]
        checks = Counter(f["check"] for t in analyzed for f in t.findings)
        if self.parse_error or not self.theorems:
            status = "not_analyzed"
        elif not analyzed:
            status = "not_analyzed"
        elif flagged:
            status = "flagged"
        else:
            status = "clean_static"
        return {
            "problem_id": p.problem_id,
            "repo": p.repo,
            "repo_url": p.repo_url,
            "pbt_name": p.pbt_name,
            "is_canonical": p.is_canonical,
            "implementation_level": p.implementation_level,
            "impl_autoform_success": p.impl_autoform_success,
            "status": status,
            "parse_error": self.parse_error or None,
            "theorems_found": len(self.theorems),
            "theorems_declared_by_dataset": p.num_theorems_declared,
            "theorems_analyzed": len(analyzed),
            "theorems_flagged": len(flagged),
            "sorry_placeholders": count_sorries(p.spec),
            "has_reference_python": bool(p.python),
            "checks_fired": dict(checks),
            "dataset_claims_invokes_impl": p.claims_invokes_impl,
            "theorems": [t.to_json() for t in self.theorems],
        }


def count_sorries(spec: str) -> int:
    return len(re.findall(r"\bsorry\b", strip_comments(spec)))


def analyze_problem(p: Problem) -> ProblemVerdict:
    try:
        spec = strip_comments(p.spec)
        impl_names = collect_defined_names(p.impl)
        impl_stubs = collect_stub_names(p.impl)
        decls = split_decls(spec)
        spec_axioms = {
            n.split(".")[-1] for kw, n, _ in decls if kw in ("axiom", "opaque")
        }
        # names defined *inside* the spec also count as subjects for dep-vacuity, since
        # a spec may inline the function under test.
        spec_defs = {
            n.split(".")[-1] for kw, n, _ in decls if kw in ("def", "abbrev")
        }
        subjects = impl_names | spec_defs
        thms = [
            analyze_theorem(n, b, subjects, impl_stubs, spec_axioms)
            for kw, n, b in decls
            if kw in ("theorem", "lemma")
        ]
        if not thms:
            return ProblemVerdict(p, [], parse_error="no theorem declarations recognized")
        return ProblemVerdict(p, thms)
    except Exception as e:  # never let one bad row abort a 9k-row run
        return ProblemVerdict(p, [], parse_error=f"analyzer exception: {type(e).__name__}: {e}")


# --------------------------------------------------------------------------------------
# Aggregation & reporting
# --------------------------------------------------------------------------------------


def aggregate(verdicts: Iterable[dict]) -> dict:
    agg = {
        "problems_seen": 0,
        "problems_analyzed": 0,
        "problems_not_analyzed": 0,
        "problems_flagged": 0,
        "problems_clean_static": 0,
        "theorems_seen": 0,
        "theorems_analyzed": 0,
        "theorems_not_analyzed": 0,
        "theorems_flagged": 0,
        "sorry_placeholders": 0,
        "checks_fired": Counter(),
        "theorem_checks_fired": Counter(),
        "flagged_by_repo": Counter(),
        "problems_by_repo": Counter(),
        "canonical_problems": 0,
        "canonical_flagged": 0,
        "dataset_invokes_agreement": Counter(),
    }
    for v in verdicts:
        agg["problems_seen"] += 1
        agg["problems_by_repo"][v["repo"]] += 1
        agg["sorry_placeholders"] += v["sorry_placeholders"]
        agg["theorems_seen"] += v["theorems_found"]
        agg["theorems_analyzed"] += v["theorems_analyzed"]
        agg["theorems_not_analyzed"] += v["theorems_found"] - v["theorems_analyzed"]
        agg["theorems_flagged"] += v["theorems_flagged"]
        if v["is_canonical"]:
            agg["canonical_problems"] += 1
        if v["status"] == "not_analyzed":
            agg["problems_not_analyzed"] += 1
            continue
        agg["problems_analyzed"] += 1
        for k, n in v["checks_fired"].items():
            agg["theorem_checks_fired"][k] += n
            agg["checks_fired"][k] += 1
        if v["status"] == "flagged":
            agg["problems_flagged"] += 1
            agg["flagged_by_repo"][v["repo"]] += 1
            if v["is_canonical"]:
                agg["canonical_flagged"] += 1
        else:
            agg["problems_clean_static"] += 1
        claim = v["dataset_claims_invokes_impl"]
        if claim is not None:
            ours = not any(
                t["analyzed"] and not t["mentions_impl"] for t in v["theorems"]
            )
            agg["dataset_invokes_agreement"][f"dataset={claim},gate={ours}"] += 1
    for k in ("checks_fired", "theorem_checks_fired", "dataset_invokes_agreement"):
        agg[k] = dict(agg[k])
    agg["flagged_by_repo"] = dict(Counter(agg["flagged_by_repo"]).most_common(25))
    agg["problems_by_repo"] = {"distinct_repos": len(agg["problems_by_repo"])}
    return agg


def pct(a: int, b: int) -> str:
    return f"{100.0 * a / b:.1f}%" if b else "n/a"


def render_summary(report: dict) -> str:
    a = report["aggregate"]
    src = report["source"]
    L = []
    L.append("=" * 78)
    L.append("FVSpec anti-vacuity gate — static screen over LLM-generated Lean specs")
    L.append("=" * 78)
    L.append(f"source        : {src['provenance']}")
    L.append(f"dataset file  : {src['file']}  ({src['rows_in_file']} rows)")
    L.append(f"limit         : {src['limit'] if src['limit'] is not None else 'none (full run)'}")
    L.append("")
    L.append("-- coverage (what was actually looked at) ------------------------------")
    L.append(f"problems read              : {a['problems_seen']}")
    L.append(f"  analyzed                 : {a['problems_analyzed']} ({pct(a['problems_analyzed'], a['problems_seen'])})")
    L.append(f"  NOT analyzed             : {a['problems_not_analyzed']}  <- not 'passed'")
    L.append(f"theorems found             : {a['theorems_seen']}")
    L.append(f"  analyzed                 : {a['theorems_analyzed']}")
    L.append(f"  NOT analyzed             : {a['theorems_not_analyzed']}  <- not 'passed'")
    L.append(f"sorry placeholders         : {a['sorry_placeholders']}")
    L.append(f"distinct source repos      : {a['problems_by_repo']['distinct_repos']}")
    L.append("")
    L.append("-- verdicts ------------------------------------------------------------")
    L.append(
        f"problems flagged           : {a['problems_flagged']} "
        f"({pct(a['problems_flagged'], a['problems_analyzed'])} of analyzed)"
    )
    L.append(
        f"problems clean (static)    : {a['problems_clean_static']} "
        f"({pct(a['problems_clean_static'], a['problems_analyzed'])} of analyzed)"
    )
    L.append(
        f"theorems flagged           : {a['theorems_flagged']} "
        f"({pct(a['theorems_flagged'], a['theorems_analyzed'])} of analyzed)"
    )
    L.append(
        f"canonical problems flagged : {a['canonical_flagged']} of {a['canonical_problems']} "
        f"({pct(a['canonical_flagged'], a['canonical_problems'])})"
    )
    L.append("")
    L.append("-- findings by check (problems / theorems) -----------------------------")
    for k in sorted(a["theorem_checks_fired"], key=lambda k: -a["theorem_checks_fired"][k]):
        L.append(
            f"  {k:<28} {a['checks_fired'].get(k, 0):>6} problems  "
            f"{a['theorem_checks_fired'][k]:>7} theorems"
        )
    if a["dataset_invokes_agreement"]:
        L.append("")
        L.append("-- cross-check vs dataset's own `actually_invokes_given` ---------------")
        for k, n in sorted(a["dataset_invokes_agreement"].items()):
            L.append(f"  {k:<40} {n}")
    L.append("")
    L.append("-- most-flagged source repos ------------------------------------------")
    for r, n in list(a["flagged_by_repo"].items())[:10]:
        L.append(f"  {n:>5}  {r}")
    L.append("")
    L.append("-- honesty: what this run did NOT check --------------------------------")
    for c in report["not_checked"]:
        L.append(f"  - {c}")
    L.append("")
    L.append(
        "A `clean_static` verdict means only that none of the checks that ran fired.\n"
        "It is NOT a proof of non-vacuity; the sufficient test is the mutation /\n"
        "Plausible-refutation gate, which requires elaborating the specs in Lean."
    )
    L.append("=" * 78)
    return "\n".join(L)


# --------------------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------------------


def default_cache() -> Path:
    env = os.environ.get("FVSPEC_CACHE")
    if env:
        return Path(env)
    return Path(tempfile.gettempdir()) / "fvspec-cache"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        prog="fvspec.py",
        description="Run the Autoform anti-vacuity gate over the FVSpec benchmark.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=FETCH_HELP,
    )
    ap.add_argument(
        "--path",
        type=Path,
        default=None,
        help="local FVSpec checkout, data dir, or train.jsonl (skips all network access)",
    )
    ap.add_argument("--limit", type=int, default=None, help="analyze at most N problems")
    ap.add_argument(
        "--out", type=Path, default=Path("fvspec-report.json"), help="JSON report path"
    )
    ap.add_argument(
        "--cache",
        type=Path,
        default=default_cache(),
        help="scratch dir for the clone/download (never the project dir)",
    )
    ap.add_argument(
        "--canonical-only",
        action="store_true",
        help="only the one canonical formalization per source PBT (2,772 of 9,415)",
    )
    ap.add_argument(
        "--per-theorem",
        action="store_true",
        help="include full per-theorem detail in the JSON (large)",
    )
    ap.add_argument("--quiet", action="store_true", help="suppress the readable summary")
    args = ap.parse_args(argv)

    jsonl, provenance = acquire(args.path, args.cache)
    rows_in_file = sum(1 for _ in jsonl.open("r", encoding="utf-8", errors="replace"))
    print(f"[fvspec] source: {provenance} ({rows_in_file} rows)", file=sys.stderr)

    problems: list[Problem] = []
    for p in read_problems(jsonl, None if args.canonical_only else args.limit):
        if args.canonical_only and not p.is_canonical:
            continue
        problems.append(p)
        if args.limit is not None and len(problems) >= args.limit:
            break

    verdicts = []
    for i, p in enumerate(problems, 1):
        verdicts.append(analyze_problem(p).to_json())
        if not args.quiet and i % 1000 == 0:
            print(f"[fvspec] analyzed {i}/{len(problems)}", file=sys.stderr)

    slim = []
    for v in verdicts:
        v2 = dict(v)
        if not args.per_theorem:
            v2["theorems"] = [
                t
                for t in v["theorems"]
                if t["status"] in ("flagged", "not_analyzed")
            ]
        slim.append(v2)

    report = {
        "tool": "autoform/scripts/fvspec.py",
        "gate": "anti-vacuity (static, source-level analogue of Autoform/Harness/Audit.lean)",
        "source": {
            "provenance": provenance,
            "file": str(jsonl),
            "rows_in_file": rows_in_file,
            "limit": args.limit,
            "canonical_only": args.canonical_only,
            "problems_analyzed_here": len(problems),
        },
        "checks_run": CHECKS_RUN,
        "not_checked": CHECKS_NOT_RUN,
        "verdict_semantics": {
            "flagged": "at least one anti-vacuity check fired on at least one theorem",
            "clean_static": "no check that ran fired; NOT a certificate of non-vacuity",
            "not_analyzed": "the parser could not handle this spec; no claim is made",
        },
        "aggregate": aggregate(verdicts),
        "problems": slim,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2), encoding="utf-8")

    summary = render_summary(report)
    if not args.quiet:
        print(summary)
    print(f"[fvspec] wrote {args.out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
