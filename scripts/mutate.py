#!/usr/bin/env python3
"""Source-level mutation gate for Lean definitions (STRATEGY.md §8/§13, Tier 3).

The dependency-vacuity check (`#audit_depends`) is *necessary* but not *sufficient*:
a theorem can mention a definition and still say nothing about it. The sufficient test
is mutation, as in IronSpec (specification validation) and MutantChick (Coq): inject a
bug into the *implementation*, rebuild, and see whether the theorem still proves.

  * mutant makes the proof fail  -> the mutant is KILLED: the theorem has teeth.
  * mutant compiles unchanged    -> the mutant SURVIVED: the theorem is vacuous with
                                    respect to that bug, and must be scored a FAILURE.

Two modes:

  1. **Hand-written Lean** (the original). Theorems and definitions live in one file;
     mutate the definitions, rebuild that file.

         mutate.py Autoform/Lang/Imp/Semantics.lean Autoform.Lang.Imp.Semantics

  2. **Translated modules** (`Autoform/Generated/*.lean`). A generated module is a data
     literal and contains no theorems at all, so the file that is mutated and the file
     that is rebuilt are different, and the interesting operators are perturbations of
     the *embedded* program rather than of Lean tokens (see `gen_mutants_generated`).

         mutate.py Autoform/Generated/Cachetools.lean Autoform.Generated.Cachetools \
                   --spec-file Autoform/Specs/CachetoolsSpec.lean \
                   --spec-module Autoform.Specs.CachetoolsSpec \
                   --decls f_...,f_...

     `--decls` restricts the mutation population to the functions the theorems are about.
     Without it the score measures *coverage* (how much of a 233-function module is
     specified) rather than *vacuity* (whether the specifications that exist have teeth),
     and the two must not be conflated. Report both, separately.

The `module` field written to the JSON report is the module that was MUTATED, because
`scripts/sacm.py` attributes G4 (specification non-vacuity) by that field, and the subject
of the claim is the subject of the mutations.

Usage:
    mutate.py <lean-file> <module-name> [--theorems a,b,c] [--decls d,e,f]
              [--spec-file PATH] [--spec-module MOD] [--generated]
              [--max-mutants N] [--timeout S] [--json PATH] [--seed N]

Only definitions (`def`/`abbrev`/`instance`) are mutated; theorems are left alone --
mutating the proof would prove nothing about the specification.
"""
from __future__ import annotations

import argparse
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile

# ---------------------------------------------------------------------------
# declaration map: which source lines belong to which declaration
# ---------------------------------------------------------------------------

DECL_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|partial\s+|noncomputable\s+|unsafe\s+)*'
    r'(theorem|lemma|example|def|abbrev|instance|inductive|structure|class)\b\s*([A-Za-z_][A-Za-z0-9_\'!?.₀-₉]*)?'
)

THEOREM_KINDS = {"theorem", "lemma"}
DEF_KINDS = {"def", "abbrev", "instance"}
# inductives are *specifications*, not implementations: mutating them mutates the
# thing the theorem is stated against, which proves nothing. They are parsed only so
# their lines are not misattributed to the preceding definition.
SPEC_KINDS = {"inductive", "structure", "class"}


class Decl:
    def __init__(self, kind, name, start):
        self.kind, self.name, self.start, self.end = kind, name, start, start

    def __repr__(self):
        return f"<{self.kind} {self.name} {self.start}-{self.end}>"


def parse_decls(lines):
    """Return declarations with 1-based inclusive line ranges."""
    decls = []
    for i, line in enumerate(lines, start=1):
        m = DECL_RE.match(line)
        if m:
            decls.append(Decl(m.group(1), m.group(2) or f"<anon@{i}>", i))
    for j, d in enumerate(decls):
        d.end = (decls[j + 1].start - 1) if j + 1 < len(decls) else len(lines)
    return decls


def decl_at(decls, line):
    for d in decls:
        if d.start <= line <= d.end:
            return d
    return None


# ---------------------------------------------------------------------------
# mutation operators
# ---------------------------------------------------------------------------

class Mutant:
    def __init__(self, op, line, old, new, decl):
        self.op, self.line, self.old, self.new, self.decl = op, line, old, new, decl

    @property
    def diff(self):
        return f"{self.decl} L{self.line} [{self.op}]\n  - {self.old.rstrip()}\n  + {self.new.rstrip()}"

    def to_json(self):
        return {"op": self.op, "line": self.line, "decl": self.decl,
                "before": self.old.rstrip(), "after": self.new.rstrip()}


def _pair_swaps(pairs):
    """Build a list of (compiled-regex, replacement-fn) for token-level swaps."""
    out = []
    for a, b in pairs:
        out.append((a, b))
        out.append((b, a))
    return out


# tokens are matched with surrounding-space discipline so we do not rewrite
# identifiers or comment prose.
ARITH = _pair_swaps([("+", "-"), ("*", "/")])
CMP = _pair_swaps([("<", ">"), ("≤", "≥"), ("<=", ">="), ("==", "!="), ("≤", "<"), ("≥", ">")])
BOOL_OPS = _pair_swaps([("&&", "||")])
LIT_BOOL = _pair_swaps([("true", "false")])


def _token_mutations(op_name, text, swaps, word=False):
    """Yield (new_text, description) for each single-occurrence token swap."""
    results = []
    for src, dst in swaps:
        if word:
            pat = re.compile(r'(?<![A-Za-z0-9_])' + re.escape(src) + r'(?![A-Za-z0-9_])')
        else:
            pat = re.compile(r'(?<=\s)' + re.escape(src) + r'(?=\s)')
        for m in pat.finditer(text):
            results.append((text[:m.start()] + dst + text[m.end():], f"{op_name}:{src}->{dst}"))
    return results


INT_LIT = re.compile(r'(?<![A-Za-z0-9_.])(\d+)(?![A-Za-z0-9_.])')
ITE = re.compile(r'\bif\s+(.+?)\s+then\s+(.+?)\s+else\s+(.+)$')
ARM = re.compile(r'^(\s*\|\s*.+?=>)(\s*)(\S.*)$')


def gen_mutants(lines, decls):
    """Generate one-at-a-time mutants of every definition body in the file."""
    mutants = []
    defs = [d for d in decls if d.kind in DEF_KINDS]

    # per-definition "default" RHS used by the match-arm-deletion operator
    default_rhs = {}
    for d in defs:
        for ln in range(d.start, d.end + 1):
            m = ARM.match(lines[ln - 1])
            if m and "=>" not in m.group(3):
                default_rhs.setdefault(d.name, m.group(3).strip())
                break

    for d in defs:
        for ln in range(d.start, d.end + 1):
            raw = lines[ln - 1]
            code = raw.split("--")[0]
            if not code.strip() or code.lstrip().startswith(("/-", "-/", "*")):
                continue

            cand = []
            cand += _token_mutations("arith", raw, ARITH)
            cand += _token_mutations("cmp", raw, CMP)
            cand += _token_mutations("bool", raw, BOOL_OPS)
            cand += _token_mutations("lit", raw, LIT_BOOL, word=True)

            # off-by-one on integer literals
            for m in INT_LIT.finditer(code):
                for delta in (1, -1):
                    v = int(m.group(1)) + delta
                    if v < 0:
                        continue
                    cand.append((raw[:m.start()] + str(v) + raw[m.end():],
                                 f"offbyone:{m.group(1)}->{v}"))

            # swap the branches of an if-then-else
            m = ITE.search(code)
            if m:
                swapped = code[:m.start()] + f"if {m.group(1)} then {m.group(3).rstrip()} else {m.group(2)}"
                cand.append((swapped + "\n", "ite-swap"))

            # delete a match arm's body: replace it with the definition's default RHS
            m = ARM.match(raw)
            if m and d.name in default_rhs and m.group(3).strip() != default_rhs[d.name] \
                    and "=>" not in m.group(3):
                cand.append((m.group(1) + m.group(2) + default_rhs[d.name] + "\n", "arm-delete"))

            for new, op in cand:
                if new != raw:
                    mutants.append(Mutant(op, ln, raw, new, d.name))
    return mutants


# ---------------------------------------------------------------------------
# mutation operators for *translated* modules (`Autoform/Generated/*.lean`)
# ---------------------------------------------------------------------------
#
# A generated module is not code in the usual sense: it is a giant data literal,
#
#     def f_x : Func := { name := "...", params := [...], body := (.seq (.assign ...) ...) }
#
# so the operators above (which swap Lean-level `+`/`<`/`&&` tokens) find almost nothing
# to do. The interesting perturbations are perturbations of the *embedded program*: the
# operator string inside `Expr.binop`, the polarity flag of `Expr.inOp`/`Expr.isOp`, the
# choice of field or variable name, whether a statement returns or merely evaluates, and
# whether a branch of a `Stmt.seq` happens at all.
#
# These are exactly the bugs a specification about translated code is supposed to notice,
# and they are the reason G4 could not previously be supported for a translated module:
# the gate had no operator that could touch one.

# `.binop "OP"` — the embedded operator. Swaps stay inside an equivalence class
# (arithmetic for arithmetic, comparison for comparison) so the mutant remains
# type-correct in the object language and the failure is behavioural, not syntactic.
AST_BINOP_SWAPS = {
    "+": "-", "-": "+", "*": "+", "/": "*", "%": "/",
    "<": "<=", "<=": "<", ">": ">=", ">=": ">",
    "==": "!=", "!=": "==",
    "&&": "||", "||": "&&",
}
AST_BINOP = re.compile(r'(\.binop\s+")([^"]+)(")')
AST_UNOP = re.compile(r'(\.unop\s+")([^"]+)(")')
AST_UNOP_SWAPS = {"-": "+", "!": "-", "~": "-"}

# `.inOp neg` / `.isOp neg` — the negation flag. Flipping it inverts every membership or
# identity test, which is a silent wrong answer rather than a crash.
AST_POLARITY = re.compile(r'(\.(?:inOp|isOp)\s+)(true|false)\b')

# `.ret e` vs `.expr e`: evaluate-and-return versus evaluate-and-discard. The classic
# "forgot the return statement" bug, and invisible to any specification that only talks
# about the shape of the AST.
AST_RET = re.compile(r'\(\.ret\b')
AST_EXPR = re.compile(r'\(\.expr\b')

# literals inside the embedded program
AST_INT = re.compile(r'\(\.int\s+(-?\d+)\)')
AST_BOOL = re.compile(r'\(\.bool\s+(true|false)\)')

# field access / mutation: `(.field (.name "self") "F")`, `(.setField _ "F" _)`
AST_FIELD = re.compile(r'(\.field\s+\([^()]*\)\s+")([^"]+)(")')
AST_SETFIELD = re.compile(r'(\.setField\s+\([^()]*\)\s+")([^"]+)(")')
AST_NAME = re.compile(r'(\.name\s+")([^"]+)(")')
AST_ASSIGN = re.compile(r'(\.assign\s+")([^"]+)(")')

# a line that is a self-contained, balanced statement term — the unit the `seq`-deletion
# operator can remove without disturbing the surrounding parenthesis structure.
STMT_HEADS = ("(.assign ", "(.setField ", "(.expr ", "(.ret ", "(.raise ", "(.del ",
              "(.setIndex ")


def _balanced(text):
    depth = 0
    for ch in text:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


def _decl_strings(lines, d, pat, group=2):
    """Every distinct value of capture `group` of `pat` inside declaration `d`."""
    seen = []
    for ln in range(d.start, d.end + 1):
        for m in pat.finditer(lines[ln - 1]):
            v = m.group(group)
            if v not in seen:
                seen.append(v)
    return seen


def gen_mutants_generated(lines, decls):
    """Mutants of a machine-generated module: perturb the *embedded program*."""
    mutants = []
    defs = [d for d in decls if d.kind in DEF_KINDS]

    for d in defs:
        # alternative names available for the name/field-swap operators, taken from the
        # same declaration so the mutant stays plausible rather than obviously broken.
        params = []
        for ln in range(d.start, d.end + 1):
            m = re.search(r'params := \[(.*?)\]', lines[ln - 1])
            if m:
                params = re.findall(r'"([^"]*)"', m.group(1))
        fields = _decl_strings(lines, d, AST_FIELD) + _decl_strings(lines, d, AST_SETFIELD)
        names = _decl_strings(lines, d, AST_NAME)

        for ln in range(d.start, d.end + 1):
            raw = lines[ln - 1]
            if raw.lstrip().startswith("--") or raw.lstrip().startswith("/-"):
                continue
            cand = []

            def sub_at(m, repl, op):
                cand.append((raw[:m.start()] + repl + raw[m.end():], op))

            for m in AST_BINOP.finditer(raw):
                nw = AST_BINOP_SWAPS.get(m.group(2))
                if nw:
                    sub_at(m, m.group(1) + nw + m.group(3), f"ast-binop:{m.group(2)}->{nw}")
            for m in AST_UNOP.finditer(raw):
                nw = AST_UNOP_SWAPS.get(m.group(2))
                if nw:
                    sub_at(m, m.group(1) + nw + m.group(3), f"ast-unop:{m.group(2)}->{nw}")
            for m in AST_POLARITY.finditer(raw):
                nw = "false" if m.group(2) == "true" else "true"
                sub_at(m, m.group(1) + nw, f"ast-polarity:{m.group(2)}->{nw}")
            for m in AST_RET.finditer(raw):
                sub_at(m, "(.expr", "ast-ret->expr")
            for m in AST_EXPR.finditer(raw):
                sub_at(m, "(.ret", "ast-expr->ret")
            for m in AST_INT.finditer(raw):
                v = int(m.group(1))
                for nv in (v + 1, v - 1):
                    sub_at(m, f"(.int {nv})", f"ast-int:{v}->{nv}")
            for m in AST_BOOL.finditer(raw):
                nw = "false" if m.group(1) == "true" else "true"
                sub_at(m, f"(.bool {nw})", f"ast-bool:{m.group(1)}->{nw}")
            for pat, tag in ((AST_FIELD, "ast-field"), (AST_SETFIELD, "ast-setfield")):
                for m in pat.finditer(raw):
                    alt = next((f for f in fields if f != m.group(2)), None)
                    if alt is None:
                        alt = m.group(2) + "__mutated"
                    sub_at(m, m.group(1) + alt + m.group(3), f"{tag}:{m.group(2)}->{alt}")
            for m in AST_NAME.finditer(raw):
                pool = [n for n in (params + names) if n != m.group(2)]
                if pool:
                    sub_at(m, m.group(1) + pool[0] + m.group(3),
                           f"ast-name:{m.group(2)}->{pool[0]}")
            for m in AST_ASSIGN.finditer(raw):
                pool = [n for n in (params + names) if n != m.group(2)]
                if pool:
                    sub_at(m, m.group(1) + pool[0] + m.group(3),
                           f"ast-assign:{m.group(2)}->{pool[0]}")

            # `seq`-branch deletion: a whole statement on its own line, replaced by `.skip`.
            body = raw.strip().rstrip(",")
            trail = ""
            while body.endswith(")") and not _balanced(body):
                body, trail = body[:-1], ")" + trail
            if any(body.startswith(hd) for hd in STMT_HEADS) and _balanced(body):
                indent = raw[:len(raw) - len(raw.lstrip())]
                comma = "," if raw.rstrip().endswith(",") else ""
                cand.append((indent + ".skip" + trail + comma + "\n", "ast-seq-delete"))

            for new, op in cand:
                if new != raw:
                    mutants.append(Mutant(op, ln, raw, new, d.name))
    return mutants


# ---------------------------------------------------------------------------
# build harness
# ---------------------------------------------------------------------------

ERR_RE = re.compile(r'^(?:.*?):(\d+):(\d+):\s*(error|warning)', re.M)


def lake_env():
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    return env


def run_build(root, module, timeout):
    try:
        r = subprocess.run(["lake", "build", module], cwd=root, env=lake_env(),
                           capture_output=True, text=True, timeout=timeout)
        return r.returncode, (r.stdout or "") + (r.stderr or ""), False
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"") if isinstance(e.stdout, bytes) else (e.stdout or "")
        if isinstance(out, bytes):
            out = out.decode("utf-8", "replace")
        return 1, out, True


# Lean/lake has emitted diagnostics in two shapes across toolchain versions:
#     <path>:<line>:<col>: error: <msg>          (leading position)
#     error: <path>:<line>:<col>: <msg>          (leading severity, Lean 4.30)
# Matching only the first silently returns "no attributable errors" on a modern
# toolchain, which collapses every mutant onto the coarse whole-build fallback and makes
# per-theorem attribution meaningless while still printing a plausible score. Both are
# matched, and `error_lines_sanity` below refuses to let the failure be silent.
_ERR_POS_FIRST = re.compile(r'^(.*?):(\d+):(\d+):\s*error', re.M)
_ERR_SEV_FIRST = re.compile(r'^error:\s*(\S.*?):(\d+):(\d+):', re.M)


def all_error_lines(output):
    """(basename, line) for every positional error in the build output, whatever file."""
    out = []
    for pat in (_ERR_POS_FIRST, _ERR_SEV_FIRST):
        for m in pat.finditer(output):
            path = m.group(1).strip()
            out.append((os.path.basename(path), int(m.group(2))))
    return out


def error_lines(output, target_basename):
    """Line numbers carrying an error, restricted to the named file."""
    out = []
    for pat in (_ERR_POS_FIRST, _ERR_SEV_FIRST):
        for m in pat.finditer(output):
            path = m.group(1).strip()
            if target_basename in path or path in ("", "."):
                out.append(int(m.group(2)))
    return sorted(set(out))


# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------

def find_root(path):
    d = os.path.dirname(os.path.abspath(path))
    while d != "/":
        if os.path.exists(os.path.join(d, "lakefile.toml")) or \
           os.path.exists(os.path.join(d, "lakefile.lean")):
            return d
        d = os.path.dirname(d)
    return os.getcwd()


def main():
    ap = argparse.ArgumentParser(description="Lean source-level mutation gate")
    ap.add_argument("lean_file")
    ap.add_argument("module")
    ap.add_argument("--theorems", default=None, help="comma-separated theorem names")
    ap.add_argument("--spec-file", default=None,
                    help="file holding the THEOREMS, if different from the file being "
                         "mutated (the translated-module case: mutate "
                         "Autoform/Generated/X.lean, gate Autoform/Specs/XSpec.lean)")
    ap.add_argument("--spec-module", default=None,
                    help="module to rebuild; defaults to <module>. With --spec-file this "
                         "must be the module that CONTAINS the theorems, so that a "
                         "surviving mutant means the theorem really did not notice.")
    ap.add_argument("--decls", default=None,
                    help="comma-separated definition names to restrict the mutation "
                         "population to. Use it to point the gate at the functions the "
                         "theorems are ABOUT: mutants of other functions survive by "
                         "construction and measure coverage, not vacuity.")
    ap.add_argument("--generated", action="store_true",
                    help="force the translated-module operators (auto-enabled for files "
                         "under Autoform/Generated/)")
    ap.add_argument("--max-mutants", type=int, default=20)
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--json", dest="json_path", default="mutation.json")
    ap.add_argument("--seed", type=int, default=20260819)
    args = ap.parse_args()

    random.seed(args.seed)
    path = os.path.abspath(args.lean_file)
    root = find_root(path)
    base = os.path.basename(path)

    with open(path, "r", encoding="utf-8") as f:
        original = f.read()
    lines = original.splitlines(keepends=True)
    decls = parse_decls(lines)

    # Where do the theorems live? Same file by default; a separate file when the subject
    # is a machine-generated module, which by construction contains no theorems at all.
    spec_path = os.path.abspath(args.spec_file) if args.spec_file else path
    spec_base = os.path.basename(spec_path)
    if spec_path == path:
        spec_lines, spec_decls = lines, decls
    else:
        with open(spec_path, "r", encoding="utf-8") as f:
            spec_lines = f.read().splitlines(keepends=True)
        spec_decls = parse_decls(spec_lines)
    build_module = args.spec_module or args.module
    generated = args.generated or ("Autoform/Generated/" in path.replace(os.sep, "/"))

    if args.theorems:
        targets = [t.strip() for t in args.theorems.split(",") if t.strip()]
    else:
        targets = [d.name for d in spec_decls if d.kind in THEOREM_KINDS]
    if not targets:
        print("no theorems found; nothing to gate."); return 2

    tmap = {d.name: d for d in spec_decls if d.kind in THEOREM_KINDS and d.name in targets}
    missing = [t for t in targets if t not in tmap]
    for t in missing:
        print(f"warning: theorem {t!r} not found in {spec_base}")
    targets = [t for t in targets if t in tmap]
    if not targets:
        return 2

    # Safety net: a mutation run that is interrupted (or killed by an impatient operator)
    # otherwise leaves a mutant on disk, where a concurrent commit can capture it. The
    # backup is written once, before anything is touched, and removed on a clean exit.
    backup = path + ".mutate-backup"
    with open(backup, "w", encoding="utf-8") as f:
        f.write(original)

    all_mutants = (gen_mutants_generated(lines, decls) if generated
                   else gen_mutants(lines, decls))
    if args.decls:
        keep = {d.strip() for d in args.decls.split(",") if d.strip()}
        all_mutants = [m for m in all_mutants if m.decl in keep]
        missing = keep - {m.decl for m in all_mutants}
        for d in sorted(missing):
            print(f"warning: no mutant generated for declaration {d!r}")
    random.shuffle(all_mutants)
    mutants = all_mutants[:args.max_mutants]

    print(f"file      : {path}")
    print(f"module    : {args.module}")
    print(f"operators : {'translated-module (AST literal)' if generated else 'Lean definition'}")
    if spec_path != path:
        print(f"spec file : {spec_path}")
        print(f"built     : {build_module}")
    print(f"theorems  : {', '.join(targets)}")
    print(f"mutants   : {len(mutants)} of {len(all_mutants)} generated\n")

    print("baseline build ...", flush=True)
    rc, out, to = run_build(root, build_module, args.timeout)
    if rc != 0:
        print("BASELINE FAILS TO BUILD -- fix the file first.")
        print(out[-2000:])
        return 3
    print("baseline ok\n")

    stats = {t: {"killed": 0, "survived": 0, "survivors": []} for t in targets}
    invalid, records, coarse, inconclusive = 0, [], 0, 0

    try:
        for i, mut in enumerate(mutants, 1):
            new_lines = list(lines)
            new_lines[mut.line - 1] = mut.new
            with open(path, "w", encoding="utf-8") as f:
                f.write("".join(new_lines))

            rc, out, timed_out = run_build(root, build_module, args.timeout)
            # Errors in the *mutated* file mean the mutant is not well-typed; errors in
            # the *spec* file mean a theorem noticed. When the two are the same file
            # these collapse to the original behaviour.
            errs = error_lines(out, base)
            spec_errs = errs if spec_path == path else error_lines(out, spec_base)
            # Errors in files that are neither the mutated file nor the spec file are
            # somebody else's problem: a broken dependency, a concurrent edit, a stale
            # cache. Counting such a build failure as a "kill" would credit the theorem
            # with catching a bug it never saw — the exact self-deception this gate
            # exists to prevent — so those mutants are reported INCONCLUSIVE and left
            # out of the score entirely.
            foreign = [l for l in all_error_lines(out)
                       if l[0] not in (base, spec_base)]
            hit_defs = {decl_at(decls, l).name for l in errs
                        if decl_at(decls, l) and decl_at(decls, l).kind in DEF_KINDS}
            hit_thms = {decl_at(spec_decls, l).name for l in spec_errs
                        if decl_at(spec_decls, l)
                        and decl_at(spec_decls, l).kind in THEOREM_KINDS}

            rec = mut.to_json()
            if rc != 0 and not errs and not spec_errs and foreign:
                rec["verdict"] = "inconclusive"
                rec["foreign_errors"] = sorted({f for f, _ in foreign})
                inconclusive += 1
                print(f"[{i}/{len(mutants)}] INCONCL. {mut.op:22s} L{mut.line} ({mut.decl}) "
                      f"— build broke in {', '.join(sorted({f for f, _ in foreign}))}, "
                      f"nothing to attribute")
            elif rc != 0 and hit_defs and not hit_thms:
                # the mutation broke the definition itself: not a behavioural bug
                rec["verdict"] = "invalid"
                invalid += 1
                print(f"[{i}/{len(mutants)}] INVALID  {mut.op:22s} L{mut.line} ({mut.decl}) "
                      f"— mutant does not typecheck")
            else:
                rec["verdict"] = {}
                rec["timeout"] = timed_out
                if rc != 0 and not errs and not spec_errs:
                    coarse += 1
                    rec["attribution"] = "coarse"
                for t in targets:
                    # A build failure with no attributable line is counted as a kill for
                    # every theorem — coarse, but it must not fire merely because the
                    # errors landed in the *spec* file, which is the normal cross-file
                    # case and is attributable via `hit_thms`.
                    unattributable = rc != 0 and not errs and not spec_errs
                    dead = (t in hit_thms) or timed_out or unattributable
                    if dead:
                        stats[t]["killed"] += 1
                    else:
                        stats[t]["survived"] += 1
                        stats[t]["survivors"].append(mut.to_json())
                    rec["verdict"][t] = "killed" if dead else "survived"
                tag = ",".join(f"{t}={v}" for t, v in rec["verdict"].items())
                mark = "KILLED " if all(v == "killed" for v in rec["verdict"].values()) else "SURVIVED"
                print(f"[{i}/{len(mutants)}] {mark} {mut.op:22s} L{mut.line} ({mut.decl}) {tag}")
            records.append(rec)
    finally:
        with open(path, "w", encoding="utf-8") as f:
            f.write(original)
        if os.path.exists(backup):
            os.remove(backup)
        # make sure the restored file is what the build cache sees next time
        run_build(root, build_module, args.timeout)

    print("\n=== mutation score ===")
    # `module` is the module that was MUTATED, not the one that was rebuilt: scripts/sacm.py
    # attributes G4 (specification non-vacuity) by this field, and the claim being supported
    # is a claim about the subject of the mutations.
    report = {"file": path, "module": args.module, "seed": args.seed,
              "operators": "generated-ast" if generated else "lean-def",
              "spec_file": spec_path if spec_path != path else None,
              "spec_module": build_module,
              "decls": sorted({m.decl for m in mutants}),
              "mutants_generated": len(all_mutants), "mutants_run": len(mutants),
              "invalid": invalid, "inconclusive": inconclusive,
              "theorems": {}, "mutants": records}
    exit_code = 0
    for t in targets:
        k, s = stats[t]["killed"], stats[t]["survived"]
        score = (k / (k + s)) if (k + s) else 0.0
        verdict = "HAS TEETH" if score == 1.0 else ("WEAK" if score > 0 else "VACUOUS")
        print(f"{t}: killed {k}, survived {s}  score {score:.2%}  [{verdict}]")
        for sv in stats[t]["survivors"]:
            print(f"    survivor: {sv['decl']} L{sv['line']} [{sv['op']}]")
            print(f"      - {sv['before']}")
            print(f"      + {sv['after']}")
        report["theorems"][t] = {"killed": k, "survived": s, "score": score,
                                 "verdict": verdict, "survivors": stats[t]["survivors"]}
        if s:
            exit_code = 1
    if invalid:
        print(f"({invalid} mutants discarded: they broke the definition's own typechecking)")
    if inconclusive:
        print(f"({inconclusive} mutants INCONCLUSIVE: the build failed in an unrelated "
              f"file — concurrent edit or broken dependency — so no verdict is honest. "
              f"They are excluded from the score, not counted as kills.)")
    if coarse:
        print(f"WARNING: {coarse} mutant(s) failed the build with no line attributable to "
              f"either file. Those were credited to EVERY theorem, so the per-theorem "
              f"breakdown for them is not trustworthy — see STRATEGY.md 14's caveat.")
    report["coarse_attributions"] = coarse

    with open(args.json_path, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)
    print(f"\nwrote {os.path.abspath(args.json_path)}")
    return exit_code


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\ninterrupted", file=sys.stderr)
        sys.exit(130)
