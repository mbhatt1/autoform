#!/usr/bin/env python3
"""pr_mode.py -- per-function evidence for the functions a change touched.

    pr_mode.py <repo> --base REF [--head REF] [--subdir DIR] [--module M]
               [--ast FILE] [--tests DIR] [--cases N] [--mutants N]
               [--out DIR] [--sarif FILE] [--markdown FILE]

A pull request changes a handful of functions; the rest of the corpus is as verified as
it was before. This runs the ordinary chain -- export, render, type-check, differential
oracle, ledger, synthesized proofs, mutation gate -- on those functions only, and
reports what each stage established about each of them. Every stage is the existing
script (`cartographer/render_lean.py`, `scripts/differential.py`,
`scripts/ledger.lean.tmpl`, `scripts/synth_specs.py`, `scripts/mutate.py`); nothing is
re-implemented here, only selected and read back.

Which functions changed
-----------------------
`git diff --name-status BASE [HEAD]` names the files (the working tree when `--head` is
omitted, untracked files included). For a Python file the functions are found with the
standard-library `ast` module at both commits: a `def` (method, nested function) whose
AST differs between base and head, or that exists only at head, is *changed*; one that
exists only at base is *removed*. The exporter's neutral AST carries no line numbers, so
this is the only source of positions, and it is used whether or not Joern is installed
(`detection: python-ast`). For every other language the exporter's AST decides: every
function it exported from a changed file counts as changed (`detection: changed-file`),
which over-approximates a one-line edit to a whole file and says so.

Which chain runs
----------------
The neutral AST of the head tree comes from Joern (`joern-parse` + `export_ast.sc`, the
same two calls as `autoform.sh` stages 1 and 3) or from `--ast FILE`, an AST the
exporter produced earlier; the report records which, with the file's digest. Without
either there is no exporter output, so no function can be translated and the report says
so for each. The AST is then cut down to the changed functions, their enclosing scopes
and nested functions, and the transitive callees that resolve inside the AST
(`selection.closure`), so a call from a changed function still has a definition to run.

Evidence levels (lowest first; a function is reported at the highest level it reached,
never higher)
-------------
    none           not exported by the frontend, or no exporter output at all
    hole           the translation contains a hole (labels listed); nothing about the
                   function's behaviour is established
    translated     hole-free, rendered to Lean and type-checked; the oracle did not
                   adjudicate it (the reason is `conformance.json` `coverage.by_status`)
    oracle-agreed  every recorded runtime case agreed with the model (`conformance.json`
                   `runtime_cases`); no theorem about it was proved
    proved         a theorem about the recorded cases is proved in the kernel
                   (`Autoform/SpecsGen/<M>.lean`, `specs.json`)
    refuted        the model and the runtime disagree on a recorded input
                   (`conformance.json` `divergence_detail`), or a candidate theorem
                   about it was refuted (`specs.json` status `refuted`)

`removed` functions are listed, not levelled. A mutation-gate verdict (`mutation.json`)
is attached to a proved function's theorems and never changes its level.

Exit: 0 reported (no refutation); 1 at least one function refuted; 2 could not run
(not a Git repository, unknown ref, no module name, ...). A stage that fails or is
skipped is named in the report with its reason and leaves the functions it would have
served at the level below.
"""
from __future__ import annotations

import argparse
import ast as pyast
import datetime
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "cartographer"))
import deep_json  # noqa: E402
import regression  # noqa: E402
from generator_lowering import analysis_functions  # noqa: E402

SCHEMA_VERSION = 1
LEVELS = ("none", "hole", "translated", "oracle-agreed", "proved", "refuted")
RANK = {level: index for index, level in enumerate(LEVELS)}
PYTHON_SUFFIXES = {".py"}
CODE_SUFFIXES = {".py", ".c", ".h", ".cc", ".cpp", ".cxx", ".hpp", ".java", ".go",
                 ".js", ".mjs", ".cjs", ".ts", ".kt", ".kts"}
SARIF_SCHEMA = "https://docs.oasis-open.org/sarif/sarif/v2.1.0/errata01/os/schemas/sarif-schema-2.1.0.json"
SARIF_LEVEL = {"none": "warning", "hole": "warning", "translated": "note",
               "oracle-agreed": "note", "proved": "note", "refuted": "error"}
RULES = {
    "none": ("No evidence", "The frontend exported nothing for this function, or there was "
             "no exporter output; nothing about it is established."),
    "hole": ("Translation hole", "The translation contains a hole: the model does not cover "
             "the construct named by the label, so nothing about the function's behaviour "
             "is established."),
    "translated": ("Translated", "Hole-free and type-checked as Lean; the runtime oracle did "
                   "not adjudicate any case, so the model is unconfirmed."),
    "oracle-agreed": ("Oracle agreed", "Every recorded runtime case agreed with the model; "
                      "no theorem about the function was proved."),
    "proved": ("Proved", "A theorem about the recorded runtime cases is proved in the Lean "
               "kernel. The claim is about those cases, not all inputs."),
    "refuted": ("Refuted", "The model and the runtime disagree on a recorded input, or a "
                "candidate theorem about the function was refuted. A witness is recorded."),
}


class PrError(ValueError):
    """The run cannot start (exit 2)."""


# --------------------------------------------------------------------------- git

def git(repo, *args, check=True, binary=False):
    result = subprocess.run(["git", "-c", "core.hooksPath=/dev/null", *args], cwd=str(repo),
                            text=not binary, capture_output=True)
    if check and result.returncode != 0:
        error = result.stderr if binary else (result.stderr.strip() or result.stdout.strip())
        raise PrError(f"git {' '.join(args)}: {error.decode(errors='replace') if binary else error}")
    return result


def resolve_ref(repo, ref):
    """A full commit id, fetching a missing ref once (shallow clones)."""
    result = git(repo, "rev-parse", "--verify", "--quiet", f"{ref}^{{commit}}", check=False)
    if result.returncode == 0:
        return result.stdout.strip()
    fetch = git(repo, "fetch", "--depth", "1", "origin", ref, check=False)
    if fetch.returncode == 0:
        result = git(repo, "rev-parse", "--verify", "--quiet", "FETCH_HEAD^{commit}", check=False)
        if result.returncode == 0:
            return result.stdout.strip()
    raise PrError(f"unknown ref {ref!r} in {repo}")


def changed_files(repo, base, head):
    """`(status, path)` for every file that differs; the working tree when head is None."""
    args = ["diff", "--name-status", "--no-renames", base] + ([head] if head else [])
    entries = []
    for line in git(repo, *args).stdout.splitlines():
        parts = line.split("\t")
        if len(parts) >= 2:
            entries.append((parts[0][:1], parts[-1]))
    if head is None:
        untracked = git(repo, "ls-files", "--others", "--exclude-standard").stdout.splitlines()
        entries.extend(("A", path) for path in untracked if path)
    return sorted(set(entries), key=lambda entry: entry[1])


def read_at(repo, ref, path):
    """File content at a commit, or from the working tree when ref is None."""
    if ref is None:
        try:
            return (Path(repo) / path).read_bytes()
        except OSError:
            return None
    result = git(repo, "show", f"{ref}:{path}", check=False, binary=True)
    return result.stdout if result.returncode == 0 else None


# ------------------------------------------------------------ Python functions

def python_functions(source, relfile):
    """`name -> {start, end, digest}` for every def in a Python file, named the way the
    exporter names them: `<relfile>:<module>.<qualified name>`."""
    try:
        tree = pyast.parse(source)
    except (SyntaxError, ValueError) as exc:
        return None, f"{relfile}: {exc.__class__.__name__}: {exc}"
    found = {}

    def visit(node, scope):
        for child in pyast.iter_child_nodes(node):
            if isinstance(child, (pyast.FunctionDef, pyast.AsyncFunctionDef)):
                qualified = scope + [child.name]
                start = min([child.lineno] + [d.lineno for d in child.decorator_list])
                name = f"{relfile}:<module>.{'.'.join(qualified)}"
                found[name] = {"start": start, "end": child.end_lineno or child.lineno,
                               "digest": hashlib.sha256(pyast.dump(child).encode()).hexdigest()}
                visit(child, qualified)
            elif isinstance(child, pyast.ClassDef):
                visit(child, scope + [child.name])
            else:
                visit(child, scope)

    visit(tree, [])
    return found, None


def _relative_to_source(path, subdir):
    if not subdir or subdir == ".":
        return path
    prefix = subdir.rstrip("/") + "/"
    return path[len(prefix):] if path.startswith(prefix) else None


def changed_functions(repo, base, head, subdir=None):
    """Which functions a change touched, before any exporter runs.

    Returns `{functions: [...], removed: [...], files: [...], errors: [...]}`. Python
    functions are named and positioned now; other languages are listed by file and
    resolved against the exporter's AST by `select_functions`."""
    functions, removed, files, errors = [], [], [], []
    for status, path in changed_files(repo, base, head):
        relfile = _relative_to_source(path, subdir)
        suffix = PurePosixPath(path).suffix.lower()
        record = {"path": path, "status": status, "file": relfile,
                  "language": "python" if suffix in PYTHON_SUFFIXES else
                  ("other" if suffix in CODE_SUFFIXES else "non-code")}
        files.append(record)
        if relfile is None or record["language"] == "non-code":
            record["analysed"] = False
            continue
        if record["language"] != "python":
            record["analysed"] = "changed-file"
            continue
        record["analysed"] = "python-ast"
        before = read_at(repo, base, path) if status != "A" else None
        after = read_at(repo, head, path) if status != "D" else None
        old, error = python_functions(before, relfile) if before is not None else ({}, None)
        if error:
            errors.append(error + " (at base)")
            old = {}
        new, error = python_functions(after, relfile) if after is not None else ({}, None)
        if error:
            errors.append(error + " (at head)")
            new = {}
        for name, info in sorted(new.items()):
            if name not in old:
                change = "added"
            elif old[name]["digest"] != info["digest"]:
                change = "modified"
            else:
                continue
            functions.append({"name": name, "path": path, "file": relfile, "change": change,
                              "line": info["start"], "end_line": info["end"],
                              "detection": "python-ast", "language": "python"})
        for name in sorted(set(old) - set(new)):
            removed.append({"name": name, "path": path, "file": relfile, "change": "removed",
                            "detection": "python-ast", "language": "python"})
    return {"functions": functions, "removed": removed, "files": files, "errors": errors}


# ---------------------------------------------------------------- the exporter

def joern_home():
    home = Path(os.environ.get("JOERN_HOME") or Path.home() / "joern")
    if (home / "joern-cli").is_dir():
        home = home / "joern-cli"
    return home


def export_ast(source, out, log_dir, timeout):
    """`joern-parse` + `export_ast.sc`, exactly as `autoform.sh` stages 1 and 3."""
    joern = joern_home()
    if not (joern / "joern-parse").exists():
        raise PrError(f"no Joern frontend at {joern / 'joern-parse'} (set JOERN_HOME); "
                      "pass --ast FILE to use an AST the exporter produced earlier")
    env = dict(os.environ, LANG=os.environ.get("LANG") or "C.UTF-8",
               LC_ALL=os.environ.get("LC_ALL") or "C.UTF-8",
               JAVA_TOOL_OPTIONS=(os.environ.get("JAVA_TOOL_OPTIONS", "") + " -Dfile.encoding=UTF-8"))
    with tempfile.TemporaryDirectory(prefix="autoform-pr-export-") as work:
        cpg = Path(work) / "cpg.bin"
        parse = subprocess.run([str(joern / "joern-parse"), str(source), "--output", str(cpg)],
                               cwd=work, env=env, text=True, capture_output=True, timeout=timeout)
        (Path(log_dir) / "parse.log").write_text(parse.stdout + parse.stderr)
        if parse.returncode != 0:
            raise PrError(f"joern-parse failed (exit {parse.returncode}); see parse.log")
        export = subprocess.run([str(joern / "joern"), "--script", str(ROOT / "cartographer/export_ast.sc"),
                                 "--param", f"cpgPath={cpg}", "--param", f"out={out}",
                                 "--param", f"dataModel={os.environ.get('AUTOFORM_DATA_MODEL', 'lp64')}"],
                                cwd=work, env=env, text=True, capture_output=True, timeout=timeout)
        (Path(log_dir) / "export.log").write_text(export.stdout + export.stderr)
        if export.returncode != 0 or not re.search(r"^exported", export.stdout, re.M):
            raise PrError("export_ast.sc did not report success; see export.log")
    return Path(out)


# -------------------------------------------------------------- the selection

_CALLEE_KEYS = ("f", "m", "callee", "fn", "cls", "c", "target")


def _callee_names(body):
    names = set()
    for node in deep_json.dict_nodes(body):
        kind = node.get("k")
        if kind in ("call", "mcall", "new", "construct", "callm", "scall"):
            for key in _CALLEE_KEYS:
                value = node.get(key)
                if isinstance(value, str) and value:
                    names.add(value)
    return names


def _resolve(callee, by_name, by_suffix):
    if callee in by_name:
        return {callee}
    return set(by_suffix.get(callee.rsplit(".", 1)[-1], ()))


def select_functions(functions, changed_names):
    """The AST cut down to the changed functions, their scopes and their callees.

    Kept: every changed function present in the AST; its enclosing scopes (`a.b` for
    `a.b.c`) and nested functions (`a.b.c.*`); module-level entries, which hold the
    module's state; and, to a fixed point, every function a kept body calls that resolves
    in the AST by exact name or by its last component. Over-inclusion only makes the
    module larger; under-inclusion would turn a resolvable call into an unresolved one."""
    by_name = {f["name"]: f for f in functions if isinstance(f.get("name"), str)}
    by_suffix = {}
    for name in by_name:
        by_suffix.setdefault(name.rsplit(".", 1)[-1], set()).add(name)
    keep, missing = set(), []
    for name in changed_names:
        if name in by_name:
            keep.add(name)
        else:
            missing.append(name)
        for other in by_name:
            if other.startswith(name + ".") or name.startswith(other + "."):
                keep.add(other)
    for name in by_name:
        if name.endswith(":<module>"):
            keep.add(name)
    closure = set()
    pending = list(keep)
    while pending:
        current = pending.pop()
        for callee in _callee_names(by_name[current].get("body")):
            for resolved in _resolve(callee, by_name, by_suffix):
                if resolved not in keep:
                    keep.add(resolved)
                    closure.add(resolved)
                    pending.append(resolved)
    selected = [f for f in functions if isinstance(f.get("name"), str) and f["name"] in keep]
    return selected, sorted(closure), missing


# ------------------------------------------------------------------ the chain

def _write_json(path, value):
    """Serialise on a thread with a deep stack: a long function body is a right-nested
    `seq` chain, and `json.dumps` recurses once per level."""
    import threading
    box = {}

    def go():
        try:
            box["text"] = json.dumps(value, indent=1)
        except BaseException as exc:  # noqa: BLE001
            box["error"] = exc

    limit = sys.getrecursionlimit()
    sys.setrecursionlimit(max(limit, 200_000))
    try:
        threading.stack_size(256 * 1024 * 1024)
    except (ValueError, RuntimeError):
        pass
    thread = threading.Thread(target=go)
    thread.start()
    thread.join()
    sys.setrecursionlimit(limit)
    if "error" in box:
        raise box["error"]
    Path(path).write_text(box["text"] + "\n")


class Chain:
    """Runs the existing stages in order and records what each did."""

    def __init__(self, root, report, module, source, python, timeout, log):
        self.root, self.report, self.module = Path(root), Path(report), module
        self.source, self.python, self.timeout, self.log = Path(source), python, timeout, log
        self.stages = {}
        self.env = dict(os.environ)
        self.env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + self.env.get("PATH", "")
        self.env.setdefault("AUTOFORM_PYTHON", python)
        self.lake = shutil.which("lake", path=self.env["PATH"])

    def skip(self, name, reason):
        self.stages[name] = {"status": "skipped", "reason": reason}
        self.log(f"==> {name}: skipped: {reason}")

    def run(self, name, command, *, cwd=None, log_name=None, ok=(0,)):
        self.log(f"==> {name}")
        start = time.monotonic()
        record = {"status": "failed", "command": [str(c) for c in command]}
        try:
            result = subprocess.run([str(c) for c in command], cwd=str(cwd or self.root),
                                    env=self.env, text=True, capture_output=True,
                                    timeout=self.timeout)
            record["exit_code"] = result.returncode
            output = result.stdout + result.stderr
            record["status"] = "passed" if result.returncode in ok else "failed"
        except subprocess.TimeoutExpired as exc:
            output = ((exc.stdout or b"").decode(errors="replace") +
                      (exc.stderr or b"").decode(errors="replace"))
            record["reason"] = f"timed out after {self.timeout:g}s"
        record["seconds"] = round(time.monotonic() - start, 2)
        (self.report / (log_name or name + ".log")).write_text(output)
        record["log"] = log_name or name + ".log"
        if record["status"] == "failed" and "reason" not in record:
            tail = [line for line in output.splitlines() if line.strip()][-3:]
            record["reason"] = f"exit {record.get('exit_code')}: " + " | ".join(tail)[:400]
        self.stages[name] = record
        return record["status"] == "passed"

    def render(self, ast_path):
        target = self.root / "Autoform/Generated" / f"{self.module}.lean"
        if any(p.with_name(p.name + ".mutate-backup").exists() for p in [target]):
            raise PrError(f"{target}.mutate-backup exists: a mutation run owns this module")
        return self.run("render", [self.python, self.root / "cartographer/render_lean.py",
                                   ast_path, target, self.module])

    def build(self):
        if not self.lake:
            self.skip("build", "lake is not on PATH (install elan; see docs/running.md)")
            return False
        return self.run("build", [self.lake, "build", "Autoform.Runtime",
                                  f"Autoform.Generated.{self.module}"])

    def oracle(self, ast_path, cases, tests):
        if not self.lake:
            self.skip("oracle", "lake is not on PATH")
            return None
        command = [self.python, self.root / "scripts/differential.py", ast_path, self.source,
                   self.module, str(cases)]
        if tests:
            command += ["--tests", tests]
        self.run("oracle", command, cwd=self.report, log_name="conformance.log", ok=(0, 1))
        path = self.report / "conformance.json"
        return deep_json.load(path) if path.is_file() else None

    def ledger(self):
        if not self.lake:
            self.skip("ledger", "lake is not on PATH")
            return None
        template = (self.root / "scripts/ledger.lean.tmpl").read_text().replace("@MODULE@", self.module)
        with tempfile.TemporaryDirectory(prefix="autoform-pr-ledger-") as work:
            lean_file = Path(work) / "Ledger.lean"
            lean_file.write_text(template)
            passed = self.run("ledger", [self.lake, "env", "lean", lean_file])
        produced = self.root / f"ledger-{self.module}.json"
        if produced.is_file():
            shutil.move(str(produced), str(self.report / f"ledger-{self.module}.json"))
        if not passed:
            return None
        path = self.report / f"ledger-{self.module}.json"
        return json.loads(path.read_text()) if path.is_file() else None

    def specs(self, ast_path, cases):
        if not self.lake:
            self.skip("specs", "lake is not on PATH")
            return None
        out = self.report / "specs.json"
        self.run("specs", [self.python, "-u", self.root / "scripts/synth_specs.py", ast_path,
                           self.source, self.module, "--conformance", self.report / "conformance.json",
                           "--conformance-only", "--domain", str(cases), "--sample-subjects", "0",
                           "--json", out])
        return json.loads(out.read_text()) if out.is_file() else None

    def mutate(self, mutants):
        """`mutate.py` exits 0 (every mutant killed), 1 (a survivor), 2 (a theorem untested
        or a mutant inconclusive) or 3 (its diagnostics could not be attributed). The
        first three are verdicts, recorded per theorem in `mutation.json`; only the last,
        or no report at all, is a failed stage."""
        out = self.report / "mutation.json"
        self.run("mutation", [self.python, self.root / "scripts/mutate.py",
                              self.root / "Autoform/Generated" / f"{self.module}.lean",
                              f"Autoform.Generated.{self.module}",
                              "--spec-file", self.root / "Autoform/SpecsGen" / f"{self.module}.lean",
                              "--spec-module", f"Autoform.SpecsGen.{self.module}",
                              "--spec-report", self.report / "specs.json",
                              "--max-mutants", str(mutants), "--json", out], ok=(0, 1, 2))
        report = json.loads(out.read_text()) if out.is_file() else None
        stage = self.stages["mutation"]
        if stage["status"] != "passed" or report is None or report.get("status") == "ATTRIBUTION_BROKEN":
            stage["status"] = "failed"
            stage.setdefault("reason", (report or {}).get("reason") or "no mutation.json was written")
            return None
        verdicts = {}
        for theorem in (report.get("theorems") or {}).values():
            verdicts[theorem.get("verdict")] = verdicts.get(theorem.get("verdict"), 0) + 1
        stage.pop("reason", None)
        stage["note"] = (f"{report.get('mutants_run', 0)} mutant(s) run; " +
                         ", ".join(f"{n} {v}" for v, n in sorted(verdicts.items(), key=str)))
        return report


# ----------------------------------------------------------------- evidence

def _theorem_artifact(module, theorem):
    return {"kind": "theorem", "path": f"Autoform/SpecsGen/{module}.lean", "theorem": theorem}


def evidence(changed, selected, conformance, specs, mutation, stages, module, exporter):
    """One record per changed function: the highest level its evidence reaches, the
    reason in words, and the artifact each level traces to."""
    lowered = {f["name"]: f for f in analysis_functions(selected)} if selected else {}
    by_status = ((conformance or {}).get("coverage") or {}).get("by_status") or {}
    cases = {}
    for case in (conformance or {}).get("runtime_cases") or []:
        bucket = cases.setdefault(case.get("name"), {"agree": 0, "diverge": 0, "inconclusive": 0})
        comparison = case.get("comparison")
        bucket["agree" if comparison == "agree" else "diverge" if comparison == "diverge"
               else "inconclusive"] += 1
    divergences = {}
    for index, entry in enumerate((conformance or {}).get("divergence_detail") or []):
        divergences.setdefault(entry.get("function"), []).append(index)
    theorems = {}
    for record in (specs or {}).get("specs") or []:
        theorems.setdefault(record.get("subject"), []).append(record)
    budget = {}
    for entry in (specs or {}).get("budget_excluded") or []:
        budget.setdefault(entry.get("subject"), []).append(entry)
    gate = (mutation or {}).get("theorems") or {}
    build_ok = stages.get("build", {}).get("status") == "passed"
    specs_stage = stages.get("specs", {})

    results = []
    for function in changed:
        name = function["name"]
        record = dict(function, level="none", reason="", artifacts=[], holes=[],
                      oracle=None, theorems=[], mutation=None)
        results.append(record)
        if exporter["status"] != "available":
            record["reason"] = f"no exporter output: {exporter['reason']}"
            continue
        if name not in lowered:
            record["reason"] = ("the frontend exported no function by this name "
                                f"(ast-{module}.json); its evidence cannot be looked up")
            continue
        record["artifacts"].append({"kind": "ast", "path": f"ast-{module}.json", "function": name})
        holes = regression.function_holes(lowered[name])
        if holes:
            record.update(level="hole", holes=holes,
                          reason="translation holes: " + ", ".join(sorted(set(holes))))
            continue
        if not build_ok:
            stage = stages.get("render" if stages.get("render", {}).get("status") != "passed" else "build", {})
            record["reason"] = ("hole-free, but the rendered module was not type-checked: "
                                + stage.get("reason", "stage did not run"))
            continue
        record.update(level="translated")
        record["artifacts"].append({"kind": "render", "path": f"Autoform/Generated/{module}.lean",
                                    "definition": "f_" + re.sub(r"[^A-Za-z0-9]", "_", name)})
        status = by_status.get(name)
        record["oracle"] = {"status": status, **cases.get(name, {"agree": 0, "diverge": 0, "inconclusive": 0})}
        if name in divergences:
            record.update(level="refuted",
                          reason=f"the model and the runtime disagree on {len(divergences[name])} "
                                 "recorded input(s)")
            record["artifacts"].append({"kind": "divergence", "path": "conformance.json",
                                        "divergence_detail": divergences[name]})
            continue
        if status != "compared" or record["oracle"]["agree"] == 0:
            oracle_stage = stages.get("oracle", {})
            why = status if status else oracle_stage.get("reason", "the oracle did not run")
            record["reason"] = f"type-checked; not adjudicated by the oracle: {why}"
            continue
        record.update(level="oracle-agreed",
                      reason=f"{record['oracle']['agree']} recorded case(s) agreed with the runtime")
        record["artifacts"].append({"kind": "conformance", "path": "conformance.json",
                                    "runtime_cases": record["oracle"]["agree"]})
        own = theorems.get(name, [])
        record["theorems"] = [{"id": t.get("id"), "status": t.get("status"), "proved": bool(t.get("proved")),
                               "reason": t.get("reason", "")} for t in own]
        refuted = [t for t in own if t.get("status") == "refuted"]
        if refuted:
            record.update(level="refuted",
                          reason="candidate theorem refuted: " + "; ".join(
                              f"{t.get('id')} ({t.get('reason') or 'counterexample'})" for t in refuted))
            record["artifacts"].append({"kind": "specs", "path": "specs.json",
                                        "theorems": [t.get("id") for t in refuted]})
            continue
        proved = [t for t in own if t.get("proved")]
        if proved and (specs or {}).get("build_clean"):
            record.update(level="proved",
                          reason="proved in the kernel: " + ", ".join(t["id"] for t in proved)
                                 + f" ({record['oracle']['agree']} recorded case(s))")
            for theorem in proved:
                record["artifacts"].append(_theorem_artifact(module, theorem["id"]))
            record["artifacts"].append({"kind": "specs", "path": "specs.json",
                                        "theorems": [t["id"] for t in proved]})
            verdicts = {t["id"]: gate[t["id"]] for t in proved if t["id"] in gate}
            if verdicts:
                record["mutation"] = {
                    "killed": sum(v.get("killed", 0) for v in verdicts.values()),
                    "survived": sum(v.get("survived", 0) for v in verdicts.values()),
                    "verdicts": {k: v.get("verdict") for k, v in verdicts.items()}}
                record["artifacts"].append({"kind": "mutation", "path": "mutation.json",
                                            "theorems": sorted(verdicts)})
            elif stages.get("mutation", {}).get("status") == "skipped":
                record["mutation"] = {"skipped": stages["mutation"]["reason"]}
            continue
        if name in budget:
            record["reason"] += "; proof over budget: " + "; ".join(
                f"{b.get('theorem')} ({b.get('reason')})" for b in budget[name])
        elif specs_stage.get("status") != "passed":
            record["reason"] += "; proof stage " + specs_stage.get("status", "did not run") + (
                ": " + specs_stage["reason"] if specs_stage.get("reason") else "")
        elif own:
            record["reason"] += "; theorem(s) emitted but not proved: " + ", ".join(
                f"{t.get('id')} ({t.get('status')})" for t in own)
        else:
            record["reason"] += "; no theorem was emitted for it"
    return results


# ------------------------------------------------------------------ outputs

def sarif_document(report):
    rules = [{"id": f"autoform/{level}", "name": RULES[level][0].replace(" ", ""),
              "shortDescription": {"text": RULES[level][0]},
              "fullDescription": {"text": RULES[level][1]},
              "help": {"text": RULES[level][1] + " See docs/evidence-levels.md."},
              "defaultConfiguration": {"level": SARIF_LEVEL[level]},
              "properties": {"tags": ["autoform", "evidence-level"]}} for level in LEVELS]
    index = {rule["id"]: i for i, rule in enumerate(rules)}
    results = []
    for function in report["functions"]:
        level = function["level"]
        text = f"{function['name']}: {level} -- {function['reason']}"
        artifacts = "; ".join(
            a.get("theorem") or a.get("path") for a in function["artifacts"]) or "no artifact"
        results.append({
            "ruleId": f"autoform/{level}", "ruleIndex": index[f"autoform/{level}"],
            "level": SARIF_LEVEL[level],
            "message": {"text": text + f" [artifacts: {artifacts}]"},
            "locations": [{"physicalLocation": {
                "artifactLocation": {"uri": function["path"], "uriBaseId": "%SRCROOT%"},
                "region": {"startLine": max(1, int(function.get("line") or 1))}}}],
            "partialFingerprints": {"autoform/function": function["name"]},
            "properties": {"function": function["name"], "level": level,
                           "change": function["change"], "detection": function["detection"],
                           "artifacts": function["artifacts"]}})
    return {
        "$schema": SARIF_SCHEMA, "version": "2.1.0",
        "runs": [{
            "tool": {"driver": {"name": "autoform", "semanticVersion": report["tool_version"],
                                "informationUri": "https://github.com/b1oo/autoform",
                                "rules": rules}},
            "automationDetails": {"id": f"autoform/pr/{report['module']}"},
            "versionControlProvenance": [{"repositoryUri": report["repository"]["uri"],
                                          "revisionId": report["head"]["commit"] or "working-tree"}],
            "results": results,
            "properties": {"base": report["base"], "head": report["head"],
                           "stages": report["stages"], "exporter": report["exporter"]},
        }],
    }


def validate_sarif(document):
    """Problems with a SARIF document against the shape GitHub code scanning ingests:
    SARIF 2.1.0, one run, a named driver with rules, each result naming a rule with a
    level GitHub knows, a message and a relative file location on a positive line."""
    problems = []
    if document.get("version") != "2.1.0":
        problems.append("version must be '2.1.0'")
    runs = document.get("runs")
    if not isinstance(runs, list) or not runs:
        return problems + ["runs must be a non-empty list"]
    for run in runs:
        driver = (run.get("tool") or {}).get("driver") or {}
        if not isinstance(driver.get("name"), str) or not driver["name"]:
            problems.append("tool.driver.name is required")
        rules = driver.get("rules") or []
        ids = [rule.get("id") for rule in rules]
        if len(set(ids)) != len(ids):
            problems.append("rule ids must be unique")
        for rule in rules:
            if not (rule.get("shortDescription") or {}).get("text"):
                problems.append(f"rule {rule.get('id')} needs shortDescription.text")
        results = run.get("results")
        if not isinstance(results, list):
            problems.append("results must be a list")
            continue
        if len(results) > 25000:
            problems.append("GitHub ingests at most 25000 results per run")
        for n, result in enumerate(results):
            rule_id = result.get("ruleId")
            if rule_id not in ids:
                problems.append(f"result {n}: ruleId {rule_id!r} is not in tool.driver.rules")
            elif result.get("ruleIndex") is not None and ids[result["ruleIndex"]] != rule_id:
                problems.append(f"result {n}: ruleIndex does not point at {rule_id}")
            if result.get("level") not in ("none", "note", "warning", "error"):
                problems.append(f"result {n}: level {result.get('level')!r} is not a SARIF level")
            if not (result.get("message") or {}).get("text"):
                problems.append(f"result {n}: message.text is required")
            locations = result.get("locations") or []
            if not locations:
                problems.append(f"result {n}: a location is required for code scanning")
            for location in locations:
                physical = location.get("physicalLocation") or {}
                uri = (physical.get("artifactLocation") or {}).get("uri")
                if not isinstance(uri, str) or not uri or uri.startswith("/") or "://" in uri or uri.startswith(".."):
                    problems.append(f"result {n}: artifactLocation.uri must be a relative path")
                line = (physical.get("region") or {}).get("startLine")
                if not isinstance(line, int) or isinstance(line, bool) or line < 1:
                    problems.append(f"result {n}: region.startLine must be an integer >= 1")
    return problems


def markdown_comment(report):
    counts = {level: 0 for level in LEVELS}
    for function in report["functions"]:
        counts[function["level"]] += 1
    head = report["head"]["commit"] or "working tree"
    lines = [f"## autoform: evidence for the functions changed since `{report['base']['commit'][:12]}`",
             "",
             f"Base `{report['base']['commit'][:12]}` → head `{head[:12] if report['head']['commit'] else head}`"
             f"; module `{report['module']}`; exporter: {report['exporter']['status']}"
             + (f" ({report['exporter']['reason']})" if report['exporter'].get('reason') else "") + ".",
             "",
             "| level | functions |", "|---|---|"]
    lines += [f"| {level} | {counts[level]} |" for level in LEVELS]
    lines += ["", "Levels never round up: a function is listed at the highest level its own "
              "artifacts reach (`docs/evidence-levels.md`).", ""]
    if report["functions"]:
        lines += ["| function | change | level | evidence | artifact |", "|---|---|---|---|---|"]
        for function in report["functions"]:
            artifacts = "<br>".join(
                (f"`{a['path']}` `{a['theorem']}`" if a.get("theorem") else f"`{a['path']}`")
                for a in function["artifacts"]) or "none"
            where = f"`{function['path']}`" + (f":{function['line']}" if function.get("line") else "")
            extra = ""
            if function.get("mutation") and "killed" in function["mutation"]:
                verdicts = ", ".join(sorted(set(function["mutation"]["verdicts"].values())))
                extra = (f" Mutation gate: {verdicts} ({function['mutation']['killed']} killed, "
                         f"{function['mutation']['survived']} survived).")
            elif function.get("mutation") and function["mutation"].get("skipped"):
                extra = f" Mutation gate skipped: {function['mutation']['skipped']}."
            lines.append(f"| `{function['name']}`<br>{where} | {function['change']} | "
                         f"**{function['level']}** | {function['reason']}{extra} | {artifacts} |")
        lines.append("")
    else:
        lines += ["No changed function was found in the analysed files.", ""]
    if report["removed"]:
        lines += ["Removed at head (nothing to verify): " +
                  ", ".join(f"`{f['name']}`" for f in report["removed"]), ""]
    skipped_files = [f for f in report["files"] if f.get("analysed") is False]
    if skipped_files:
        lines += ["Changed files not analysed (outside `--subdir` or not source code): " +
                  ", ".join(f"`{f['path']}`" for f in skipped_files), ""]
    noted = [f for f in report["files"] if f.get("note")]
    if noted:
        lines += ["Changed files with no function to report: " +
                  "; ".join(f"`{f['path']}` ({f['note']})" for f in noted), ""]
    if report["selection"].get("missing"):
        lines += ["Changed functions the exporter did not export: " +
                  ", ".join(f"`{n}`" for n in report["selection"]["missing"]), ""]
    if report.get("errors"):
        lines += ["Detection errors: " + "; ".join(report["errors"]), ""]
    lines += ["<details><summary>Stages</summary>", "", "| stage | status | seconds | note |", "|---|---|---|---|"]
    for name, stage in report["stages"].items():
        lines.append(f"| {name} | {stage.get('status')} | {stage.get('seconds', '')} | "
                     f"{stage.get('reason') or stage.get('note') or ''} |")
    lines += ["", "</details>", "",
              f"Detection: {report['detection']}. Selection: {len(report['selection']['selected'])} "
              f"function(s) in the module, {len(report['selection']['closure'])} pulled in as callees.",
              f"Report: `{report['report_dir']}`."]
    return "\n".join(lines) + "\n"


# --------------------------------------------------------------------- main

def run(args, log=print):
    repo = Path(args.repo).resolve()
    if not (repo / ".git").exists():
        raise PrError(f"{repo} is not a Git checkout (no .git); pr mode diffs two commits of one repository")
    if not re.fullmatch(r"[A-Z][A-Za-z0-9_]*", args.module):
        raise PrError("--module must be a Lean identifier beginning with an uppercase letter")
    base = resolve_ref(repo, args.base)
    head = resolve_ref(repo, args.head) if args.head else None
    subdir = (args.subdir or "").strip("/") or None
    report_dir = Path(args.out or ROOT / "artifacts/pr" / args.module).resolve()
    report_dir.mkdir(parents=True, exist_ok=True)
    for name in ("conformance.json", "specs.json", "mutation.json", f"ledger-{args.module}.json",
                 f"ast-{args.module}.json", "pr.json"):
        (report_dir / name).unlink(missing_ok=True)

    log(f"==> changed functions: {base[:12]}..{head[:12] if head else 'working tree'}")
    detected = changed_functions(repo, base, head, subdir)
    for error in detected["errors"]:
        log("   !! " + error)

    # The head tree the chain runs on: the working tree, or an export of --head.
    scratch = None
    if head is None:
        source = repo / subdir if subdir else repo
    else:
        scratch = tempfile.mkdtemp(prefix="autoform-pr-head-")
        archive = git(repo, "archive", "--format=tar", head, binary=True)
        subprocess.run(["tar", "-x", "-C", scratch], input=archive.stdout, check=True)
        source = Path(scratch) / subdir if subdir else Path(scratch)
    if not source.is_dir():
        raise PrError(f"--subdir {subdir!r} is not a directory at head")

    python = sys.executable
    chain = Chain(ROOT, report_dir, args.module, source, python, args.stage_timeout, log)
    exporter = {"status": "unavailable", "reason": ""}
    functions = None
    full_ast = report_dir / f"ast-{args.module}.full.json"
    try:
        if args.ast:
            supplied = Path(args.ast).resolve()
            shutil.copy(supplied, full_ast)
            exporter = {"status": "available", "source": "supplied", "path": str(supplied),
                        "sha256": hashlib.sha256(full_ast.read_bytes()).hexdigest(),
                        "reason": f"--ast {supplied.name} (an AST the exporter produced earlier; Joern not run)"}
        else:
            start = time.monotonic()
            try:
                export_ast(source, full_ast, report_dir, args.stage_timeout)
                exporter = {"status": "available", "source": "joern", "joern": str(joern_home()),
                            "sha256": hashlib.sha256(full_ast.read_bytes()).hexdigest(),
                            "reason": "", "seconds": round(time.monotonic() - start, 2)}
            except (PrError, subprocess.TimeoutExpired) as exc:
                exporter = {"status": "unavailable", "reason": str(exc)}
                log(f"   !! export: {exc}")
        chain.stages["export"] = {"status": "passed" if exporter["status"] == "available" else "failed",
                                  **{k: v for k, v in exporter.items() if k != "status"}}
        if exporter["status"] == "available":
            functions = deep_json.load(full_ast)
            if isinstance(functions, dict):
                functions = functions.get("functions", [])

        # Functions in non-Python changed files are whatever the exporter exported from them.
        changed = list(detected["functions"])
        if functions is not None:
            by_file = {}
            for function in functions:
                if isinstance(function.get("name"), str) and function.get("file"):
                    by_file.setdefault(function["file"], []).append(function["name"])
            for record in detected["files"]:
                if record.get("analysed") == "changed-file":
                    if not by_file.get(record["file"]):
                        record["note"] = "the exporter exported no function from this file"
                    for name in by_file.get(record["file"], []):
                        if not name.endswith(":<module>"):
                            changed.append({"name": name, "path": record["path"], "file": record["file"],
                                            "change": "modified" if record["status"] == "M" else "added",
                                            "line": None, "end_line": None,
                                            "detection": "changed-file", "language": "other"})
        else:
            for record in detected["files"]:
                if record.get("analysed") == "changed-file":
                    record["note"] = "no exporter output, so its functions cannot be named"
        changed.sort(key=lambda f: (f["path"], f.get("line") or 0, f["name"]))
        detection = ("python-ast for Python files; changed-file (every exported function of a "
                     "changed file) for other languages")

        selected, closure, missing = [], [], [f["name"] for f in changed]
        conformance = ledger = specs = mutation = None
        if functions is not None and changed:
            selected, closure, missing = select_functions(functions, [f["name"] for f in changed])
            ast_path = report_dir / f"ast-{args.module}.json"
            _write_json(ast_path, selected)
            if selected:
                if chain.render(ast_path) and chain.build():
                    conformance = chain.oracle(ast_path, args.cases, args.tests)
                    ledger = chain.ledger()
                    divergences = (conformance or {}).get("divergences")
                    compared = ((conformance or {}).get("coverage") or {}).get("compared", 0)
                    if conformance is None:
                        chain.skip("specs", "the oracle produced no conformance.json")
                    elif divergences:
                        chain.skip("specs", f"the oracle recorded {divergences} divergence(s); "
                                            "synth_specs.py refuses divergent observations")
                    elif not compared:
                        chain.skip("specs", "the oracle compared no function, so there is no observation to prove")
                    else:
                        specs = chain.specs(ast_path, args.cases)
                    proved = (specs or {}).get("proved", 0) if specs else 0
                    if not args.mutants:
                        chain.skip("mutation", "--mutants 0")
                    elif not proved or not (specs or {}).get("build_clean"):
                        chain.skip("mutation", "no proved theorem to gate")
                    else:
                        mutation = chain.mutate(args.mutants)
                else:
                    for name in ("oracle", "ledger", "specs", "mutation"):
                        chain.skip(name, "the rendered module was not type-checked")
            else:
                chain.skip("render", "no changed function is in the exporter's output")
        elif functions is not None:
            chain.skip("render", "no changed function")
        else:
            for name in ("render", "build", "oracle", "ledger", "specs", "mutation"):
                chain.skip(name, "no exporter output")

        results = evidence(changed, selected, conformance, specs, mutation, chain.stages,
                           args.module, exporter)
        report = {
            "schema_version": SCHEMA_VERSION, "tool_version": _tool_version(),
            "generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "module": args.module, "report_dir": str(report_dir),
            "repository": {"path": str(repo), "uri": _origin(repo), "subdir": subdir or "."},
            "base": {"ref": args.base, "commit": base},
            "head": {"ref": args.head, "commit": head},
            "detection": detection, "exporter": exporter,
            "files": detected["files"], "errors": detected["errors"],
            "selection": {"changed": [f["name"] for f in changed], "selected": [f["name"] for f in selected],
                          "closure": closure, "missing": missing},
            "stages": chain.stages,
            "ledger": {k: ledger[k] for k in ("functions", "holes", "holeFree", "holesByLabel")
                       if ledger and k in ledger} if ledger else None,
            "functions": results, "removed": detected["removed"],
            "summary": {level: sum(1 for f in results if f["level"] == level) for level in LEVELS},
        }
        _write_json(report_dir / "pr.json", report)
        if args.sarif:
            document = sarif_document(report)
            problems = validate_sarif(document)
            if problems:
                raise PrError("SARIF output failed validation: " + "; ".join(problems))
            Path(args.sarif).parent.mkdir(parents=True, exist_ok=True)
            Path(args.sarif).write_text(json.dumps(document, indent=1) + "\n")
        if args.markdown:
            Path(args.markdown).parent.mkdir(parents=True, exist_ok=True)
            Path(args.markdown).write_text(markdown_comment(report))
        log(f"==> {len(results)} changed function(s): " +
            ", ".join(f"{level} {n}" for level, n in report["summary"].items() if n) +
            (f"; removed {len(detected['removed'])}" if detected["removed"] else ""))
        for function in results:
            log(f"   {function['level']:<14} {function['name']}: {function['reason']}")
        log(f"==> report: {report_dir / 'pr.json'}")
        return 1 if report["summary"]["refuted"] else 0
    finally:
        if scratch:
            shutil.rmtree(scratch, ignore_errors=True)


def _tool_version():
    try:
        text = (ROOT / "pyproject.toml").read_text()
        match = re.search(r'^version\s*=\s*"([^"]+)"', text, re.M)
        if match:
            return match.group(1)
    except OSError:
        pass
    return "0"


def _origin(repo):
    result = git(repo, "remote", "get-url", "origin", check=False)
    url = result.stdout.strip() if result.returncode == 0 else ""
    return re.sub(r"://[^@/]+@", "://", url) if url else Path(repo).as_uri()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[1],
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("repo", help="a Git checkout (the .git directory is required)")
    parser.add_argument("--base", required=True, help="the commit the change is measured against")
    parser.add_argument("--head", help="the changed commit (default: the working tree, untracked files included)")
    parser.add_argument("--subdir", help="directory inside the repository to analyse")
    parser.add_argument("--module", default="PullRequest",
                        help="Lean module name for the changed functions (default: PullRequest)")
    parser.add_argument("--ast", help="a neutral AST the exporter produced for the head tree; "
                                      "used instead of running Joern, and recorded as such")
    parser.add_argument("--tests", help="a test suite outside the source tree for the oracle (differential.py --tests)")
    parser.add_argument("--cases", type=int, default=int(os.environ.get("AUTOFORM_CASES", "5")),
                        help="random cases per function for the oracle (default: 5)")
    parser.add_argument("--mutants", type=int, default=0,
                        help="mutants for the mutation gate over the proved theorems (default: 0 = skip)")
    parser.add_argument("--stage-timeout", type=float, default=1800,
                        help="seconds each stage may take (default: 1800)")
    parser.add_argument("--out", help="report directory (default: artifacts/pr/<module>)")
    parser.add_argument("--sarif", help="write SARIF 2.1.0 here (one result per changed function)")
    parser.add_argument("--markdown", help="write the review comment here")
    args = parser.parse_args(argv)
    if args.cases < 1 or args.mutants < 0 or args.stage_timeout <= 0:
        parser.error("--cases must be >= 1, --mutants >= 0, --stage-timeout > 0")
    try:
        return run(args)
    except PrError as exc:
        print(f"pr_mode: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
