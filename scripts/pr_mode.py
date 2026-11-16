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
function it exported from a changed file is a candidate (`detection: changed-file`).
When the behaviour stage has exported the base tree (it runs before the head chain for
this reason), the candidates are compared with it per function
(`classify_against_base`): a function whose AST JSON is identical at both revisions is
`unchanged` and dropped, one absent at base is `added`, a base function absent at head is
`removed`, a lone signature change of one `file + class + method` is `modified` with
`signature_change`, and lambdas are matched by body rather than by index (`pr.json`
`change_identity`). The base tree is exported whenever there are such candidates, even
when no runtime can compare them. Without a base export (`--no-behaviour`, or a failed
export) the whole-file over-approximation stands and `change_identity` says why. The
exporter's AST has no positions for exported functions, so these carry no line.

A changed `.rs` file never enters that chain: the exporter has no Rust frontend. When
the repository (or --subdir) at base is a Cargo library, the Rust leg (`rust_regress`,
docs/rust.md "Regressions across commits") compares the crate across the revisions the
way `autoform regress` does, and a public function whose rustdoc span sits on the
changed lines of a changed file is *changed* (`detection: rustdoc`; one only at head is
*added*, one only at base goes to `removed`). A public function on no changed line that
the leg found to behave differently (a private callee changed) is listed too, with a
`change_detail` saying so. The leg's per-function verdict becomes the function's
`behaviour` (below); it has no evidence level.

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
                   `runtime_cases`); no theorem about it was proved. A verdict the
                   oracle replayed from its cache counts (its key binds the model, the
                   cases and the runtime source); `oracle.cached_from` says so
    proved         a theorem about the recorded cases is proved in the kernel
                   (`Autoform/SpecsGen/<M>.lean`, `specs.json`)
    refuted        the model and the runtime disagree on a recorded input
                   (`conformance.json` `divergence_detail`), or a candidate theorem
                   about it was refuted (`specs.json` status `refuted`)

`removed` functions are listed, not levelled. A mutation-gate verdict (`mutation.json`)
is attached to a proved function's theorems and never changes its level.

Behaviour (cross-revision)
--------------------------
Separately from the level, each changed function gets a `behaviour`: the BASE commit's
model run against the HEAD runtime on the same inputs (`run_behaviour`), with a same-base
control that suppresses model noise. A language is compared when the oracle has a
cross-revision backend for it (`runtime_backends.CROSS_REVISION_INPUTS`) and its
toolchain is on PATH: Python (head tests + random cases), Java and Kotlin
(`java_backend`'s seeded random inputs), Go (`go_backend`), JavaScript/TypeScript
(`node_backend`) C where `cc` is present (the native C oracle's seeded typed-boundary inputs to scalar
fixed-width functions of `.c` files) and C++ where `c++` is present (the same oracle's
seeded inputs to free and static member functions on fixed-width integers, called
through C ABI thunks by qualified name), each on inputs built from the base export
alone. Rust is compared only by the Rust leg: when the change touches `.rs` files of a
Cargo library at base, `rust_regress` replays the base revision's Aeneas model cases
and seeded native-only inputs on the head's native harness, with the same control
excluding unstable cases; a function it calls `regression` or `behaviour-change` is
`changed` (with counter-inputs), `unchanged` is `unchanged-on-inputs`, and anything
else (signature changed, not encodable, inconclusive, added at head) is
`not-compared` with the leg's reason. Missing Rust prerequisites name the tools and
leave the changed `.rs` files `not-compared`; when nothing else was analysed the run
exits 2. The language is taken from each function's file extension
(`runtime_backends.LANG_BY_EXT`, refined by `PR_LANGUAGE`: a `.h` is C++ in a C++ corpus
and otherwise neither C nor C++ here); a function
in another language, or one its backend cannot call (an instance method, a
non-primitive or pointer signature), is `not-compared` with the reason. An archived revision has
no installed packages, so the working tree's `node_modules` are linked into it
(`link_installed_dependencies`; `pr.json` `dependencies`).

Exit codes
----------
    0  reported: nothing refuted (and, under --fail-on, the gate had evidence)
    1  at least one function refuted, or, with `--fail-on behaviour-changed`, a changed
       function's behaviour changed
    2  could not run (not a Git repository, unknown ref, no module name, a supported
       source file changed but the exporter produced no AST, the Rust leg's
       prerequisites missing or the leg itself refused with nothing else analysed, ...)
    3  inconclusive, no evidence: `--fail-on behaviour-changed` or `--fail-on
       no-evidence` was given and not one changed non-test function reached behaviour
       `changed` or `unchanged-on-inputs`. The gate compared nothing, so it neither
       passes nor fails the change; the log and the first line of `--markdown` say so.
       Exit 1 and 2 take precedence. Without `--fail-on` this never happens.

A stage that fails or is
skipped is named in the report with its reason and leaves the functions it would have
served at the level below. A change with nothing to analyse (no changed file in a
supported language, or no changed `def` in the changed Python files) exits 0 without
running the exporter; `pr.json` records the reason as the `export` stage's, and every
other stage is skipped with it.

Nothing here reads a CI system's environment: the base, head and output paths are
arguments, so the same command runs under any CI or none (docs/github-action.md, "Other
CI systems").
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
from urllib.parse import quote

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "cartographer"))
import deep_json  # noqa: E402
import regression  # noqa: E402
import source_context  # noqa: E402
from generator_lowering import analysis_functions  # noqa: E402

SCHEMA_VERSION = 1
LEVELS = ("none", "hole", "translated", "oracle-agreed", "proved", "refuted")
RANK = {level: index for index, level in enumerate(LEVELS)}
PYTHON_SUFFIXES = {".py"}
CODE_SUFFIXES = {".py", ".c", ".h", ".cc", ".cpp", ".cxx", ".hpp", ".java", ".go",
                 ".js", ".mjs", ".cjs", ".jsx", ".ts", ".tsx", ".mts", ".cts", ".kt", ".kts"}
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


BEHAVIOUR_RULE = ("autoform/behaviour-changed", "Behaviour changed",
                  "The model of the base revision and the runtime of the head revision disagree on "
                  "a concrete input from the head's tests: the change altered what this function "
                  "does on that input. A behaviour change is not a failure.")
BEHAVIOURS = ("changed", "unchanged-on-inputs", "not-compared")
MAX_COUNTER_INPUTS = 3
ADDED_AT_HEAD = "added at head: it has no base model to compare"
TEST_TOPLEVEL_DIRS = ("tests", "test")
FAIL_ON = ("behaviour-changed", "no-evidence")
EXIT_INCONCLUSIVE = 3
EVIDENCE_BEHAVIOURS = ("changed", "unchanged-on-inputs")
REASON_CAP = 300
TEST_DIRS = {"test", "tests", "__tests__", "androidTest", "testFixtures", "integrationTest"}
TEST_STEM = re.compile(r"^test_|_test$|^Test[A-Z_]|[a-z0-9]Tests?$|\.(?:test|spec)$")
# A function's language is its file extension read through the oracle's own table
# (`runtime_backends.LANG_BY_EXT`); which languages the cross-revision comparison runs, and on
# what inputs, is `runtime_backends.CROSS_REVISION_INPUTS` (`behaviour_toolchain`).


class PrError(ValueError):
    """The run cannot start (exit 2)."""


# --------------------------------------------------------------- reason text

_CLASSPATH = re.compile(r"(?:/[^\s:;'\"\[\],]*[:;])+/[^\s:;'\"\[\],]*")
_ARCHIVE = re.compile(r"[^\s:;'\"\[\],]*\.(?:jar|aar|zip)\b")


def readable(text, cap=REASON_CAP):
    """A reason as one short line a reviewer can read: whitespace collapsed, classpath
    entries (a `:`-separated run of absolute paths, any `.jar`) replaced by
    `<classpath>`, and capped at `cap` characters. A reason that embeds a whole
    dependency classpath tells a reader nothing and buries the cause."""
    text = re.sub(r"\s+", " ", str(text or "")).strip()
    text = _ARCHIVE.sub("<classpath>", _CLASSPATH.sub("<classpath>", text))
    text = re.sub(r"<classpath>(?:[\s,'\"]*<classpath>)+", "<classpath>", text)
    return text if len(text) <= cap else text[:cap - 3].rstrip() + "..."


def _without_dumps(text):
    """A stage-log tail with any printed dict/JSON dump cut off at its opening brace:
    `differential.py` prints `backend_info` as JSON, and that is not a reason."""
    return " | ".join(re.sub(r"\s*[\{\[]['\"].*$", " {...}", part) for part in str(text or "").split(" | "))


def skip_reason(text):
    """The oracle's per-function skip reason (`backend_skipped`), summarized. A Kotlin
    compile failure carries the last 3000 characters of kotlinc's output; the first
    complete `error:` line (file name only) is the cause."""
    text = str(text or "")
    if text.startswith("kotlinc failed"):
        lines = [line.strip() for line in text.splitlines()[1:] + text.splitlines()[:1]]
        errors = [line for line in lines if "error:" in line]
        if errors:
            location, _, message = errors[0].partition("error:")
            location = location.rstrip(": ").rsplit("/", 1)[-1]
            return readable(f"kotlinc failed: {location + ': ' if location else ''}error:{message}")
        return "kotlinc failed"
    return readable(text)


def compile_failure(info, skipped):
    """Why an oracle that had candidates built no case, when compilation is why: javac's
    bucketed `compile_failure_causes`, or kotlinc's first error. None otherwise."""
    candidates = (info.get("primitive_static_candidates") or 0) + \
        (info.get("primitive_instance_candidates") or 0) + (info.get("files_candidate") or 0)
    if not candidates:
        return None
    causes = info.get("compile_failure_causes") or {}
    if causes:
        failed, total = info.get("files_failed"), info.get("files_candidate")
        scope = f" on {failed}/{total} candidate file(s)" if failed is not None and total else ""
        # `compile_kotlin` buckets kotlinc's errors the same way; name the compiler that ran.
        compiler = "kotlinc" if any(k.startswith("kotlin") for k in info) else "javac"
        return f"{compiler} failed{scope}: " + ", ".join(f"{cause} x{n}" for cause, n in causes.items())
    kotlin = next((v for v in skipped.values() if str(v).startswith("kotlinc failed")), None)
    return skip_reason(kotlin) if kotlin else None


def oracle_failure(conformance, name):
    """`<status>: <the function's own skip reason> (<backend>, N cases built)` for a
    function the oracle wrote a `conformance.json` about but did not compare. Built from
    the report's fields, never by printing `backend_info`."""
    info = conformance.get("backend_info") or {}
    skipped = conformance.get("backend_skipped") or {}
    backend = conformance.get("backend") or conformance.get("runtime") or "unknown backend"
    built = info.get("cases_built")
    if not isinstance(built, int):
        built = len(conformance.get("runtime_cases") or [])
    status = str(conformance.get("backend_status") or "")
    if not status or status == "available":
        status = str(conformance.get("status") or "the function was not exercised")
    # `differential.py` appends the backend_info dict after an em dash; drop it.
    status = re.split(r"\s+—\s+", status, maxsplit=1)[0].strip()
    if not built and (not status.startswith("UNSUPPORTED: toolchain")):
        cause = compile_failure(info, skipped)
        if cause:
            # Candidates existed and did not compile: that is the cause, not "no testable
            # surface".
            status = "UNSUPPORTED: " + cause
    own = skip_reason(skipped[name]) if skipped.get(name) else ""
    if own and own in status:
        own = ""
    # Capped short enough that the caller's prefix and the suffix both survive the cap.
    suffix = f" ({backend}, {built} cases built)"
    return readable(f"{status}{': ' + own if own else ''}", cap=REASON_CAP - 80 - len(suffix)) + suffix


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
    raise PrError(f"unknown ref {ref!r} in {repo} (a shallow CI clone may not hold it, and "
                  "fetching it from `origin` failed: fetch more history first, e.g. "
                  "`git fetch --unshallow`, or pass a commit id the clone has)")


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


def _changed_head_lines(before, after):
    """Head line numbers (1-based) an edit touched: every inserted or replaced line, and
    for a pure deletion the head line that follows it (where the removed code ran)."""
    import difflib
    if after is None:
        return set()
    old = (before or b"").decode("utf-8", "replace").splitlines()
    new = after.decode("utf-8", "replace").splitlines()
    lines = set()
    for tag, _, _, j1, j2 in difflib.SequenceMatcher(None, old, new, autojunk=False).get_opcodes():
        if tag in ("replace", "insert"):
            lines.update(range(j1 + 1, j2 + 1))
        elif tag == "delete":
            lines.add(j1 + 1)
    return lines


_STRING_LITERAL = re.compile(r"""(?<![\w\\])(["'])((?:[^"'\\\n]|\\[nt"'\\])*)\1""")


def source_string_literals(text, limit=24):
    """Short string constants spelled in a source file, in order (simple escapes only; a
    Kotlin/TS template with `$` is not a constant and is skipped)."""
    out = []
    for _, body in _STRING_LITERAL.findall(text):
        if "$" in body or len(body) > 64:
            continue
        value = (body.replace("\\n", "\n").replace("\\t", "\t").replace('\\"', '"')
                 .replace("\\'", "'").replace("\\\\", "\\"))
        if value not in out:
            out.append(value)
        if len(out) >= limit:
            break
    return out


def _relative_to_source(path, subdir):
    if not subdir or subdir == ".":
        return path
    prefix = subdir.rstrip("/") + "/"
    return path[len(prefix):] if path.startswith(prefix) else None


def changed_functions(repo, base, head, subdir=None):
    """Which functions a change touched, before any exporter runs.

    Returns `{functions: [...], removed: [...], files: [...], errors: [...]}`. Python
    functions are named and positioned now; other languages are listed by file and
    resolved against the exporter's AST by `select_functions`; a `.rs` file is the Rust
    leg's (`analysed: rust-file`, never the exporter's)."""
    functions, removed, files, errors = [], [], [], []
    for status, path in changed_files(repo, base, head):
        relfile = _relative_to_source(path, subdir)
        suffix = PurePosixPath(path).suffix.lower()
        record = {"path": path, "status": status, "file": relfile,
                  "language": "python" if suffix in PYTHON_SUFFIXES else
                  ("rust" if suffix == ".rs" else
                  ("other" if suffix in CODE_SUFFIXES else "non-code"))}
        files.append(record)
        if relfile is None or record["language"] == "non-code":
            record["analysed"] = False
            continue
        if record["language"] == "rust":
            # Never a Joern `changed-file`: the exporter has no Rust frontend. The Rust
            # leg (`run_rust_leg`) names and compares these functions itself.
            record["analysed"] = "rust-file"
            continue
        if record["language"] != "python":
            record["analysed"] = "changed-file"
            continue
        record["analysed"] = "python-ast"
        before = read_at(repo, base, path) if status != "A" else None
        after = read_at(repo, head, path) if status != "D" else None
        head_lines = _changed_head_lines(before, after)
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
                              "changed_lines": sorted(l for l in head_lines
                                                      if info["start"] <= l <= info["end"]),
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


# parse.log when the default `dataflowOss` overlay, not the frontend, failed.
DATAFLOW_OVERLAY_FAILURE = r"ReachingDefPass|dataflowengineoss"


def export_ast(source, out, log_dir, timeout):
    """`joern-parse` + `export_ast.sc`, exactly as `autoform.sh` stages 1 and 3.

    The frontend gets the arguments `source_context.context` assembles for this tree
    -- the preprocessor configuration (CPP_DEFINES, the compilation database,
    kernel-tree defines), the delombok mode, the over-cap excludes -- the same list
    `autoform.sh` reads from source_context.py's args file, plus `--language` when
    AUTOFORM_FRONTEND forces a frontend (autoform.sh's LANGUAGE_ARGS), so the head and
    base exports parse a C tree's `#ifdef`s the way `autoform source` does; the export
    used to pass only the delombok mode, and a C repository analysed with `autoform pr`
    lost its defines and its compilation database.

    Returns extra fields for the `exporter` record: `frontend_args` (the arguments the
    frontend was given) and `overlays` when the dataflow overlay had to be skipped
    (cartographer/prepare_cpg.sc)."""
    joern = joern_home()
    if not (joern / "joern-parse").exists():
        raise PrError(f"no Joern frontend at {joern / 'joern-parse'} (set JOERN_HOME); "
                      "pass --ast FILE to use an AST the exporter produced earlier")
    try:
        frontend_args = source_context.context(source)["frontend_args"]
    except ValueError as exc:
        # `autoform.sh` refuses here too: a tree whose frontend configuration is broken
        # (a compilation database that does not exist, an AUTOFORM_MAX_FILE_BYTES that
        # is not a number) is never parsed with the configuration silently dropped.
        raise PrError(str(exc)) from None
    # `autoform.sh` passes `--language $AUTOFORM_FRONTEND` before the frontend args
    # (its LANGUAGE_ARGS); a frontend forced for `autoform source` reaches the head and
    # base trees of a pull request too.
    language_args = (["--language", os.environ["AUTOFORM_FRONTEND"]]
                     if os.environ.get("AUTOFORM_FRONTEND") else [])
    env = dict(os.environ, LANG=os.environ.get("LANG") or "C.UTF-8",
               LC_ALL=os.environ.get("LC_ALL") or "C.UTF-8",
               JAVA_TOOL_OPTIONS=(os.environ.get("JAVA_TOOL_OPTIONS", "") + " -Dfile.encoding=UTF-8"))
    if os.environ.get("AUTOFORM_JOERN_XMX"):
        # The heap knob autoform.sh honours (docs/scale.md, "Operating limits").
        env["JAVA_OPTS"] = env.get("JAVA_OPTS", "") + " -Xmx" + os.environ["AUTOFORM_JOERN_XMX"]
    with tempfile.TemporaryDirectory(prefix="autoform-pr-export-") as work:
        cpg = Path(work) / "cpg.bin"
        parse = subprocess.run([str(joern / "joern-parse"), str(source), "--output", str(cpg)]
                               + language_args + frontend_args,
                               cwd=work, env=env, text=True, capture_output=True, timeout=timeout)
        parse_log = parse.stdout + parse.stderr
        (Path(log_dir) / "parse.log").write_text(parse_log)
        overlays = None
        if parse.returncode != 0 and re.search(DATAFLOW_OVERLAY_FAILURE, parse_log):
            # The one failure with a fallback, as in autoform.sh's parse stage: the frontend
            # succeeded and the default dataflowOss overlay crashed after it (real Kotlin).
            overlays = ("dataflowOss skipped: the default joern-parse failed in the dataflow "
                        "overlay; the exporter reads no dataflow")
            raw = Path(work) / "cpg-raw.bin"
            parse_log += f"\nautoform: {overlays}; re-parsing with --nooverlays + cartographer/prepare_cpg.sc\n"
            step = subprocess.run([str(joern / "joern-parse"), str(source), "--nooverlays", "--output", str(raw)]
                                  + language_args + frontend_args,
                                  cwd=work, env=env, text=True, capture_output=True, timeout=timeout)
            parse_log += step.stdout + step.stderr
            if step.returncode == 0:
                step = subprocess.run([str(joern / "joern"), "--script", str(ROOT / "cartographer/prepare_cpg.sc"),
                                       "--param", f"cpgPath={raw}", "--param", f"out={cpg}"],
                                      cwd=work, env=env, text=True, capture_output=True, timeout=timeout)
                parse_log += step.stdout + step.stderr
            (Path(log_dir) / "parse.log").write_text(parse_log)
            if step.returncode != 0 or not re.search(r"^prepared cpg without dataflowOss", step.stdout, re.M):
                raise PrError("joern-parse failed in the dataflow overlay and the no-dataflow fallback "
                              f"failed too (exit {step.returncode}); see parse.log")
        elif parse.returncode != 0:
            raise PrError(f"joern-parse failed (exit {parse.returncode}); see parse.log")
        export = subprocess.run([str(joern / "joern"), "--script", str(ROOT / "cartographer/export_ast.sc"),
                                 "--param", f"cpgPath={cpg}", "--param", f"out={out}",
                                 "--param", f"dataModel={os.environ.get('AUTOFORM_DATA_MODEL', 'lp64')}"],
                                cwd=work, env=env, text=True, capture_output=True, timeout=timeout)
        (Path(log_dir) / "export.log").write_text(export.stdout + export.stderr)
        if export.returncode != 0 or not re.search(r"^exported", export.stdout, re.M):
            raise PrError("export_ast.sc did not report success; see export.log")
    return {"frontend_args": frontend_args, **({"overlays": overlays} if overlays else {})}


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


# ------------------------------------------------- change identity (non-Python)

_SIGNATURE = re.compile(r"(.*):([^:]*\(.*\))")
_LAMBDA_SEGMENT = re.compile(r"[.:]<lambda>\d+")   # `.<lambda>3` (Python, JVM), `:<lambda>0` (JS)


def _fingerprint(record, rename=None):
    """sha256 of a function record's canonical JSON with its `name` left out, walked
    with an explicit stack (a long body is a right-nested `seq` chain deeper than the
    Python stack). A string in `rename` is read as its image, so a reference to a
    renumbered lambda reads as the base's name for it."""
    rename = rename or {}
    digest = hashlib.sha256()
    # `sourceName` of a lambda is `<lambda>N`: an index, not part of what it does.
    pending = [{k: v for k, v in record.items() if k not in ("name", "sourceName")}]
    while pending:
        item = pending.pop()
        if isinstance(item, bytes):
            digest.update(item)
        elif isinstance(item, dict):
            pending.append(b"}")
            for key in sorted(item, reverse=True):
                pending += [item[key], json.dumps(key).encode() + b":"]
            pending.append(b"{")
        elif isinstance(item, list):
            pending.append(b"]")
            pending += reversed(item)
            pending.append(b"[")
        else:
            digest.update(json.dumps(rename.get(item, item) if isinstance(item, str) else item).encode() + b",")
    return digest.hexdigest()


def _method_key(name):
    """`file + class + method`: the exporter's name without its signature suffix
    (`p.C.f:int(int)` -> `p.C.f`), or None when the name carries no signature."""
    match = _SIGNATURE.fullmatch(name)
    return match.group(1) if match else None


def _lambda_owner(name):
    """`p.C.f` for `p.C.f.<lambda>3:...` (nested lambdas included); None for a non-lambda."""
    method = _method_key(name) or name
    match = _LAMBDA_SEGMENT.search(method)
    return method[:match.start()] if match else None


def classify_against_base(changed, files, head_functions, base_functions):
    """Reclassify the `changed-file` candidates (every function the exporter exported from
    a changed non-Python file) against the base tree's export.

    * byte-identical record (the function's AST JSON, name aside) at base and head:
      `unchanged`, dropped from the changed set -- unless it contains a hole, which
      carries none of the source it stands for: then it stays `modified`, with a
      `change_detail` saying so (`counts.identical_but_holed`);
    * a lambda is identified by its body, not its index: a head lambda whose record is
      identical to a base lambda of the same file and enclosing method is unchanged
      whatever either is numbered, and references to it in an enclosing body are read
      under the base's name before that body is compared. A lambda left without an
      identical partner is paired as `modified` (`base_name`) only when it is the one
      unmatched lambda of its method with its signature on both sides;
    * same name at both, different record: `modified`;
    * absent at base, and the only head function that is absent at base with this
      `file + class + method` while exactly one base function with it is absent at head:
      `modified` with `signature_change` (an arity or parameter-type change). Two or
      more candidates on either side are an ambiguity, so no pairing is guessed: they
      stay `added` / `removed`;
    * otherwise absent at base: `added`; a base function absent at head and not paired:
      `removed`;
    * a Kotlin lambda that is `modified` brings back the one named function enclosing it
      when that function is otherwise unchanged (`encloses_changed_lambdas`): the JVM
      cannot call a lambda by name, so it is compared through its enclosing function.

    The exporter's AST carries no source positions for exported functions, so `line`
    stays None (python-ast detection is the only source of lines). Python candidates
    pass through untouched. Returns `{changed, removed, unchanged, renumbered, counts}`."""
    analysed = {r["file"]: r for r in files if r.get("analysed") == "changed-file"}

    def index(functions):
        return {f["name"]: f for f in functions or []
                if isinstance(f.get("name"), str) and f.get("file") in analysed
                and not f["name"].endswith(":<module>")}

    head, base = index(head_functions), index(base_functions)
    verdict, rename, claimed = {}, {}, set()
    # Lambdas first, innermost first, so an enclosing lambda's body is read with its
    # inner lambdas' base names.
    head_lambdas = sorted((n for n in head if _lambda_owner(n) is not None),
                          key=lambda n: (-n.count("<lambda>"), n))
    by_identity = {}
    base_fp = {}
    for depth in sorted({n.count("<lambda>") for n in head_lambdas}, reverse=True):
        for name in [n for n in base if _lambda_owner(n) is not None and n.count("<lambda>") == depth]:
            base_fp[name] = _fingerprint(base[name], None)
            by_identity.setdefault((base[name]["file"], _lambda_owner(name), base_fp[name]), []).append(name)
        level = [n for n in head_lambdas if n.count("<lambda>") == depth]
        fps = {n: _fingerprint(head[n], rename) for n in level}
        for name in level:   # a same-named identical base lambda is preferred
            if name in base and base_fp.get(name) == fps[name] and name not in claimed:
                claimed.add(name)
                verdict[name] = ("unchanged", name)
        for name in level:
            if name in verdict:
                continue
            pool = [b for b in by_identity.get((head[name]["file"], _lambda_owner(name), fps[name]), [])
                    if b not in claimed]
            if pool:
                claimed.add(pool[0])
                verdict[name] = ("unchanged", pool[0])
                rename[name] = pool[0]
        for name in level:
            if name not in verdict and name in base and name not in claimed:
                claimed.add(name)
                verdict[name] = ("modified", name)
        # A lambda both renumbered and edited has no identical partner; it is paired only
        # when it is the one unmatched lambda of its method with this signature on both sides.
        signature = lambda n: _SIGNATURE.fullmatch(n).group(2) if _SIGNATURE.fullmatch(n) else ""
        left_head, left_base = {}, {}
        for name in level:
            if name not in verdict:
                left_head.setdefault((head[name]["file"], _lambda_owner(name), signature(name)), []).append(name)
        for name in base:
            if name not in claimed and _lambda_owner(name) is not None and name.count("<lambda>") == depth:
                left_base.setdefault((base[name]["file"], _lambda_owner(name), signature(name)), []).append(name)
        for key, names in left_head.items():
            if len(names) == 1 and len(left_base.get(key, [])) == 1:
                (old,) = left_base[key]
                claimed.add(old)
                verdict[names[0]] = ("renumbered", old)
                rename[names[0]] = old
    for name in head:
        if name in verdict or name not in base or name in claimed:
            continue
        claimed.add(name)
        same = _fingerprint(head[name], rename) == _fingerprint(base[name], None)
        verdict[name] = ("unchanged" if same else "modified", name)
    # Signature changes: one unmatched head function, one unmatched base function, same key.
    keyed_head, keyed_base = {}, {}
    for name in head:
        if name not in verdict and _method_key(name) and _lambda_owner(name) is None:
            keyed_head.setdefault((head[name]["file"], _method_key(name)), []).append(name)
    for name in base:
        if name not in claimed and _method_key(name) and _lambda_owner(name) is None:
            keyed_base.setdefault((base[name]["file"], _method_key(name)), []).append(name)
    for key, names in keyed_head.items():
        if len(names) == 1 and len(keyed_base.get(key, [])) == 1:
            (old,) = keyed_base[key]
            claimed.add(old)
            verdict[names[0]] = ("signature", old)
    for name in head:
        verdict.setdefault(name, ("added", None))
    # A hole stands for source the exporter did not translate and carries none of it, so
    # two revisions that differ only inside a hole export the same record (measured on a
    # TypeScript package: a reordered object spread, `op:spread`, and an edited template
    # literal, `op:formatString`, were both identical to the base export and dropped).
    # Identical up to its holes is not evidence of no edit: such a function stays changed.
    for name, (kind, other) in list(verdict.items()):
        if kind == "unchanged" and regression.function_holes(head[name]):
            verdict[name] = ("holed", other)

    out, unchanged, counts = [], [], {"unchanged": 0, "modified": 0, "added": 0,
                                      "signature_changed": 0, "removed": 0,
                                      "identical_but_holed": 0, "renumbered_lambdas": len(rename)}
    for function in changed:
        if function.get("detection") != "changed-file" or function["name"] not in verdict:
            out.append(function)
            continue
        kind, other = verdict[function["name"]]
        if kind == "unchanged":
            unchanged.append(function["name"])
            counts["unchanged"] += 1
            continue
        record = dict(function, change="added" if kind == "added" else "modified")
        if kind == "signature":
            record.update(base_name=other, signature_change={"base": other},
                          change_detail=f"signature changed (base: {other})")
            counts["signature_changed"] += 1
        elif kind == "renumbered":
            record.update(base_name=other, change_detail=f"lambda renumbered and edited (base: {other})")
            counts["modified"] += 1
        elif kind == "holed":
            labels = ", ".join(sorted(set(regression.function_holes(head[function["name"]]))))
            record.update(change_detail=f"identical to the base export except inside its holes ({labels}), "
                                        "which carry no source, so not provably unchanged",
                          identical_but_holed=True)
            if other != function["name"]:
                record["base_name"] = other
            counts["identical_but_holed"] += 1
        else:
            counts[kind] += 1
        out.append(record)
    # A Kotlin lambda is compiled to a synthetic method that no source name calls, so the
    # JVM oracle cannot call it ("lambda: not callable by name"). An edit inside one is
    # compared through the named function that encloses it: that function runs the
    # lambda, so its behaviour is the lambda's in context. Selection only: an enclosing
    # function identical at both revisions (it refers to the lambda by name) is put back
    # into the changed set as a gate subject, saying why; nothing else changes.
    owners = {}
    for record in out:
        if (record.get("change") == "modified" and record.get("detection") == "changed-file"
                and str(record.get("file", "")).endswith((".kt", ".kts")) and _lambda_owner(record["name"])):
            owners.setdefault(_lambda_owner(record["name"]), []).append(record["name"])
    for owner, lambdas in sorted(owners.items()):
        named = [n for n in head if _method_key(n) == owner and _lambda_owner(n) is None]
        if len(named) != 1 or named[0] not in unchanged:
            continue
        source = next((f for f in changed if f["name"] == named[0]), None)
        if source is None:
            continue
        unchanged.remove(named[0])
        counts["unchanged"] -= 1
        counts["modified"] += 1
        out.append(dict(source, change="modified", encloses_changed_lambdas=sorted(lambdas),
                        change_detail="identical to the base export, compared for the changed lambda(s) "
                                      "it encloses, which are not callable by name: "
                                      + ", ".join(sorted(lambdas))))
    removed = []
    for name in sorted(set(base) - claimed):
        record = analysed[base[name]["file"]]
        removed.append({"name": name, "path": record["path"], "file": record["file"], "change": "removed",
                        "detection": "changed-file", "language": source_language(record["file"])})
    counts["removed"] = len(removed)
    for record in analysed.values():
        names = [n for n in head if head[n]["file"] == record["file"]]
        if names and all(verdict[n][0] == "unchanged" for n in names) and not any(
                r["file"] == record["file"] for r in removed):
            record["note"] = ("every exported function is identical to the base export "
                              "(the edit is outside every function body)")
    return {"changed": out, "removed": removed, "unchanged": sorted(unchanged),
            "renumbered": dict(sorted(rename.items())), "counts": counts}


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

    def __init__(self, root, report, module, source, python, timeout, log, oracle_env=None):
        self.root, self.report, self.module = Path(root), Path(report), module
        self.source, self.python, self.timeout, self.log = Path(source), python, timeout, log
        self.stages = {}
        self.env = dict(os.environ)
        # The oracle's interpreter and pytest settings (`oracle_settings`); differential.py
        # reads them, re-executes itself under the interpreter and records both.
        self.env.update(oracle_env or {})
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
            record["reason"] = readable(_without_dumps(f"exit {record.get('exit_code')}: " + " | ".join(tail)),
                                        cap=400)
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
        command += getattr(self, "oracle_extra", [])
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
        # A verdict the oracle replayed from its cache (`compared: cached from <time>`) is
        # about byte-identical inputs: the same model (function, rendering, callees, module
        # bodies, semantics, renderer, harness, toolchain), the same recorded cases and the
        # same runtime source and version (`oracle_cache.py`; a verdict from another
        # revision of the function's source misses). It counts as compared; the record
        # says it was replayed and when it was computed.
        cached_from = None
        if isinstance(status, str) and status.startswith("compared: cached from "):
            cached_from = status[len("compared: cached from "):]
            status = "compared"
            record["oracle"]["cached_from"] = cached_from
        if name in divergences:
            record.update(level="refuted",
                          reason=f"the model and the runtime disagree on {len(divergences[name])} "
                                 "recorded input(s)")
            record["artifacts"].append({"kind": "divergence", "path": "conformance.json",
                                        "divergence_detail": divergences[name]})
            continue
        if status != "compared" or record["oracle"]["agree"] == 0:
            oracle_stage = stages.get("oracle", {})
            if status:
                why = status
            elif conformance is not None:
                why = oracle_failure(conformance, name)
            else:
                why = _without_dumps(oracle_stage.get("reason", "the oracle did not run"))
            record["reason"] = f"type-checked; not adjudicated by the oracle: {why}"
            continue
        replayed = (f" (verdicts replayed from the oracle cache, computed {cached_from} on "
                    "byte-identical model, cases and runtime source)" if cached_from else "")
        record.update(level="oracle-agreed",
                      reason=f"{record['oracle']['agree']} recorded case(s) agreed with the runtime"
                             + replayed)
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
                                 + f" ({record['oracle']['agree']} recorded case(s){replayed})")
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
    for record in results:
        record["reason"] = readable(record["reason"])
    return results



# ------------------------------------------------------ behaviour (cross-revision)

def _show(value, heap, depth=0):
    """A recorded oracle value as short text."""
    if not isinstance(value, list) or not value:
        return repr(value)
    tag = value[0]
    if tag == "ref" and len(value) > 1 and isinstance(value[1], int) and depth < 2 \
            and 0 <= value[1] < len(heap or []):
        entry = heap[value[1]]
        if isinstance(entry, list) and len(entry) >= 2 and isinstance(entry[1], list) and entry[1] \
                and all(isinstance(f, list) and f and isinstance(f[0], str) for f in entry[1]):
            cls = str(entry[0]).rsplit(".", 1)[-1]
            fields = ", ".join(f"{re.sub(r'^_[A-Za-z0-9]+__', '', f[0]).lstrip('_')}={_show(f[1], heap, depth + 1)}"
                               for f in entry[1] if len(f) > 1)
            return f"{cls}{{{fields}}}"
        return f"{entry[0] if isinstance(entry, list) and entry else 'object'}"
    if tag == "fn":
        return str(value[1]).rsplit(".", 1)[-1] if len(value) > 1 else "fn"
    if tag == "unit":
        return "unit"
    return f"{tag} {', '.join(_show(v, heap, depth + 1) for v in value[1:])}".strip()


def _model_result(text):
    """`Autoform.Core.EResult.val (Autoform.Core.Val.unit)` as 'returns unit'."""
    text = re.sub(r"Autoform\.Core\.", "", str(text or ""))
    match = re.fullmatch(r"EResult\.val \(?Val\.(.*?)\)?", text)
    if match:
        inner = match.group(1)
        return "returns " + (inner if inner else "a value")
    match = re.fullmatch(r"EResult\.exn \(?(.*?)\)?", text)
    if match:
        return "raises " + match.group(1)
    return text or "unknown"


def _runtime_result(outcome):
    if isinstance(outcome, list) and outcome and outcome[0] == "exn":
        return "raises " + str(outcome[1] if len(outcome) > 1 else "?")
    if isinstance(outcome, list) and outcome and outcome[0] == "val":
        return "returns " + _show(outcome[1] if len(outcome) > 1 else ["unit"], [])
    return "unknown"


def _row_key(row):
    return (row.get("function"), row.get("args"), row.get("detail"), row.get("lean_repr"),
            json.dumps((row.get("observation") or {}).get("outcome")))


def _counter_input(row):
    observation = row.get("observation") or {}
    heap = observation.get("heap") or (row.get("case") or {}).get("heap") or []
    receiver = observation.get("self") or (row.get("case") or {}).get("self")
    name = str(row.get("function", ""))
    # Python `m.py:<module>.C.f` -> `C.f`; JS/TS `m.ts::program:C:f` -> `C.f`;
    # JVM `pkg.Cls.f:int(int)` -> `Cls.f`.
    short = name.split(":<module>.")[-1] if ":<module>." in name else \
        name.split("::program:")[-1].replace(":", ".") if "::program:" in name else \
        ".".join(name.split(":", 1)[0].rsplit(".", 2)[-2:])
    return {"call": f"{short}{row.get('args', '()')}",
            "receiver": _show(receiver, heap) if receiver else None,
            "base_model": _model_result(row.get("lean_repr")),
            "head_runtime": _runtime_result(observation.get("outcome")),
            "detail": row.get("detail"), "origin": row.get("origin")}


def behaviour_results(changed, cross, control, notes):
    """`behaviour` per changed function from the cross-revision `conformance.json`
    (`cross`: base model, head runtime) and, when there were divergences, the same-base
    control (`control`: base model, base runtime, the same inputs).

    A divergence that the control also records (same function, inputs, detail, both
    results) is model noise, not a revision difference: it is removed from `changed` and
    counted in `suppressed_as_model_noise`, per function and in total. Nothing else is
    dropped. `notes` maps a function name to a reason it was not compared at all."""
    out, suppressed_total = {}, 0
    cases = {}
    for case in (cross or {}).get("runtime_cases") or []:
        bucket = cases.setdefault(case.get("name"), {"agree": 0, "diverge": 0, "inconclusive": 0})
        comparison = case.get("comparison")
        bucket["agree" if comparison == "agree" else "diverge" if comparison == "diverge"
               else "inconclusive"] += 1
    control_rows = {}
    for row in (control or {}).get("divergence_detail") or []:
        control_rows[_row_key(row)] = control_rows.get(_row_key(row), 0) + 1
    rows = {}
    for row in (cross or {}).get("divergence_detail") or []:
        rows.setdefault(row.get("function"), []).append(row)
    status = ((cross or {}).get("coverage") or {}).get("by_status") or {}
    for function in changed:
        name = function["name"]
        if name in notes:
            out[name] = {"status": "not-compared", "reason": notes[name], "compared": 0,
                         "counter_inputs": [], "suppressed_as_model_noise": 0}
            continue
        count = cases.get(name, {"agree": 0, "diverge": 0, "inconclusive": 0})
        real, noise = [], 0
        for row in rows.get(name, []):
            key = _row_key(row)
            if control_rows.get(key, 0) > 0:
                control_rows[key] -= 1
                noise += 1
            else:
                real.append(row)
        suppressed_total += noise
        base = {"compared": count["agree"] + len(real), "agree": count["agree"],
                "inconclusive": count["inconclusive"], "suppressed_as_model_noise": noise}
        if real:
            shown, seen = [], set()
            # One counter-input per distinct call and outcome, the shortest calls first:
            # the smallest input that shows the change is the one a reviewer can read.
            for r in sorted(real, key=lambda r: len(str(r.get("args", "")))):
                item = _counter_input(r)
                key = (item["call"], item.get("receiver"), item["base_model"], item["head_runtime"])
                if key not in seen and len(shown) < MAX_COUNTER_INPUTS:
                    seen.add(key)
                    shown.append(item)
            out[name] = dict(base, status="changed", counter_inputs=shown, diverging=len(real),
                reason=f"{len(real)} input(s) where the base model and the head runtime disagree")
        elif count["agree"]:
            coverage = ((cross or {}).get("change_coverage") or {}).get(name) or {}
            reached = coverage.get("covered")
            out[name] = dict(base, status="unchanged-on-inputs", counter_inputs=[],
                             reason=f"{count['agree']} case(s) compared, all agreed; this is not a proof "
                                    "of equivalence on other inputs"
                                    + (f"; {noise} divergent case(s) suppressed as model noise" if noise else "")
                                    + (f"; branch coverage: the inputs did not reach the change "
                                       f"({coverage.get('note')})" if reached is False else
                                       "; branch coverage: every changed statement and branch outcome "
                                       "was executed by a compared input" if reached else ""))
            if coverage:
                out[name]["change_coverage"] = coverage
                out[name]["change_covered"] = reached
        else:
            # A function the runtime backend would not call (the JVM oracle: an instance
            # method, a non-primitive signature, a file javac refused) keeps its reason.
            skipped = ((cross or {}).get("backend_skipped") or {}).get(name)
            # With no case kept the oracle writes no per-function status; a module that
            # failed to import is still named, with its exception (`import_errors`).
            import_error = ((cross or {}).get("import_errors") or {}).get(name.split(":<module>")[0])
            if not status.get(name) and import_error:
                status = dict(status, **{name: "module failed to import: " + import_error})
            why = (f"all {noise} divergent case(s) also diverge in the same-base control "
                   "(model noise), none was left to compare" if noise else
                   f"the oracle did not call it: {skip_reason(skipped)}" if skipped else
                   f"no case was compared ({count['inconclusive']} inconclusive; oracle status: "
                   f"{status.get(name) or 'function not exercised'})")
            out[name] = dict(base, status="not-compared", counter_inputs=[], reason=why)
    for record in out.values():
        record["reason"] = readable(_without_dumps(record["reason"]))
    return out, suppressed_total


def _is_test_path(rel):
    top = PurePosixPath(rel).parts
    return bool(top) and (top[0] in TEST_TOPLEVEL_DIRS or
                          (len(top) == 1 and (top[0].startswith("test_") or top[0] == "conftest.py")))


def build_hybrid(base_source, head_source):
    """Base library with the head's tests overlaid: the tests (top-level `tests/`,
    `test/`, `test_*.py`, `conftest.py`) are replaced by the head's, so inputs and the
    callables they build (a test's `lambda`) exist in the model. Returns the overlaid
    relative paths."""
    base_source, head_source = Path(base_source), Path(head_source)
    overlaid = []
    for entry in sorted(base_source.iterdir()):
        if _is_test_path(entry.name):
            shutil.rmtree(entry) if entry.is_dir() else entry.unlink()
    for entry in sorted(head_source.iterdir()):
        if _is_test_path(entry.name) and entry.name != ".git":
            if entry.is_dir():
                shutil.copytree(entry, base_source / entry.name,
                                ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
            else:
                shutil.copy2(entry, base_source / entry.name)
            overlaid.append(entry.name)
    return overlaid


def _native_c():
    """`scripts/native_c.py`, imported on first use (for `cpp_corpus`)."""
    import native_c
    return native_c


def _backends():
    """`scripts/runtime_backends.py`: its language tables are the ones the oracle itself
    routes by (`differential.py` binds them), so pr mode cannot drift from them. Imported
    on first use; `differential.py` itself is never imported (it re-executes on import)."""
    import runtime_backends
    return runtime_backends


_UNWALKED = {".git", "node_modules", ".lake", ".venv", "__pycache__"}


def link_installed_dependencies(repo, tree):
    """Link the working tree's installed Node packages into `tree`, a `git archive` of one
    revision, at the same relative paths, and return what was linked.

    `node_modules` is not committed, so an archive has none and every module that imports
    a package fails to load (the runtime backends resolve `node_modules` in the tree they
    are given and its ancestors: `runtime_backends.copy_sources`). The packages are the
    ones installed in the working tree, i.e. those of the checked-out revision; the report
    names each link. When the repository root has none, the nearest `node_modules` above
    it is linked at the archive's root, as Node would reach it past the checkout."""
    repo, tree = Path(repo).resolve(), Path(tree)
    linked = []
    for current, dirs, _ in os.walk(repo):
        if "node_modules" in dirs:
            installed = Path(current) / "node_modules"
            rel = installed.relative_to(repo)
            target = tree / rel
            if target.parent.is_dir() and not os.path.lexists(target):
                target.symlink_to(installed, target_is_directory=True)
                linked.append(rel.as_posix())
        dirs[:] = sorted(d for d in dirs if d not in _UNWALKED)
    if not os.path.lexists(tree / "node_modules"):
        for ancestor in repo.parents:
            if (ancestor / "node_modules").is_dir():
                (tree / "node_modules").symlink_to(ancestor / "node_modules", target_is_directory=True)
                linked.append(str(ancestor / "node_modules"))
                break
    return linked


# The oracle maps every C-family extension to its `c` runtime (`native_c` tells C++ units
# apart itself), but pr mode routes C and C++ as two rows of
# `runtime_backends.CROSS_REVISION_INPUTS`: `c` covers `.c` translation units, `cpp` the C++
# sources (C ABI thunks by qualified name, needs `c++`). A `.h` is shared by C and C++: it is
# `cpp` in a C++ corpus (`native_c.cpp_corpus`, see `function_language`) and otherwise a
# pr-only `c-header` label, `not-compared` with a reason, because the native C oracle calls
# only functions defined in a `.c` unit.
PR_LANGUAGE = {".h": "c-header", ".cpp": "cpp", ".cc": "cpp", ".cxx": "cpp",
               ".hh": "cpp", ".hpp": "cpp", ".hxx": "cpp"}


def source_language(path):
    """The oracle's language for a file's extension (`python`, `java`, `kotlin`, `go`,
    `js`, `ts`, `c` for `.c`, ...); `cpp` for C++ sources and `c-header` for `.h`
    (`PR_LANGUAGE`); `other` for an extension the oracle does not map."""
    suffix = PurePosixPath(path or "").suffix.lower()
    if suffix in PR_LANGUAGE:
        return PR_LANGUAGE[suffix]
    return _backends().LANG_BY_EXT.get(suffix, "other")


def function_language(f, cpp_headers=False):
    """`source_language` of a changed function's file, except that a `.h` header is
    `cpp` when the corpus is C++ (`cpp_headers`); in any other corpus it is unchanged."""
    path = f.get("file") or f.get("path")
    if cpp_headers and PurePosixPath(path or "").suffix == ".h":
        return "cpp"
    return source_language(path)


def behaviour_toolchain(language):
    """None when the cross-revision oracle can run `language` here, else the reason not:
    the language needs a backend in `runtime_backends.CROSS_REVISION_INPUTS` and its
    toolchain on PATH (`runtime_backends.cross_revision_unavailable`)."""
    if language == "c-header":
        return ("C/C++ header function: a `.h` is shared by C and C++, and in a C corpus "
                "the native C oracle calls only functions defined in a `.c` unit")
    return _backends().cross_revision_unavailable(language)




def behaviour_plan(changed, cpp_headers=False):
    """`(language, notes)`: the one language the cross-revision run compares (the oracle
    runs one runtime per base export) and, for every changed function it will not
    compare, why. The language comes from each function's file extension
    (`function_language`)."""
    notes, by_language = {}, {}
    for f in changed:
        language = function_language(f, cpp_headers)
        why = behaviour_toolchain(language)
        if why:
            notes[f["name"]] = why
        else:
            by_language.setdefault(language, []).append(f["name"])
    if not by_language:
        return None, notes
    language = max(sorted(by_language), key=lambda k: len(by_language[k]))
    for other, names in by_language.items():
        if other != language:
            for name in names:
                notes[name] = (f"{other} function: the cross-revision oracle runs one language "
                               f"per change and this one compared {language}")
    return language, notes


def _compared_languages(changed, results, cpp_headers=False):
    return sorted({function_language(f, cpp_headers) for f in changed
                   if (results.get(f["name"]) or {}).get("status") in ("changed", "unchanged-on-inputs")})


def run_behaviour(repo, base, head_source, subdir, changed, module, report_dir, cases,
                  tests, python, timeout, log, refine=None, oracle_env=None, head_functions=None):
    """The cross-revision oracle. Returns `(behaviour, stages, summary)`; never raises
    for a failed stage (the reason becomes `not-compared`).

    `refine`, when given, is called with the base export once it is loaded and returns
    the changed set to compare instead (`classify_against_base`: a function identical at
    both revisions is not compared, an added one has no base model).

    Python: base model (head tests overlaid, `plain_class_values.py` applied) against the
    head runtime on the head tests' inputs and random cases. Every other language with a
    backend in `runtime_backends.CROSS_REVISION_INPUTS` (Java, Kotlin, Go, JavaScript,
    TypeScript, C, C++): base model against the head runtime on the inputs that backend builds
    from the base export alone, so they are the same at both revisions; no test overlay,
    no PYTHONPATH. A function the backend cannot call keeps the backend's own reason
    (`backend_skipped`). C runs the native C oracle's seeded typed-boundary inputs on
    scalar fixed-width entry points of the head tree's `.c` units (`native_c`), and C++
    the same oracle's inputs on free and static member functions through C ABI thunks
    named by qualified name (a header is a unit of its own in a C++ corpus); a case
    the model leaves as a hole (undefined behaviour) is inconclusive, never a
    divergence. `languages` in the summary lists the languages of the functions
    actually compared.

    When no changed function is in a language compared here but `refine` is given, the
    base tree is still exported, for change identity alone."""
    stages = {}
    cpp_headers = any(PurePosixPath(f.get("file") or f.get("path") or "").suffix == ".h"
                      for f in changed) and _native_c().cpp_corpus(head_source)
    language, notes = behaviour_plan(changed, cpp_headers)
    no_language = "no changed function in a language the cross-revision oracle runs here"
    if language is None and refine is None:
        return (behaviour_results(changed, None, None, notes)[0],
                {"behaviour": {"status": "skipped", "reason": no_language}},
                {"suppressed_as_model_noise": 0, "languages": []})
    python_leg = language == "python"
    if not python_leg:
        tests = None   # every other backend builds its own inputs; it reads no test suite
    work = Path(tempfile.mkdtemp(prefix="autoform-pr-base-"))
    behaviour_dir = Path(report_dir) / "behaviour"
    (behaviour_dir / "cross").mkdir(parents=True, exist_ok=True)
    (behaviour_dir / "control").mkdir(parents=True, exist_ok=True)
    base_module = module + "Base"

    def finish(reason):
        stages["behaviour"] = {"status": "failed", "reason": reason}
        log(f"   !! behaviour: {reason}")
        merged = dict(notes)
        for f in changed:
            merged.setdefault(f["name"], reason)
        return behaviour_results(changed, None, None, merged)[0], stages, \
            {"suppressed_as_model_noise": 0, "languages": []}

    try:
        archive = git(repo, "archive", "--format=tar", base, binary=True)
        subprocess.run(["tar", "-x", "-C", str(work)], input=archive.stdout, check=True)
        base_source = work / subdir if subdir else work
        # Only the Python leg reads tests, so only it has anything to overlay.
        overlaid = build_hybrid(base_source, head_source) if python_leg else []
        start = time.monotonic()
        raw, ast_full = behaviour_dir / "raw.json", behaviour_dir / f"ast-{base_module}.full.json"
        try:
            # The same export as the head's, so the base tree is parsed with the base
            # tree's own frontend configuration (an archived base's compile_commands.json
            # may honestly differ from the head's); what that export reports about the
            # configuration it used is recorded in the stage below.
            base_export = export_ast(base_source, raw, behaviour_dir, timeout)
        except (PrError, subprocess.TimeoutExpired) as exc:
            return finish(f"base export unavailable: {exc}")
        if language is None:
            shutil.copy(raw, ast_full)
            note = "base source as committed, exported for change identity only"
        elif not python_leg:
            # plain_class_values.py models Python class-body attributes; nothing to do.
            shutil.copy(raw, ast_full)
            note = (f"base source as committed ({language}: no test overlay; "
                    f"{_backends().CROSS_REVISION_INPUTS[language]})")
        else:
            result = subprocess.run([python, str(ROOT / "cartographer/plain_class_values.py"),
                                     str(raw), str(base_source), str(ast_full)],
                                    capture_output=True, text=True)
            if result.returncode != 0:
                return finish("plain_class_values.py failed: " + (result.stderr.strip()[-300:] or "?"))
            note = ("base library + head tests (overlaid: " + ", ".join(overlaid or ["none"])
                    + "); plain_class_values applied")
        # The base export's own record -- the frontend arguments it used, any skipped
        # overlay -- joins the stage; a stub in its place (the offline tests) records nothing.
        stages["behaviour-export"] = {"status": "passed", "seconds": round(time.monotonic() - start, 2),
                                      "note": note,
                                      **(base_export if isinstance(base_export, dict) else {}),
                                      "sha256": hashlib.sha256(ast_full.read_bytes()).hexdigest()}
        functions = deep_json.load(ast_full)
        if isinstance(functions, dict):
            functions = functions.get("functions", [])
        if refine is not None:
            changed = refine(functions)
            kept = {f["name"] for f in changed}
            notes = {n: v for n, v in notes.items() if n in kept}
            if not changed:
                stages["behaviour"] = {"status": "skipped", "reason":
                                       "every changed-file function is identical to the base export"}
                return {}, stages, {"suppressed_as_model_noise": 0, "languages": []}
        if language is None:
            stages["behaviour"] = {"status": "skipped", "reason": no_language}
            return (behaviour_results(changed, None, None, notes)[0], stages,
                    {"suppressed_as_model_noise": 0, "languages": []})
        # Installed packages are not in a `git archive`: give the base tree the working
        # tree's (after its export, so the exporter never walks them).
        linked = link_installed_dependencies(repo, work)
        if linked:
            stages["behaviour-export"]["dependencies"] = linked
        compared = [f for f in changed if f["name"] not in notes]
        selected, closure, missing = select_functions(functions, [f["name"] for f in compared])
        for name in missing:
            function = next((f for f in changed if f["name"] == name), {})
            notes.setdefault(name, ADDED_AT_HEAD
                             if function.get("change") == "added" else
                             f"{function['change_detail']}: the cross-revision oracle pairs the revisions "
                             "by full name, so there is no base model under the head's name"
                             if function.get("base_name") else
                             "the exporter did not export it from the base tree")
        for f in compared:
            if f["change"] == "added" or (python_leg and _is_test_path(f["file"])):
                notes.setdefault(f["name"], ADDED_AT_HEAD if f["change"] == "added"
                                 else "test code: its model is the head's own file")
        if not selected:
            return finish("no changed function is in the base export")
        # Python: the model is the WHOLE base export, not the cut `select_functions` makes
        # for the head chain: a receiver the oracle records holds callables (a test's
        # `getsizeof=lambda ...`) that must exist in the model to be encoded, and with the
        # cut every such case was refused (measured on cachetools: 0 cases for
        # `Cache.__setitem__`). The report is still restricted to the changed functions.
        #
        # Every other backend builds its inputs and receivers from the signature, the
        # JVM/Node/native runtime and the static values the runtime reports, never from a
        # recorded object graph, so the model needs only what the compared functions can
        # reach: the functions of their files (constructors, enums, companions, statics)
        # and everything those call (`select_functions`), the same cut the head chain
        # type-checks. The whole export is still handed to the oracle (`--universe`) for
        # name resolution and literal mining, so the inputs do not change. A call out of
        # the cut is an unresolved call, i.e. a hole: inconclusive, never a verdict.
        # Measured on a 7,384-function Java base export comparing 1 function: the base
        # model build went from 386 s (render 2.3 s) to 6.3 s (0.1 s), the verdict unchanged.
        ast_path = behaviour_dir / f"ast-{base_module}.json"
        compared_names = {f["name"] for f in compared if f["name"] not in notes}
        if python_leg:
            shutil.copy(ast_full, ast_path)
            model_scope = f"whole base export ({len(functions)} functions)"
        else:
            files = {f.get("file") for f in functions if f.get("name") in compared_names}
            roots = [f["name"] for f in functions
                     if isinstance(f.get("name"), str) and f.get("file") in files]
            cut, _, _ = select_functions(functions, roots)
            _write_json(ast_path, cut)
            model_scope = (f"{len(cut)} of {len(functions)} base functions: the compared "
                           f"functions' {len(files)} file(s) and their callees")
        stages["behaviour-export"]["model"] = model_scope
        cross = Chain(ROOT, behaviour_dir / "cross", base_module, head_source, python, timeout, log,
                      oracle_env)
        ok = cross.render(ast_path) and cross.build()
        stages.update({f"behaviour-{k}": v for k, v in cross.stages.items()})
        if not ok:
            return finish("the base model did not render/type-check: " +
                          "; ".join(v.get("reason", "") for v in cross.stages.values() if v.get("reason")))
        # Cross-revision: base model, head runtime (and head tests, for Python); --no-cache
        # so a cached verdict of another revision is never replayed. The runtime root is
        # the head checkout (the control's, the base checkout): java_backend reads
        # `f["file"]` relative to it, and the base export names files relative to the
        # base checkout, which has the same layout.
        focus_file = behaviour_dir / "focus.json"
        focus_file.write_text(json.dumps(sorted(f["name"] for f in compared
                                                if f["name"] not in notes)))
        extra = ["--no-cache", "--focus", str(focus_file), "--literal-inputs"]
        if not python_leg:
            extra += ["--universe", str(ast_full)]
        # The head revision's literals of each compared function join its base literals,
        # in one file both the cross run and the control read, so they draw the same inputs.
        head_literals = {}
        for f in head_functions or ():
            if isinstance(f, dict) and f.get("name") in compared_names:
                strings, _ = _backends().mined_literals(f)
                if strings:
                    head_literals[f["name"]] = strings
        # ... and the string constants of its source file at both revisions: a Java/Kotlin
        # `static final String` or a TS `const` is a field initializer, not in any exported
        # body, and is exactly what such a function compares its argument with.
        for f in compared:
            if f["name"] not in compared_names or not f.get("file"):
                continue
            found = []
            for tree in (base_source, Path(head_source)):
                try:
                    found += source_string_literals((tree / f["file"]).read_text(errors="replace"))
                except OSError:
                    pass
            merged = list(dict.fromkeys(head_literals.get(f["name"], []) + found))
            if merged:
                head_literals[f["name"]] = merged
        if head_literals:
            literals_file = behaviour_dir / "head-literals.json"
            literals_file.write_text(json.dumps(head_literals, indent=1, sort_keys=True))
            extra += ["--literals", str(literals_file)]
        changed_lines = {}
        for f in compared:
            if python_leg and f["name"] in compared_names and f.get("changed_lines"):
                changed_lines.setdefault(f["file"], set()).update(f["changed_lines"])
        coverage_extra = []
        if changed_lines:
            lines_file = behaviour_dir / "changed-lines.json"
            lines_file.write_text(json.dumps({k: sorted(v) for k, v in sorted(changed_lines.items())}))
            coverage_extra = ["--changed-lines", str(lines_file)]
        if python_leg and (Path(head_source) / "src").is_dir():
            # `src/` layout: put it first on the import path so the runtime under test is
            # the head checkout, not a copy of the package installed in this interpreter.
            cross.env["PYTHONPATH"] = os.pathsep.join(
                [str(Path(head_source) / "src")] + ([cross.env["PYTHONPATH"]] if cross.env.get("PYTHONPATH") else []))
        cross.oracle_extra = extra + coverage_extra
        cross_conf = cross.oracle(ast_path, cases, tests)
        stages["behaviour-oracle"] = cross.stages.get("oracle", {})
        # A killed oracle is a timeout, not a missing report: say which, per function.
        timed_out = str(stages["behaviour-oracle"].get("reason", ""))
        if timed_out.startswith("timed out"):
            return finish(f"the cross-revision oracle {timed_out}")
        if cross_conf is None:
            return finish("the cross-revision oracle produced no conformance.json")
        control_conf = None
        if cross_conf.get("divergences"):
            control = Chain(ROOT, behaviour_dir / "control", base_module, base_source, python, timeout, log,
                            oracle_env)
            control.oracle_extra = extra
            if python_leg and (base_source / "src").is_dir():
                control.env["PYTHONPATH"] = str(base_source / "src")
            control_conf = control.oracle(ast_path, cases, tests)
            stages["behaviour-control"] = control.stages.get("oracle", {})
            if control_conf is None:
                stages["behaviour-control"]["note"] = "no control: divergences are NOT filtered"
        results, suppressed = behaviour_results(changed, cross_conf, control_conf, notes)
        stages["behaviour"] = {"status": "passed", "note":
                               f"{len(functions)} function(s) in the base module ({language}); "
                               f"suppressed-as-model-noise: {suppressed}"}
        return results, stages, {"suppressed_as_model_noise": suppressed,
                                 "languages": _compared_languages(changed, results, cpp_headers),
                                 "control": "run" if control_conf is not None else
                                            ("not needed: no divergence" if not cross_conf.get("divergences")
                                             else "unavailable"),
                                 "model": f"base {base[:12]}" + (" + head tests" if python_leg else ""),
                                 "runtime": "head",
                                 "inputs": _backends().CROSS_REVISION_INPUTS[language],
                                 "cases_per_function": cases}
    except (subprocess.CalledProcessError, OSError, PrError) as exc:
        return finish(f"{type(exc).__name__}: {exc}")
    finally:
        shutil.rmtree(work, ignore_errors=True)


# ------------------------------------------------------------------ the Rust leg

def _rust_regress():
    """`scripts/rust_regress.py`, imported on first use: a change with no Rust file pays
    nothing for the import, and the tests substitute the entry point."""
    import rust_regress
    return rust_regress


def _rust_aeneas():
    """`scripts/rust_aeneas.py` the same way, for the prerequisite check."""
    import rust_aeneas
    return rust_aeneas


def rust_crate_at(repo, ref, subdir):
    """rust_regress's library test (`cargo_library_at`, the one `autoform regress --lang
    auto` makes), judged on the tree committed at `ref`: the Rust leg runs when the
    repository (or --subdir) at BASE is a Cargo library."""
    return _rust_regress().cargo_library_at(repo, ref, subdir)


def _rust_counter_input(name, fn, ex):
    """One rust_regress example (`args` as Rust literals, `base_native`, `base_model`,
    `head_native`) as a counter-input. `base_model` is None for a native-only function
    and `div` where Aeneas gave no verdict; the base revision's native result is kept
    beside it (`base_runtime`), since for a behaviour change that is what head left."""
    model = ex.get("base_model")
    return {"call": f"{name}({', '.join(ex.get('args') or [])})", "receiver": None,
            "base_model": model if model is not None else "none (no model: native-only)",
            "base_runtime": ex.get("base_native"), "head_runtime": ex.get("head_native"),
            "detail": None, "origin": fn.get("evidence")}


def _rust_behaviour(name, fn, added, not_encodable):
    """One rust_regress verdict mapped to pr mode's behaviour record: regression /
    behaviour-change -> `changed` with the counter-inputs, unchanged ->
    `unchanged-on-inputs`, anything the leg could not compare (not-comparable,
    inconclusive) -> `not-compared` with its reason. A function only at head has no base
    to compare (`ADDED_AT_HEAD`); one the harness cannot encode at base was never called."""
    if name in added:
        return {"status": "not-compared", "reason": ADDED_AT_HEAD, "compared": 0,
                "counter_inputs": [], "suppressed_as_model_noise": 0}
    if name in not_encodable:
        return {"status": "not-compared",
                "reason": readable("the Rust harness cannot encode it at the base revision: "
                                   + str(not_encodable[name])),
                "compared": 0, "counter_inputs": [], "suppressed_as_model_noise": 0}
    if fn is None:
        return {"status": "not-compared", "compared": 0, "counter_inputs": [],
                "suppressed_as_model_noise": 0,
                "reason": "the Rust leg has no case for it (no model case and no seeded input)"}
    diverging = fn.get("regression", 0) + fn.get("behaviour-change", 0)
    record = {"compared": diverging + fn.get("unchanged", 0), "agree": fn.get("unchanged", 0),
              "inconclusive": fn.get("inconclusive", 0), "suppressed_as_model_noise": 0}
    if fn.get("unstable"):
        # The leg's control: cases it excluded as unstable, never counted either way.
        record["unstable"] = fn["unstable"]
    if fn["status"] in ("regression", "behaviour-change"):
        record.update(status="changed", diverging=diverging, counter_inputs=[
            _rust_counter_input(name, fn, ex) for ex in (fn.get("examples") or [])[:MAX_COUNTER_INPUTS]],
            reason=readable(
                f"{diverging} input(s) where the head revision departs from the base revision"
                + (f" ({fn['regression']} regression(s): the base native result agreed with the "
                   "base model, head's does not)" if fn.get("regression") else "")
                + (f" ({fn['behaviour-change']} behaviour change(s): head's native result differs "
                   "from base's where no model verdict exists)" if fn.get("behaviour-change") else "")))
    elif fn["status"] == "unchanged":
        record.update(status="unchanged-on-inputs", counter_inputs=[],
                      reason=f"{fn['unchanged']} case(s) compared, all agreed; this is not a "
                             "proof of equivalence on other inputs")
    else:
        reasons = fn.get("reasons") or {}
        why = fn.get("reason") or "; ".join(f"{r} ({n} case(s))" for r, n in sorted(reasons.items()))
        record.update(status="not-compared", counter_inputs=[],
                      reason=readable(f"the Rust leg could not compare it ({fn['status']}): "
                                      + (why or "no case replayed")))
    return record


def rust_leg_results(report, repo, base, head, subdir, rust_files):
    """`(functions, removed, behaviours)` for one rust_regress report: a record per
    public function the change touched, the public functions it removed, and the
    behaviour record of each reported function.

    Touched means the function's rustdoc span (`function_spans`, by display name, files
    relative to the crate) sits on changed lines of a changed `.rs` file: the head span
    decides for a function that exists at head; one only at base whose file changed is
    removed (listed with the leg's reason, like a removed Python function, not compared).
    A public function on no changed line that the leg nevertheless found `regression`
    or `behaviour-change` (a private callee or a type it uses changed) is reported too,
    with that said: pruning it would drop a comparison the leg made. A function whose
    span names no file cannot be placed and is left to the leg's own report."""
    head_spans = (report.get("function_spans") or {}).get("head") or {}
    base_spans = (report.get("function_spans") or {}).get("base") or {}
    added = set(report.get("functions_added_at_head") or [])
    not_encodable = report.get("functions_not_encodable") or {}
    per_fn = {f["function"]: f for f in report.get("functions") or []}
    lines = {record["file"]: (_changed_head_lines(read_at(repo, base, record["path"])
                                                  if record["status"] != "A" else None,
                                                  read_at(repo, head, record["path"])
                                                  if record["status"] != "D" else None),
                              record["path"])
             for record in rust_files}
    functions, removed, behaviours = [], [], {}
    for name in sorted(set(per_fn) | added | set(not_encodable) | set(head_spans)):
        head_span, base_span = head_spans.get(name), base_spans.get(name)
        fn = per_fn.get(name)
        flagged = (fn or {}).get("status") in ("regression", "behaviour-change")
        detail = None
        if head_span is None:
            if base_span is not None and base_span.get("file") in lines:
                removed.append({"name": name, "path": lines[base_span["file"]][1],
                                "file": base_span["file"], "change": "removed",
                                "detection": "rustdoc", "language": "rust",
                                "reason": (fn or {}).get("reason") or "removed at head"})
            continue
        file = head_span.get("file")
        span = set(range(head_span["begin_line"], head_span["end_line"] + 1))
        if name in added:
            # A function only at head is in its file's diff by definition.
            if file not in lines:
                continue
            change = "added"
        elif file in lines and span & lines[file][0]:
            change = "modified"
        elif flagged and file:
            change = "modified"
            detail = ("not on the changed lines: the Rust leg observed its behaviour change "
                      "(a callee or a type it uses changed)")
        else:
            continue
        path = lines[file][1] if file in lines else (f"{subdir}/{file}" if subdir else file)
        record = {"name": name, "path": path, "file": file, "change": change,
                  "line": head_span["begin_line"], "end_line": head_span["end_line"],
                  "detection": "rustdoc", "language": "rust"}
        if detail:
            record["change_detail"] = detail
        functions.append(record)
        behaviours[name] = _rust_behaviour(name, fn, added, not_encodable)
    return functions, removed, behaviours


def run_rust_leg(repo, base, head, head_source, subdir, rust_files, report_dir, log):
    """The Rust leg on a change inside a Cargo library: `rust_regress` on the base and
    head trees, the same comparison `autoform regress` runs, kept to the changed public
    functions (`rust_leg_results`).

    -> `(functions, removed, behaviours, stage, summary)`. The leg itself decides what it
    can compare; here a missing prerequisite or a refused leg is a stage outcome with the
    reason, never a fabricated verdict, and the files are left `not compared` with it
    (with nothing else analysed the run exits 2, the way a failed export does, in `run`)."""
    def refused(status, reason):
        reason = readable(reason)
        for record in rust_files:
            record["note"] = "not compared: " + reason
        return [], [], {}, {"status": status, "reason": reason}, \
            {"languages": [], "suppressed_as_model_noise": 0,
             "rust": {"status": "not-compared", "reason": reason}}

    missing = _rust_aeneas().missing()
    if missing:
        return refused("skipped", f"Rust prerequisites missing: {', '.join(missing)} "
                                  "(see docs/rust.md)")
    work = tempfile.mkdtemp(prefix="autoform-pr-rust-")
    try:
        archive = git(repo, "archive", "--format=tar", base, binary=True)
        subprocess.run(["tar", "-x", "-C", work], input=archive.stdout, check=True)
        base_source = Path(work) / subdir if subdir else Path(work)
        out = Path(report_dir) / "rust"
        out.mkdir(parents=True, exist_ok=True)
        head_label = head[:12] if head else "working tree"
        log(f"==> rust leg: rust_regress {base[:12]}..{head_label}")
        try:
            code = _rust_regress().main(["--base", str(base_source), "--head", str(head_source),
                                         "--out", str(out), "--base-label", base[:12],
                                         "--head-label", head_label])
        except Exception as exc:  # the leg crashed: a reason, never a verdict
            return refused("failed", f"the Rust leg did not run: {type(exc).__name__}: {exc}")
        written = out / "rust-regression.json"
        if code not in (0, 1) or not written.is_file():
            # The leg refused (a tool, the base model, a build, the control): it wrote why.
            error = out / "rust-regress-error.json"
            detail = json.loads(error.read_text()) if error.is_file() else {}
            hint = f" ({detail['hint']})" if detail.get("hint") else ""
            return refused("failed", f"the Rust leg did not run: {detail.get('error') or 'exit %s' % code}: "
                                     f"{detail.get('message', '')}{hint}")
        report = json.loads(written.read_text())
        functions, removed, behaviours = rust_leg_results(report, repo, base, head, subdir, rust_files)
        for record in rust_files:
            if not any(f["path"] == record["path"] for f in functions + removed):
                record["note"] = "the Rust leg found no public function the change touched"
        flagged = (report.get("control") or {}).get("flagged", 0)
        unstable = (report.get("cases") or {}).get("unstable", 0)
        stage = {"status": "passed",
                 "note": f"{report.get('total_cases', 0)} case(s) run at base, the control and "
                         f"head; the control flagged {flagged}, {unstable} unstable case(s) excluded",
                 "report": os.path.join("rust", "rust-regression.json")}
        summary = {"languages": ["rust"], "suppressed_as_model_noise": 0,
                   "rust": {"control": f"run: the base tree rebuilt and run again, {flagged} case(s) "
                                       "flagged and excluded as unstable",
                            "model": f"base {base[:12]}: the Aeneas model and its native runs",
                            "runtime": "head: the native harness (debug profile)",
                            "inputs": "the base model's oracle cases, and seeded inputs for public "
                                      "functions the harness can call but the model does not translate",
                            "exit_code": code}}
        return functions, removed, behaviours, stage, summary
    finally:
        shutil.rmtree(work, ignore_errors=True)


# ------------------------------------------------------------------ outputs

def sarif_document(report):
    rules = [{"id": f"autoform/{level}", "name": RULES[level][0].replace(" ", ""),
              "shortDescription": {"text": "Head model conformance: " + RULES[level][0]},
              "fullDescription": {"text": RULES[level][1] + " This is about the head revision's "
                                  "model, not a verdict on the change (see the behaviour result)."},
              "help": {"text": RULES[level][1] + " See docs/evidence-levels.md."},
              "defaultConfiguration": {"level": SARIF_LEVEL[level]},
              "properties": {"tags": ["autoform", "evidence-level"]}} for level in LEVELS]
    rules.append({"id": BEHAVIOUR_RULE[0], "name": "BehaviourChanged",
                  "shortDescription": {"text": BEHAVIOUR_RULE[1]},
                  "fullDescription": {"text": BEHAVIOUR_RULE[2]},
                  "help": {"text": BEHAVIOUR_RULE[2] + " See docs/evidence-levels.md."},
                  "defaultConfiguration": {"level": "warning"},
                  "properties": {"tags": ["autoform", "behaviour"]}})
    index = {rule["id"]: i for i, rule in enumerate(rules)}
    results = []
    for function in report["functions"]:
        level = function["level"]
        behaviour = function.get("behaviour") or {}
        # The PR verdict first; the level is the head model's conformance.
        verdict = (f"PR verdict: {behaviour['status']} ({behaviour.get('reason', '')}); "
                   if behaviour.get("status") else "PR verdict: not run; ")
        text = (f"{function['name']}: {verdict}head model conformance: {level} -- "
                f"{function['reason']}")
        artifacts = "; ".join(
            a.get("theorem") or a.get("path") for a in function["artifacts"]) or "no artifact"
        results.append({
            "ruleId": f"autoform/{level}", "ruleIndex": index[f"autoform/{level}"],
            "level": SARIF_LEVEL[level],
            "message": {"text": text + f" [artifacts: {artifacts}]"},
            "locations": [{"physicalLocation": {
                "artifactLocation": {"uri": _sarif_uri(function["path"]), "uriBaseId": "%SRCROOT%"},
                "region": {"startLine": max(1, int(function.get("line") or 1))}}}],
            "partialFingerprints": {"autoform/function": function["name"]},
            "properties": {"function": function["name"], "level": level,
                           "head_model_conformance": level,
                           "pr_verdict": behaviour.get("status") or "not-run",
                           "change": function["change"], "detection": function["detection"],
                           "artifacts": function["artifacts"]}})
    verdicts = []
    for function in report["functions"]:
        behaviour = function.get("behaviour") or {}
        if behaviour.get("status") != "changed":
            continue
        shown = "; ".join(f"{c['call']}" + (f" on {c['receiver']}" if c.get("receiver") else "") +
                          f": base model {c['base_model']}, "
                          + (f"base runtime {c['base_runtime']}, " if c.get("base_runtime") else "")
                          + f"head runtime {c['head_runtime']}"
                          for c in behaviour["counter_inputs"])
        verdicts.append({
            "ruleId": BEHAVIOUR_RULE[0], "ruleIndex": index[BEHAVIOUR_RULE[0]], "level": "warning",
            "message": {"text": f"{function['name']}: behaviour changed -- {shown}"},
            "locations": [{"physicalLocation": {
                "artifactLocation": {"uri": _sarif_uri(function["path"]), "uriBaseId": "%SRCROOT%"},
                "region": {"startLine": max(1, int(function.get("line") or 1))}}}],
            "partialFingerprints": {"autoform/function": function["name"],
                                    "autoform/behaviour": "changed"},
            "properties": {"function": function["name"], "behaviour": behaviour}})
    results = verdicts + results   # the PR verdicts lead
    return {
        "$schema": SARIF_SCHEMA, "version": "2.1.0",
        "runs": [{
            "tool": {"driver": {"name": "autoform", "version": report["tool_version"],
                                "semanticVersion": report["tool_version"],
                                "informationUri": "https://github.com/b1oo/autoform",
                                "rules": rules}},
            "automationDetails": {"id": f"autoform/pr/{report['module']}"},
            "versionControlProvenance": [{"repositoryUri": report["repository"]["uri"],
                                          "revisionId": report["head"]["commit"] or "working-tree"}],
            "results": results,
            "properties": {"base": report["base"], "head": report["head"],
                           "stages": report["stages"], "exporter": report["exporter"],
                           **({"gate": report["gate"]} if report.get("gate") else {})},
        }],
    }


def _sarif_uri(path):
    """A repository-relative path as a SARIF `uri` (a URI reference, RFC 3986): a space or
    a non-ASCII character in a file name is percent-encoded, a `/` is kept."""
    return quote(path, safe="/")


def validate_sarif(document):
    """Problems with a SARIF document against the shape GitHub code scanning ingests:
    SARIF 2.1.0, one run, a named driver with rules, each result naming a rule with a
    level GitHub knows, a message and a relative file location on a positive line. The
    tool version, the `%SRCROOT%` base of every relative URI and an absolute
    `repositoryUri` are required too: a consumer other than GitHub resolves locations
    and identifies runs by them."""
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
        if not driver.get("version") and not driver.get("semanticVersion"):
            problems.append("tool.driver.version is required")
        for provenance in run.get("versionControlProvenance") or []:
            if not re.match(r"[A-Za-z][A-Za-z0-9+.-]*:", provenance.get("repositoryUri") or ""):
                problems.append("versionControlProvenance.repositoryUri must be an absolute URI")
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
                elif uri != quote(uri, safe="/%"):
                    problems.append(f"result {n}: artifactLocation.uri must be percent-encoded")
                if (physical.get("artifactLocation") or {}).get("uriBaseId") != "%SRCROOT%":
                    problems.append(f"result {n}: a relative artifactLocation.uri needs uriBaseId %SRCROOT%")
                line = (physical.get("region") or {}).get("startLine")
                if not isinstance(line, int) or isinstance(line, bool) or line < 1:
                    problems.append(f"result {n}: region.startLine must be an integer >= 1")
    return problems


def behaviour_markdown(report):
    """The PR verdict section: one row per changed function with its behaviour
    (`changed`, `unchanged-on-inputs`, `not-compared`), counter-inputs under it."""
    summary = report.get("behaviour")
    rows = [(f, f["behaviour"]) for f in report["functions"] if f.get("behaviour")]
    if not rows:
        return ["### PR verdict", "", "Not run: no behaviour comparison (base model against "
                "head runtime) was made" + (" (--no-behaviour)" if summary is None else "") + ".", ""]
    lines = ["### PR verdict", ""]
    counts = {b: sum(1 for _, r in rows if r["status"] == b) for b in BEHAVIOURS}
    languages = ", ".join((summary or {}).get("languages") or []) or "none"
    gate = report.get("gate") or {}
    fails = "behaviour-changed" in (gate.get("fail_on") or [])
    lines += ["Base-revision model against head-revision runtime on the same inputs (Python: "
              "the head tests', random and literal-derived; Java/Kotlin: seeded random and "
              "literal-derived; Go/JS/TS: fixed pools and literals; C: seeded typed "
              "boundaries; Rust: the base revision's Aeneas model cases and seeded "
              "native-only inputs on the head's native harness). "
              f"Languages compared: {languages}. "
              + ("A behaviour change fails this gate (--fail-on behaviour-changed). " if fails else
                 "A behaviour change is reported, not failed. ")
              + ", ".join(f"{n} {b}" for b, n in counts.items())
              + (f"; suppressed-as-model-noise: {summary['suppressed_as_model_noise']}" if summary else "")
              + ".", ""]
    lines += ["| function | change | PR verdict | detail |", "|---|---|---|---|"]
    for function, record in rows:
        verdict = f"**{record['status']}**" if record["status"] == "changed" else record["status"]
        change = function["change"] + (" (identical except inside holes)"
                                       if function.get("identical_but_holed") else "")
        lines.append(f"| `{function['name']}` | {change} | {verdict} | {record['reason']} |")
    lines.append("")
    for function, record in rows:
        if record["status"] != "changed":
            continue
        lines.append(f"* `{function['name']}` -- **behaviour: changed** ({record['diverging']} input(s))")
        for item in record["counter_inputs"]:
            lines.append(f"  * `{item['call']}`" + (f" on `{item['receiver']}`" if item.get("receiver") else "")
                         + f": base model {item['base_model']}; "
                         + (f"base runtime {item['base_runtime']}; " if item.get("base_runtime") else "")
                         + f"head runtime {item['head_runtime']}")
    failed = [f"{n}: {v.get('reason') or v.get('status')}" for n, v in ((summary or {}).get("stages") or {}).items()
              if v.get("status") in ("failed", "skipped")]
    if failed:
        lines += ["", "Behaviour stages that did not run: " + "; ".join(failed) + "."]
    if summary and summary.get("suppressed_as_model_noise"):
        lines += ["", f"suppressed-as-model-noise: {summary['suppressed_as_model_noise']} divergent case(s) "
                      "also diverge when the base model runs against the base runtime on the same "
                      "inputs (same-base control), so they are not attributed to the change."]
    return lines + [""]


def is_test_function(function):
    """Test code by path: a top-level `tests/`/`test/`, any `test`-like directory
    (`src/test/java`, `__tests__`), or a test-named file (`test_*.py`, `*_test.go`,
    `FooTest.java`, `*.spec.ts`, `conftest.py`)."""
    rel = function.get("file") or function.get("path") or ""
    path = PurePosixPath(rel)
    if _is_test_path(rel) or any(part in TEST_DIRS for part in path.parts[:-1]):
        return True
    return path.name == "conftest.py" or bool(TEST_STEM.search(path.stem))


def evidence_gate(results, fail_on):
    """The `--fail-on` evidence check, or None when no `--fail-on` asks for one.

    A behaviour gate that compared nothing must not look like one that compared
    everything and found it unchanged: when not one changed non-test function reached
    behaviour `changed` or `unchanged-on-inputs`, the gate is `inconclusive` (exit 3).
    A change whose only changed functions are test code (or that changed no function)
    has nothing for the gate to compare and is not inconclusive.

    A function identical to the base export except inside its holes
    (`identical_but_holed`) stays listed but is a gate subject only when nothing else
    is: the export cannot say whether it changed, and counting it made "none of the 19
    changed functions was compared" out of a change to a few.

    An `unchanged-on-inputs` function whose compared inputs never executed its change
    (`change_covered` False: a changed statement never ran, or a changed condition only
    ever went one way) is compared, but not on the change: when every compared function
    is such, the gate is inconclusive too. The exit code is filled in by `run`."""
    if not set(fail_on) & set(FAIL_ON):
        return None
    code = [f for f in results if not is_test_function(f)]
    holed = [f for f in code if f.get("identical_but_holed")]
    subjects = [f for f in code if not f.get("identical_but_holed")] or holed
    compared = [f for f in subjects
                if (f.get("behaviour") or {}).get("status") in EVIDENCE_BEHAVIOURS]
    unreached = [f["name"] for f in compared
                 if (f.get("behaviour") or {}).get("status") == "unchanged-on-inputs"
                 and (f.get("behaviour") or {}).get("change_covered") is False]
    gate = {"fail_on": sorted(set(fail_on)), "subjects": len(subjects), "compared": len(compared)}
    if holed and subjects is not holed:
        gate["identical_but_holed_not_counted"] = len(holed)
    if unreached:
        gate["change_not_reached"] = unreached
    if subjects and not compared:
        return dict(gate, status="inconclusive", exit_code=EXIT_INCONCLUSIVE,
                    reason=f"inconclusive: no evidence: none of the {len(subjects)} changed non-test "
                           "function(s) was behaviour-compared (changed or unchanged-on-inputs), so "
                           "this gate checked nothing; this is neither a pass nor a failure"
                           + (f" ({len(holed)} more, identical to the base except inside holes, "
                              "are listed but not counted)" if gate.get("identical_but_holed_not_counted") else ""))
    if compared and len(unreached) == len(compared):
        return dict(gate, status="inconclusive", exit_code=EXIT_INCONCLUSIVE,
                    reason=f"inconclusive: the {len(compared)} compared function(s) agreed only on inputs "
                           "that never executed the change (branch coverage), so this gate did not "
                           "check it; this is neither a pass nor a failure")
    return dict(gate, status="evidence")


def markdown_comment(report):
    counts = {level: 0 for level in LEVELS}
    for function in report["functions"]:
        counts[function["level"]] += 1
    head = report["head"]["commit"] or "working tree"
    gate = report.get("gate") or {}
    lines = [f"**autoform: INCONCLUSIVE (exit {EXIT_INCONCLUSIVE}): {gate['reason']}.**", ""] \
        if gate.get("status") == "inconclusive" else []
    lines += [f"## autoform: evidence for the functions changed since `{report['base']['commit'][:12]}`",
             "",
             f"Base `{report['base']['commit'][:12]}` → head `{head[:12] if report['head']['commit'] else head}`"
             f"; module `{report['module']}`; exporter: {report['exporter']['status']}"
             + (f" ({report['exporter']['reason']})" if report['exporter'].get('reason') else "") + ".",
             ""]
    # The PR verdict leads: what the change did (base model against head runtime). The
    # evidence level below is about the HEAD model alone and is not a verdict on the PR.
    lines += behaviour_markdown(report)
    lines += ["### Head model conformance", "",
              "How far the head revision's own model is established against the head runtime "
              "(not a verdict on the change: a function whose behaviour changed can be "
              "`proved` here).", "",
              "| head model conformance | functions |", "|---|---|"]
    lines += [f"| {level} | {counts[level]} |" for level in LEVELS]
    lines += ["", "Levels never round up: a function is listed at the highest level its own "
              "artifacts reach (`docs/evidence-levels.md`).", ""]
    if report["functions"]:
        lines += ["| function | change | head model conformance | evidence | artifact |",
                  "|---|---|---|---|---|"]
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
            change = function["change"] + (f" ({function['change_detail']})"
                                           if function.get("change_detail") else "")
            lines.append(f"| `{function['name']}`<br>{where} | {change} | "
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


ORACLE_PYTHON_ENV = "AUTOFORM_ORACLE_PYTHON"
PYTEST_ADDOPTS_ENV = "AUTOFORM_ORACLE_PYTEST_ADDOPTS"
# A project-local virtualenv at the analysed repository's root, tried only when neither
# --python nor $AUTOFORM_ORACLE_PYTHON is given and the change touches an analysed Python
# file: the project's tests import its dependencies, which autoform's own interpreter
# usually lacks (measured: a pandas project ran 0 tests under it). Windows
# `Scripts\python.exe` layouts are not candidates.
PROJECT_VENVS = (".venv/bin/python", "venv/bin/python")


def oracle_settings(python=None, pytest_addopts=None, environ=None, repo=None, python_change=False):
    """`(env, record)`: the environment the oracle runs with, and what pr.json says about it.

    The Python oracle runs the project's tests and calls its functions IN its own process,
    so its interpreter must be one that imports the project (`--python`, else
    `AUTOFORM_ORACLE_PYTHON`, else, for a Python change only, the lone project-local
    virtualenv at `repo`'s root, else this interpreter). It is validated here, before any
    stage runs: an interpreter that cannot start would otherwise surface as a stage
    failure much later. The interpreter is not resolved through symlinks: a virtualenv's
    `bin/python` is a link to a base interpreter that lacks the venv's packages.
    Auto-detection never guesses: exactly one PROJECT_VENVS candidate is used and
    recorded as `auto: <dir>`, more than one stays unused and is named in a note, and a
    non-Python change (`python_change` False) never triggers it."""
    environ = os.environ if environ is None else environ
    requested = python or environ.get(ORACLE_PYTHON_ENV)
    origin = setting = "--python" if python else ORACLE_PYTHON_ENV
    note = None
    env = {}
    addopts = pytest_addopts or environ.get(PYTEST_ADDOPTS_ENV)
    if addopts:
        if addopts not in ("project", "ignore"):
            raise PrError(f"{PYTEST_ADDOPTS_ENV} must be 'project' or 'ignore', not {addopts!r}")
        env[PYTEST_ADDOPTS_ENV] = addopts
    if not requested and repo is not None and python_change:
        # lexists: a venv whose base interpreter is gone (a dangling `bin/python` link) is
        # still the project's venv, and is refused below rather than silently skipped.
        found = [rel for rel in PROJECT_VENVS if os.path.lexists(Path(repo) / rel)]
        if len(found) == 1:
            requested = str(Path(repo) / found[0])
            origin, setting = f"auto-detected {found[0]}", "auto: " + found[0].split("/")[0]
        elif found:
            note = (f"project virtualenvs at the repository root: {', '.join(found)}; more than "
                    "one, so none was chosen rather than guessed (pass --python)")
    if not requested:
        record = {"path": sys.executable, "version": sys.version.split()[0],
                  "setting": "default: the interpreter running autoform",
                  "pytest_addopts": addopts or "project"}
        if note:
            record["note"] = note
        return env, record
    path = os.path.abspath(os.path.expanduser(requested))
    if not (os.path.isfile(path) and os.access(path, os.X_OK)):
        raise PrError(f"oracle interpreter {path} (from {origin}) is not an executable file")
    try:
        probe = subprocess.run([path, "-c", "import sys; print(sys.version.split()[0]); "
                                "print(int(sys.version_info >= (3, 10)))"],
                               capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise PrError(f"oracle interpreter {path} (from {origin}) did not start: {exc}") from exc
    lines = probe.stdout.split()
    if probe.returncode != 0 or len(lines) != 2:
        raise PrError(f"oracle interpreter {path} (from {origin}) did not start: "
                      f"exit {probe.returncode}: " + (probe.stderr.strip()[-300:] or "?"))
    if lines[1] != "1":
        raise PrError(f"oracle interpreter {path} (from {origin}) is Python {lines[0]}; "
                      "the oracle needs 3.10+")
    env[ORACLE_PYTHON_ENV] = path
    return env, {"path": path, "version": lines[0], "setting": setting,
                 "pytest_addopts": addopts or "project"}


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
    # The Rust leg: the exporter has no Rust frontend, so a `.rs` file never enters the
    # chain. When the repository (or --subdir) at base is a Cargo library, rust_regress
    # compares the crate across the revisions the way `autoform regress` does, and the
    # changed public functions join the report with their behaviour and no evidence level.
    rust_files = [r for r in detected["files"] if r.get("analysed") == "rust-file"]
    crate_at_base = rust_crate_at(repo, base, subdir) if rust_files else False
    rust_leg = bool(rust_files) and crate_at_base and args.behaviour
    if rust_files and not rust_leg:
        why = ("--no-behaviour: the Rust leg is part of the behaviour comparison"
               if not args.behaviour else
               "no Cargo library at base" + (f" under --subdir {subdir}" if subdir else "")
               + " (a Cargo.toml with [package], and src/lib.rs or [lib]): the Rust leg runs "
               "only on a Cargo library")
        for record in rust_files:
            record["note"] = "not compared: " + why
    rust_behaviours = rust_stage = rust_summary = None

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
    # A project virtualenv is auto-detected only for a Python change -- no other change
    # runs the project's suite -- and at the repository root, not in the scratch head
    # tree: a virtualenv is untracked, so it never survives `git archive`.
    python_change = any(r.get("analysed") == "python-ast" for r in detected["files"])
    oracle_env, oracle_interpreter = oracle_settings(getattr(args, "python", None),
                                                     getattr(args, "pytest_addopts", None),
                                                     repo=repo, python_change=python_change)
    log(f"==> oracle interpreter: {oracle_interpreter['path']} ({oracle_interpreter['version']}; "
        f"{oracle_interpreter['setting']})"
        + (f" -- {oracle_interpreter['note']}" if oracle_interpreter.get("note") else ""))
    chain = Chain(ROOT, report_dir, args.module, source, python, args.stage_timeout, log, oracle_env)
    if (Path(source) / "src").is_dir():
        # `src/` layout, as the behaviour leg does: the head checkout's package must be the
        # one the head oracle's suite imports (measured: without it every test module of
        # a src-layout package failed to collect with "No module named <package>").
        chain.env["PYTHONPATH"] = os.pathsep.join(
            [str(Path(source) / "src")] + ([chain.env["PYTHONPATH"]] if chain.env.get("PYTHONPATH") else []))
    exporter ={"status": "unavailable", "reason": ""}
    functions = None
    full_ast = report_dir / f"ast-{args.module}.full.json"
    # Nothing to analyse (documentation, configuration, a file outside --subdir, a Python
    # edit outside every def): say so and stop before the exporter, which on a large
    # repository is the most expensive stage and would establish nothing here.
    nothing = None
    if not detected["functions"] and not any(r.get("analysed") == "changed-file" for r in detected["files"]) \
            and not rust_leg:
        nothing = ("no changed function in a changed Python file" if any(
            r.get("analysed") == "python-ast" for r in detected["files"]) else
            ("--no-behaviour: the Rust leg, the only comparison these file(s) have, did not run"
             if not args.behaviour and crate_at_base else
             "the changed Rust file(s) are outside a Cargo library at base, and the Rust leg "
             "runs only on a crate") if rust_files else
            "no changed file is source code in a supported language" +
            (f" under --subdir {subdir}" if subdir else ""))
    try:
        if nothing:
            exporter = {"status": "not-run", "reason": nothing}
            log(f"==> nothing to analyse: {nothing}")
        elif rust_leg and not detected["functions"] \
                and not any(r.get("analysed") == "changed-file" for r in detected["files"]):
            # Rust only: the exporter has no Rust frontend, so a Joern run would write an
            # empty AST of the tree and read as a failed export. The leg names the
            # functions itself.
            exporter = {"status": "not-run",
                        "reason": "every changed source file is Rust; the Rust leg compares it "
                                  "(the exporter has no Rust frontend)"}
            log("==> export: not run: " + exporter["reason"])
        elif args.ast:
            supplied = Path(args.ast).resolve()
            shutil.copy(supplied, full_ast)
            exporter = {"status": "available", "source": "supplied", "path": str(supplied),
                        "sha256": hashlib.sha256(full_ast.read_bytes()).hexdigest(),
                        "reason": f"--ast {supplied.name} (an AST the exporter produced earlier; Joern not run)"}
        else:
            start = time.monotonic()
            try:
                notes = export_ast(source, full_ast, report_dir, args.stage_timeout)
                exporter = {"status": "available", "source": "joern", "joern": str(joern_home()),
                            "sha256": hashlib.sha256(full_ast.read_bytes()).hexdigest(),
                            "reason": "", "seconds": round(time.monotonic() - start, 2),
                            **(notes if isinstance(notes, dict) else {})}
            except (PrError, subprocess.TimeoutExpired) as exc:
                exporter = {"status": "unavailable", "reason": str(exc)}
                log(f"   !! export: {exc}")
        chain.stages["export"] = {"status": "passed" if exporter["status"] == "available" else
                                  "skipped" if exporter["status"] == "not-run" else "failed",
                                  **{k: v for k, v in exporter.items() if k != "status"}}
        if exporter["status"] == "available":
            functions = deep_json.load(full_ast)
            if isinstance(functions, dict):
                functions = functions.get("functions", [])
            if not functions and exporter.get("source") == "joern":
                # Joern can write a CPG with no method at all and still exit 0 (a failed
                # delombok, a frontend that skipped every file). An empty AST of a tree
                # with changed source is a failed export, never "no changed function".
                exporter = {"status": "unavailable",
                            "reason": "the exporter produced an empty AST (0 functions); see parse.log"}
                chain.stages["export"] = {"status": "failed", "reason": exporter["reason"]}
                log(f"   !! export: {exporter['reason']}")
                functions = None

        # An archived head has no installed packages: link the working tree's, after the
        # export so the exporter never walks them (the runtime backends need them).
        dependencies = link_installed_dependencies(repo, scratch) if scratch else []

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
                                            "detection": "changed-file",
                                            "language": source_language(record["file"])})
        else:
            for record in detected["files"]:
                if record.get("analysed") == "changed-file":
                    record["note"] = "no exporter output, so its functions cannot be named"
        changed.sort(key=lambda f: (f["path"], f.get("line") or 0, f["name"]))
        removed = list(detected["removed"])

        # The behaviour stage exports the base tree; it runs before the head chain so
        # that export can say which changed-file functions really changed
        # (`classify_against_base`) and the chain runs on those only.
        identity = {}
        behaviour_summary = behaviours = None
        candidates = any(f["detection"] == "changed-file" for f in changed)

        def refine(base_functions):
            identity.update(classify_against_base(changed, detected["files"], functions, base_functions))
            return identity["changed"]

        if args.behaviour and changed:
            behaviours, extra_stages, behaviour_summary = run_behaviour(
                repo, base, source, subdir, changed, args.module, report_dir,
                args.behaviour_cases, args.tests, python, args.stage_timeout, log,
                refine if candidates else None, oracle_env=oracle_env, head_functions=functions)
            behaviour_summary = dict(behaviour_summary, stages=extra_stages)
        elif not args.behaviour:
            log("==> behaviour: skipped: --no-behaviour")
        if identity:
            changed = identity["changed"]
            removed = sorted(removed + identity["removed"], key=lambda f: (f["path"], f["name"]))
            change_identity = {"status": "base-export", "counts": identity["counts"],
                               "unchanged": identity["unchanged"], "renumbered_lambdas": identity["renumbered"]}
            detection = ("python-ast for Python files; for other languages, the exporter's AST "
                         "of base and head compared per function (changed-file, refined: "
                         "identical functions dropped, signature changes paired, lambdas "
                         "matched by body)")
        else:
            why = ("--no-behaviour (the base tree is exported by the behaviour stage only)"
                   if not args.behaviour else
                   ((behaviour_summary or {}).get("stages", {}).get("behaviour") or {}).get("reason")
                   or "the base tree was not exported")
            change_identity = {"status": "unavailable", "reason": why} if candidates else None
            detection = ("python-ast for Python files; changed-file (every exported function of a "
                         "changed file) for other languages"
                         + (f"; not refined against the base: {why}" if candidates else ""))

        # The Rust leg runs after the identity refinement: its functions are never Joern
        # candidates, never compared against a base export, and never reach the chain.
        if rust_leg:
            rust_functions, rust_removed, rust_behaviours, rust_stage, rust_summary = run_rust_leg(
                repo, base, head, source, subdir, rust_files, report_dir, log)
            changed = sorted(changed + rust_functions,
                             key=lambda f: (f["path"], f.get("line") or 0, f["name"]))
            removed = sorted(removed + rust_removed, key=lambda f: (f["path"], f["name"]))
            detection += ("; rustdoc spans for Rust (public functions on the changed lines, "
                          "compared by path and signature at both revisions)")
            behaviour_summary = dict(behaviour_summary or {"suppressed_as_model_noise": 0},
                                     languages=sorted(set((behaviour_summary or {}).get("languages") or [])
                                                      | set(rust_summary["languages"])),
                                     rust=rust_summary["rust"],
                                     stages=dict((behaviour_summary or {}).get("stages") or {},
                                                 rust=rust_stage))

        chain_changed = [f for f in changed if f.get("language") != "rust"]
        selected, closure, missing = [], [], [f["name"] for f in chain_changed]
        conformance = ledger = specs = mutation = None
        if functions is not None and chain_changed:
            selected, closure, missing = select_functions(functions, [f["name"] for f in chain_changed])
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
                chain.skip(name, nothing or "no exporter output")

        results = evidence(changed, selected, conformance, specs, mutation, chain.stages,
                           args.module, exporter)
        if behaviours is not None:
            for record in results:
                record["behaviour"] = behaviours.get(record["name"])
        for record in results:
            if record.get("language") == "rust":
                # No Lean chain and no evidence level for Rust: the PR verdict is the
                # leg's comparison, and the reason names that, not the Joern frontend
                # (which would otherwise claim the function was missing from its AST).
                record["behaviour"] = (rust_behaviours or {}).get(record["name"])
                record["reason"] = ("no evidence level for Rust (the Lean chain has no Rust "
                                    "frontend); the PR verdict is the Rust leg's (rust_regress, "
                                    "docs/rust.md)")
        report = {
            "schema_version": SCHEMA_VERSION, "tool_version": _tool_version(),
            "generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "module": args.module, "report_dir": str(report_dir),
            "repository": {"path": str(repo), "uri": _origin(repo), "subdir": subdir or "."},
            "base": {"ref": args.base, "commit": base},
            "head": {"ref": args.head, "commit": head},
            "detection": detection, "exporter": exporter,
            **({"dependencies": {"linked": dependencies, "from": "the working tree's installed "
                                 "packages (not part of the commit)"}} if dependencies else {}),
            **({"change_identity": change_identity} if change_identity else {}),
            "files": detected["files"], "errors": detected["errors"],
            "selection": {"changed": [f["name"] for f in changed], "selected": [f["name"] for f in selected],
                          "closure": closure, "missing": missing},
            "stages": chain.stages, "oracle_interpreter": oracle_interpreter,
            "ledger": {k: ledger[k] for k in ("functions", "holes", "holeFree", "holesByLabel")
                       if ledger and k in ledger} if ledger else None,
            "functions": results, "removed": removed,
            "summary": {level: sum(1 for f in results if f["level"] == level) for level in LEVELS},
        }
        if behaviour_summary is not None:
            counts = {b: sum(1 for f in results if (f.get("behaviour") or {}).get("status") == b)
                      for b in BEHAVIOURS}
            report["behaviour"] = dict(behaviour_summary, summary=counts)
        gate = evidence_gate(results, args.fail_on)
        changed_behaviour = (report.get("behaviour") or {}).get("summary", {}).get("changed", 0)
        # The exit code, decided before anything is written so pr.json carries it whatever
        # the gate's status (it used to be null whenever the status was `evidence`).
        if exporter["status"] == "unavailable":
            exit_code = 2
        elif report["summary"]["refuted"] or ("behaviour-changed" in args.fail_on and changed_behaviour):
            exit_code = 1
        elif gate is not None and gate["status"] == "inconclusive":
            exit_code = EXIT_INCONCLUSIVE
        elif rust_stage is not None and rust_stage["status"] in ("failed", "skipped") and not results:
            # The Rust leg wanted to run and could not (its prerequisites missing, its
            # base model refused, a harness build failed) and no other function was
            # analysed: exiting 0 would pass a CI gate on a comparison that never
            # happened, the same way a failed export does.
            exit_code = 2
        else:
            exit_code = 0
        if gate is not None:
            report["gate"] = dict(gate, exit_code=exit_code)
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
            (f"; removed {len(removed)}" if removed else ""))
        if report.get("behaviour"):
            log("==> behaviour: " + ", ".join(f"{n} {b}" for b, n in report["behaviour"]["summary"].items() if n)
                + f"; suppressed-as-model-noise: {report['behaviour']['suppressed_as_model_noise']}")
        for function in results:
            log(f"   {function['level']:<14} {function['name']}: {function['reason']}")
        log(f"==> report: {report_dir / 'pr.json'}")
        if exporter["status"] == "unavailable":
            # A supported source file changed and no AST came back: nothing was analysed,
            # so the run could not do its job. Exiting 0 here let a CI gate pass on a
            # crashed frontend (measured: joern-parse failing on a missing launcher
            # dependency reported "0 changed function(s)" and exit 0).
            log(f"   !! could not analyse the change: {exporter['reason']}")
        elif exit_code == EXIT_INCONCLUSIVE:
            # A CI gate that compared nothing must not exit like a clean pass (measured: a
            # behaviour gate exited 0 on seeded regressions it had not compared at all).
            log(f"   !! {gate['reason']} (exit {EXIT_INCONCLUSIVE})")
        elif exit_code == 2:
            # The Rust leg is the whole analysis here, and it did not run.
            log(f"   !! could not analyse the change: {rust_stage['reason']} (exit 2)")
        return exit_code
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
    """`origin` as an absolute URI with any credentials removed (a CI clone URL often
    carries a job token), or the checkout's `file:` URI when there is no `origin`. The
    scp-like form `user@host:path` that self-hosted Git servers hand out is not a URI,
    so it is rewritten as `ssh://host/path`; a local path becomes a `file:` URI."""
    result = git(repo, "remote", "get-url", "origin", check=False)
    url = result.stdout.strip() if result.returncode == 0 else ""
    if not url:
        return Path(repo).as_uri()
    if "://" in url:
        # Userinfo and query/fragment can carry a token (`?private_token=`); neither belongs in SARIF.
        return re.sub(r"[?#].*$", "", re.sub(r"://[^@/]+@", "://", url))
    scp = re.fullmatch(r"(?:[^@/:]+@)?([^/:]+):(.+)", url)
    if scp and len(scp.group(1)) > 1:   # `C:\...` is a Windows path, not a host
        return f"ssh://{scp.group(1)}/{scp.group(2).lstrip('/')}"
    path = Path(url)
    return (path if path.is_absolute() else Path(repo) / path).resolve().as_uri()


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
    parser.add_argument("--python", help="interpreter the Python oracle runs the project's tests and functions "
                                         "under: one with the project's dependencies installed (default: "
                                         "$AUTOFORM_ORACLE_PYTHON, else the repository's lone .venv or venv "
                                         "at its root for a Python change, else this interpreter); recorded")
    parser.add_argument("--pytest-addopts", choices=("project", "ignore"),
                        help="'ignore' runs the project's tests without its pytest addopts (-o addopts=), "
                             "e.g. when they need a plugin the interpreter lacks; recorded in the "
                             "measurement basis (default: $AUTOFORM_ORACLE_PYTEST_ADDOPTS, else 'project')")
    parser.add_argument("--cases", type=int, default=int(os.environ.get("AUTOFORM_CASES", "5")),
                        help="random cases per function for the oracle (default: 5)")
    parser.add_argument("--no-behaviour", dest="behaviour", action="store_false",
                        help="skip the cross-revision behaviour comparison (base model vs head runtime)")
    parser.add_argument("--fail-on", action="append", default=[], choices=FAIL_ON,
                        help="behaviour-changed: also exit 1 when a changed function's behaviour changed "
                             "(default: only a refutation fails; a behaviour change may be intended). "
                             "Either value exits 3 (inconclusive) when no changed non-test function was "
                             "behaviour-compared; no-evidence applies only that rule")
    parser.add_argument("--behaviour-cases", type=int, default=100,
                        help="oracle cases per function for the behaviour comparison (default: 100)")
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
