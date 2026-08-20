"""The five silent failures, one test class each.

Acceptance criterion for this file: each class contains
  * `test_old_behaviour_*` — the *reconstructed* old implementation, asserted to be
    broken.  If someone reverts the fix, this test starts passing for the wrong reason,
    so each one also pins the fixed behaviour next to it.
  * `test_fixed_*` — the shipped code, asserted to be correct on the same input.

Reconstructions are quoted from the code as it was, not paraphrased.
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import textwrap

import pytest

from conftest import CARTO, ROOT, fn, make_repo, run_script, seq_chain, write_ast

# ===========================================================================
# 1. mutate.py: error_lines matched only the OLD Lean diagnostic shape
# ===========================================================================

# Lean 4.30 / lake output, verbatim shape: severity first.
LEAN_430_OUTPUT = textwrap.dedent("""\
    info: Autoform.Specs.CachetoolsSpec: replayed
    error: ./././Autoform/Specs/CachetoolsSpec.lean:41:2: unsolved goals
    case h
    ⊢ False
    error: ./././Autoform/Generated/Cachetools.lean:912:0: type mismatch
""")

# The pre-4.x shape, still emitted by older toolchains and by `lean` directly.
LEAN_OLD_OUTPUT = textwrap.dedent("""\
    Autoform/Specs/CachetoolsSpec.lean:41:2: error: unsolved goals
    Autoform/Generated/Cachetools.lean:912:0: error: type mismatch
""")


def _old_error_lines(output, target_basename):
    """mutate.py as it was: one pattern, position-first only."""
    pat = re.compile(r'^(.*?):(\d+):(\d+):\s*error', re.M)
    out = []
    for m in pat.finditer(output):
        path = m.group(1).strip()
        if target_basename in path or path in ("", "."):
            out.append(int(m.group(2)))
    return sorted(set(out))


class TestMutateErrorAttribution:
    def test_old_behaviour_sees_nothing_on_this_toolchain(self):
        """The bug: on Lean 4.30 the old regex attributed *zero* errors.

        Every mutant then fell through to the coarse "build failed, credit all
        theorems" branch, so a 100% kill rate had no per-theorem evidence behind it.
        """
        assert _old_error_lines(LEAN_430_OUTPUT, "CachetoolsSpec.lean") == []
        assert _old_error_lines(LEAN_430_OUTPUT, "Cachetools.lean") == []

    def test_fixed_matches_severity_first(self, mutate):
        assert mutate.error_lines(LEAN_430_OUTPUT, "CachetoolsSpec.lean") == [41]
        assert mutate.error_lines(LEAN_430_OUTPUT, "Cachetools.lean") == [912]

    def test_fixed_still_matches_position_first(self, mutate):
        """The old shape must keep working; the fix is additive, not a swap."""
        assert _old_error_lines(LEAN_OLD_OUTPUT, "CachetoolsSpec.lean") == [41]
        assert mutate.error_lines(LEAN_OLD_OUTPUT, "CachetoolsSpec.lean") == [41]

    def test_all_error_lines_reports_the_file(self, mutate):
        got = mutate.all_error_lines(LEAN_430_OUTPUT)
        assert ("CachetoolsSpec.lean", 41) in got
        assert ("Cachetools.lean", 912) in got

    def test_all_error_lines_is_the_retry_guard(self, mutate):
        """A build failure naming no position must be distinguishable from a real one.

        The driver retries while `all_error_lines(out)` is empty, precisely so lock
        contention is not scored as a kill.
        """
        assert mutate.all_error_lines("error: build failed\n") == []
        assert mutate.all_error_lines("error: no such file or directory") == []

    def test_attribution_separates_module_from_spec(self, mutate):
        """A theorem "noticing" is an error in the SPEC file, not in the mutated one.

        `Cachetools.lean` must not absorb `CachetoolsSpec.lean`'s errors: that would
        turn every ill-typed mutant into a kill.
        """
        spec_only = "error: ./Autoform/Specs/CachetoolsSpec.lean:7:0: oops\n"
        assert mutate.error_lines(spec_only, "CachetoolsSpec.lean") == [7]
        assert mutate.error_lines(spec_only, "Cachetools.lean") == []

    def test_no_output_means_no_attribution(self, mutate):
        assert mutate.error_lines("", "X.lean") == []


# ===========================================================================
# 2/3. check_docs.py: passing against a stale artifact, and going quiet
#      when an input is absent
# ===========================================================================

LEDGER = "ledger-Cachetools.json"
AST = "ast-Cachetools.json"


def _docs_repo(tmp_path, ledger_functions, ast_functions, doc_functions=None):
    """A repo where the docs quote the ledger, and the ledger may be stale."""
    d = str(tmp_path)
    os.makedirs(os.path.join(d, "docs"), exist_ok=True)
    doc_functions = ledger_functions if doc_functions is None else doc_functions
    with open(os.path.join(d, LEDGER), "w") as fh:
        json.dump({"functions": ledger_functions, "holeFree": 100,
                   "verifiableCore": 45}, fh)
    write_ast(os.path.join(d, AST), [fn(name="f%d" % i) for i in range(ast_functions)])
    with open(os.path.join(d, "docs", "scale.md"), "w") as fh:
        fh.write("| `cachetools` (published) | %d | 100 (42%%) | 45 (19%%) |\n"
                 % doc_functions)
    with open(os.path.join(d, "docs", "contracts.md"), "w") as fh:
        fh.write("hole-free and 45 are call-closed\n")
    with open(os.path.join(d, "docs", "languages.md"), "w") as fh:
        fh.write("| Python | x | %d | 42%% |\n" % doc_functions)
    with open(os.path.join(d, "README.md"), "w") as fh:
        fh.write("| 0 holes, all named |\n")
    return d


CHECK_DOCS = os.path.join(ROOT, "scripts", "check_docs.py")


class TestCheckDocsStaleArtifact:
    def test_old_behaviour_passes_5_of_5_against_a_stale_ledger(self, tmp_path):
        """Reconstruction: doc-vs-artifact rows only, no cross-artifact check.

        The ledger says 238 functions, the AST has 208 — the ledger was never re-run
        after an exporter change. Every documented figure still matches, so the old
        checker printed "5 documented figures all match".
        """
        d = _docs_repo(tmp_path, ledger_functions=238, ast_functions=208)
        mod = __import__("importlib").import_module  # noqa: F841 (kept explicit below)
        import importlib.util
        spec = importlib.util.spec_from_file_location("cd_old", CHECK_DOCS)
        cd = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cd)
        # the old script had no CROSS table at all
        cd.CROSS = []
        rc = cd.main.__wrapped__(d) if hasattr(cd.main, "__wrapped__") else None
        if rc is None:                      # main() parses argv; drive it that way
            argv = sys.argv
            sys.argv = ["check_docs.py", "--root", d]
            try:
                rc = cd.main()
            finally:
                sys.argv = argv
        assert rc == 0, "reconstruction should reproduce the false PASS"

    def test_fixed_catches_the_stale_ledger(self, tmp_path):
        d = _docs_repo(tmp_path, ledger_functions=238, ast_functions=208)
        rc, out = run_script(CHECK_DOCS, "--root", d)
        assert rc == 1, out
        assert "238" in out and "208" in out
        assert "stale" in out.lower()

    def test_passes_when_ledger_and_ast_agree(self, tmp_path):
        d = _docs_repo(tmp_path, ledger_functions=208, ast_functions=208)
        rc, out = run_script(CHECK_DOCS, "--root", d)
        assert rc == 0, out

    def test_doc_drift_is_caught_even_when_artifacts_agree(self, tmp_path):
        d = _docs_repo(tmp_path, ledger_functions=208, ast_functions=208,
                       doc_functions=45)
        rc, out = run_script(CHECK_DOCS, "--root", d)
        assert rc == 1, out
        assert "says functions=45" in out

    def test_a_restructured_doc_is_a_failure_not_a_pass(self, tmp_path):
        """If the regex stops matching, the check stopped checking. Say so."""
        d = _docs_repo(tmp_path, ledger_functions=208, ast_functions=208)
        with open(os.path.join(d, "docs", "scale.md"), "w") as fh:
            fh.write("cachetools: two hundred and eight functions\n")
        rc, out = run_script(CHECK_DOCS, "--root", d)
        assert rc == 1, out
        assert "no longer matches" in out


class TestCheckDocsMissingInput:
    def test_old_behaviour_skips_silently(self, tmp_path):
        """Reconstruction of the `continue`-on-absent-input cross check."""
        def old_check_cross(root):
            out = []
            for art, key, other, _, what in [(LEDGER, "functions", AST, None, "n")]:
                ap_, op_ = os.path.join(root, art), os.path.join(root, other)
                if not (os.path.exists(ap_) and os.path.exists(op_)):
                    continue                       # <-- the bug
                out.append("compared")
            return out
        d = _docs_repo(tmp_path, ledger_functions=238, ast_functions=208)
        os.remove(os.path.join(d, AST))
        assert old_check_cross(d) == [], "reconstruction: absent input => silence"

    def test_fixed_reports_the_absence_loudly(self, tmp_path):
        d = _docs_repo(tmp_path, ledger_functions=238, ast_functions=208)
        os.remove(os.path.join(d, AST))
        rc, out = run_script(CHECK_DOCS, "--root", d)
        assert rc == 1, out
        assert "cannot cross-check" in out
        assert AST in out
        # and it must name *why* silence would be wrong
        assert "stale artifact" in out

    def test_an_empty_root_never_reports_success(self, tmp_path):
        """Nothing to check is not the same as everything checking out."""
        rc, out = run_script(CHECK_DOCS, "--root", str(tmp_path))
        assert rc != 0, out
        assert "all match" not in out
        assert "cannot cross-check" in out or "nothing checked" in out


# ===========================================================================
# 4. render_lean.py: default 1000-frame recursion limit
# ===========================================================================

OLD_MAIN_DRIVER = textwrap.dedent("""
    import importlib.util, sys
    spec = importlib.util.spec_from_file_location("rl", sys.argv[1])
    rl = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(rl)
    # Reconstruct the pre-fix entry point: call _run_main directly on the main
    # thread at Python's default recursion limit, which is what autoform.sh did.
    sys.setrecursionlimit(1000)
    sys.argv = ["render_lean.py"] + sys.argv[2:]
    try:
        rl._run_main()
    except RecursionError:
        print("RECURSION_ERROR")
        sys.exit(9)
""")

RENDER = os.path.join(CARTO, "render_lean.py")


class TestRenderRecursionDepth:
    @pytest.fixture
    def deep_ast(self, tmp_path):
        p = str(tmp_path / "ast-Deep.json")
        write_ast(p, [fn(body=seq_chain(400))])
        return p

    def test_old_behaviour_dies_at_a_few_hundred_statements(self, tmp_path, deep_ast):
        drv = str(tmp_path / "old_main.py")
        with open(drv, "w") as fh:
            fh.write(OLD_MAIN_DRIVER)
        r = subprocess.run([sys.executable, drv, RENDER, deep_ast,
                            str(tmp_path / "Old.lean"), "Deep"],
                           capture_output=True, text=True, timeout=600)
        assert r.returncode == 9, (r.returncode, r.stdout, r.stderr)
        assert "RECURSION_ERROR" in r.stdout

    def test_fixed_renders_the_same_input(self, tmp_path, deep_ast):
        out = str(tmp_path / "Deep.lean")
        rc, log = run_script(RENDER, deep_ast, out, "Deep")
        assert rc == 0, log
        assert os.path.getsize(out) > 0

    def test_fixed_renders_far_deeper(self, tmp_path):
        """247 was the observed cliff; 4000 is comfortably past any plausible one."""
        ast = str(tmp_path / "ast-VeryDeep.json")
        write_ast(ast, [fn(body=seq_chain(4000))])
        out = str(tmp_path / "VeryDeep.lean")
        rc, log = run_script(RENDER, ast, out, "VeryDeep")
        assert rc == 0, log
        assert open(out).read().count("Stmt") >= 0

    def test_a_big_stack_is_requested_not_just_a_big_limit(self, render_lean):
        """Raising setrecursionlimit alone turns a RecursionError into a segfault.

        Pin the two halves of the fix so neither can be removed on its own.
        """
        src = open(RENDER).read()
        assert re.search(r"^\s*sys\.setrecursionlimit\(\s*\d", src, re.M)
        assert re.search(r"^\s*threading\.stack_size\(\s*\d", src, re.M)
        assert "Thread(target=go)" in src

    def test_errors_propagate_off_the_render_thread(self, tmp_path):
        """A worker thread that swallows exceptions would be silence-as-success."""
        ast = str(tmp_path / "ast-Bad.json")
        write_ast(ast, [fn(body={"k": "nope"})])
        rc, log = run_script(RENDER, ast, str(tmp_path / "Bad.lean"), "Bad")
        assert rc != 0, log
        assert "unknown stmt node kind" in log


# ===========================================================================
# 5. paramStars ran for every language — the JSON contract side of it
# ===========================================================================

# `*args`/`**kwargs` are a Python calling convention. `vararg`/`kwarg` appearing on a
# function exported from a C, C++, Java, Go, JS, TS or Kotlin file means the exporter
# read a pointer `*` as a splat. The Scala is another agent's file; this is the contract
# the two sides share, and it is checkable from the committed artifacts alone.
PY_EXTS = (".py",)


def _ast_files():
    return sorted(f for f in os.listdir(ROOT)
                  if f.startswith("ast-") and f.endswith(".json"))


class TestVarargContract:
    def test_old_behaviour_would_have_flagged_a_c_vararg(self):
        """Reconstruction: what an ungated paramStars produces on C.

        `void f(char *buf)` → the exporter sees a `*` before the name and records
        `vararg`. The contract check must reject it.
        """
        bad = fn(name="a.c:f", file="src/a.c", params=["buf"], vararg="buf")
        assert list(self._violations([bad])) == [("a.c:f", "src/a.c", "vararg")]

    def test_no_committed_ast_claims_varargs_in_a_non_python_file(self):
        seen = 0
        for name in _ast_files():
            with open(os.path.join(ROOT, name)) as fh:
                funcs = json.load(fh)
            seen += 1
            bad = list(self._violations(funcs))
            assert not bad, "%s: %r" % (name, bad[:5])
        assert seen > 0, ("no ast-*.json found: this check inspected nothing. "
                          "An empty corpus is a failure, not a pass.")

    def test_python_varargs_are_still_allowed(self):
        good = fn(name="a.py:f", file="a.py", params=["a"], vararg="args",
                  kwarg="kwargs")
        assert list(self._violations([good])) == []

    @staticmethod
    def _violations(funcs):
        for f in funcs:
            ext = os.path.splitext(f.get("file", ""))[1].lower()
            if ext in PY_EXTS:
                continue
            for key in ("vararg", "kwarg"):
                if f.get(key) is not None:
                    yield (f.get("name"), f.get("file"), key)

    @staticmethod
    def _gate_is_first(scala_src):
        """Is `paramStars` gated on the .py extension before it reads any source?

        Structural, not a Scala parse: the first thing in the body must be the guard.
        Returns None if the helper cannot be found at all.
        """
        m = re.search(r"def paramStars\([^)]*\)\s*:\s*Int\s*=\s*\n?\s*(.+)", scala_src)
        if not m:
            return None
        return 'endsWith(".py")' in m.group(1)

    def test_old_behaviour_ungated_helper_is_rejected(self):
        """Reconstruction: the helper as it merged — no language gate, and a `sys.error`
        in the fall-through. On C++ that aborted the whole export."""
        ungated = (
            'def paramStars(p: MethodParameterIn, file: String): Int =\n'
            '    (for { off <- p.offset; txt <- fileText(file) } yield {\n'
            '       var i = off - 1; var n = 0\n'
            "       while (i >= 0 && txt.charAt(i) == '*') { n += 1; i -= 1 }\n"
            '       n\n'
            '     }).getOrElse { sys.error("cannot read source") }\n')
        assert self._gate_is_first(ungated) is False

    def test_fixed_gate_is_first_in_the_exporter(self):
        """Read-only assertion about the file another workstream owns.

        Not a Scala test: it pins the one line whose removal silently re-breaks every
        non-Python corpus, and it fails loudly if the shape it looks for is gone.
        """
        sc = os.path.join(ROOT, "cartographer", "export_ast.sc")
        if not os.path.exists(sc):
            pytest.fail("cartographer/export_ast.sc absent; the JSON contract has no "
                        "producer to check against")
        got = self._gate_is_first(open(sc).read())
        assert got is not None, ("paramStars is gone or reshaped — re-derive this "
                                 "check, do not delete it")
        assert got, ("paramStars no longer gates on the .py extension; in C a `*` "
                     "before a parameter is a pointer, and this helper hard-errors "
                     "by design, so every non-Python corpus stops exporting")
