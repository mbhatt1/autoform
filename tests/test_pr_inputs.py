"""Oracle inputs that reach a change, the cross-revision model cut, Node module loading
and the pr report's verdict wording.

A seeded `or` -> `and` regression in a function that returns early unless both node
names contain ':' passed the behaviour gate on 122 cases: the suite's never put a ':'
in exactly one argument and the random cases were integers only. These pin the pieces
that close that: literal-derived string inputs (`runtime_backends.mined_literals`,
`differential.literal_cases`), seeded so the same export yields the same inputs at both
revisions; branch coverage of the changed lines (`differential.change_coverage`), so an
`unchanged-on-inputs` that never reached the change does not pass the gate; type-only
imports of uninstalled npm packages dropped the way tsc drops them, and the packages that
are still missing named with the fix; and the report bugs (null shown as `unit`, kotlinc
reported as javac, the level read as the PR verdict, a null `gate.exit_code`, holed
functions counted as gate subjects, two wordings for an added function, an unexplained
"signature/parameter count disagree"). The Kotlin cast test needs Joern
(`AUTOFORM_TEST_JOERN=1`); the Node tests need `node`.
"""
from __future__ import annotations

import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

from conftest import ROOT, SCRIPTS, load

ROOT = Path(ROOT)
pr_mode = load(str(Path(SCRIPTS) / "pr_mode.py"), "af_pr_mode_inputs")
backends = load(str(Path(SCRIPTS) / "runtime_backends.py"), "af_runtime_backends_inputs")

needs_node = pytest.mark.skipif(shutil.which("node") is None, reason="node is required")

LEAD = '''
def lead(source_node, destination_node, fn, mode="default"):
    """Lead time, e.g. 'hub:US'."""
    if ":" not in source_node and ":" not in destination_node:
        return 0
    a, b = source_node.split(":", 1)
    c, d = destination_node.split(":", 1)
    try:
        return int(fn(b, d))
    except Exception:
        return 0
'''


def body(*strings, ints=()):
    """A tiny exported body holding these literals (and a docstring that must be ignored)."""
    items = [{"k": "exprS", "e": {"k": "str", "v": "a docstring is not a literal"}}]
    items += [{"k": "inOp", "a": {"k": "str", "v": s}, "b": {"k": "name", "v": "x"}} for s in strings]
    items += [{"k": "binop", "a": {"k": "int", "v": str(i)}} for i in ints]
    return {"k": "block", "stmts": items}


# ------------------------------------------------------------- literal inputs

def test_literals_are_mined_from_the_body_then_the_file_without_docstrings():
    f = {"name": "m.py:<module>.f", "file": "m.py", "body": body(":", ints=[86400])}
    g = {"name": "m.py:<module>.g", "file": "m.py", "body": body("hub")}
    other = {"name": "n.py:<module>.h", "file": "n.py", "body": body("elsewhere")}
    strings, ints = backends.mined_literals(f, [f, g, other], extra=["head-only"])
    assert strings == [":", "head-only", "hub"]
    assert ints == [86400]
    built = backends.string_inputs(strings)
    # A separator that splits, a compared constant, a prefix, and the pair joined.
    for wanted in ("a:b", ":", ":a", "hub", "hub:", ""):
        assert wanted in built
    assert backends.integer_inputs([86400]) == [86400, 86399, 86401]


def test_literal_cases_reach_the_branch_and_are_the_same_on_every_run(differential, tmp_path,
                                                                    keep_random_state):
    namespace = {}
    exec(compile(LEAD, str(tmp_path / "m.py"), "exec"), namespace)
    f = {"name": "m.py:<module>.lead", "file": "m.py", "params": ["source_node", "destination_node", "fn", "mode"],
         "paramTypes": ["__builtin.str", "__builtin.str", "typing.Callable", "__builtin.str"],
         "body": body(":")}
    stats = {"skip_unencodable_ret": 0}
    first = differential.literal_cases(f, namespace["lead"], [f], 60, stats)
    again = differential.literal_cases(f, namespace["lead"], [f], 60, stats)
    assert [c["args"] for c in first] == [c["args"] for c in again]
    assert {c["origin"] for c in first} == {"literal"}
    # Some input puts ':' in exactly one argument: under `and` that one raises at the split.
    one_colon = [c for c in first
                 if (":" in c["args"][0][1]) != (":" in c["args"][1][1])]
    assert one_colon and any(c["outcome"][0] == "exn" for c in one_colon)
    # An int-annotated parameter keeps the small integers.
    assert all(c["args"][2][0] == "int" for c in first)


def test_source_file_constants_join_the_literals():
    """A Java `static final String` is a field initializer, in no exported body."""
    java = ('public final class Code {\n  public static final String INVALID = "INVALID";\n'
            '  // it\'s the default\n  static String f(String c) { return "A:" + c; }\n'
            '  String t = "x$y";\n}\n')
    assert pr_mode.source_string_literals(java) == ["INVALID", "A:"]


def test_without_string_or_unannotated_parameters_nothing_is_added(differential):
    f = {"name": "m.py:<module>.n", "file": "m.py", "params": ["n"], "paramTypes": ["__builtin.int"],
         "body": body(":")}
    assert differential.literal_cases(f, lambda n: n, [f], 10, {"skip_unencodable_ret": 0}) == []


@pytest.fixture
def keep_random_state():
    """The oracle's global generator is seeded once per process; other tests' expected
    draws depend on its position, so these tests leave it where they found it."""
    import random
    state = random.getstate()
    yield
    random.setstate(state)


def test_c_literal_cases_are_seeded_and_absent_without_literals(differential, keep_random_state):
    import ctypes
    plain = list(differential.c_argument_cases([ctypes.c_int], 8, lambda: 1, boundaries=True))
    assert all(origin != "boundary-literal" for _, origin in plain)
    mined = list(differential.c_argument_cases([ctypes.c_int], 8, lambda: 1, boundaries=True,
                                               literals=[65520, 65521, 65522]))
    literal = [args for args, origin in mined if origin == "boundary-literal"]
    assert literal and all(a[0] in (65520, 65521, 65522) for a in literal)
    again = list(differential.c_argument_cases([ctypes.c_int], 8, lambda: 1, boundaries=True,
                                               literals=[65520, 65521, 65522]))
    assert [a for a, o in again if o == "boundary-literal"] == literal


# ------------------------------------------------------------- change coverage

def _observe(differential, fn, calls):
    seen = []
    for args in calls:
        recorder = differential.ArcRecorder(fn.__code__)
        try:
            with recorder:
                fn(*args)
        except Exception:                                   # noqa: BLE001
            pass
        seen.append((recorder.lines, recorder.arcs))
    return seen


def test_a_changed_condition_that_only_went_one_way_is_not_covered(differential, tmp_path):
    (tmp_path / "m.py").write_text(LEAD)
    namespace = {}
    exec(compile(LEAD, str(tmp_path / "m.py"), "exec"), namespace)
    lead = namespace["lead"]
    record = {"name": "m.py:<module>.lead", "file": "m.py"}
    changed = {4}                       # the `if` line
    # The suite's inputs: both names always carry ':', and integers raise in the test.
    suite = _observe(differential, lead, [("plant:f", "hub:US", lambda *a: 6), (3, 4, 5, 6)])
    got = differential.change_coverage(record, str(tmp_path), changed, suite)
    assert got["covered"] is False and "never evaluated true" in got["note"]
    both = suite + _observe(differential, lead, [("x", "y", None)])
    got = differential.change_coverage(record, str(tmp_path), changed, both)
    assert got["covered"] is True
    assert differential.change_coverage(record, str(tmp_path), changed, [])["covered"] is None


def test_a_changed_statement_never_executed_is_named(differential, tmp_path):
    (tmp_path / "m.py").write_text(LEAD)
    namespace = {}
    exec(compile(LEAD, str(tmp_path / "m.py"), "exec"), namespace)
    record = {"name": "m.py:<module>.lead", "file": "m.py"}
    seen = _observe(differential, namespace["lead"], [("x", "y", None)])
    got = differential.change_coverage(record, str(tmp_path), {9}, seen)   # `return int(...)`
    assert got["covered"] is False and got["unexecuted_lines"] == [9]


def test_changed_head_lines_cover_edits_and_deletion_points():
    before = b"a\nb\nc\nd\n"
    after = b"a\nB\nc\n"
    assert pr_mode._changed_head_lines(before, after) == {2, 4}


def test_an_unchanged_verdict_whose_inputs_missed_the_change_does_not_pass_the_gate():
    name = "m.py:<module>.lead"
    cross = {"runtime_cases": [{"name": name, "comparison": "agree"}] * 5,
             "change_coverage": {name: {"covered": False, "note": "the condition at line 4 never evaluated true"}}}
    record = {"name": name, "path": "m.py", "file": "m.py", "change": "modified", "line": 1,
              "detection": "python-ast", "language": "python"}
    out, _ = pr_mode.behaviour_results([record], cross, None, {})
    assert out[name]["status"] == "unchanged-on-inputs" and out[name]["change_covered"] is False
    assert "branch coverage: the inputs did not reach the change" in out[name]["reason"]
    gate = pr_mode.evidence_gate([dict(record, behaviour=out[name])], ["behaviour-changed"])
    assert gate["status"] == "inconclusive" and gate["exit_code"] == pr_mode.EXIT_INCONCLUSIVE
    assert gate["change_not_reached"] == [name]
    covered = dict(cross, change_coverage={name: {"covered": True}})
    out, _ = pr_mode.behaviour_results([record], covered, None, {})
    assert pr_mode.evidence_gate([dict(record, behaviour=out[name])], ["behaviour-changed"])["status"] == "evidence"


# ------------------------------------------------------------- the gate and the report

def _fn(name, status, **extra):
    return dict({"name": name, "path": "A.java", "file": "A.java", "change": "modified", "line": None,
                 "detection": "changed-file", "language": "java",
                 "behaviour": {"status": status, "reason": "r"}}, **extra)


def test_functions_identical_but_for_holes_are_listed_but_not_gate_subjects():
    results = [_fn("A.f:int(int)", "unchanged-on-inputs"),
               _fn("A.g:int(int)", "not-compared", identical_but_holed=True),
               _fn("A.h:int(int)", "not-compared", identical_but_holed=True)]
    gate = pr_mode.evidence_gate(results, ["behaviour-changed"])
    assert gate["status"] == "evidence" and gate["subjects"] == 1
    assert gate["identical_but_holed_not_counted"] == 2
    # ... unless nothing else is there: then they are the subjects, and nothing was compared.
    gate = pr_mode.evidence_gate(results[1:], ["behaviour-changed"])
    assert gate["status"] == "inconclusive" and gate["subjects"] == 2


def test_kotlin_compile_failures_name_kotlinc():
    info = {"primitive_instance_candidates": 1, "kotlin_compile_attempts": [],
            "compile_failure_causes": {"unresolved reference": 1}, "files_failed": 1, "files_candidate": 1}
    assert pr_mode.compile_failure(info, {}).startswith("kotlinc failed on 1/1")
    java = {"primitive_static_candidates": 1, "compile_failure_causes": {"missing symbol": 1}}
    assert pr_mode.compile_failure(java, {}).startswith("javac failed")


def test_identical_counter_inputs_are_shown_once():
    name = "p.C.f:java.lang.String(java.lang.String)"
    row = {"function": name, "args": "(null)", "detail": "jvm=str 'X' lean=str 'Y'",
           "lean_repr": 'Autoform.Core.EResult.val (Autoform.Core.Val.str "Y")', "origin": "random",
           "observation": {"outcome": ["val", ["str", "X"]]}}
    record = {"name": name, "path": "C.java", "file": "C.java", "change": "modified"}
    out, _ = pr_mode.behaviour_results([record], {"runtime_cases": [], "divergence_detail": [row] * 4},
                                       None, {})
    assert out[name]["diverging"] == 4 and len(out[name]["counter_inputs"]) == 1
    assert out[name]["counter_inputs"][0]["call"] == "C.f(null)"


def test_a_jvm_null_argument_is_shown_as_null(differential):
    assert differential.show_arg(["unit"], "java") == "null"
    assert differential.show_arg(["unit"], "kotlin") == "null"
    assert differential.show_arg(["unit"], "python") == "unit"
    assert differential.show_arg(["str", "a"], "java") == "str 'a'"


def test_the_verdict_leads_the_markdown_and_sarif_and_the_gate_carries_its_exit_code():
    function = _fn("A.f:int(int)", "changed", level="proved", reason="proved in the kernel", artifacts=[])
    function["behaviour"].update(diverging=1, counter_inputs=[{"call": "A.f(int 1)", "base_model": "returns int 1",
                                                               "head_runtime": "returns int 2"}])
    report = {"tool_version": "0", "module": "M", "report_dir": "/tmp/x",
              "repository": {"uri": "file:///tmp/r", "path": "/tmp/r", "subdir": "."},
              "base": {"ref": "b", "commit": "a" * 40}, "head": {"ref": "h", "commit": "b" * 40},
              "detection": "changed-file", "exporter": {"status": "available"}, "files": [], "errors": [],
              "selection": {"changed": [], "selected": [], "closure": [], "missing": []},
              "stages": {}, "functions": [function], "removed": [], "summary": {},
              "behaviour": {"suppressed_as_model_noise": 0, "languages": ["java"]},
              "gate": {"fail_on": ["behaviour-changed"], "status": "evidence", "exit_code": 1}}
    text = pr_mode.markdown_comment(report)
    assert text.index("### PR verdict") < text.index("### Head model conformance")
    assert "| `A.f:int(int)` | modified | **changed** |" in text
    assert "fails this gate" in text
    sarif = pr_mode.sarif_document(report)
    assert pr_mode.validate_sarif(sarif) == []
    results = sarif["runs"][0]["results"]
    assert results[0]["ruleId"] == "autoform/behaviour-changed"
    level = results[1]["message"]["text"]
    assert level.index("PR verdict: changed") < level.index("head model conformance: proved")
    assert sarif["runs"][0]["properties"]["gate"]["exit_code"] == 1
    source = (ROOT / "scripts/pr_mode.py").read_text()
    assert 'report["gate"] = dict(gate, exit_code=exit_code)' in source


def test_one_wording_for_an_added_function():
    source = (ROOT / "scripts/pr_mode.py").read_text()
    assert "added at head, no base behaviour" not in source
    assert source.count("ADDED_AT_HEAD") >= 3


def test_a_signature_count_mismatch_says_which_counts(differential, tmp_path, keep_random_state):
    member_ext = {"name": "p.V.allowed:boolean(p.Config,java.lang.String,java.lang.String)",
                  "file": "V.kt", "params": ["this", "a", "b"], "body": {"k": "skip"},
                  "paramTypes": ["p.V", "java.lang.String", "java.lang.String"]}
    odd = {"name": "p.J.f:int(int,int)", "file": "J.java", "params": ["a"], "body": {"k": "skip"}}
    _, _, skipped = differential.java_backend(str(tmp_path), [member_ext], 1, kotlin=True)
    assert "member extension function" in skipped[member_ext["name"]]
    assert "Config" in skipped[member_ext["name"]] and "3 type(s) for 2 parameter(s)" in skipped[member_ext["name"]]
    _, _, skipped = differential.java_backend(str(tmp_path), [odd], 1)
    assert "lists 2 parameter type(s) (int, int)" in skipped[odd["name"]]
    assert "has 1 (a)" in skipped[odd["name"]]


# ------------------------------------------------------------- the cross-revision model cut

def test_the_non_python_base_model_is_the_compared_files_and_their_callees():
    source = (ROOT / "scripts/pr_mode.py").read_text()
    start = source.index("def run_behaviour(")
    block = source[start:source.index("def sarif_document(", start)]
    assert "cut, _, _ = select_functions(functions, roots)" in block
    assert '"--universe", str(ast_full)' in block
    assert "shutil.copy(ast_full, ast_path)" in block          # Python keeps the whole export
    funcs = [{"name": "p.A.f:int(int)", "file": "A.java", "body": {"k": "call", "f": "p.B.g:int(int)"}},
             {"name": "p.A.<init>:void()", "file": "A.java", "body": {"k": "skip"}},
             {"name": "p.B.g:int(int)", "file": "B.java", "body": {"k": "skip"}},
             {"name": "p.C.h:int(int)", "file": "C.java", "body": {"k": "skip"}}]
    cut, _, _ = pr_mode.select_functions(funcs, [f["name"] for f in funcs if f["file"] == "A.java"])
    assert sorted(f["name"] for f in cut) == ["p.A.<init>:void()", "p.A.f:int(int)", "p.B.g:int(int)"]


# ------------------------------------------------------------- Node module loading

def _ts_tree(root, keep=False):
    (root / "src").mkdir(parents=True)
    options = {"strict": True, **({"verbatimModuleSyntax": True} if keep else {})}
    (root / "tsconfig.json").write_text(json.dumps({"compilerOptions": options}))
    (root / "src/a.ts").write_text(
        "import { Stage } from '@scope/types-only';\n"
        "import type { Other } from 'other-types';\n"
        "import { helper } from './b';\n"
        "export function f(s: Stage, n: number): number { return n + 1; }\n"
        "export function g(x: string): string { return helper(x); }\n")
    (root / "src/b.ts").write_text(
        "import R from '@scope/runtime';\n"
        "import { join } from 'node:path';\n"
        "export function helper(x: string): string { return R.go(x) + join('a', 'b'); }\n")


@needs_node
def test_type_only_imports_of_missing_packages_are_dropped_and_the_rest_named(tmp_path):
    _ts_tree(tmp_path / "tree")
    (tmp_path / "work").mkdir()
    missing, info = backends.prepare_node_imports(tmp_path / "tree", tmp_path / "work")
    a = (tmp_path / "tree/src/a.ts").read_text()
    assert "@scope/types-only" not in a and a.count("\n") == 5      # lines kept
    assert info["type_only_imports_elided"] == 1
    # `a.ts` still loads `@scope/runtime` through `./b`: named, with the fix.
    assert missing[str(tmp_path / "tree/src/a.ts")] == ["@scope/runtime"]
    reason = backends.missing_packages_reason(missing[str(tmp_path / "tree/src/a.ts")])
    assert "@scope/runtime" in reason and "npm ci" in reason


@needs_node
def test_a_project_that_keeps_type_imports_is_left_alone(tmp_path):
    _ts_tree(tmp_path / "tree", keep=True)
    (tmp_path / "work").mkdir()
    _, info = backends.prepare_node_imports(tmp_path / "tree", tmp_path / "work")
    assert info["type_only_imports_elided"] == 0
    assert "@scope/types-only" in (tmp_path / "tree/src/a.ts").read_text()


@needs_node
def test_the_node_backend_loads_a_module_once_its_type_only_import_is_dropped(tmp_path):
    _ts_tree(tmp_path / "tree")
    work = tmp_path / "work"
    work.mkdir()
    funcs = [{"name": "src/a.ts::program:f", "file": "src/a.ts", "params": ["s", "n"],
              "paramTypes": ["ANY", "__ecma.Number"], "body": {"k": "skip"}},
             {"name": "src/a.ts::program:g", "file": "src/a.ts", "params": ["x"],
              "paramTypes": ["__ecma.String"], "body": {"k": "skip"}}]
    cases, info, skipped = backends.node_backend(str(tmp_path / "tree"), funcs, 2, "ts", str(work))
    # The module imports `./b`, which needs `@scope/runtime`: the load fails, and says why.
    assert "1 package(s) not installed, run `npm ci`" in skipped["src/a.ts::program:f"]
    assert "@scope/runtime" in skipped["src/a.ts::program:f"]
    assert info["imports"]["type_only_imports_elided"] == 1
    (tmp_path / "tree/src/b.ts").write_text("export function helper(x: string): string { return x; }\n")
    work2 = tmp_path / "work2"
    work2.mkdir()
    cases, info, skipped = backends.node_backend(str(tmp_path / "tree"), funcs, 2, "ts", str(work2))
    assert {c["name"] for c in cases} == {"src/a.ts::program:f", "src/a.ts::program:g"}, skipped


# ------------------------------------------------------------- the Kotlin cast label

KOTLIN_CAST = """
package p
fun pick(m: Map<String, Any>): String = m["k"] as String
fun maybe(m: Map<String, Any>): String? = m["k"] as? String
"""


def test_a_kotlin_cast_is_not_labelled_as_a_c_pointer_cast(tmp_path):
    if os.environ.get("AUTOFORM_TEST_JOERN") != "1":
        pytest.skip("set AUTOFORM_TEST_JOERN=1 to export Kotlin through Joern")
    home = Path(os.environ.get("JOERN_HOME", Path.home() / "joern"))
    joern = home / "joern-cli" if (home / "joern-cli").is_dir() else home
    if not (joern / "joern").is_file():
        pytest.skip("Joern not found (JOERN_HOME)")
    (tmp_path / "src").mkdir()
    (tmp_path / "src/C.kt").write_text(KOTLIN_CAST)
    for args in ([joern / "joern-parse", tmp_path / "src", "--output", tmp_path / "cpg.bin"],
                 [joern / "joern", "--script", ROOT / "cartographer/export_ast.sc",
                  "--param", "cpgPath=%s" % (tmp_path / "cpg.bin"),
                  "--param", "out=%s" % (tmp_path / "ast.json"), "--param", "dataModel=lp64"]):
        r = subprocess.run([str(a) for a in args], cwd=str(tmp_path), capture_output=True, text=True,
                           timeout=900)
        assert r.returncode == 0, (r.stdout + r.stderr)[-2000:]
    text = (tmp_path / "ast.json").read_text()
    assert "op:cast:pointer" not in text
    assert "op:cast:kotlin-as" in text
