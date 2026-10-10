"""The differential oracle's per-function verdict cache (`scripts/oracle_cache.py`).

Two layers. The keying and the store are tested directly on a hand-made AST, without a
corpus or a Lean build: which inputs invalidate which functions is the whole soundness
argument of the cache, so it is tested as data. The end-to-end behaviour -- a second run
reports from the cache and SAYS so, a one-function change re-compares that function
only, `--no-cache` re-compares everything -- runs the real oracle on the Node fixture of
`tests/test_differential_backends.py` and is gated like it (`AUTOFORM_TEST_ORACLES=1`).
"""
import copy
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import oracle_cache  # noqa: E402

from test_differential_backends import (FIXTURES, GENERATED, _oracle_env,  # noqa: E402,F401
                                        generated_module, _skip_unless_runnable)


def _fn(name, body, **extra):
    return dict(name=name, file="pkg/m.py", params=["x"], body=body, **extra)


def _funcs():
    """A module body, a class with a base class (whose dunder is reached by dispatch),
    a method calling a sibling by name, a free function reaching a method by `fnref`,
    and an unrelated free function."""
    mod = "pkg/m.py:<module>"
    return [
        dict(name=mod, file="pkg/m.py", params=[], body={"k": "skip"},
             classDeclarations=[
                 {"name": mod + ".Base", "shortName": "Base", "bases": [],
                  "attributes": []},
                 {"name": mod + ".Cache", "shortName": "Cache", "bases": [mod + ".Base"],
                  "attributes": []}]),
        _fn(mod + ".Base.__len__", {"k": "ret", "e": {"k": "int", "v": "1"}}),
        _fn(mod + ".Cache.get", {"k": "ret", "e": {"k": "mcall", "recv": {"k": "name", "v": "self"},
                                                   "m": "peek", "args": []}}),
        _fn(mod + ".Cache.peek", {"k": "ret", "e": {"k": "int", "v": "2"}}),
        _fn(mod + ".use", {"k": "ret", "e": {"k": "callV", "f": {"k": "fnref", "v": mod + ".Cache.get"},
                                             "args": []}}),
        _fn(mod + ".alone", {"k": "ret", "e": {"k": "int", "v": "3"}}),
    ]


def _cases(funcs):
    mod = "pkg/m.py:<module>"
    heap_cache = [[mod + ".Cache", [], None]]
    return {
        mod + ".Base.__len__": [dict(name=mod + ".Base.__len__", heap=[[mod + ".Base", [], None]],
                                 self=["ref", 0], args=[], outcome=["val", ["int", 1]],
                                 origin="test-suite")],
        mod + ".Cache.get": [dict(name=mod + ".Cache.get", heap=heap_cache, self=["ref", 0],
                                 args=[], outcome=["val", ["int", 2]], origin="test-suite")],
        mod + ".Cache.peek": [dict(name=mod + ".Cache.peek", heap=heap_cache, self=["ref", 0],
                                  args=[], outcome=["val", ["int", 2]], origin="constructed")],
        mod + ".use": [dict(name=mod + ".use", heap=[], self=None, args=[["int", 1]],
                           outcome=["val", ["int", 2]], origin="random")],
        mod + ".alone": [dict(name=mod + ".alone", heap=[], self=None, args=[["int", 1]],
                             outcome=["val", ["int", 3]], origin="random")],
    }


ENV = {"schema": oracle_cache.SCHEMA, "semantics": "s" * 64, "renderer": "r" * 64,
       "harness": "h" * 64, "toolchain": "t" * 64, "runtime": "Python 3.11.9"}


def _keys(funcs, cases, env=ENV):
    return {n: p["key"] for n, p in oracle_cache.plan(funcs, cases, env).items()}


def _changed(before, after):
    return {n for n in before if before[n] != after[n]}


def test_dependencies_follow_names_dispatch_and_inheritance():
    funcs = _funcs()
    deps = oracle_cache.dependencies(funcs, _cases(funcs))
    mod = "pkg/m.py:<module>"
    # a sibling method reached by `mcall`, and the base class's dunder by dispatch
    assert deps[mod + ".Cache.get"] >= {mod + ".Cache.peek", mod + ".Base.__len__"}
    # a free function that holds an `fnref` to a method reaches, through it, the
    # sibling it calls and the inherited dunder
    assert deps[mod + ".use"] >= {mod + ".Cache.get", mod + ".Cache.peek", mod + ".Base.__len__"}
    # a non-dunder method of the class is not pulled in by the class alone: `peek`
    # names nothing, so it depends only on the dunders it could dispatch to
    assert deps[mod + ".Cache.peek"] == frozenset({mod + ".Base.__len__"})
    # the unrelated free function depends on nothing
    assert deps[mod + ".alone"] == frozenset()


def test_one_function_change_invalidates_it_and_its_dependents_only():
    funcs = _funcs()
    cases = _cases(funcs)
    before = _keys(funcs, cases)
    changed = copy.deepcopy(funcs)
    peek = next(f for f in changed if f["name"].endswith("Cache.peek"))
    peek["body"] = {"k": "ret", "e": {"k": "int", "v": "20"}}
    after = _keys(changed, cases)
    mod = "pkg/m.py:<module>"
    assert _changed(before, after) == {mod + ".Cache.peek", mod + ".Cache.get", mod + ".use"}
    # a base-class dunder change reaches every subclass method and whoever calls them
    changed = copy.deepcopy(funcs)
    size = next(f for f in changed if f["name"].endswith("Base.__len__"))
    size["body"] = {"k": "ret", "e": {"k": "int", "v": "10"}}
    after = _keys(changed, cases)
    assert _changed(before, after) == {mod + ".Base.__len__", mod + ".Cache.get",
                                       mod + ".Cache.peek", mod + ".use"}


def test_module_body_semantics_runtime_and_cases_invalidate():
    funcs = _funcs()
    cases = _cases(funcs)
    before = _keys(funcs, cases)
    # the module body runs as an initializer for every function: everything misses
    changed = copy.deepcopy(funcs)
    changed[0]["body"] = {"k": "setGlobal", "x": "LIMIT", "e": {"k": "int", "v": "9"}}
    assert _changed(before, _keys(changed, cases)) == set(before)
    # the semantics, the renderer, the harness, the toolchain, the runtime: everything
    for part in ("semantics", "renderer", "harness", "toolchain", "runtime"):
        env = dict(ENV, **{part: "changed"})
        assert _changed(before, _keys(funcs, cases, env)) == set(before), part
    # a different recorded outcome for one function: that function only
    changed_cases = copy.deepcopy(cases)
    changed_cases["pkg/m.py:<module>.alone"][0]["outcome"] = ["val", ["int", 4]]
    assert _changed(before, _keys(funcs, changed_cases)) == {"pkg/m.py:<module>.alone"}
    # an extra case for one function: that function only
    changed_cases = copy.deepcopy(cases)
    changed_cases["pkg/m.py:<module>.alone"].append(
        dict(changed_cases["pkg/m.py:<module>.alone"][0], args=[["int", 2]]))
    assert _changed(before, _keys(funcs, changed_cases)) == {"pkg/m.py:<module>.alone"}


def test_store_hit_miss_and_invalidate(tmp_path):
    funcs = _funcs()
    cases = _cases(funcs)
    plan = oracle_cache.plan(funcs, cases, ENV)
    name = "pkg/m.py:<module>.alone"
    entry, why = oracle_cache.lookup(tmp_path, name, plan[name])
    assert entry is None and why == "no entry"
    verdicts = {d: {"kind": "agree", "desc": "cpython=3 lean=3", "lean_repr": "Val.int 3"}
                for d in plan[name]["cases"]}
    path = oracle_cache.store(tmp_path, name, plan[name], verdicts, module="M",
                              when="2026-10-10T00:00:00Z")
    assert path.parent == tmp_path and path.suffix == ".json"
    entry, why = oracle_cache.lookup(tmp_path, name, plan[name])
    assert why == "hit" and entry["computed_at"] == "2026-10-10T00:00:00Z"
    assert entry["verdicts"][plan[name]["cases"][0]]["kind"] == "agree"
    # the function's translation changed: a miss that names the input that moved
    changed = copy.deepcopy(funcs)
    next(f for f in changed if f["name"] == name)["body"] = {"k": "ret", "e": {"k": "int", "v": "4"}}
    entry, why = oracle_cache.lookup(tmp_path, name, oracle_cache.plan(changed, cases, ENV)[name])
    assert entry is None and why == "function changed"
    # the recorded cases changed
    changed_cases = copy.deepcopy(cases)
    changed_cases[name][0]["args"] = [["int", 7]]
    entry, why = oracle_cache.lookup(tmp_path, name, oracle_cache.plan(funcs, changed_cases, ENV)[name])
    assert entry is None and why == "cases changed"
    # the semantics changed
    entry, why = oracle_cache.lookup(
        tmp_path, name, oracle_cache.plan(funcs, cases, dict(ENV, semantics="x"))[name])
    assert entry is None and why == "environment changed"
    # an entry from another schema is not read
    data = json.loads(path.read_text())
    data["schema"] = oracle_cache.SCHEMA + 1
    path.write_text(json.dumps(data))
    assert oracle_cache.lookup(tmp_path, name, plan[name]) == (None, "no entry")


RENDERED = """import Autoform.Lang.Core.Semantics
namespace Autoform.Generated.M

/-- `pkg/m.py:<module>.alone`  (from `pkg/m.py`) -/
def f_pkg_m_py__module__alone : Func :=
  { name := "pkg/m.py:<module>.alone"
  , body := (.ret (.lit (.int 3))) }

/-- `pkg/m.py:<module>.Cache.peek`  (from `pkg/m.py`) -/
def f_pkg_m_py__module__Cache_peek : Func :=
  { name := "pkg/m.py:<module>.Cache.peek"
  , body := (.ret (.lit (.int 2))) }

/-- `<autoform>.<generator>.__next__` -/
def f__autoform___generator____next__ : Func :=
  { name := "<autoform>.<generator>.__next__", body := .skip }

/-- Module-level initializers -/
def moduleInits : List Func := [f_pkg_m_py__module_]

def program : Program := { dialect := .python, funcs := [
  f_pkg_m_py__module__alone,
  f_pkg_m_py__module__Cache_peek
] }

end Autoform.Generated.M
"""


def test_rendered_definition_is_part_of_the_key(tmp_path):
    """A hand edit to the `.lean` that no AST change explains must invalidate exactly
    the definition it touches (and its dependents); the stale cache would otherwise
    replay an agreement about a definition the interpreter never saw."""
    lean = tmp_path / "M.lean"
    lean.write_text(RENDERED)
    chunks, rest = oracle_cache.rendered_chunks([lean])
    assert set(chunks) == {"pkg/m.py:<module>.alone", "pkg/m.py:<module>.Cache.peek",
                           "<autoform>.<generator>.__next__"}
    funcs = _funcs()
    cases = _cases(funcs)
    before = _keys(funcs, cases)
    with_lean = {n: p["key"] for n, p in oracle_cache.plan(funcs, cases, ENV, rendered=[lean]).items()}
    assert _changed(before, with_lean) == set(before)          # the module is now an input
    lean.write_text(RENDERED.replace("(.int 3)", "(.int 4)"))
    edited = {n: p["key"] for n, p in oracle_cache.plan(funcs, cases, ENV, rendered=[lean]).items()}
    assert _changed(with_lean, edited) == {"pkg/m.py:<module>.alone"}
    chunks2, rest2 = oracle_cache.rendered_chunks([lean])
    assert rest2 == rest and chunks2["pkg/m.py:<module>.Cache.peek"] == chunks["pkg/m.py:<module>.Cache.peek"]
    # a dependent follows its callee's rendering; the context follows everything else
    lean.write_text(RENDERED.replace("(.int 2)", "(.int 5)"))
    edited = {n: p["key"] for n, p in oracle_cache.plan(funcs, cases, ENV, rendered=[lean]).items()}
    assert _changed(with_lean, edited) == {"pkg/m.py:<module>.Cache.peek", "pkg/m.py:<module>.Cache.get",
                                           "pkg/m.py:<module>.use"}
    lean.write_text(RENDERED.replace("body := .skip", "body := (.ret (.lit (.int 0)))"))
    edited = {n: p["key"] for n, p in oracle_cache.plan(funcs, cases, ENV, rendered=[lean]).items()}
    assert _changed(with_lean, edited) == set(before)
    name = "pkg/m.py:<module>.alone"
    plan = oracle_cache.plan(funcs, cases, ENV, rendered=[lean])
    oracle_cache.store(tmp_path / "c", name, plan[name], {d: {"kind": "agree"} for d in plan[name]["cases"]},
                       module="M")
    lean.write_text(RENDERED.replace("(.int 3)", "(.int 4)"))
    plan = oracle_cache.plan(funcs, cases, ENV, rendered=[lean])
    assert oracle_cache.lookup(tmp_path / "c", name, plan[name]) == (None, "rendering changed")


def test_entry_paths_are_distinct_and_filesystem_safe(tmp_path):
    a = oracle_cache.entry_path(tmp_path, "pkg/m.py:<module>.Cache.get")
    b = oracle_cache.entry_path(tmp_path, "pkg/m.py:<module>.Cache.get<undecorated>")
    assert a != b and a.parent == b.parent == tmp_path
    assert re.fullmatch(r"[A-Za-z0-9_.-]+\.json", a.name)


# ------------------------------------------------------------------ end to end

def _run_oracle(ast, source, module, work, cache, *extra):
    r = subprocess.run([sys.executable, str(ROOT / "scripts/differential.py"), str(ast),
                        str(source), module, "3", "--language", "js",
                        "--cache-dir", str(cache), *extra],
                       capture_output=True, text=True, cwd=work, env=_oracle_env(),
                       timeout=900)
    report = json.loads((work / "conformance.json").read_text())
    summary = next((l for l in r.stdout.splitlines() if " COMPARED" in l), "")
    compared_line = re.search(r", (\d+) COMPARED ", summary)
    return r, report, summary, int(compared_line.group(1)) if compared_line else None


def test_second_run_is_served_from_the_cache_and_says_so(tmp_path, generated_module):
    filename, text, funcs, _, runtimes = FIXTURES["js"]
    _skip_unless_runnable(runtimes)
    source = tmp_path / "source"
    source.mkdir()
    (source / filename).write_text(text)
    ast = tmp_path / "ast.json"
    ast.write_text(json.dumps(funcs))
    module = "DiffOracleCacheJs"
    generated_module(module, ast)
    cache = tmp_path / "cache"
    names = {f["name"] for f in funcs}

    work = tmp_path / "run1"; work.mkdir()
    r, report, summary, compared = _run_oracle(ast, source, module, work, cache)
    assert r.returncode == 0, (r.stdout[-2000:], r.stderr[-2000:])
    assert report["cache"]["functions_from_cache"] == 0
    assert report["cache"]["functions_stored"] == len(names)
    assert compared == len(names) and "cached" not in summary
    assert not any("cached_from" in c for c in report["runtime_cases"])
    assert len(list(cache.glob("*.json"))) == len(names)

    work = tmp_path / "run2"; work.mkdir()
    r, report2, summary, compared = _run_oracle(ast, source, module, work, cache)
    assert r.returncode == 0, (r.stdout[-2000:], r.stderr[-2000:])
    # nothing was compared now, and the summary says exactly that
    assert compared == 0 and "COMPARED now" in summary
    assert report2["cache"]["functions_from_cache"] == len(names)
    assert report2["cache"]["functions_compared_now"] == 0
    assert report2["coverage"]["compared"] == len(names)
    assert report2["coverage"]["compared_now"] == 0
    assert report2["coverage"]["compared_from_cache"] == len(names)
    assert all(c.get("cached_from") == report2["cache"]["cached_from"][0]
               for c in report2["runtime_cases"])
    assert all(v.startswith("compared: cached from ")
               for v in report2["coverage"]["by_status"].values())
    assert report2["coverage"]["status_counts"]["compared"] == len(names)
    # the agreement itself is the same evidence, now attributed to its run
    assert report2["agree"] == report["agree"] and report2["divergences"] == 0

    # the rendered definition of one function is edited by hand (no AST change): that
    # function is re-compared against the edited module and DIVERGES, which a replay
    # of its stored agreement would have hidden; the others are replayed
    lean = GENERATED / (module + ".lean")
    rendered = lean.read_text()
    assert rendered.count("(.int 40)") == 1
    lean.write_text(rendered.replace("(.int 40)", "(.int 42)"))
    forty = next(f for f in funcs if f["name"].endswith("forty"))
    work = tmp_path / "run3-edited-lean"; work.mkdir()
    r, report_e, summary, compared = _run_oracle(ast, source, module, work, cache)
    assert r.returncode == 1, (r.stdout[-2000:], r.stderr[-2000:])
    assert compared == 1, summary
    assert report_e["cache"]["misses"] == {forty["name"]: "rendering changed"}
    # every case of the edited function diverges (one per recorded call), none other
    assert report_e["divergences"] == report_e["cache"]["cases_compared_now"] >= 1
    assert {d["function"] for d in report_e["divergence_detail"]} == {forty["name"]}
    assert all(d["cached_from"] is None for d in report_e["divergence_detail"])
    assert report_e["agree"] == report["agree"] - report_e["divergences"]
    lean.write_text(rendered)

    # one function changes (source and translation): it is re-compared, the others
    # are replayed, and the summary counts the one real comparison
    (source / filename).write_text(text.replace("return 40", "return 41"))
    changed = copy.deepcopy(funcs)
    forty = next(f for f in changed if f["name"].endswith("forty"))
    forty["body"] = {"k": "ret", "e": {"k": "int", "v": "41"}}
    assert forty["name"] == report_e["divergence_detail"][0]["function"]
    ast.write_text(json.dumps(changed))
    generated_module(module, ast)
    work = tmp_path / "run3"; work.mkdir()
    r, report3, summary, compared = _run_oracle(ast, source, module, work, cache)
    assert r.returncode == 0, (r.stdout[-2000:], r.stderr[-2000:])
    assert compared == 1
    assert report3["cache"]["functions_compared_now"] == 1
    assert report3["cache"]["misses"] == {forty["name"]: "function changed"}
    assert report3["divergences"] == 0
    assert report3["coverage"]["by_status"][forty["name"]] == "compared"
    assert report3["cache"]["functions_stored"] == 1

    # --no-cache: everything is compared now, nothing is replayed
    work = tmp_path / "run4"; work.mkdir()
    r, report4, summary, compared = _run_oracle(ast, source, module, work, cache, "--no-cache")
    assert r.returncode == 0, (r.stdout[-2000:], r.stderr[-2000:])
    assert compared == len(names) and "cached" not in summary
    assert report4["cache"]["consulted"] is False
    assert report4["cache"]["functions_from_cache"] == 0
    assert set(report4["cache"]["miss_reasons"]) == {"--no-cache"}
