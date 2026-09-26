"""Traversal order and sharing affect generated helper identities and truth caches."""
from copy import deepcopy
from pathlib import Path
import subprocess
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "cartographer"))
from ast_tools import rewrite_json
from generator_lowering import lower_generators, name, node, transform, walk
from python_truth_lowering import lower_truth_conditions
from python_truth_values import lower_truth_values


def test_passes_remain_importable_as_namespace_modules():
    result = subprocess.run([sys.executable, "-c", "from cartographer import "
        "generator_lowering, python_truth_lowering, python_truth_values"],
        cwd=Path(__file__).resolve().parents[1], capture_output=True, text=True)
    assert result.returncode == 0, result.stderr


def test_walk_and_transform_preserve_their_distinct_orders():
    source = {"k": "root", "a": [{"k": "first"}, {"k": "second"}],
              "b": {"k": "last"}, "scalar": None}
    before = deepcopy(source)
    visited = []

    def rewrite(copied):
        visited.append(copied["k"])
        if copied["k"] == "second":
            return {"k": "replacement", "child": {"k": "new"}}
        return copied

    result = transform(source, rewrite)
    assert [item["k"] for item in walk(source)] == ["root", "last", "second", "first"]
    assert visited == ["first", "second", "last", "root"]
    assert list(result) == list(source)
    assert result["a"][1] == {"k": "replacement", "child": {"k": "new"}}
    assert result["a"] is not source["a"]
    assert source == before


@pytest.mark.parametrize("memoize, visits", [(False, 2), (True, 1)])
def test_rewrite_alias_policy_includes_lists(memoize, visits):
    shared = [{"k": "leaf"}]
    source = [shared, shared]
    originals = []

    def rewrite(original, copied):
        originals.append(original)
        copied["visit"] = len(originals)
        return copied

    result = rewrite_json(source, rewrite, memoize=memoize)
    assert len(originals) == visits
    assert all(original is shared[0] for original in originals)
    assert (result[0] is result[1]) is memoize
    assert (result[0][0] is result[1][0]) is memoize
    assert result[0] is not shared
    assert source == [[{"k": "leaf"}], [{"k": "leaf"}]]


@pytest.mark.parametrize("memoize", [False, True])
def test_deep_mixed_containers_do_not_use_python_recursion(memoize):
    source = None
    for _ in range(12000):
        source = {"child": [source]}
    result = rewrite_json(source, lambda original, copied: copied, memoize=memoize)
    for _ in range(12000):
        assert result is not source
        assert result["child"] is not source["child"]
        result, source = result["child"][0], source["child"][0]
    assert result is source is None


def test_each_generator_expression_occurrence_gets_its_own_factory():
    expression = node("genExpr", sink="sink", generator={"locals": ["x"], "captures": []},
        body=node("forIn", x="x", e=name("values"), body=node("exprS", e=node(
            "mcall", recv=name("sink"), m="append", args=[name("x")]))))
    function = {"name": "probe", "params": [],
                "body": node("ret", e=node("tupleE", items=[expression, expression]))}
    before = deepcopy(function)
    lowered = lower_generators([function])[0]
    calls = lowered["body"]["e"]["items"]
    assert [call["f"] for call in calls] == ["probe.<genexpr>0", "probe.<genexpr>9"]
    assert [helper["name"] for helper in lowered["generatorHelpers"]] == [
        "<autoform>.<generator>." + method
        for method in ("__init__", "__iter__", "__read_local__", "__next__", "send", "close", "throw")
    ] + ["<generator>.probe.<genexpr>0.<resume>", "probe.<genexpr>0",
         "<generator>.probe.<genexpr>9.<resume>", "probe.<genexpr>9"]
    assert function == before


def test_shared_truth_expressions_keep_one_helper_and_source_analysis():
    cached = node("name", v="a", pythonTruthCache=node("name", v="cache"))
    shared = node("binop", op="&&", a=cached, b=name("b"))
    expression = node("binop", op="||", a=shared, b=shared)
    body = node("ret", e=node("tupleE", items=[expression, expression]))
    analysis = node("ifte", c=expression, t=node("skip"), e=node("skip"))
    function = {"name": "probe", "file": "probe.py", "body": body, "analysisBody": analysis,
                "generatorHelpers": [{"name": "resume", "body": body}]}
    before = deepcopy(function)
    lowered = lower_truth_values([function])[0]
    assert [helper["name"] for helper in lowered["truthHelpers"]] == [
        "probe<truth:0>", "probe<truth:1>", "resume<truth:0>", "resume<truth:1>"]
    items = lowered["body"]["e"]["items"]
    assert items[0] is items[1]
    assert items[0]["a"]["f"] == node("closure", f="probe<truth:1>")
    pair = lowered["truthHelpers"][0]["body"]["a"]["e"]
    assert pair["items"][1] == name("cache")
    assert lowered["analysisBody"] is analysis
    assert lowered["generatorHelpers"][0]["analysisBody"] is body
    conditioned = lower_truth_conditions(lowered)
    assert conditioned["analysisBody"] is analysis
    assert conditioned["generatorHelpers"][0]["analysisBody"] is body
    assert function == before


def test_condition_cache_and_shared_value_form_remain_distinct():
    state = name("state")
    cached = node("name", v="value", pythonTruthCache=state)
    condition = node("unop", op="!", a=node("binop", op="||", a=cached, b=name("other")))
    branch = node("ifte", c=condition, t=node("skip"), e=node("skip"))
    result = lower_truth_conditions([condition, branch, branch])
    assert result[1] is result[2]
    assert result[0] == condition
    predicate = result[1]["c"]["a"]["c"]
    assert predicate == node("cond",
        c=node("binop", op="==", a=state, b=node("int", v=0)),
        t=node("cond", c=name("value"), t=node("bool", v=True), e=node("bool", v=False)),
        e=node("binop", op="==", a=state, b=node("int", v=2)))
    assert predicate["c"]["a"] is result[0]["a"]["a"]["pythonTruthCache"]
