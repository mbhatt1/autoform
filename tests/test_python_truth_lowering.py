"""Translation regressions for Python's distinct value and jump contexts."""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'cartographer'))
from python_truth_lowering import lower_truth_conditions


def test_value_expression_is_preserved_and_input_is_not_mutated():
    expression = {'k': 'binop', 'op': '&&', 'a': {'k': 'name', 'v': 'x'},
                  'b': {'k': 'name', 'v': 'y'}}
    value = {'k': 'ret', 'e': expression}
    condition = {'k': 'ifte', 'c': expression, 't': {'k': 'skip'}, 'e': {'k': 'skip'}}
    result = lower_truth_conditions([value, condition])
    assert result[0] == value
    assert condition['c'] is expression
    assert result[1]['c']['k'] == 'cond'
    assert result[1]['c']['c'] == expression['a']
    assert result[1]['c']['e'] == {'k': 'bool', 'v': False}


def test_deep_conditions_do_not_use_python_recursion():
    condition = {'k': 'name', 'v': 'last'}
    for _ in range(12000):
        condition = {'k': 'binop', 'op': '&&', 'a': {'k': 'name', 'v': 'x'}, 'b': condition}
    result = lower_truth_conditions({'k': 'ifte', 'c': condition,
                                     't': {'k': 'skip'}, 'e': {'k': 'skip'}})
    assert result['c']['k'] == 'cond'


def test_deep_value_chains_keep_helpers_outside_source_population():
    from python_truth_values import lower_truth_values
    expression = {'k': 'name', 'v': 'first'}
    for _ in range(1600):
        expression = {'k': 'binop', 'op': '&&', 'a': expression,
                      'b': {'k': 'name', 'v': 'next'}}
    body = {'k': 'ret', 'e': expression}
    function = {'name': 'probe', 'file': 'probe.py', 'params': [], 'body': body}
    result = lower_truth_values([function])
    assert len(result) == 1
    assert len(result[0]['truthHelpers']) == 1600
    assert result[0]['analysisBody'] is body
    assert result[0]['body']['e']['k'] == 'index'
    assert function['body'] is body
