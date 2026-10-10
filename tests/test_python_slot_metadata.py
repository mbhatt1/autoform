"""Recover static layouts and refuse class-creation behavior we cannot execute."""
from test_python_signatures import _decode


def declaration(body):
    return _decode('class _Cell:\n' + body)['classDeclarations'][0]


def test_private_and_single_string_slots():
    result = declaration('    __slots__ = ("value", "__private")\n')
    assert result['slots'] == ['value', '_Cell__private']
    slots = {row['name']: row['value'] for row in result['attributes'] if row['kind'] == 'slot'}
    assert slots == {'value': '_Cell.value', '_Cell__private': '_Cell._Cell__private'}
    assert result['definitionBarrier'] is None
    assert declaration('    __slots__ = "whole_name"\n')['slots'] == ['whole_name']


def test_empty_layout_differs_from_implicit_dictionary():
    assert declaration('    __slots__ = ()\n')['slots'] == []
    assert declaration('    pass\n')['slots'] is None


def test_dynamic_invalid_and_conflicting_layouts_remain_gaps():
    for body, reason in [
        ('    __slots__ = make_names()\n', 'dynamic-slot-layout'),
        ('    __slots__ = ("bad name",)\n', 'dynamic-slot-layout'),
        ('    __slots__ = ("x", "x")\n', 'duplicate-slot-name'),
        ('    __slots__ = ("x",)\n    x = 1\n', 'slot-member-conflict'),
        ('    __slots__ = ()\n    __slots__ = ("x",)\n', 'redefined-slot-layout'),
    ]:
        assert declaration(body)['definitionBarrier'] == 'class-definition:' + reason
