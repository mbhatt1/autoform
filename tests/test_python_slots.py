"""Snapshots preserve distinct descriptor storage, initialization and aliasing."""
import importlib.util
import sys

import pytest


def test_slot_snapshots_use_declaring_storage(tmp_path, monkeypatch, differential):
    path = tmp_path / 'slot_state.py'
    path.write_text('''class Base:
    __slots__ = ('value', '__private', 'unset')
class Child(Base):
    __slots__ = ('value', '__dict__')
class StringSlot:
    __slots__ = 'whole_name'
''')
    spec = importlib.util.spec_from_file_location('slot_state', path)
    module = importlib.util.module_from_spec(spec)
    monkeypatch.setitem(sys.modules, 'slot_state', module)
    spec.loader.exec_module(module)
    identities = differential.class_identity_index([{'classDeclarations': [
        {'name': 'slot_state.py:<module>.' + cls}
        for cls in ('Base', 'Child', 'StringSlot')]}], tmp_path)
    obj = module.Child()
    module.Base.value.__set__(obj, 11)
    obj.value = 19
    obj._Base__private = obj
    obj.__dict__['value'] = 23
    encoder = differential.Encoder(identities)
    assert encoder.enc(obj) == ('ref', 0)
    assert dict(encoder.heap[0][1]) == {
        'value': ('int', 23),
        '<slot>slot_state.py:<module>.Base.value': ('int', 11),
        '<slot>slot_state.py:<module>.Child.value': ('int', 19),
        '<slot>slot_state.py:<module>.Base._Base__private': ('ref', 0),
    }
    item = module.StringSlot()
    item.whole_name = obj
    assert encoder.enc(item) == ('ref', 1)
    assert dict(encoder.heap[1][1]) == {
        '<slot>slot_state.py:<module>.StringSlot.whole_name': ('ref', 0)}
    obj.__dict__['<slot>forged'] = 9
    with pytest.raises(differential.Unencodable, match='non-ordinary-instance-dictionary'):
        differential.Encoder(identities).enc(obj)
