"""Native snapshots must not borrow a same-named class from another module."""
import importlib.util
import sys

import pytest


def load_classes(tmp_path, monkeypatch, differential):
    modules, declarations = [], []
    for name in ('first', 'second'):
        path = tmp_path / (name + '.py')
        path.write_text('class Same:\n    def method(self): return 1\n'
                        'class list:\n    pass\n')
        spec = importlib.util.spec_from_file_location(name, path)
        module = importlib.util.module_from_spec(spec)
        monkeypatch.setitem(sys.modules, name, module)
        spec.loader.exec_module(module)
        modules.append(module)
        declarations.extend({'name': name + '.py:<module>.' + cls}
                            for cls in ('Same', 'list'))
    identities = differential.class_identity_index(
        [{'classDeclarations': declarations}], tmp_path)
    return modules, declarations, identities


def test_snapshots_keep_module_identity_and_builtin_spelling(tmp_path, monkeypatch, differential):
    modules, _, identities = load_classes(tmp_path, monkeypatch, differential)
    enc = differential.Encoder(identities)
    first, second = modules[0].Same(), modules[1].Same()
    assert enc.enc(first) == ('ref', 0)
    assert enc.enc(second) == ('ref', 1)
    assert enc.enc(first) == ('ref', 0)
    assert [item[0] for item in enc.heap] == [
        'first.py:<module>.Same', 'second.py:<module>.Same']
    assert enc.enc(modules[1].Same) == ('fn', 'second.py:<module>.Same<meta>')
    assert enc.enc(modules[1].list()) == ('ref', 2)
    assert enc.heap[2][0] == 'second.py:<module>.list'
    assert enc.enc([]) == ('list', [])


def test_duplicate_declaration_refuses_snapshot(tmp_path, monkeypatch, differential):
    modules, declarations, _ = load_classes(tmp_path, monkeypatch, differential)
    identities = differential.class_identity_index(
        [{'classDeclarations': declarations + [declarations[0]]}], tmp_path)
    with pytest.raises(differential.Unencodable, match='class-identity-unresolved'):
        differential.Encoder(identities).enc(modules[0].Same())


def test_unrecovered_state_is_not_erased(tmp_path, monkeypatch, differential):
    modules, _, identities = load_classes(tmp_path, monkeypatch, differential)
    enc = differential.Encoder(identities)
    with pytest.raises(differential.Unencodable, match='bound-callable-state'):
        enc.enc(modules[0].Same().method)
    class Local:
        pass
    with pytest.raises(differential.Unencodable, match='local-class-captures'):
        enc.enc(Local())
    class Items(list):
        pass
    with pytest.raises(differential.Unencodable, match='container-subclass-state'):
        enc.enc(Items([1]))
    class Number(int):
        pass
    with pytest.raises(differential.Unencodable, match='primitive-subclass-state'):
        enc.enc(Number(3))


def test_legacy_ast_keeps_its_measurement_basis(differential):
    assert differential.class_identity_index([{'name': 'old'}], '.') is None


def test_class_outcomes_compare_the_full_identity(tmp_path, monkeypatch, differential):
    modules, _, identities = load_classes(tmp_path, monkeypatch, differential)
    enc = differential.Encoder(identities)
    first, second = (enc.enc(module.Same) for module in modules)
    assert differential.same(first, first, 0)
    assert not differential.same(first, second, 0)
    assert not differential.same(first, ('fn', 'Same<meta>'), 0)
    assert not differential.same(('fn', 'Same'), first, 0)
    assert not differential.same(('tuple', [first]), ('tuple', [second]), 0)
    assert not differential.same(('dict', [(('str', 'class'), first)]),
                                 ('dict', [(('str', 'class'), second)]), 0)
    # Ordinary function outcomes retain the separately reported name-only rule.
    assert differential.same(('fn', 'outer.<locals>.inner'),
                             ('fn', 'mod.py:<module>.outer.inner'), 0)


def test_function_qualname_cannot_impersonate_a_class(tmp_path, monkeypatch, differential):
    _, _, identities = load_classes(tmp_path, monkeypatch, differential)
    def ordinary():
        return None
    ordinary.__qualname__ = 'first.py:<module>.Same<meta>'
    with pytest.raises(differential.Unencodable, match='callable-class-identity-collision'):
        differential.Encoder(identities).enc(ordinary)
