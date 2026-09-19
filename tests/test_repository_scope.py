"""Repository coverage must retain code omitted by a selected frontend.

These guards are independent of parser success: a language partition cannot claim
files merely because it was selected, and a complete scan is not a source proof.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import sys

import pytest

from conftest import SCRIPTS, fn, load


@pytest.fixture
def repository_scope():
    return load(str(Path(SCRIPTS) / 'repository_scope.py'), 'af_repository_scope')


@pytest.fixture
def inventory():
    return load(str(Path(SCRIPTS) / 'repository_inventory.py'), 'af_scope_inventory')


def write_model(tmp_path, functions):
    path = tmp_path / 'ast.json'
    path.write_text(json.dumps(functions))
    return path


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_selection_keeps_only_requested_language_and_synthetic_helpers(tmp_path, repository_scope):
    source = tmp_path / 'source'
    source.mkdir()
    functions = [fn(name='python_f', file='lib/f.py'),
                 fn(name='java_f', file='src/F.java'),
                 fn(name='scala_f', file='src/F.scala'),
                 fn(name='module_objects', file='')]
    ast = write_model(tmp_path, functions)
    before = digest(ast)
    report = tmp_path / 'selection.json'

    repository_scope.select_ast(ast, source, 'python', report)

    assert json.loads(ast.read_text()) == [functions[0], functions[3]]
    selection = json.loads(report.read_text())
    assert selection['input_sha256'] == before
    assert selection['output_sha256'] == digest(ast)
    assert selection['kept_functions'] == 2
    assert len(selection['excluded_functions']) == 2
    assert selection['kept_files'] == ['lib/f.py']
    assert {f['file'] for f in selection['excluded_functions']} == {'src/F.java', 'src/F.scala'}


def test_selection_preserves_deep_ast_without_changing_recursion_limit(tmp_path, repository_scope):
    source = tmp_path / 'source'
    source.mkdir()
    ast = tmp_path / 'ast.json'
    depth = 5000
    body = ('{"k":"seq","a":{"k":"skip"},"b":' * depth
            + '{"k":"ret","e":{"k":"int","v":17}}' + '}' * depth)
    ast.write_text('[{"name":"deep","file":"deep.py","params":[],"body":' + body
                   + '},{"name":"other","file":"Other.java","params":[],"body":{"k":"skip"}}]')
    recursion_limit = sys.getrecursionlimit()

    repository_scope.select_ast(ast, source, 'python', tmp_path / 'selection.json')

    assert sys.getrecursionlimit() == recursion_limit
    deep_json = load(str(Path(SCRIPTS) / 'deep_json.py'), 'af_scope_deep_json')
    selected = deep_json.load(ast)
    assert len(selected) == 1
    node = selected[0]['body']
    for _ in range(depth):
        assert node['k'] == 'seq' and node['a'] == {'k': 'skip'}
        node = node['b']
    assert node == {'k': 'ret', 'e': {'k': 'int', 'v': 17}}


@pytest.mark.parametrize('functions', [[], [fn(name='module_objects', file='')],
                                       [fn(file='Other.java'), fn(name='module_objects', file='')]])
def test_synthetic_helpers_cannot_make_an_empty_partition_successful(tmp_path, repository_scope, functions):
    source = tmp_path / 'source'
    source.mkdir()
    ast = write_model(tmp_path, functions)
    report = tmp_path / 'selection.json'

    with pytest.raises(ValueError):
        repository_scope.select_ast(ast, source, 'python', report)

    assert report.is_file(), 'A rejected empty partition still needs a scope record.'
    assert json.loads(report.read_text())['kept_files'] == []


def test_selection_does_not_attribute_external_paths_to_the_checkout(tmp_path, repository_scope):
    source = tmp_path / 'source'
    source.mkdir()
    functions = [fn(name='relative', file='./a.py'),
                 fn(name='absolute', file=str(source / 'b.py')),
                 fn(name='escape', file='../external.py'),
                 fn(name='outside', file=str(tmp_path / 'external.py'))]
    ast = write_model(tmp_path, functions)
    report = tmp_path / 'selection.json'

    repository_scope.select_ast(ast, source, 'python', report)

    assert [f['name'] for f in json.loads(ast.read_text())] == ['relative', 'absolute']
    assert set(json.loads(report.read_text())['kept_files']) == {'a.py', 'b.py'}


def test_selection_does_not_follow_source_symlinks_outside_scope(tmp_path, repository_scope):
    source = tmp_path / 'source'
    source.mkdir()
    outside = tmp_path / 'outside'
    outside.mkdir()
    (outside / 'escaped.py').write_text('def escaped(): return 17\n')
    (source / 'linked').symlink_to(outside, target_is_directory=True)
    ast = write_model(tmp_path, [fn(name='local', file='local.py'),
                                 fn(name='escaped', file='linked/escaped.py')])

    repository_scope.select_ast(ast, source, 'python', tmp_path / 'selection.json')

    assert [f['name'] for f in json.loads(ast.read_text())] == ['local']


def make_source(tmp_path, files):
    source = tmp_path / 'source'
    source.mkdir()
    for name, text in files.items():
        path = source / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    return source


def statuses(result):
    return {item['path']: item['status'] for item in result['files']}


def test_coverage_retains_unsupported_unparsed_and_unknown_files(tmp_path, repository_scope, inventory):
    source = make_source(tmp_path, {
        'python/parsed.py': 'def f(): return 17\n',
        'python/broken.py': 'def unparsed(:\n',
        'jvm/Spark.scala': 'object Spark {}\n',
        'jvm/Helper.java': 'class Helper {}\n',
        'custom/program.mystery': 'unknown executable syntax\n',
        'pom.xml': '<project/>\n',
    })
    before = inventory.discover(source)
    ast = write_model(tmp_path, [fn(file='python/parsed.py')])

    result = repository_scope.coverage(before, inventory.discover(source), ast, {})

    assert statuses(result) == {
        'python/parsed.py': 'represented', 'python/broken.py': 'unrepresented',
        'jvm/Spark.scala': 'unsupported', 'jvm/Helper.java': 'unrepresented',
        'custom/program.mystery': 'unclassified', 'pom.xml': 'auxiliary',
    }
    assert result['counts'] == {
        'represented': 1, 'unrepresented': 2, 'unsupported': 1,
        'unclassified': 1, 'auxiliary': 1, 'outside_partition': 0,
    }
    assert result['scan_complete'] is True
    assert result['source_stable'] is True
    assert result['source_census_complete'] is False


def test_partition_coverage_does_not_absorb_other_supported_languages(tmp_path, repository_scope, inventory):
    source = make_source(tmp_path, {'f.py': 'def f(): return 17\n',
                                    'F.java': 'class F {}\n',
                                    'F.scala': 'object F {}\n'})
    before = inventory.discover(source)
    ast = write_model(tmp_path, [fn(file='f.py'), fn(name='jvm_f', file='F.java')])

    result = repository_scope.coverage(before, before, ast, {}, language='python')

    assert statuses(result) == {'f.py': 'represented', 'F.java': 'outside_partition',
                                'F.scala': 'unsupported'}
    assert result['counts']['represented'] == 1


@pytest.mark.parametrize('relative', ['pom.xml', 'requirements.lock', 'data/config.json'])
def test_changed_build_dependency_or_configuration_file_invalidates_scope(tmp_path, repository_scope, inventory, relative):
    source = make_source(tmp_path, {'f.py': 'def f(): return 17\n', relative: 'version 1\n'})
    before = inventory.discover(source)
    ast = write_model(tmp_path, [fn(file='f.py')])
    (source / relative).write_text('version 2\n')

    result = repository_scope.coverage(before, inventory.discover(source), ast, {})

    assert result['source_stable'] is False
    assert {entry['path'] for entry in result['source_changes']} == {relative}
    assert statuses(result)['f.py'] == 'represented'


def test_deleted_source_stays_in_population_and_new_source_is_a_change(tmp_path, repository_scope, inventory):
    source = make_source(tmp_path, {'f.py': 'def f(): return 17\n', 'lost.py': 'def lost(): return 2\n'})
    before = inventory.discover(source)
    ast = write_model(tmp_path, [fn(file='f.py')])
    (source / 'lost.py').unlink()
    (source / 'new.scala').write_text('object New {}\n')

    result = repository_scope.coverage(before, inventory.discover(source), ast, {})

    assert statuses(result)['lost.py'] == 'unrepresented'
    assert {entry['path'] for entry in result['source_changes']} == {'lost.py', 'new.scala'}
    assert result['source_stable'] is False


@pytest.mark.parametrize('ast_content', [None, 'not-json', '{}', '[]',
                                       '[{"name":"synthetic","file":"","body":{"k":"skip"}}]'])
def test_missing_invalid_or_synthetic_only_ast_cannot_cover_source(tmp_path, repository_scope, inventory, ast_content):
    source = make_source(tmp_path, {'f.py': 'def f(): return 17\n'})
    before = inventory.discover(source)
    ast = tmp_path / 'ast.json'
    if ast_content is not None:
        ast.write_text(ast_content)

    result = repository_scope.coverage(before, before, ast, {})

    assert statuses(result) == {'f.py': 'unrepresented'}
    assert result['source_census_complete'] is False


def test_coverage_normalizes_paths_without_credit_for_external_files(tmp_path, repository_scope, inventory):
    source = make_source(tmp_path, {'a.py': 'pass\n', 'b.py': 'pass\n', 'c.py': 'pass\n'})
    before = inventory.discover(source)
    outside = str(tmp_path / 'c.py')
    ast = write_model(tmp_path, [fn(name='a', file='./a.py'),
                                 fn(name='b', file=str(source / 'b.py')),
                                 fn(name='c', file=outside),
                                 fn(name='escape', file='../c.py')])

    result = repository_scope.coverage(before, before, ast, {})

    assert statuses(result) == {'a.py': 'represented', 'b.py': 'represented', 'c.py': 'unrepresented'}
    assert set(result['unexpected_ast_files']) == {outside, '../c.py'}


def test_special_files_stay_gaps_even_if_named_in_ast(tmp_path, repository_scope, inventory):
    source = make_source(tmp_path, {'actual.py': 'pass\n'})
    (source / 'linked.py').symlink_to(source / 'actual.py')
    os.mkfifo(source / 'queue.py')
    before = inventory.discover(source)
    ast = write_model(tmp_path, [fn(name='link', file='linked.py'), fn(name='queue', file='queue.py')])

    result = repository_scope.coverage(before, before, ast, {})

    assert statuses(result)['linked.py'] == 'unclassified'
    assert statuses(result)['queue.py'] == 'unclassified'
    assert result['counts']['represented'] == 0


def test_incomplete_scans_never_turn_into_complete_source_census(tmp_path, repository_scope, inventory):
    source = make_source(tmp_path, {'f.py': 'pass\n'})
    before = inventory.discover(source)
    after = dict(before, scan_complete=False,
                 errors=[{'path': 'hidden', 'reason': 'permission denied'}])
    ast = write_model(tmp_path, [fn(file='f.py')])

    result = repository_scope.coverage(before, after, ast, {'sourceCensusComplete': True})

    assert result['scan_complete'] is False
    assert result['source_stable'] is False
    assert result['source_census_complete'] is False


def test_frontend_truncation_remains_an_explicit_coverage_gap(tmp_path, repository_scope, inventory):
    source = make_source(tmp_path, {'f.py': 'def f(): return 17\ndef omitted(): return 4\n'})
    before = inventory.discover(source)
    ast = write_model(tmp_path, [fn(file='f.py')])

    result = repository_scope.coverage(before, before, ast,
                                       {'truncatedByMethodLimit': True, 'sourceCensusComplete': True})

    assert statuses(result)['f.py'] == 'represented'
    assert result['truncated_by_method_limit'] is True
    assert result['source_census_complete'] is False
