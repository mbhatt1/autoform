"""Gradle and Maven layouts: build products and test sources are excluded, never dropped.

A JVM frontend parses the whole tree it is given, so compiled-in annotation-processor
output and test source sets used to enter the model as if they were the program. The
inventory now records them under `excluded` with a reason, and the AST selection drops
the same functions under the same reason. No Joern is needed: the AST below is the
function list a frontend would export for every Java/Kotlin file in the tree.

Build outputs (`build/`, `target/`, `.gradle/`) are gitignored, so the committed
fixture holds only sources and build files; each test materializes the outputs the
way a local build leaves them. This repository ignores every `build/` directory, so
the source package named `build` is materialized too.
"""
from __future__ import annotations

import json
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

from conftest import ROOT, SCRIPTS, fn, load

FIXTURE = Path(ROOT) / 'tests' / 'fixtures' / 'jvm_multimodule'

MATERIALIZED = {
    'gradle': {
        '.gradle/8.5/fileHashes/fileHashes.lock': '',
        'core/build/generated/sources/annotationProcessor/java/main/org/example/core/PricingBuilder.java':
            'package org.example.core;\nclass PricingBuilder { static int f() { return 1; } }\n',
        'core/build/classes/java/main/org/example/core/Pricing.class': '\xca\xfe',
        'service/build/tmp/kotlin/Quote.kt': 'fun copied() = 0\n',
        'core/generated-src/org/example/core/Proto.java':
            'package org.example.core;\nclass Proto { static int f() { return 2; } }\n',
        # A package named `build` inside a source set is source, not build output.
        'core/src/main/java/org/example/core/build/Steps.java':
            'package org.example.core.build;\npublic final class Steps {\n'
            '    public static int next(int step) { return step + 1; }\n}\n',
    },
    'maven': {
        'api/target/generated-sources/annotations/org/example/api/LimitsMapper.java':
            'package org.example.api;\nclass LimitsMapper { static int f() { return 3; } }\n',
        'api/target/classes/org/example/api/Limits.class': '\xca\xfe',
    },
}


@pytest.fixture
def inventory():
    return load(str(Path(SCRIPTS) / 'repository_inventory.py'), 'af_layout_inventory')


@pytest.fixture
def repository_scope():
    return load(str(Path(SCRIPTS) / 'repository_scope.py'), 'af_layout_scope')


def project(tmp_path, kind):
    root = tmp_path / kind
    shutil.copytree(FIXTURE / kind, root)
    for relative, content in MATERIALIZED[kind].items():
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
    return root


def frontend_ast(tmp_path, root):
    """One function per Java/Kotlin file, as a frontend that ignores the layout exports."""
    functions = [fn(name=str(path.relative_to(root)) + ':f', file=str(path.relative_to(root)))
                 for path in sorted(root.rglob('*')) if path.suffix in ('.java', '.kt')]
    functions.append(fn(name='<global>', file=''))
    path = tmp_path / 'ast.json'
    path.write_text(json.dumps(functions))
    return path


def test_gradle_multimodule_layout_is_reported_and_build_products_are_recorded_exclusions(
        tmp_path, inventory):
    root = project(tmp_path, 'gradle')
    report = inventory.discover(root)
    assert report['scan_complete']
    assert report['layout'] == {
        'build_systems': ['gradle'],
        # `service` has no build file: it is a module by source root, not by build file.
        'modules': ['.', 'core'],
        'source_roots': ['core/src/main/java', 'service/src/main/kotlin'],
    }
    assert report['excluded'] == [
        {'path': '.gradle', 'reason': 'build_output'},
        {'path': 'core/build', 'reason': 'build_output'},
        {'path': 'core/generated-src', 'reason': 'generated_code'},
        {'path': 'core/src/main/java/org/example/core/generated', 'reason': 'generated_code'},
        {'path': 'core/src/test', 'reason': 'test_source_set'},
        {'path': 'core/src/testFixtures', 'reason': 'test_source_set'},
        {'path': 'service/build', 'reason': 'build_output'},
        {'path': 'service/src/test', 'reason': 'test_source_set'},
    ]
    paths = {record['path'] for record in report['files']}
    # A package named `build` inside a source set is ordinary source.
    assert 'core/src/main/java/org/example/core/build/Steps.java' in paths
    assert report['languages']['java']['supported_files'] == [
        'core/src/main/java/org/example/core/Pricing.java',
        'core/src/main/java/org/example/core/build/Steps.java']
    assert report['languages']['kotlin']['supported_files'] == [
        'service/src/main/kotlin/org/example/service/Quote.kt']
    assert report['counts']['excluded'] == len(report['excluded'])


def test_maven_multimodule_layout_excludes_target_and_tests(tmp_path, inventory):
    root = project(tmp_path, 'maven')
    report = inventory.discover(root)
    assert report['layout'] == {'build_systems': ['maven'], 'modules': ['.', 'api'],
                                'source_roots': ['api/src/main/java']}
    assert report['excluded'] == [{'path': 'api/src/test', 'reason': 'test_source_set'},
                                  {'path': 'api/target', 'reason': 'build_output'}]
    assert report['languages']['java']['files'] == ['api/src/main/java/org/example/api/Limits.java']


def test_layout_rules_need_a_build_file_in_or_above_the_directory(tmp_path, inventory):
    # Outside a Gradle/Maven tree `build/`, `target/` and `src/test/` stay ordinary
    # directories; the one exclusion a non-JVM repository gets is unchanged.
    for relative in ('build/a.py', 'target/b.py', 'generated/c.py', 'src/test/java/T.java',
                     'tools/pom.xml', 'tools/build/d.py'):
        (tmp_path / relative).parent.mkdir(parents=True, exist_ok=True)
        (tmp_path / relative).write_text('x')
    report = inventory.discover(tmp_path)
    assert report['excluded'] == [{'path': 'tools/build', 'reason': 'build_output'}]
    assert {'build/a.py', 'target/b.py', 'generated/c.py',
            'src/test/java/T.java'} <= {record['path'] for record in report['files']}
    assert report['layout']['build_systems'] == ['maven']
    assert report['layout']['modules'] == ['tools']


@pytest.mark.parametrize('kind', sorted(MATERIALIZED))
def test_selection_and_coverage_agree_with_the_inventory_end_to_end(
        tmp_path, inventory, repository_scope, kind):
    root = project(tmp_path, kind)
    before = inventory.discover(root)
    ast = frontend_ast(tmp_path, root)
    selection = repository_scope.select_ast(ast, root, 'java', tmp_path / 'selection.json')
    excluded_by_layout = {f['file']: f['reason'] for f in selection['excluded_functions']
                          if f['reason'] != 'outside selected source language or source directory'}
    # Every function the layout drops lies under a directory the inventory excluded
    # for the same reason, so the two records can never disagree about scope.
    for filename, reason in excluded_by_layout.items():
        assert any((filename + '/').startswith(entry['path'] + '/') and entry['reason'] == reason
                   for entry in before['excluded']), filename
    assert set(selection['kept_files']) == set(before['languages']['java']['supported_files'])
    coverage = repository_scope.coverage(before, inventory.discover(root), ast, {}, 'java')
    assert coverage['unexpected_ast_files'] == []
    assert coverage['counts']['unrepresented'] == 0
    assert coverage['counts']['represented'] == len(before['languages']['java']['supported_files'])


def test_layout_only_selection_runs_on_jvm_roots_and_is_inert_elsewhere(tmp_path, repository_scope):
    root = project(tmp_path, 'gradle')
    ast = frontend_ast(tmp_path, root)
    report = tmp_path / 'selection.json'
    proc = subprocess.run([sys.executable, str(Path(SCRIPTS) / 'repository_scope.py'),
                           str(ast), str(root), 'any', str(report)],
                          capture_output=True, text=True, timeout=30)
    assert proc.returncode == 0, proc.stderr
    selection = json.loads(report.read_text())
    assert selection['language'] is None
    kept = {f['file'] for f in json.loads(ast.read_text())}
    # Kotlin stays: `any` filters by layout, not by language.
    assert kept == {'', 'core/src/main/java/org/example/core/Pricing.java',
                    'core/src/main/java/org/example/core/build/Steps.java',
                    'service/src/main/kotlin/org/example/service/Quote.kt'}
    assert {f['reason'] for f in selection['excluded_functions']} == {
        'build_output', 'generated_code', 'test_source_set'}

    plain = tmp_path / 'plain'
    (plain / 'build').mkdir(parents=True)
    plain_ast = tmp_path / 'plain-ast.json'
    plain_ast.write_text(json.dumps([fn(name='f', file='build/f.py')]))
    original = plain_ast.read_bytes()
    assert repository_scope.select_ast(plain_ast, plain, None, tmp_path / 'plain.json') is None
    assert plain_ast.read_bytes() == original and not (tmp_path / 'plain.json').exists()


def test_selection_refuses_a_jvm_model_with_only_excluded_sources(tmp_path, repository_scope):
    root = tmp_path / 'tests-only'
    (root / 'src/test/java').mkdir(parents=True)
    (root / 'pom.xml').write_text('<project/>')
    ast = tmp_path / 'ast.json'
    ast.write_text(json.dumps([fn(name='T.f', file='src/test/java/T.java')]))
    with pytest.raises(ValueError, match='outside build outputs'):
        repository_scope.select_ast(ast, root, None, tmp_path / 'selection.json')
    assert json.loads((tmp_path / 'selection.json').read_text())['excluded_functions'] == [
        {'name': 'T.f', 'file': 'src/test/java/T.java', 'reason': 'test_source_set'}]
