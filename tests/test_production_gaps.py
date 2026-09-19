"""Regressions for defects found while making the tool run on arbitrary codebases.

Each test below corresponds to something that was *silently* wrong: a caveat that was
recorded but never read, a compile step that discarded most of a real repository, a
health check that passed on a machine with nothing installed, and a clone that was
never deleted. As with the rest of this suite, the point is to make those loud.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
sys.path.insert(0, str(ROOT / 'scripts'))


# --------------------------------------------------------------------------- #
# The dialect caveat used to be write-only.
#
# `differential.py` recorded `dialect_is_exact: false` for Java, Kotlin and Go -- all
# three are interpreted under `.cLike` -- and nothing downstream ever read it. A Java
# guarantee therefore listed three generic assumptions and omitted the one this
# project's headline finding (floored vs truncated `%`) says is a correctness issue.
# --------------------------------------------------------------------------- #

@pytest.fixture(scope="module")
def guarantee():
    import guarantee as module
    return module


def test_inexact_dialect_becomes_a_declared_assumption(guarantee):
    assumptions = guarantee.dialect_assumptions(
        {'language': 'java', 'dialect_expected': 'cLike', 'dialect_is_exact': False})
    assert len(assumptions) == 1
    text = assumptions[0]
    assert 'java' in text and 'cLike' in text


def test_exact_dialect_adds_no_assumption(guarantee):
    assert guarantee.dialect_assumptions(
        {'language': 'python', 'dialect_expected': 'python', 'dialect_is_exact': True}) == []


def test_absent_conformance_adds_no_assumption(guarantee):
    # A missing conformance report must not silently manufacture a caveat, nor crash.
    assert guarantee.dialect_assumptions({}) == []


# --------------------------------------------------------------------------- #
# javac source roots.
#
# Compiling one file at a time with no -sourcepath fails on any real project the
# moment a candidate references another class in the SAME project. On Apache Spark
# that left 8 of 55 candidate files compiling; the rest reported
# "package org.apache.spark... does not exist".
# --------------------------------------------------------------------------- #

def test_source_root_is_the_package_path_stripped(tmp_path, differential):
    src = tmp_path / 'proj' / 'src' / 'main' / 'java' / 'com' / 'example'
    src.mkdir(parents=True)
    (src / 'A.java').write_text('package com.example;\npublic class A {}\n')
    assert differential.java_source_roots([str(src / 'A.java')]) == [
        str(tmp_path / 'proj' / 'src' / 'main' / 'java')]


def test_default_package_uses_the_containing_directory(tmp_path, differential):
    (tmp_path / 'A.java').write_text('public class A {}\n')
    assert differential.java_source_roots([str(tmp_path / 'A.java')]) == [str(tmp_path)]


def test_commented_out_package_declaration_is_not_believed(tmp_path, differential):
    # A root derived from a commented declaration would be wrong, and a wrong
    # -sourcepath entry makes javac resolve the wrong file rather than fail loudly.
    (tmp_path / 'A.java').write_text('// package com.example;\n/* package x.y; */\npublic class A {}\n')
    assert differential.java_source_roots([str(tmp_path / 'A.java')]) == [str(tmp_path)]


def test_path_disagreeing_with_its_package_yields_no_root(tmp_path, differential):
    (tmp_path / 'A.java').write_text('package com.example;\npublic class A {}\n')
    assert differential.java_source_roots([str(tmp_path / 'A.java')]) == []


def test_compile_failures_are_categorised_not_just_counted(differential):
    assert 'package' in differential.java_failure_category(
        'X.java:3: error: package com.foo does not exist')
    assert differential.java_failure_category('X.java:9: error: cannot find symbol') \
        == 'unresolved symbol (missing classpath or source root)'
    assert differential.java_failure_category('') == 'other javac error'


@pytest.mark.skipif(not __import__('shutil').which('javac'), reason='javac not installed')
def test_sourcepath_lets_an_intra_project_reference_compile(tmp_path, differential):
    """The exact Spark failure, in miniature: A uses B from the same project."""
    root = tmp_path / 'src' / 'main' / 'java' / 'com' / 'example'
    root.mkdir(parents=True)
    (root / 'B.java').write_text('package com.example;\npublic class B { static int v() { return 7; } }\n')
    (root / 'A.java').write_text(
        'package com.example;\npublic class A { public static int f() { return B.v(); } }\n')
    a, classes = str(root / 'A.java'), str(tmp_path / 'out')
    os.makedirs(classes, exist_ok=True)

    without = subprocess.run(['javac', '-nowarn', '-proc:none', '-d', classes, a],
                             capture_output=True, text=True)
    assert without.returncode != 0, 'expected the un-helped compile to fail'

    roots = differential.java_source_roots([a])
    with_path = subprocess.run(
        ['javac', '-nowarn', '-proc:none', '-sourcepath', os.pathsep.join(roots),
         '-d', classes, a], capture_output=True, text=True)
    assert with_path.returncode == 0, with_path.stderr


# --------------------------------------------------------------------------- #
# `doctor` used to print a name->path map and `return 0` unconditionally, so a
# machine with no Lean and no Joern passed its own health check.
# --------------------------------------------------------------------------- #

def run_doctor(*args, env=None):
    environment = dict(os.environ, PYTHONPATH=str(ROOT / 'src'))
    environment.update(env or {})
    return subprocess.run([sys.executable, '-m', 'autoform', 'doctor', *args],
                          capture_output=True, text=True, env=environment, cwd=str(ROOT))


def test_doctor_fails_when_a_required_tool_is_absent():
    result = run_doctor(env={'JOERN_HOME': '/nonexistent-joern'})
    assert result.returncode == 1, result.stdout
    report = json.loads(result.stdout)
    assert report['joern']['status'] == 'missing'
    assert report['joern']['required'] is True
    # It must say which check failed, on stderr, not merely exit non-zero.
    assert 'joern' in result.stderr


def test_doctor_reports_versions_against_the_packaged_pins():
    report = json.loads(run_doctor().stdout)
    assert report['python']['status'] == 'ok'
    for name in ('lean', 'lake', 'joern'):
        if report[name]['path'] is not None:
            assert 'expected_version' in report[name], name


def test_doctor_marks_optional_tools_as_not_required():
    report = json.loads(run_doctor(env={'JOERN_HOME': '/nonexistent-joern'}).stdout)
    for name in ('java', 'go', 'node', 'kotlinc', 'pypcode'):
        assert report[name]['required'] is False, name


# --------------------------------------------------------------------------- #
# Clones were never deleted: every run of a Git URL left a full checkout behind.
# --------------------------------------------------------------------------- #

def test_discard_checkout_removes_only_clones_we_made(tmp_path):
    from autoform import cli
    clone = tmp_path / 'sources' / 'M-abcd1234' / 'checkout'
    clone.mkdir(parents=True)
    cli.discard_checkout({'kind': 'git', 'checkout': str(clone)})
    assert not clone.parent.exists()


def test_discard_checkout_never_deletes_a_local_source_tree(tmp_path):
    from autoform import cli
    local = tmp_path / 'my-project'
    local.mkdir()
    cli.discard_checkout({'kind': 'local', 'checkout': str(local)})
    assert local.is_dir(), 'a directory the user supplied was never ours to delete'


def test_keep_checkout_retains_the_clone(tmp_path):
    from autoform import cli
    clone = tmp_path / 'sources' / 'M-abcd1234' / 'checkout'
    clone.mkdir(parents=True)
    cli.discard_checkout({'kind': 'git', 'checkout': str(clone)}, keep=True)
    assert clone.is_dir()


def test_failed_clone_leaves_no_temporary_tree(tmp_path):
    from autoform import cli, repository
    workspace = cli.prepare_workspace(tmp_path / 'workspace')
    with pytest.raises(ValueError):
        repository.resolve_source(
            'file://' + str(tmp_path / 'absent.git'), workspace, 'Check')
    sources = workspace / 'sources'
    assert not sources.exists() or list(sources.iterdir()) == []


# --------------------------------------------------------------------------- #
# Character literals were parsed as integers.
#
# `parseIntLiteral` stripped every `'` to support C++14 digit separators
# (1'000'000), so the character literal `'0'` became the string "0" and parsed as
# the integer 0 -- the digit's VALUE instead of its codepoint 48. `'A'` was
# unaffected, because "A" is not all digits, so it fell through to the
# character-literal branch and correctly produced 65. That asymmetry is why it
# survived: a corpus had to compare both to see it.
#
# Found by the differential oracle on org.json's JSONTokener.dehexchar, which
# diverged from the JVM on 3 of 5 cases. `c >= '0' && c <= '9'` is the most common
# character-range idiom in any parser.
# --------------------------------------------------------------------------- #

EXPORTER = ROOT / 'cartographer' / 'export_ast.sc'


def test_quoted_character_literal_is_not_an_integer_literal():
    source = EXPORTER.read_text()
    assert "if (trimmed.length >= 3 && trimmed.head == '\\'' && trimmed.last == '\\'') return None" in source, (
        "parseIntLiteral must refuse a quoted character literal so the character-literal "
        "branch can resolve its codepoint; without this, '0' parses as the integer 0.")


def test_digit_separators_are_only_stripped_between_digits():
    source = EXPORTER.read_text()
    assert 'replaceAll("(?<=[0-9a-fA-F])\'(?=[0-9a-fA-F])", "")' in source, (
        "a C++14 digit separator only separates DIGITS; stripping every quote is what "
        "consumed the character literal's quotes in the first place")
    assert 'raw.trim.replace("\'", "")' not in source, "the unconditional quote strip is back"


@pytest.mark.skipif(not os.environ.get('AUTOFORM_TEST_JOERN'),
                    reason='set AUTOFORM_TEST_JOERN=1 to parse/export with Joern')
def test_exported_char_literal_is_its_codepoint(tmp_path):
    """End to end through the real exporter: '0' must be 48, not 0."""
    joern = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (joern / 'joern-cli').is_dir():
        joern /= 'joern-cli'
    if not (joern / 'joern').is_file():
        pytest.skip('set JOERN_HOME to a joern-cli directory')
    env = dict(os.environ)
    env['PATH'] = str(Path.home() / '.elan/bin') + os.pathsep + env.get('PATH', '')
    src = tmp_path / 'src'
    src.mkdir()
    (src / 'Chars.java').write_text(
        'public class Chars {\n'
        '  public static int digit(char c) { return c >= \'0\' && c <= \'9\' ? c - \'0\' : -1; }\n'
        '}\n')
    subprocess.run([str(joern / 'joern-parse'), str(src), '--language', 'JAVASRC',
                    '--output', 'cpg.bin'], cwd=tmp_path, env=env, check=True,
                   capture_output=True, timeout=900)
    subprocess.run([str(joern / 'joern'), '--script', str(EXPORTER),
                    '--param', 'cpgPath=cpg.bin', '--param', 'out=ast.json'],
                   cwd=tmp_path, env=env, check=True, capture_output=True, timeout=900)
    blob = json.loads((tmp_path / 'ast.json').read_text())
    functions = blob['functions'] if isinstance(blob, dict) else blob
    digit = [f for f in functions if 'digit' in f['name']]
    assert digit, 'exporter produced no `digit` function'

    def int_literals(node):
        # `v` is emitted as a string for int literals; compare numerically.
        if isinstance(node, dict):
            if node.get('k') == 'int':
                yield int(node['v'])
            for value in node.values():
                yield from int_literals(value)
        elif isinstance(node, list):
            for value in node:
                yield from int_literals(value)

    literals = set(int_literals(digit[0]['body']))
    assert 48 in literals and 57 in literals, (
        "'0' and '9' must export as codepoints 48 and 57, not the digits 0 and 9; "
        f"got {sorted(literals)}")
    assert 0 not in literals and 9 not in literals, (
        f"a digit character literal still exported as its value: {sorted(literals)}")
