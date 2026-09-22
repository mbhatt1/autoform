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
    # `--json` is the machine-readable form; the default is a human summary with an
    # install line per problem (tests/test_cli.py covers that surface).
    environment = dict(os.environ, PYTHONPATH=str(ROOT / 'src'))
    environment.update(env or {})
    return subprocess.run([sys.executable, '-m', 'autoform', 'doctor', '--json', *args],
                          capture_output=True, text=True, env=environment, cwd=str(ROOT))


def test_doctor_fails_when_a_required_tool_is_absent():
    result = run_doctor(env={'JOERN_HOME': '/nonexistent-joern'})
    assert result.returncode == 1, result.stdout
    report = json.loads(result.stdout)['tools']
    assert report['joern']['status'] == 'missing'
    assert report['joern']['required'] is True
    # It must say which check failed, on stderr, not merely exit non-zero.
    assert 'joern' in result.stderr


def test_doctor_reports_versions_against_the_packaged_pins():
    report = json.loads(run_doctor().stdout)['tools']
    assert report['python']['status'] == 'ok'
    for name in ('lean', 'lake', 'joern'):
        if report[name]['path'] is not None:
            assert 'expected_version' in report[name], name


def test_doctor_marks_optional_tools_as_not_required():
    report = json.loads(run_doctor(env={'JOERN_HOME': '/nonexistent-joern'}).stdout)['tools']
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

EXPORTER = ROOT / "cartographer" / "export_ast.sc"
SEMANTICS = ROOT / "Autoform" / "Lang" / "Core" / "Semantics.lean"
SYNTAX = ROOT / "Autoform" / "Lang" / "Core" / "Syntax.lean"
RENDERER = ROOT / "cartographer" / "render_lean.py"


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


class TestLiteralParameterDefaults:
    """Python defaults, for the case where Core does not need function-object state.

    `def f(x, n=1)` used to hole the whole definition as `call:python-defaults`, because
    Python evaluates a default once when the `def` runs and stores it on the function
    object, which Core has no representation for. That is the right answer for
    `n=time.monotonic` and the wrong one for `n=1`: a literal's value does not depend on
    when it is evaluated and evaluating it has nothing to observe, so binding it at call
    time is indistinguishable from binding it at definition time. Only literals qualify,
    and a function mixing a literal with anything else still holes in full -- binding
    half the defaults and silently dropping the rest is a wrong answer, not a missing one.
    """

    def render(self, signature, params, name='f'):
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            'render_lean', Path(__file__).resolve().parents[1] / 'cartographer/render_lean.py')
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return '\n'.join(mod.render_func({
            'name': name, 'file': 'm.py', 'params': params,
            'body': {'k': 'ret', 'e': {'k': 'name', 'v': params[0]}},
            'pythonSignature': signature}, 'f_test'))

    def test_a_literal_default_reaches_the_rendered_signature(self):
        text = self.render(
            {'positionalOnly': [], 'keywordOnly': [], 'required': ['a'], 'isMethod': False,
             'defaults': [['b', {'k': 'int', 'v': '1'}], ['c', {'k': 'str', 'v': 'hi'}],
                          ['d', {'k': 'bool', 'v': True}], ['e', {'k': 'unit'}]]},
            ['a', 'b', 'c', 'd', 'e'])
        # `.lit` is the `DefaultValue` constructor: the field also admits `.fnref` for a
        # default whose value is an in-program function, which is time-invariant for the
        # same reason a literal is.
        assert ('defaults := [("b", (.lit (.int 1))), ("c", (.lit (.str "hi"))), '
                '("d", (.lit (.bool true))), ("e", (.lit .unit))]') in text

    def test_a_non_literal_default_is_refused_by_the_renderer(self):
        """The exporter is supposed to have holed this. If it ever does not, the
        renderer must fail loudly rather than emit something that looks like a default."""
        with pytest.raises(ValueError, match='not a literal'):
            self.render(
                {'positionalOnly': [], 'keywordOnly': [], 'required': ['a'],
                 'defaults': [['b', {'k': 'name', 'v': 'math'}]]},
                ['a', 'b'])

    def test_a_default_on_a_required_parameter_is_refused(self):
        """`required` means "has no default". The two fields disagreeing about one
        parameter is a corrupt signature, not something to pick a winner for."""
        with pytest.raises(ValueError, match='invalid Python defaults'):
            self.render(
                {'positionalOnly': [], 'keywordOnly': [], 'required': ['a', 'b'],
                 'defaults': [['b', {'k': 'int', 'v': '1'}]]},
                ['a', 'b'])

    def test_the_exporter_holes_a_mixed_default_list(self):
        """All-or-nothing, asserted on the exporter source: the literal half of a mixed
        signature must not be emitted on its own."""
        source = EXPORTER.read_text()
        assert 'if any(lit is None for _, lit in values):' in source
        assert "return {'defaults': True, 'defaultValues': []}" in source

    def test_core_binds_defaults_before_arguments(self):
        """Ordering is the rule "a default applies exactly when the parameter was not
        passed". Seeding first and letting real arguments overwrite is what implements
        it; reversing it would make every default win over its own argument."""
        semantics = (Path(__file__).resolve().parents[1]
                     / 'Autoform/Lang/Core/Semantics.lean').read_text()
        seed = semantics.index('fn.literalDefaults.foldl')
        positional = semantics.index('let ps    := fn.posParams', seed)
        assert seed < positional



class TestBoxedContainerExporterWiring:
    """The exporter emissions held back until containers were boxed.

    Before the switchover a `del xs[i]` translated to `Stmt.delIndex` would have swapped
    a STATIC hole for a statement that holed at RUN time: identical behaviour, a smaller
    static hole count, and a hole-freedom number that improved while nothing became
    translated. Now that a Python list literal allocates and `delIndex` mutates the
    payload in place, the statement runs, so it is emitted -- for Python only, because
    only Python boxes.
    """

    def test_python_del_index_emits_delIndex(self):
        src = EXPORTER.read_text()
        assert 'case (x: AstNode) :: Nil if pyFile && asIndex(x).isDefined =>' in src
        # operands threaded in order (§16.R4): receiver then index, each may hoist a prelude
        assert 'seqOf(prelude :+ ujson.Obj("k" -> "delIndex", "a" -> vals(0), "i" -> vals(1)))' in src
        # The non-Python case keeps the hole: a C aggregate is a value with no identity.
        assert 'holeS("op:delete-index")' in src

    def test_renderer_knows_the_delIndex_shape(self):
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            'render_lean', Path(__file__).resolve().parents[1] / 'cartographer/render_lean.py')
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        head, kids = mod.stmt_shape({'k': 'delIndex',
                                     'a': {'k': 'name', 'v': 'xs'},
                                     'i': {'k': 'int', 'v': '0'}})
        assert head == '.delIndex'
        assert [k for k, _ in kids] == ['e', 'e']

    def test_adjacent_string_literals_fold_to_one_str(self):
        """`"a" "b"` is one value. An f-string uses the same operator with non-literal
        parts and keeps a hole -- folding it would need `str()` semantics per part."""
        src = EXPORTER.read_text()
        assert 'mfn == "<operator>.stringExpressionList"' in src
        assert 'parts.nonEmpty && parts.forall(_.isDefined)' in src
        assert 'hole("op:stringExpressionList:non-literal-part")' in src


class TestProgramProperties:
    """`Program.properties` is rendered from the `classProperties` the exporter puts on
    each module initializer, aggregated across files -- the same route `builtinBases`
    takes. Unlike bases it is keyed by class AND name, so a same-named property on two
    classes is two entries, not a conflict to drop: `evalExpr` dispatches on `(o.cls, f)`.
    """

    def _mod(self):
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            'render_lean', Path(__file__).resolve().parents[1] / 'cartographer/render_lean.py')
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return mod

    def test_pairs_are_aggregated_deduplicated_and_sorted(self):
        mod = self._mod()
        funcs = [{'name': 'a.py:<module>', 'classProperties': [['Cache', 'maxsize'], ['Cache', 'currsize']]},
                 {'name': 'b.py:<module>', 'classProperties': [['Cache', 'currsize'], ['TTL', 'timer']]},
                 {'name': 'a.py:<module>.f'}]
        assert mod.program_properties(funcs) == \
            '("Cache", "currsize"), ("Cache", "maxsize"), ("TTL", "timer")'

    def test_same_name_on_two_classes_is_two_entries_not_a_conflict(self):
        mod = self._mod()
        funcs = [{'name': 'm', 'classProperties': [['A', 'size'], ['B', 'size']]}]
        assert mod.program_properties(funcs) == '("A", "size"), ("B", "size")'

    def test_no_properties_renders_nothing(self):
        """An AST with no properties must render byte-identically to before this field
        existed: `properties` is only written when non-empty."""
        mod = self._mod()
        assert mod.program_properties([{'name': 'm'}]) == ''

    def test_a_malformed_entry_is_refused_not_guessed(self):
        mod = self._mod()
        with pytest.raises(ValueError, match='malformed classProperties'):
            mod.program_properties([{'name': 'm', 'classProperties': [['onlyone']]}])

class TestClassAttributeDefaultRendering:
    """`classAttrDefaults` is rendered as `(parameter, class, mangled attribute)`, and the
    renderer refuses the shapes that would let the two default fields disagree."""

    def render(self, signature, params):
        return TestLiteralParameterDefaults().render(signature, params)

    def test_a_class_attribute_default_renders(self):
        text = self.render(
            {'positionalOnly': [], 'keywordOnly': [], 'required': ['key'], 'isMethod': True,
             'classAttrDefaults': [['default', 'Cache', '_Cache__marker']]},
            ['key', 'default'])
        assert 'classAttrDefaults := [("default", "Cache", "_Cache__marker")]' in text

    def test_a_parameter_cannot_have_two_defaults(self):
        with pytest.raises(ValueError, match='class-attribute defaults'):
            self.render(
                {'positionalOnly': [], 'keywordOnly': [], 'required': [],
                 'defaults': [['d', {'k': 'unit'}]],
                 'classAttrDefaults': [['d', 'C', '_C__m']]},
                ['d'])

    def test_a_required_parameter_cannot_have_a_class_attribute_default(self):
        with pytest.raises(ValueError, match='class-attribute defaults'):
            self.render(
                {'positionalOnly': [], 'keywordOnly': [], 'required': ['d'],
                 'classAttrDefaults': [['d', 'C', '_C__m']]},
                ['d'])


class TestComprehensionLowering:
    """A comprehension is one assignment, one loop and one read, and every piece of that
    already exists in Core -- so it lowers rather than holes. What these pin is the two
    places the lowering could go quietly wrong: the loop variable leaking into the
    enclosing scope (Python 3 gives a comprehension its own), and a generator expression
    being materialised somewhere its laziness is observable.

    The behavioural check is `test_joern_native_numeric[python]` (`compList`,
    `compNoLeak`, `compDict`, `genTuple`, `genSum`, `withStmt`), which needs Joern and
    CPython; these hold the shape in place when that suite is skipped.
    """

    def test_the_three_statement_shape_is_what_is_matched(self):
        src = EXPORTER.read_text()
        assert 'def comprehensionParts(b: Block)' in src
        assert 'case (init: Call) :: loop :: (out: Identifier) :: Nil' in src
        # the container kinds, and the one Core cannot represent
        for kind in ('"<operator>.listLiteral" if kidsOf(rhs).isEmpty => Some("list")',
                     '"<operator>.dictLiteral" if kidsOf(rhs).isEmpty => Some("dict")',
                     '"<operator>.setLiteral"  if kidsOf(rhs).isEmpty => Some("set")'):
            assert kind in src, kind
        assert 'case "set"                 => (Nil, hole("expr:setComp"))' in src

    def test_the_loop_variable_is_rebound_to_an_unspellable_name(self):
        src = EXPORTER.read_text()
        assert 'def compName(x: String): String = "$comp$" + x' in src
        assert 'def renameCompBinders(v: ujson.Value)' in src
        # destructured targets (`for k, v in pairs`) follow the loop variable
        assert '(jsonNames(st("e")) intersect bound).nonEmpty) bound += st("x").str' in src
        # the first iterable is evaluated in the enclosing scope and is NOT renamed
        assert '"x" -> compName(x), "e" -> o("e"),' in src

    def test_a_generator_expression_lowers_only_where_it_is_consumed_at_once(self):
        src = EXPORTER.read_text()
        assert 'case "gen" if !eagerGen    => (Nil, hole("expr:genExp"))' in src
        assert 'genExpEager = kind == "call" && genExpConsumers.contains(c.name)' in src
        for consumer in ('"tuple"', '"sum"', '"sorted"', '"join"', '"any"', '"all"'):
            assert consumer in src.split('val genExpConsumers', 1)[1].split(')', 1)[0], consumer
        # stored or returned: `valueOf` asks with eagerGen = false
        assert 'comprehensionLowering(b, eagerGen = false)' in src
        # a plain-`expr` position has no prelude slot and says so
        assert 'hole("expr:comprehension-position")' in src

    def test_renderer_needs_no_new_shape(self):
        """The lowering reuses `assign`, `forIn`, `ifte`, `mcall`, `listE`, `dictE`, `name`."""
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            'render_lean', Path(__file__).resolve().parents[1] / 'cartographer/render_lean.py')
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        loop = {'k': 'forIn', 'x': '$comp$x', 'e': {'k': 'name', 'v': 'xs'},
                'body': {'k': 'exprS', 'e': {'k': 'mcall', 'recv': {'k': 'name', 'v': 'tmp0'},
                                            'm': 'append',
                                            'args': [{'k': 'name', 'v': '$comp$x'}]}}}
        head, kids = mod.stmt_shape(loop)
        assert head == '.forIn'
        assert '$comp$x' in mod.stmt(loop)


class TestJavaAndGoDialects:
    """`.java` and `.go` are `Dialect` constructors, not `.cLike` aliases. Three scripts
    carry an extension→dialect table each (the renderer decides, `lang_matrix.py` measures
    independently, `differential.py` records what it expects); this pins them to one
    another and to the constructors that exist in `Syntax.lean`."""

    def _module(self, rel, name):
        import importlib.util
        spec = importlib.util.spec_from_file_location(name, ROOT / rel)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return mod

    def test_renderer_routes_java_go_and_kotlin_to_their_own_constructors(self):
        render = self._module('cartographer/render_lean.py', 'render_lean_dialects')
        assert render.DIALECT['.java'] == '.java'
        assert render.DIALECT['.go'] == '.go'
        # Kotlin/JVM rides `.java`: same integer model and boolean operators; its
        # structural string `==` lands on Java's `str:reference-equality` hole.
        assert render.DIALECT['.kt'] == '.java' and '.kts' not in render.DIALECT  # Kotlin scripts: recognised, not routed (repository_inventory)
        assert render.DIALECT['.c'] == '.cLike'
        constructors = {'.python', '.cLike', '.javascript', '.java', '.go'}
        assert set(render.DIALECT.values()) <= constructors

    def test_every_rendered_dialect_is_a_constructor_in_syntax(self):
        render = self._module('cartographer/render_lean.py', 'render_lean_dialects2')
        syntax = (ROOT / 'Autoform/Lang/Core/Syntax.lean').read_text()
        block = syntax.split('inductive Dialect where', 1)[1].split('deriving', 1)[0]
        declared = {'.' + line.strip()[2:].split()[0]
                    for line in block.splitlines() if line.strip().startswith('| ')}
        assert set(render.DIALECT.values()) <= declared, declared

    def test_the_measuring_script_agrees_with_the_renderer(self):
        render = self._module('cartographer/render_lean.py', 'render_lean_dialects3')
        matrix = self._module('scripts/lang_matrix.py', 'lang_matrix_dialects')
        assert {k: '.' + v for k, v in matrix.DIALECT.items()} == render.DIALECT

    def test_differential_expects_the_same_dialects(self):
        src = (ROOT / 'scripts/differential.py').read_text()
        table = src.split('DIALECT_FOR = ', 1)[1].split('}', 1)[0] + '}'
        expected = eval(table)
        assert expected['java'][0] == 'java' and expected['go'][0] == 'go'
        assert expected['kotlin'][0] == 'java'
        # Exactness is about the UNTAGGED integer path (one width per language), which
        # is why an own constructor does not make the dialect "exact".
        assert expected['java'][1] is False and expected['go'][1] is False

    def test_java_string_equality_is_a_named_hole_not_a_guess(self):
        sem = (ROOT / 'Autoform/Lang/Core/Semantics.lean').read_text()
        syntax = (ROOT / 'Autoform/Lang/Core/Syntax.lean').read_text()
        assert 'def stringEqIsReference : Dialect → Bool' in syntax
        assert 'if d.stringEqIsReference then .hole "str:reference-equality"' in sem


class TestDunderDispatch:
    """The container protocol on user instances (docs/languages.md §10.6).

    `x in c`, `c[k]`, `c[k] = v` and `del c[k]` on an ordinary instance are method calls
    in Python. `Ctx.dunderOn` is the one place that decides whether Core makes the call,
    and these pins hold its shape in place: the dispatch is Python-only, requires the
    class to DEFINE the method (`classDefines`, so a free `__getitem__` is not the
    class's), leaves boxed containers on their structural path, and falls back to the
    hole a class without the method always had. The behaviour itself is checked by the
    `dunderProg` `#guard`s in `Semantics.lean`, against CPython, on every build.
    """

    SEM = (ROOT / 'Autoform/Lang/Core/Semantics.lean').read_text()

    def test_dispatch_is_one_named_predicate(self):
        assert 'def Ctx.dunderOn (ctx : Ctx) (h : Heap) (c : Val) (name : String) : Option (Ref × Func)' in self.SEM
        assert 'if ctx.dialect == .python then' in self.SEM.split('def Ctx.dunderOn', 1)[1].split('theorem', 1)[0]
        assert 'if ctx.classDefines o.cls name then' in self.SEM

    def test_all_four_container_operations_consult_it(self):
        for name in ('__contains__', '__getitem__', '__setitem__', '__delitem__'):
            assert f'"{name}" with' in self.SEM, name
        assert 'match ctx.dunderOn h₂ c "__contains__" with' in self.SEM
        assert 'match ctx.dunderOn h₂ c "__getitem__" with' in self.SEM
        assert 'match ctx.dunderOn h₃ (.ref r) "__setitem__" with' in self.SEM
        assert 'match ctx.dunderOn h₂ (.ref r) "__delitem__" with' in self.SEM

    def test_not_in_negates_the_methods_truthiness(self):
        assert '(if neg then !rv.truthy else rv.truthy)' in self.SEM

    def test_a_class_without_the_method_keeps_its_hole(self):
        """The fallbacks are the labels that existed before; nothing became a guess."""
        for label in ('in:non-container', 'index:unsupported',
                      'setIndex:immutable-containers', 'delIndex:immutable-containers'):
            assert f'"{label}"' in self.SEM, label
        assert '"m.py:<module>.plainIn"' in self.SEM and '"m.py:<module>.boxedIn"' in self.SEM

    def test_fuel_monotonicity_covers_the_dispatch(self):
        fm = (ROOT / 'Autoform/FuelMono.lean').read_text()
        # the four container dunders, plus the iteration protocol's `__iter__` (`hdi`)
        assert fm.count('Ctx.dunderOn_resolves hd') == 5
        assert 'Ctx.dunderOn_resolves hdi' in fm
        assert 'theorem Ctx.dunderOn_resolves' in self.SEM


class TestValueDunders:
    """Milestone 1(b): a Python class redefines what a VALUE means for its instances.

    `a == b` is `a.__eq__(b)`, `a < b` is `a.__lt__(b)`, `len(a)` is `a.__len__()`, `bool(a)`
    is `a.__bool__()` or, failing that, `a.__len__() != 0`. Core used to answer identity,
    a hole and a hole -- silent wrong answers for any class that defines the dunder. These
    pin the shape of the dispatch; the CPython comparisons themselves are the `#guard`s
    over `valueDunderProg` in Semantics.lean, checked on every build."""

    SEMANTICS = (ROOT / 'Autoform/Lang/Core/Semantics.lean').read_text()

    def test_the_comparison_family_forces_the_heap_path(self):
        # The order operators join ==/!= because `__lt__` and friends need the receiver's
        # class off the heap; a scalar comparison still never touches it.
        assert 'def isCmpOp (op : String) : Bool :=' in self.SEMANTICS
        assert 'isCmpOp op && (x.kind == 8 || y.kind == 8)' in self.SEMANTICS

    def test_dispatch_requires_the_class_to_define_the_dunder_itself(self):
        # `classDefines`, not `resolveMethod`: a free function named `__eq__` must not be
        # mistaken for a method of every class.
        for helper in ('cmpDunderTarget', 'builtinDunderTarget'):
            body = self.SEMANTICS.split(f'def {helper}', 1)[1].split('\n\n', 1)[0]
            assert 'ctx.classDefines' in body, helper
            assert 'resolveMethod' not in body, helper
            # ordinary instances only: no container payload, not a module frame
            assert 'o.payload.toVal.isSome || o.cls.startsWith "<module>"' in body, helper
            assert 'ctx.dialect != .python then none' in body, helper

    def test_not_equal_falls_back_to_the_negation_of_eq(self):
        assert 'if ctx.classDefines o.cls "__ne__" then some (r, o.cls, "__ne__", false)' in self.SEMANTICS
        assert 'else if ctx.classDefines o.cls "__eq__" then some (r, o.cls, "__eq__", true)' in self.SEMANTICS
        assert '.val (if neg then .bool (!v.truthy) else v)' in self.SEMANTICS

    def test_bool_falls_back_to_len_and_the_answers_are_type_checked(self):
        assert '| "bool" => match pick "__bool__" with' in self.SEMANTICS
        assert '| none   => pick "__len__"' in self.SEMANTICS
        # CPython: __len__ must be a non-negative int, __str__ a str, __bool__ a bool.
        assert '| "len",  .int i  => if i < 0 then .exn (.str "ValueError") else .val v' in self.SEMANTICS
        assert '| "str",  _       => .exn (.str "TypeError")' in self.SEMANTICS

    def test_every_protocol_has_a_cpython_guard(self):
        guards = self.SEMANTICS.split('private def valueDunderProg', 1)[1].split('/-! ## JavaScript', 1)[0]
        for subject in ('eqTrue', 'eqFalse', 'neFalse', 'ltTrue', 'geHole', 'lenC', 'boolC',
                        'boolZ', 'hashH', 'strH', 'identityQ', 'lenQ'):
            assert f'#guard match runFunc valueDunderProg 200 "{subject}" []' in guards, subject

    def test_the_proofs_follow_the_dispatch(self):
        fuelmono = (ROOT / 'Autoform/FuelMono.lean').read_text()
        excsafe = (ROOT / 'Autoform/Lang/Core/ExcSafe.lean').read_text()
        assert 'cases hct : cmpDunderTarget ctx h₂ op x with' in fuelmono
        assert 'cases hbt : builtinDunderTarget ctx h₁ f vs with' in fuelmono
        assert 'theorem builtinDunderResult_excSafe' in excsafe
        assert 'builtinDunderResult_excSafe _ _ _ (Prod.mk.inj hy).2' in excsafe
        # The pure fragment is call-free BY CONSTRUCTION again: a comparison can now call.
        refine = (ROOT / 'Autoform/Refine.lean').read_text()
        assert '(hop : isCmpOp op = false)' in refine



class TestJavaScriptLowering:
    """Milestone 8 (docs/GOAL-arbitrary-codebases.md): the JS/TS control and operator
    forms that used to be the top `ledger-LangJS/LangTS.json` labels now lower, gated on
    the file kind exactly as Python's lowerings are gated on `pyFile`. Source-level pins;
    the end-to-end check is the Joern-backed numeric suite."""

    def _src(self):
        return (Path(__file__).resolve().parents[1] / 'cartographer/export_ast.sc').read_text()

    def test_js_like_files_are_the_dialect_tables_extensions(self):
        src = self._src()
        assert 'def jsLikeFile: Boolean =' in src
        for ext in ('.js', '.ts', '.tsx', '.jsx', '.mjs', '.cjs'):
            assert f'"{ext}"' in src.split('def jsLikeFile', 1)[1].split('\n\n', 1)[0], ext

    def test_throw_is_a_raise_under_javascript_only(self):
        src = self._src()
        assert 'case "THROW" if (jsLikeFile || javaFile) && kids.size == 1 =>' in src  # Java shares the arm (JLS §14.18)
        assert 'case "THROW" if jsLikeFile || javaFile => holeS("control:THROW:shape")' in src
        # the generic control hole is still the fallthrough for every other language
        assert 'case t          => holeS("control:" + t)' in src

    def test_single_catch_binds_the_thrown_value(self):
        src = self._src()
        assert 'def jsTryCatch(body: ujson.Obj, c: ControlStructure): ujson.Obj' in src
        assert 'jsLikeFile && catches.size == 1 && elses.isEmpty) jsTryCatch(body, catches.head)' in src
        # a handler whose binding cannot be seen is a hole, never an unbound `e`
        assert 'holeS("control:TRY-catch-binding")' in src

    def test_void_and_non_null_assertion(self):
        src = self._src()
        assert 'mfn == "<operator>.notNullAssert" && kids.size == 1' in src
        assert 'mfn == "<operator>.void" && kids.size == 1' in src
        assert 'hole("op:void:impure-operand")' in src
        assert 'callName(c) == "<operator>.void" && kidsOf(c).size == 1' in src

    def test_await_is_still_a_counted_hole(self):
        """No lowering claims `await`: it needs suspended frames Core does not have."""
        src = self._src()
        assert '"<operator>.await"' not in src

    def test_object_literal_properties_are_payload_keys(self):
        sem = (Path(__file__).resolve().parents[1] / 'Autoform/Lang/Core/Semantics.lean').read_text()
        assert 'def jsContainerField (p : Payload) (f : String) : EResult :=' in sem
        assert 'if ctx.dialect == .javascript && o.payload.toVal.isSome then' in sem
        assert 'Stdlib.dictSet kvs (.str f) vv' in sem
        assert 'runFunc jsProg 300 "objLit" []' in sem
        excsafe = (Path(__file__).resolve().parents[1] / 'Autoform/Lang/Core/ExcSafe.lean').read_text()
        assert 'theorem jsContainerField_ne_exn' in excsafe


class TestValueCallees:
    """`f(x)(y)`: a callee that is itself a call is applied as a VALUE.

    The hole `call:computed-callee` stood for "Core has no apply-this-value form". It has
    one now (`Expr.callValue`), so the exporter lowers a `Call` callee to it and only an
    unnamed callee of some other shape stays a hole. What must never come back is the
    `call ""` emission this replaced: it type-checked and resolved to nothing.
    """

    def test_exporter_lowers_a_call_callee_to_callV(self):
        src = EXPORTER.read_text()
        assert 'case Some(cl: Call) =>' in src
        assert 'ujson.Obj("k" -> "callV", "f" -> expr(cl), "args" -> argExprs(args, kwArgs))' in src
        assert 'case _ => hole("call:no-callee-name")' in src
        assert '"call:computed-callee"' not in src
        assert 'ujson.Obj("k" -> "call", "f" -> ""' not in src

    def test_semantics_dispatches_on_the_value_and_refuses_non_callables(self):
        sem = (ROOT / 'Autoform/Lang/Core/Semantics.lean').read_text()
        assert '| n+1, h, ρ, .callValue fe args =>' in sem
        assert '.hole "call:value:not-callable"' in sem
        # CPython-checked pins: `mk(10)(2)` is 12, `d["k"](3)` is 6.
        assert 'runFunc valueCallProg 200 "chained" [] with | .val (.int 12)' in sem
        assert 'runFunc valueCallProg 200 "fromDict" [] with | .val (.int 6)' in sem
        syntax = (ROOT / 'Autoform/Lang/Core/Syntax.lean').read_text()
        assert '| callValue : Expr → List Expr → Expr' in syntax
        # The ledger neither counts a value call as a resolvable NAME nor forgets it.
        ledger = (ROOT / 'Autoform/Ledger.lean').read_text()
        assert '| .callValue f as => eCalls f ++ eCallsL as' in ledger
        assert '| .callValue f as => 1 + eRisk f + eRiskL as' in ledger


class TestModuleVariables:
    """A Python module object carries its module-level VARIABLES (Language Reference
    §3.2.9: `m.x` is `m.__dict__["x"]`), written by the module's own body as each binding
    runs, and `from m import x` reads that field at import time (§7.11). Behavioural check:
    the `modVarProg` `#guard_msgs` in `Semantics.lean`; these pin the exporter side, which
    needs Joern to exercise. Closes `import:member-not-found` on every Python module the CPG
    contains (66 of requests' 148 holes; click's `get_completion_class` divergence).
    """

    def test_a_module_level_binding_also_writes_the_module_object(self):
        src = EXPORTER.read_text()
        assert 'def bindName(nm: String, e: ujson.Value): ujson.Obj' in src
        # the globals-frame write is unchanged; the module object's field is the second copy
        assert '"a" -> ujson.Obj("k" -> "setGlobal", "x" -> nm, "e" -> e)' in src
        assert '"b" -> ujson.Obj("k" -> "setField", "r" -> moduleRef(currentModuleFull), "f" -> nm' in src
        # only a Python module has an object to write; a C `<global>` scope keeps `setGlobal`
        assert 'else if (pyModuleFullNames.contains(currentModuleFull))' in src
        # every former `setGlobal`/`assign` site goes through it
        assert 'val k = if (isGlobalWrite(' not in src

    def test_from_import_of_a_variable_reads_the_field_not_a_hole(self):
        src = EXPORTER.read_text()
        assert 'ujson.Obj("k" -> "field", "a" -> moduleRef(mod), "f" -> name)' in src
        # the old label survives only for a module without an object
        assert 'else hole("import:member-not-found")' in src
        assert '§7.11' in src and '§3.2.9' in src

    def test_module_bodies_run_in_import_dependency_order(self):
        src = EXPORTER.read_text()
        assert 'val importEdges = collection.mutable.LinkedHashMap' in src
        assert 'def recordImportEdge(target: String): Unit' in src
        # recorded for `from p import x` and for every prefix of `import a.b.c`
        assert 'recordImportEdge(mod)' in src
        assert 'segs.indices.foreach(i => moduleAtTolerant(segs.take(i + 1).mkString("/")).foreach(recordImportEdge))' in src
        # depth-first over the recorded edges; a cycle keeps its place
        assert 'importEdges.getOrElse(name, Nil).foreach(dep => if (byName.contains(dep)) visit(dep))' in src
        assert 'ordered.toList.map(emit(_, true))' in src

    def test_the_semantics_pins_the_shape_against_cpython(self):
        sem = (ROOT / 'Autoform/Lang/Core/Semantics.lean').read_text()
        assert 'def modVarProg : Program' in sem
        assert '#guard_msgs in #eval runMain modVarProg 200 [modVarObjects, modVarAInit, modVarBInit] "b.py:<module>.f" []' in sem
        # the misordered run is pinned as a named hole, not a value
        assert '#guard_msgs in #eval runMain modVarProg 200 [modVarObjects, modVarBInit, modVarAInit] "b.py:<module>.f" []' in sem

class TestGoAndCLowering:
    """Slice I of the interpreter push: Go statements the exporter used to hole and the
    Core shapes they lower to, each grounded in a quoted section of the Go specification
    (see the comments at the rules). The Core side is `goProg` in `Semantics.lean`,
    checked against `go run` on every build; these pin the exporter rules, which no
    in-repo test can execute without Joern."""

    def test_import_declarations_are_not_behaviour(self):
        src = EXPORTER.read_text()
        assert 'case _: Import     => skip' in src
        assert '"Import\n    // declarations"' in src or 'Go spec, "Import' in src

    def test_go_raw_strings_drop_carriage_returns_and_nothing_else(self):
        src = EXPORTER.read_text()
        assert "else if (goFile && c.length >= 2 && c.head == '`' && c.last == '`')" in src
        assert 'c.drop(1).dropRight(1).replace("\\r", "")' in src

    def test_go_tuple_assignment_is_two_phase(self):
        src = EXPORTER.read_text()
        assert 'def goTupleAssign(ks: List[AstNode]): ujson.Obj' in src
        # the spec sentence the temporaries exist for
        assert 'The assignment proceeds in two phases' in src
        # every right-hand value into a temporary before any target is written
        assert 'val temps = rhss.map(_ => freshExprVTemp())' in src
        # the single multi-valued form indexes a tuple; anything else is a named hole
        assert '"k" -> "index", "a" -> name(tmp), "b" -> intLit(BigInt(i))' in src
        assert 'holeS("assign:arity:go-shape")' in src
        assert 'holeS("assign:arity:target-shape")' in src
        assert 'case ks if goFile && ks.size >= 3 => goTupleAssign(ks)' in src

    def test_go_for_forms_are_type_gated(self):
        src = EXPORTER.read_text()
        # `for cond {}` only when the first child IS a boolean; a range clause is not
        assert 'goFile && ks.size == 2 && !ks(0).isInstanceOf[Block] && staticTypeOf(ks(0)) == "bool"' in src
        assert 'else if (goFile && ks.size == 1)' in src
        assert 'holeS("control:FOR:range")' in src

    def test_core_guards_exist_for_every_lowered_shape(self):
        sem = (ROOT / 'Autoform/Lang/Core/Semantics.lean').read_text()
        block = sem.split('private def goProg', 1)[1]
        for subject, value in (('swap', 21), ('destructure', 34), ('cond', 3), ('forever', 6)):
            assert f'#guard match runFunc goProg 300 "{subject}" [] with | .val (.int {value})' in block, subject

class TestSliceJDefinitionTimeSemantics:
    """Constructs whose meaning is fixed at DEFINITION time, pinned to the specification
    that fixes it: `typing.overload` stubs (docs.python.org/3/library/typing.html#typing.overload:
    the runtime dummy raises `NotImplementedError`, the following definition rebinds the
    name), decorators (Language Reference §8.7: `@f def g` is `g = f(g)`), negative
    numeric defaults (§8.7: defaults are evaluated once when the `def` executes), and
    Kotlin local functions (Kotlin spec, "Local function declaration": capture by
    reference). The decoder-level checks are in tests/test_python_signatures.py."""

    def test_an_overload_stub_is_a_raise_not_a_hole(self):
        src = EXPORTER.read_text()
        assert 'case Some(s) if s.obj.get("overloadStub").exists(_.bool) => None' in src
        assert 'obj("vararg") = "<overload-stub-args>"' in src
        assert '"op" -> "py:exception:NotImplementedError",' in src
        # the stub is checked BEFORE every binding gap, so a decorated stub inside a class
        # does not fall back to the receiver-signature refusal
        assert 'if (overloadStub) None' in src

    def test_an_external_decorator_is_named(self):
        src = EXPORTER.read_text()
        assert 'externalDecorator.map(d => "decorator:external:" + d).getOrElse("call:python-decorator-binding")' in src
        # a decorated method is a decorator gap, not a receiver gap
        assert 'else if (signature("decorated").bool) Some(decoratorGap)' in src

    def test_kotlin_local_functions_close_over_an_unmutated_scope_only(self):
        src = EXPORTER.read_text()
        assert 'holeS("kotlin:local-fn-capture-mutated")' in src
        assert 'frees.filter(n => assignCount(p, n) > 1)' in src
        # top-level Kotlin functions in the file initialiser are separate exports
        assert 'case m: Method if moduleScope && List(".kt", ".kts").exists(currentFile.endsWith) => skip' in src

class TestIterationProtocol:
    """`for x in obj` on a user instance follows the language reference: `__iter__`, then
    `__next__` until `StopIteration` (or `__getitem__` from 0 until `IndexError`), with
    `break`/`continue`/`return` meaning what §8.3 says. Behaviour is pinned by the
    `iterProg` `#guard`s in `Semantics.lean` against CPython on every build; these pin the
    shape so the design cannot drift silently."""

    SEMANTICS = (ROOT / 'Autoform/Lang/Core/Semantics.lean').read_text()
    FUELMONO = (ROOT / 'Autoform/FuelMono.lean').read_text()

    def test_for_creates_the_iterator_the_way_iter_does(self):
        # __iter__ first, then the sequence protocol, then the structural fallback
        assert 'match ctx.dunderOn h₁ v "__iter__" with' in self.SEMANTICS
        assert 'match ctx.dunderOn h₁ v "__getitem__" with' in self.SEMANTICS
        assert 'execStmt ctx n h₁ (ρ.set iterTmp v) (seqDriver x body)' in self.SEMANTICS

    def test_the_iterator_is_driven_by_a_synthesised_statement(self):
        """No ninth interpreter function: the driver is a Core statement over names no
        source can spell, so FuelMono's statement IH covers it."""
        assert 'def iterTmp : String := "$iter"' in self.SEMANTICS
        assert 'def nextDriver (x : String) (body : Stmt) : Stmt :=' in self.SEMANTICS
        assert '(.lit (.str "StopIteration")))' in self.SEMANTICS
        assert 'def seqDriver (x : String) (body : Stmt) : Stmt :=' in self.SEMANTICS
        assert '(.lit (.str "IndexError")))' in self.SEMANTICS
        assert 'simp [nextDriver, controlCovered, hb]' in self.FUELMONO
        assert 'simp [seqDriver, controlCovered, hb]' in self.FUELMONO

    def test_iter_and_next_builtins_and_the_default_form(self):
        assert '| "iter" => pick "__iter__"' in self.SEMANTICS
        assert '| "next" => pick "__next__"' in self.SEMANTICS
        assert 'def nextDefaultTarget (ctx : Ctx) (h : Heap) (f : String) (vs : List Val)' in self.SEMANTICS
        assert '| (h₂, .exn (.str "StopIteration")) => (h₂, .val d)' in self.SEMANTICS

    def test_every_protocol_claim_has_a_cpython_guard(self):
        guards = self.SEMANTICS.split('private def iterProg', 1)[1].split('/-! ## JavaScript', 1)[0]
        for subject in ('collect', 'breaks', 'viaList', 'viaSeq', 'exhausted', 'withDefault',
                        'iterThenNext'):
            assert f'#guard match runFunc iterProg 400 "{subject}" []' in guards, subject

    def test_the_spec_sections_are_cited_next_to_the_rules(self):
        for cite in ('library/functions.html#iter', 'library/functions.html#next',
                     'reference/compound_stmts.html §8.3', '"Iterator Types"'):
            assert cite in self.SEMANTICS, cite

class TestExceptBindingAndCorpusClasses:
    """`except E as e:` binds, and a class the corpus defines is an exception class.

    Both rules are the Python reference's (§8.4.1: the handler matches "the class or a
    non-virtual base class of the exception object, or a tuple that contains such a
    class"; the `as` target is bound to the exception object), applied to Core's
    representation of an exception as its class NAME. The behavioural checks are the
    `excClassProg` `#guard`s in `Semantics.lean`, against CPython; these pin the shape.
    """

    def test_core_accepts_the_programs_own_exception_classes(self):
        sem = SEMANTICS.read_text()
        syntax = SYNTAX.read_text()
        assert 'excClasses : List String := []' in syntax
        assert 'def pythonRaise (extra : List String) (v : Val) : EResult' in sem
        assert 'Stdlib.excNames.contains name || extra.contains name' in sem
        assert 'match pythonRaise ctx.excClasses v with' in sem
        # the invariant is restated over the program's classes, not weakened away
        excsafe = (ROOT / 'Autoform/Lang/Core/ExcSafe.lean').read_text()
        assert 'ExcSafeIn ctx.excClasses v' in excsafe
        assert 'sorry' not in excsafe.replace('-- sorry', '')
        stdlib = (ROOT / 'Autoform/Lang/Core/Stdlib.lean').read_text()
        assert 'def ExcSafeIn (extra : List String) (v : Val) : Prop' in stdlib

    def test_every_guard_names_a_cpython_outcome(self):
        sem = SEMANTICS.read_text()
        block = sem.split('private def excClassProg', 1)[1]
        for subject in ('catchOwn', 'catchBase', 'miss', 'bound', 'reraise', 'notExc'):
            assert f'#guard match runFunc excClassProg 200 "{subject}" []' in block, subject
        assert '.exn (.str "TypeError")' in block          # a non-exception name
        assert '.val (.str "MyErr")' in block               # the binding is the class name

    def test_exporter_closes_the_accepted_set_over_the_corpus_hierarchy(self):
        src = EXPORTER.read_text()
        assert 'val pyClassBases: Map[String, String]' in src
        assert 'def acceptedFor(types: List[String], info: ujson.Value): List[String]' in src
        assert 'def isCorpusException(name: String, bb: Map[String, List[String]]): Boolean' in src
        assert 'excAncestors(name, bb).contains("BaseException")' in src
        # a corpus type that is not an exception class stays the dynamic hole
        assert 'case "typed" if !corpusTypes.forall(isCorpusException(_, bb)) =>' in src
        # the module initializer carries the list the renderer turns into Program.excClasses
        assert 'obj("exceptionClasses") = ujson.Arr.from' in src
        assert 'extra += ", excClasses := [" + excs + "]"' in RENDERER.read_text()

    def test_binding_is_exact_or_refused_never_a_string_for_an_object(self):
        src = EXPORTER.read_text()
        # the decoder's rule
        assert 'def binding_ok(node):' in src
        assert "payload_calls = ('isinstance', 'type', 'str', 'repr', 'format')" in src
        # the exporter's holes for the payload Core does not carry
        assert 'hole("exception:payload:" + f)' in src
        assert 'hole("exception:payload:" + c.name)' in src
        # `isinstance(e, T)` is the dispatch test, not a call
        assert 'hole("exception:isinstance-type")' in src
        # re-raise of the bound name and a bare `raise` use `Stmt.raise` directly
        assert 'kind == "name" && exceptionBindings.contains(info("name").str)' in src
        assert 'info("label").str == "op:raise-bare" && pendingExceptions.nonEmpty' in src

    def test_decoder_classifies_handlers_and_raises(self):
        import subprocess, sys, json
        script = EXPORTER.read_text()
        decoder = script.split('  val pythonHandlerDecoder = """', 1)[1].split('\n"""', 1)[0]
        source = ('class MyErr(Exception):\n    pass\n\n'
                  'def boom():\n    raise MyErr("x")\n\n'
                  'def f():\n'
                  '    try:\n        boom()\n'
                  '    except (KeyError, MyErr) as e:\n        raise e\n'
                  '    except Exception as e:\n        return e.args\n'
                  '    except ValueError as e:\n        return e\n'
                  '    except os.error:\n        pass\n')
        r = subprocess.run([sys.executable, '-I', '-S', '-c', decoder], input=source,
                           text=True, capture_output=True, timeout=30)
        assert r.returncode == 0, r.stderr
        d = json.loads(r.stdout)
        handlers = next(iter(d['tries'].values()))['handlers']
        assert handlers[0]['kind'] == 'typed'
        assert handlers[0]['corpusTypes'] == ['MyErr'] and handlers[0]['builtinTypes'] == ['KeyError']
        assert handlers[0]['bindingOk'] is True          # `raise e`
        assert handlers[1]['bindingOk'] is True          # `e.args` -> payload hole
        assert handlers[2]['bindingOk'] is False         # `return e` would leak a string
        assert handlers[3] == {'binding': None, 'kind': 'hole', 'label': 'control:TRY-handler-type'}
        assert d['raises']['5:5'] == {'kind': 'name-call', 'name': 'MyErr'}
        assert d['exceptionBases']['KeyError'] == ['LookupError', 'Exception', 'BaseException']
        assert 'KeyError' in d['represented']

class TestJavaScriptObjectsAndEquality:
    """Slice G of the interpreter-for-every-language pass: `new`, `this`, `typeof`, `===`
    and `==` under `.javascript`, each rule pinned to the ECMA-262 clause it implements.
    The behavioural checks are the `jsProg` `#guard`s in `Semantics.lean` (Node's values
    in the comments); these hold the shape in place."""

    SEM = (Path(__file__).resolve().parents[1] / 'Autoform/Lang/Core/Semantics.lean').read_text()
    SYN = (Path(__file__).resolve().parents[1] / 'Autoform/Lang/Core/Syntax.lean').read_text()
    EXP = (Path(__file__).resolve().parents[1] / 'cartographer/export_ast.sc').read_text()

    def test_the_constructor_name_is_a_dialect_fact(self):
        assert 'def ctorName : Dialect → String' in self.SYN
        assert '| .javascript => "<init>"' in self.SYN
        assert 'match ctx.resolveCtor cls with' in self.SEM  # `__init__` then `<init>`: Python, JS and Java
        # the fuel-monotonicity proof cases on the same term
        fm = (Path(__file__).resolve().parents[1] / 'Autoform/FuelMono.lean').read_text()
        assert 'Ctx.resolveCtor ctx cls' in fm  # the constructor lookup FuelMono splits on

    def test_typeof_and_equality_cite_the_spec(self):
        for clause in ('§13.5.3', '§7.2.14 IsStrictlyEqual', '§7.2.13 IsLooselyEqual'):
            assert clause in self.SEM, clause
        assert 'def jsTypeof : Val → String' in self.SEM
        assert 'def jsStrictEq : Val → Val → Bool' in self.SEM
        assert 'def jsLooseEq (x y : Val) : Option Bool' in self.SEM
        # the undecidable steps hole rather than guess
        assert 'js:loose-eq:' in self.SEM
        # the null/undefined collapse is stated, not hidden
        assert '`null` and `undefined` are one value here' in self.SEM

    def test_js_equality_is_routed_before_the_numeric_arms(self):
        i = self.SEM.index('def applyBinop (d : Dialect)')
        head = self.SEM[i:i + 900]
        assert '| "js:===", _, _ | "js:!==", _, _ | "js:==", _, _ | "js:!=", _, _ => languageBinop d op a b' in head

    def test_every_rule_has_a_node_checked_guard(self):
        guards = self.SEM.split('private def jsProg', 1)[1]
        for subject in ('newPt', 'typeofs', 'eqs', 'eqObj'):
            assert f'runFunc jsProg 300 "{subject}" []' in guards, subject

    def test_exporter_treats_this_like_cpp_and_reads_the_source_for_strictness(self):
        assert 'if ((cppFile || jsLikeFile || javaFile) && n == "this") "self" else n' in self.EXP
        assert 'filterNot(x => (cppFile || jsLikeFile) && x == "this")' in self.EXP
        assert 'if (jsLikeFile) None' in self.EXP           # no receiver re-threaded as arg 0
        assert 'def binopFor(c: Call): String' in self.EXP
        assert 'c.code.contains("===") || c.code.contains("!==")' in self.EXP
        # typeof is jssrc2cpg's one-child `<operator>.instanceOf`; two children stay a hole
        assert '"op" -> "js:typeof"' in self.EXP
        assert 'hole("op:instanceof:class-hierarchy")' in self.EXP

    def test_new_folds_to_alloc_and_names_what_it_cannot_build(self):
        assert 'callName(ctor) == "<operator>.new"' in self.EXP
        assert 'ujson.Obj("k" -> "alloc", "cls" -> i.name,' in self.EXP
        assert 'hole("op:new:" + i.name)' in self.EXP
        assert 'hole("op:new:unfolded")' in self.EXP
        assert 'hole("op:new:computed-constructor")' in self.EXP

class TestSliceDPythonLabels:
    """Slice D of the arbitrary-codebases goal: the Python labels that were still holes on
    click 8.2.1 / requests 2.32.5 -- `op:logicalAnd`/`Or` (n-ary chains), `op:assert`,
    `op:setLiteral`, `expr:BLOCK-impure` -- and the one deliberately kept (`lit:bytes`).
    Every rule cites the Python Language Reference section it implements; the behavioural
    checks are the `sliceDProg` `#guard`s in `Semantics.lean` against CPython.
    """

    SEMANTICS = (ROOT / 'Autoform' / 'Lang' / 'Core' / 'Semantics.lean').read_text()
    STDLIB = (ROOT / 'Autoform' / 'Lang' / 'Core' / 'Stdlib.lean').read_text()

    def test_an_and_or_chain_folds_left_as_the_grammar_is_left_recursive(self):
        src = EXPORTER.read_text()
        assert '(mfn == "<operator>.logicalAnd" || mfn == "<operator>.logicalOr") && kids.size > 2' in src
        assert 'kids.map(expr).reduceLeft((a, b) =>' in src
        assert 'Python Language Reference §6.11 (Boolean operations)' in src

    def test_assert_lowers_to_the_reference_equivalence(self):
        src = EXPORTER.read_text()
        assert 'callName(c) == "<operator>.assert" && kidsOf(c).nonEmpty' in src
        assert '"op" -> "py:exception:AssertionError"' in src
        assert 'Python Language Reference §7.3 (The assert statement)' in src
        # the message is evaluated only on failure: it sits in the else-branch
        # the condition's prelude hoists before the test (§16.R4); the message stays lazy
        assert 'seqOf(condPrelude :+ ujson.Obj("k" -> "ifte", "c" -> condV, "t" -> skip,' in src

    def test_a_set_display_is_a_unit_valued_dict_with_distinct_keys(self):
        src = EXPORTER.read_text()
        assert 'pyFile && mfn == "<operator>.setLiteral" && kids.nonEmpty' in src
        assert 'ujson.Arr(expr(k), ujson.Obj("k" -> "unit"))' in src
        assert 'def dictOfPairs' in self.STDLIB
        assert 'Stdlib.dictOfPairs ps' in self.SEMANTICS
        for method in ('"add"', '"discard"'):
            assert method in self.STDLIB.split('def methodNames', 1)[1].split(']', 1)[0], method
        assert '| .dict kvs, "remove", [x] =>' in self.STDLIB

    def test_read_only_builtins_see_through_a_boxed_container(self):
        assert 'def unboxesArgs (name : String) : Bool :=' in self.STDLIB
        assert 'if Stdlib.unboxesArgs f then vs.map (·.unbox h₁) else vs' in self.SEMANTICS

    def test_impure_block_preludes_are_hoisted_only_where_a_prelude_exists(self):
        src = EXPORTER.read_text()
        assert 'def blockExprV(b: Block)' in src
        assert 'comprehensionLowering(b, eagerGen = genExpEager).getOrElse(blockExprV(b))' in src
        # plain `expr` still has no slot and keeps the label
        assert 'if (bad.isEmpty) bad = "expr:BLOCK-impure"' in src

    def test_bytes_stay_a_hole_with_the_reference_cited(self):
        src = EXPORTER.read_text()
        assert 'hole("lit:bytes")' in src
        assert 'Python Language Reference §2.5.5' in src

    def test_every_rule_has_a_cpython_guard(self):
        guards = self.SEMANTICS.split('private def sliceDProg', 1)[1]
        for subject in ('setLen', 'setIn', 'setAdd', 'setRemoveMissing', 'dictDup',
                        'andChain', 'assertFails', 'assertPasses'):
            assert f'#guard match runFunc sliceDProg 200 "{subject}" []' in guards, subject

class TestJavaCoreSemantics:
    """Java under `Dialect.java`: the rules landed in 16.H of docs/languages.md, each pinned
    to the text that carries its JLS citation so the citation cannot drift from the rule."""

    SEM = (Path(__file__).resolve().parents[1] / 'Autoform/Lang/Core/Semantics.lean').read_text()
    STD = (Path(__file__).resolve().parents[1] / 'Autoform/Lang/Core/Stdlib.lean').read_text()
    EXP = (Path(__file__).resolve().parents[1] / 'cartographer/export_ast.sc').read_text()

    def test_this_is_the_receiver_in_java_too(self):
        # JLS 15.8.3; without this every `this.x` in a Java method read an unbound name.
        assert 'if ((cppFile || jsLikeFile || javaFile) && n == "this") "self" else n' in self.EXP
        assert 'JLS §15.8.3' in self.EXP

    def test_signatures_are_stripped_before_method_resolution(self):
        assert 'def stripSig (k : String) : String' in self.SEM
        assert 'strEndsWith (stripSig p.1) ("." ++ cls ++ "." ++ meth)' in self.SEM
        assert 'def Ctx.resolveCtor' in self.SEM and 'ctx.resolveMethod cls "<init>"' in self.SEM
        assert '#guard stripSig "a.py:<module>.C.f" == "a.py:<module>.C.f"' in self.SEM

    def test_float_to_integral_follows_jls_5_1_3(self):
        assert 'def javaFloatToIntegral (ty : IntType) (f : Fl) : Int' in self.SEM
        assert 'JLS §5.1.3' in self.SEM
        # NaN → 0, saturation, two-step narrowing, and the C non-claim, each a #guard
        for g in ('applyUnop .java "cast:i32" (.float (Fl.ofBits 0x7FF8000000000000)) with | .val (.int 0)',
                  'applyUnop .java "cast:i32" (.float (Fl.ofBits 0x46293E5939A08CEA)) with | .val (.int 2147483647)',
                  'applyUnop .java "cast:i8" (.float (Fl.ofBits 0x4072CE6666666666)) with | .val (.int 44)',
                  'applyUnop .cLike "cast:i32" (.float (Fl.ofBits 0x400F333333333333)) with'):
            assert g in self.SEM, g

    def test_java_collections_have_their_own_table(self):
        assert 'def javaMethodNames : List String' in self.STD
        assert 'theorem knowsMethod_java_complete' in self.STD
        assert '"IndexOutOfBoundsException"' in self.STD
        assert 'method_java_none' not in self.STD.replace('the `method_java_none` that', '')

    def test_exporter_lowers_throw_arrays_and_primitive_casts_for_java(self):
        assert 'case "THROW" if (jsLikeFile || javaFile) && kids.size == 1 =>' in self.EXP
        assert 'mfn == "<operator>.arrayInitializer" && javaFile' in self.EXP
        assert 'def javaCast(kids: List[AstNode]): ujson.Obj' in self.EXP
        for w in ('case "byte"  => Some("i8")', 'case "char"  => Some("u16")', 'case "long"  => Some("i64")'):
            assert w in self.EXP, w
        assert 'hole("op:cast:java-reference")' in self.EXP

class TestStrReprFormat:
    """`str()`, `repr()` and f-strings print what CPython prints, or hole by kind.

    The labels `op:stringExpressionList:non-literal-part` (the last three holes on
    cachetools), `op:formatString:conversion-or-spec` and `op:formatString:escape` stood
    for "Core cannot turn a value into text". `Stdlib.pyStr`/`pyRepr` can now, for every
    value whose spelling is a function of the value (int, bool, None, str, list, tuple,
    dict), and `fmtE` implements the exact subset of the Format Specification
    Mini-Language; the behavioural check is the `#guard` table in `Stdlib.lean`, taken
    from CPython 3.11 rather than from memory. These pin the shape in place.
    """

    STDLIB = (ROOT / 'Autoform/Lang/Core/Stdlib.lean').read_text()

    def test_the_three_names_are_one_table_consulted_first(self):
        assert 'def strBuiltin (name : String) (args : List Val) : Option EResult :=' in self.STDLIB
        assert '    match strBuiltin name args with\n    | some r => ok r' in self.STDLIB
        for name in ('"str", "repr", "format", "int"',):
            assert name in self.STDLIB          # `format` is a known free builtin
        assert '| "format"     => [.int 0, .str ">3"]' in self.STDLIB   # completeness witness

    def test_repr_follows_unicode_repr_and_refuses_non_ascii(self):
        assert "if cs.contains '\\'' && !cs.contains '\"' then '\"' else '\\''" in self.STDLIB
        assert 'if cs.any (fun c => c.toNat > 0x7f) then none else' in self.STDLIB
        assert '#guard pyRepr (.str "é") == none' in self.STDLIB

    def test_format_spec_subset_is_exact_and_everything_else_is_a_hole(self):
        # the spec grammar the parser recognises, and the refusals for what it does not
        assert "if c == '+' || c == '-' || c == ' ' || c == 'z' || c == '#' || c == '{' then none else" in self.STDLIB
        assert '#guard fmtHoles (fmtE (.int 42) "x") "format:spec:x"' in self.STDLIB
        # the documented defaults: numbers right, strings left, `0` means `=`+fill 0 for numbers only
        assert "let align := sp.align.getD (if sp.zero then '=' else '>')" in self.STDLIB
        assert "let align := sp.align.getD '<'" in self.STDLIB
        assert '#guard fmtIs (fmtE (.str "ab") "05") "ab000"' in self.STDLIB
        # object.__format__: non-empty spec on None/list/tuple/dict is a TypeError
        assert '| .unit | .list _ | .tuple _ | .dict _ => .exn (.str "TypeError")' in self.STDLIB

    def test_floats_hole_rather_than_approximate(self):
        assert '#guard pyStr (.float (Fl.ofBits 0x3FF8000000000000)) == none' in self.STDLIB
        assert '| .float _ => .hole "format:unprintable:float"' in self.STDLIB

    def test_exception_safety_is_a_theorem_not_a_convention(self):
        for name in ('theorem strE_ne_exn', 'theorem fmtE_excSafe', 'theorem strBuiltin_excSafe'):
            assert name in self.STDLIB, name
        assert 'exact strBuiltin_excSafe' in self.STDLIB

    def test_str_falls_back_to_repr_on_an_instance(self):
        sem = (ROOT / 'Autoform/Lang/Core/Semantics.lean').read_text()
        assert '| "str"  => match pick "__str__" with' in sem
        assert '| none   => pick "__repr__"' in sem
        # the pinned f-string residue is gone: CPython's answer, not a hole
        assert '/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.str "vx!") -/' in sem

    def test_exporter_reads_conversion_and_spec_off_the_field_text(self):
        src = EXPORTER.read_text()
        assert 'def fstringField(c: Call): Either[String, ujson.Obj]' in src
        assert 'if (rest.startsWith("=")) Left("debug-specifier")' in src
        assert 'case Some(cv) if cv != \'r\' && cv != \'s\' => Left("conversion-" + cv)' in src
        assert 'Right(ujson.Obj("k" -> "call", "f" -> "format",' in src
        # `!r` before the spec: format(repr(x), spec)
        assert 'case Some(\'r\') => ujson.Obj("k" -> "call", "f" -> "repr", "args" -> ujson.Arr(base))' in src

    def test_exporter_decodes_escapes_and_doubled_braces(self):
        src = EXPORTER.read_text()
        assert 'def pyDecodeEscapes(raw: String): Option[String]' in src
        assert 'pyDecodeEscapes(l.code.replace("{{", "{").replace("}}", "}"))' in src
        assert "case 'N'  => return None" in src            # \N{name} needs the Unicode database
        # plain literals decode too, raw ones do not
        assert 'if (prefix.toLowerCase.contains("r")) Some(body) else pyDecodeEscapes(body)' in src

    def test_adjacent_literals_with_an_fstring_part_concatenate(self):
        src = EXPORTER.read_text()
        assert 'case fc: Call if callName(fc) == "<operator>.formatString" => Some(fstring(kidsOf(fc)))' in src
        assert 'else hole("op:stringExpressionList:non-literal-part")' in src


class TestPreludesEverywhere:
    """Slice R4 (docs/languages.md §17.R4): supported effectful operand positions
    hoists into the enclosing prelude instead of holing as `expr:BLOCK-impure`, and the
    hoist keeps Python's left-to-right evaluation order (Language Reference §6.16) by
    completing every earlier non-literal operand into a temporary first. Behavioural
    check: `test_joern_native_numeric[python]` (`argOrder`, `kwHoist`, `ctorHoist`,
    `tupleHoist`, `inHoist`), CPython-compared; these pin the exporter side.
    """
    SRC = EXPORTER.read_text()

    def test_call_shaped_operands_include_computed_callees(self):
        assert 'val shapeOk = Set("call", "mcall", "alloc", "callV").contains(kind) &&' in self.SRC
        # callee/receiver first, then positionals, then keywords -- §6.3.4's order
        assert '// operands in evaluation order: callee/receiver, positionals, keywords' in self.SRC
        assert 'calleeV.foreach(f => out("f") = f)' in self.SRC
        assert 'recvNode.toList.map { r => val (pr, re) = exprV(r); (pr, re: ujson.Value, Some("<recv>")) }' in self.SRC
        assert 'case (v, Some("<keyword_dict>")) => ujson.Obj("k" -> "dstarred", "a" -> v): ujson.Value' in self.SRC
        assert 'case (v, Some(k))                => ujson.Obj("k" -> "kwargE", "n" -> k, "a" -> v): ujson.Value' in self.SRC

    def test_earlier_operands_are_completed_before_a_later_effect(self):
        # the order rule: everything before the LAST effectful operand is saved, literals excepted
        assert 'if (i < lastEffect && !isLit) {' in self.SRC
        assert 'val literalKinds = Set("int", "str", "bool", "float", "unit")' in self.SRC
        # the starred refusal survives: an expansion cannot be saved by saving its container
        assert '(Nil, hole("call:effect-after-starred"))' in self.SRC

    def test_displays_and_membership_thread_their_operands(self):
        assert 'def threadInOrder(ops: List[AstNode]): (List[ujson.Obj], List[ujson.Value])' in self.SRC
        assert '(pyFile && callName(c) == "<operator>.setLiteral")) && kidsOf(c).nonEmpty =>' in self.SRC
        assert 'Set("<operator>.in", "<operator>.notIn", "<operator>.is", "<operator>.isNot").contains(callName(c))' in self.SRC
        # nothing to hoist -> byte-identical to `expr`
        assert self.SRC.count('if (prelude.isEmpty) (Nil, expr(c))   // byte-identical when nothing hoists') == 2

    def test_statement_positions_hoist_only_what_always_runs(self):
        # assert: condition hoists, message stays lazy (§7.3 evaluates it only on failure)
        assert 'val (condPrelude, condV) = exprV(ks.head)' in self.SRC
        assert '"e" -> seqOf(messagePrelude :+ ujson.Obj("k" -> "raise"' in self.SRC
        # for-in iterable, del target, non-Python raise
        assert 'kidsOf(c).find(aidx(_) == -1).flatMap(asField).map { case (r, _) => exprV(r) }' in self.SRC
        assert 'val (prelude, vals) = threadInOrder(List(recv, idx))' in self.SRC
        assert 'seqOf(prelude :+ ujson.Obj("k" -> "raise", "e" -> v))' in self.SRC

    def test_lazy_positions_are_untouched(self):
        """`and`/`or` right operands and conditional branches already run their preludes
        only on the taken path (§6.11, §6.13); this slice must not have flattened them."""
        assert 'if (op == "&&" || op == "||") {' in self.SRC
        assert '"t" -> seqOf(tPrelude :+ ujson.Obj("k" -> "assign", "x" -> tmp, "e" -> tE)),' in self.SRC



class TestGoPointersOnInteriorPointerClauses:
    """Slice R8: Go pointers ride the C interior-pointer machinery. The one Go-specific fact
    the exporter needed is the SPELLING of a pointer type -- Go's star comes first
    (spec "Pointer types": `PointerType = "*" BaseType`) -- because every downstream rule
    (`addrKind`, `pointerStructFieldOperand`, `castTargetIsPointer`) asks `isPointerType`.
    The Core side is pinned by the `goPtrProg` `#guard`s in `Semantics.lean`, whose expected
    values are `go run`'s."""

    EXP = (Path(__file__).resolve().parents[1] / 'cartographer/export_ast.sc').read_text()
    SEM = (Path(__file__).resolve().parents[1] / 'Autoform/Lang/Core/Semantics.lean').read_text()

    def test_go_pointer_types_are_star_prefixed(self):
        assert 'val go = currentFile.toLowerCase.endsWith(".go")' in self.EXP
        assert 'b.endsWith("*") || (go && b.startsWith("*"))' in self.EXP
        assert 'spec "Pointer types"' in self.EXP

    def test_core_delivers_go_pointer_semantics_on_the_c_clauses(self):
        assert 'private def goPtrProg : Program :=' in self.SEM
        assert '{ dialect := .go' in self.SEM.split('private def goPtrProg', 1)[1][:200]
        for g, v in (('ptrLocal', 5), ('ptrField', 11), ('ptrIndex', 14), ('ptrAlias', 3)):
            assert f'#guard match runFunc goPtrProg 300 "{g}" [] with | .val (.int {v})' in self.SEM, g
        assert 'Spec, "Address operators"' in self.SEM and 'Spec, "Selectors"' in self.SEM
