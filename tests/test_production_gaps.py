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
        assert 'ujson.Obj("k" -> "delIndex", "a" -> expr(recv), "i" -> expr(idx))' in src
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
        assert 'genExpEager = genExpConsumers.contains(c.name)' in src
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
        assert fm.count('Ctx.dunderOn_resolves hd') == 4
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
        assert 'case "THROW" if jsLikeFile && kids.size == 1 =>' in src
        assert 'case "THROW" if jsLikeFile => holeS("control:THROW:shape")' in src
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
