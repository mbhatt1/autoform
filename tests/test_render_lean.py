"""cartographer/render_lean.py — the printer everything downstream is a claim about.

If this file is wrong, every proof in the repo is a proof about a program nobody wrote.
Its three load-bearing invariants: total parenthesisation, determinism, and linear
output size.
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys

import pytest

from conftest import CARTO, fn, run_script, seq_chain, write_ast

RENDER = os.path.join(CARTO, "render_lean.py")


# ---------------------------------------------------------------------------
# literals
# ---------------------------------------------------------------------------

class TestLeanLiterals:
    def test_negative_ints_are_parenthesised(self, render_lean):
        assert render_lean.lean_int(-7) == "(-7)"
        assert render_lean.lean_int(0) == "0"
        assert render_lean.lean_int(7) == "7"

    def test_big_ints_arrive_as_decimal_strings(self, render_lean):
        """The exporter emits anything past 2^53 as a *string*, because a JSON number
        is a double and 0xFFFFFFFFFFFFFFFF would round. The renderer must accept it and
        must not lose a digit."""
        big = str(2 ** 64 - 1)
        assert render_lean.lean_int(big) == big
        assert render_lean.lean_int(str(-(2 ** 64))) == "(-%d)" % (2 ** 64)

    def test_a_big_int_survives_the_whole_pipeline(self, tmp_path, render_lean):
        big = 0xFFFFFFFFFFFFFFFF
        ast = str(tmp_path / "ast-Big.json")
        write_ast(ast, [fn(body={"k": "ret", "e": {"k": "int", "v": str(big)}})])
        out = str(tmp_path / "Big.lean")
        rc, log = run_script(RENDER, ast, out, "Big")
        assert rc == 0, log
        text = open(out).read()
        assert str(big) in text
        # a double round-trip would have produced 18446744073709551616
        assert "18446744073709551616" not in text

    @pytest.mark.parametrize("raw,want", [
        ("plain", '"plain"'),
        ('say "hi"', '"say \\"hi\\""'),
        ("back\\slash", '"back\\\\slash"'),
        ("line\nfeed", '"line\\nfeed"'),
        ("tab\there", '"tab\\there"'),
        ("\r", '"\\r"'),
        ("\x00", '"\\x00"'),
        ("\x7f", '"\\x7f"'),
        ("\x85", '"\\u0085"'),        # C1 control
        ("﻿", '"\\ufeff"'),      # BOM
        (" ", '"\\u2028"'),      # line separator
        ("é", '"é"'),                 # printable non-ASCII passes through
    ])
    def test_string_escaping(self, render_lean, raw, want):
        assert render_lean.lean_str(raw) == want

    def test_lone_surrogates_are_escaped_not_written_raw(self, render_lean):
        got = render_lean.lean_str("a\ud800b")
        assert got == '"a\\ud800b"'
        got.encode("utf-8")           # must not raise: the file has to be writable

    def test_bools(self, render_lean):
        assert render_lean.lean_bool(True) == "true"
        assert render_lean.lean_bool(False) == "false"


# ---------------------------------------------------------------------------
# parenthesisation
# ---------------------------------------------------------------------------

class TestParenthesisation:
    def test_non_nullary_nodes_are_always_wrapped(self, render_lean):
        """`.ret .name "a"` parses as Stmt.ret applied to three arguments."""
        s = render_lean.stmt({"k": "ret", "e": {"k": "name", "v": "a"}})
        assert s == '(.ret (.name "a"))'

    def test_nullary_constructors_are_bare(self, render_lean):
        assert render_lean.stmt({"k": "skip"}) == ".skip"
        assert render_lean.stmt({"k": "brk"}) == ".brk"
        assert render_lean.expr({"k": "unit"}) == "(.lit .unit)"

    def test_every_wrapped_output_balances(self, render_lean):
        node = {"k": "ifte", "c": {"k": "binop", "op": "<",
                                   "a": {"k": "name", "v": "i"},
                                   "b": {"k": "int", "v": -3}},
                "t": {"k": "ret", "e": {"k": "call", "f": "g",
                                        "args": [{"k": "name", "v": "i"}]}},
                "e": {"k": "skip"}}
        for text in (render_lean.stmt(node), render_lean.render(node, "s", 0)):
            assert text.count("(") == text.count(")")
            assert text.count("[") == text.count("]")

    def test_wrapped_and_flat_forms_agree_modulo_whitespace(self, render_lean):
        """Layout is cosmetic: the wrapped render must denote the same term."""
        node = seq_chain(60, lambda i: {"k": "assign", "x": "variable_%d" % i,
                                        "e": {"k": "str", "v": "x" * 20}})
        flat = re.sub(r"\s+", " ", render_lean.stmt(node))
        wrapped = re.sub(r"\s+", " ", render_lean.render(node, "s", 0))
        assert flat == wrapped


# ---------------------------------------------------------------------------
# error surface — an unknown node must never render as something plausible
# ---------------------------------------------------------------------------

class TestRendererRefuses:
    def test_unknown_expr_kind(self, render_lean):
        with pytest.raises(ValueError, match="unknown expr node kind"):
            render_lean.expr({"k": "quasiquote"})

    def test_unknown_stmt_kind(self, render_lean):
        with pytest.raises(ValueError, match="unknown stmt node kind"):
            render_lean.stmt({"k": "goto"})

    def test_missing_required_field(self, render_lean):
        with pytest.raises(ValueError, match="missing required field"):
            render_lean.expr({"k": "binop", "op": "+", "a": {"k": "int", "v": 1}})

    def test_non_object_node(self, render_lean):
        with pytest.raises(ValueError, match="not an object"):
            render_lean.expr("a")

    def test_unknown_extension_is_refused_not_defaulted(self, tmp_path):
        """Defaulting to Python's floored division for a `.tsx` file gave `-7 % 3 = 2`
        where TypeScript gives -1. An unknown extension is an error."""
        ast = str(tmp_path / "ast-X.json")
        write_ast(ast, [fn(file="a.tsx")])
        rc, log = run_script(RENDER, ast, str(tmp_path / "X.lean"), "X")
        assert rc != 0
        assert "cannot infer dialect" in log
        assert ".tsx" in log

    @pytest.mark.parametrize("ext,dialect", [
        (".py", ".python"), (".c", ".cLike"), (".cpp", ".cLike"),
        (".java", ".cLike"), (".ts", ".cLike"), (".go", ".cLike"),
    ])
    def test_dialect_inference(self, render_lean, ext, dialect):
        assert render_lean.infer_dialect([fn(file="a" + ext)]) == dialect

    def test_dialect_is_a_majority_vote_not_a_first_hit(self, render_lean):
        funcs = [fn(file="a.c")] * 3 + [fn(file="b.py")]
        assert render_lean.infer_dialect(funcs) == ".cLike"

    def test_unmodelled_builtin_base_is_refused(self, tmp_path):
        ast = str(tmp_path / "ast-B.json")
        write_ast(ast, [fn(classBases={"C": "set"})])
        rc, log = run_script(RENDER, ast, str(tmp_path / "B.lean"), "B")
        assert rc != 0
        assert "unmodelled builtin base" in log

    def test_conflicting_class_bases_are_dropped_not_guessed(self, tmp_path):
        ast = str(tmp_path / "ast-C.json")
        write_ast(ast, [fn(name="a.py:<module>", classBases={"C": "tuple"}),
                        fn(name="b.py:<module>", file="b.py",
                           classBases={"C": "list"})])
        out = str(tmp_path / "C.lean")
        rc, log = run_script(RENDER, ast, out, "C")
        assert rc == 0, log
        assert "builtinBases" not in open(out).read()


# ---------------------------------------------------------------------------
# identifiers
# ---------------------------------------------------------------------------

class TestIdent:
    def test_sanitises_and_prefixes(self, render_lean):
        assert render_lean.ident("pkg/mod.py:<module>.C.f") == \
            "f_pkg_mod_py__module__C_f"

    def test_bounded_length(self, render_lean):
        assert len(render_lean.ident("x" * 500)) == 120

    def test_collisions_are_disambiguated_in_the_module(self, tmp_path):
        """Two distinct source functions must not collapse onto one Lean name."""
        ast = str(tmp_path / "ast-D.json")
        write_ast(ast, [fn(name="a.py:f"), fn(name="a-py:f")])
        out = str(tmp_path / "D.lean")
        rc, log = run_script(RENDER, ast, out, "D")
        assert rc == 0, log
        defs = re.findall(r"^def (f_\S+) : Func", open(out).read(), re.M)
        assert len(defs) == 2 and len(set(defs)) == 2


# ---------------------------------------------------------------------------
# determinism and linearity
# ---------------------------------------------------------------------------

def _ast(tmp_path, n_funcs=20, depth=40):
    p = str(tmp_path / "ast-M.json")
    write_ast(p, [fn(name="a.py:f%d" % i, params=["p", "q"],
                     body=seq_chain(depth)) for i in range(n_funcs)])
    return p


class TestDeterminism:
    def test_two_renders_are_byte_identical(self, tmp_path):
        ast = _ast(tmp_path)
        a, b = str(tmp_path / "A.lean"), str(tmp_path / "B.lean")
        assert run_script(RENDER, ast, a, "M")[0] == 0
        assert run_script(RENDER, ast, b, "M")[0] == 0
        assert open(a).read() == open(b).read()

    def test_determinism_survives_hash_randomisation(self, tmp_path):
        """Dict iteration order must not reach the output."""
        ast = _ast(tmp_path)
        outs = []
        for seed in ("0", "1", "12345"):
            env = dict(os.environ, PYTHONHASHSEED=seed)
            dst = str(tmp_path / ("H%s.lean" % seed))
            r = subprocess.run([sys.executable, RENDER, ast, dst, "M"],
                               capture_output=True, text=True, env=env, timeout=600)
            assert r.returncode == 0, r.stderr
            outs.append(open(dst).read())
        assert outs[0] == outs[1] == outs[2]

    def test_no_timestamp_or_path_leaks_into_the_output(self, tmp_path):
        ast = _ast(tmp_path, n_funcs=2, depth=3)
        dst = str(tmp_path / "M.lean")
        assert run_script(RENDER, ast, dst, "M")[0] == 0
        text = open(dst).read()
        assert str(tmp_path) not in text
        assert not re.search(r"\b(19|20)\d\d-\d\d-\d\d\b", text)


class TestLinearity:
    """A right-nested chain of n statements used to indent 2n spaces at its deepest
    line — O(n^2) characters of whitespace. 2000 statements made a 20 MB module.
    `MAX_INDENT` caps the staircase; this pins that the size stays linear."""

    def _size(self, tmp_path, n, tag):
        ast = str(tmp_path / ("ast-L%s.json" % tag))
        write_ast(ast, [fn(body=seq_chain(n))])
        dst = str(tmp_path / ("L%s.lean" % tag))
        rc, log = run_script(RENDER, ast, dst, "L")
        assert rc == 0, log
        return os.path.getsize(dst)

    def test_output_size_is_linear_in_statement_count(self, tmp_path):
        s1 = self._size(tmp_path, 500, "a")
        s2 = self._size(tmp_path, 2000, "b")
        # quadratic growth would be ~16x; linear is ~4x. Allow generous slack.
        assert s2 < s1 * 6, "output grew %.1fx for 4x the input" % (s2 / s1)

    def test_indentation_never_exceeds_the_cap(self, tmp_path, render_lean):
        ast = str(tmp_path / "ast-Ind.json")
        write_ast(ast, [fn(body=seq_chain(600))])
        dst = str(tmp_path / "Ind.lean")
        assert run_script(RENDER, ast, dst, "Ind")[0] == 0
        worst = max(len(l) - len(l.lstrip(" ")) for l in open(dst))
        assert worst <= render_lean.MAX_INDENT + 4, worst

    def test_render_time_is_not_quadratic(self, tmp_path):
        """`flat()` used to be recomputed over the whole subtree at every level:
        250 statements took 0.33 s, 2000 took 42 s, 5000 never finished."""
        import time
        t0 = time.time(); self._size(tmp_path, 4000, "t"); dt = time.time() - t0
        assert dt < 60, "4000 statements took %.1fs" % dt


# ---------------------------------------------------------------------------
# module scaffolding
# ---------------------------------------------------------------------------

class TestModuleShape:
    def test_maxrecdepth_scales_with_function_count(self, tmp_path):
        """8000 was not enough: the `funcs := [...]` literal elaborates as nested cons
        cells, one frame per function, and Ansible has 5,546."""
        ast = str(tmp_path / "ast-N.json")
        write_ast(ast, [fn(name="a.py:f%d" % i) for i in range(3000)])
        dst = str(tmp_path / "N.lean")
        assert run_script(RENDER, ast, dst, "N")[0] == 0
        m = re.search(r"set_option maxRecDepth (\d+)", open(dst).read())
        assert m and int(m.group(1)) >= 8 * 3000

    def test_module_initializers_are_collected(self, tmp_path):
        ast = str(tmp_path / "ast-I.json")
        write_ast(ast, [fn(name="a.py:<module>"), fn(name="a.py:<module>.g"),
                        fn(name="b.py:<global>", file="b.py")])
        dst = str(tmp_path / "I.lean")
        assert run_script(RENDER, ast, dst, "I")[0] == 0
        line = [l for l in open(dst) if l.startswith("def moduleInits")][0]
        assert line.count("f_") == 2

    def test_varargs_appear_only_when_recorded(self, tmp_path):
        ast = str(tmp_path / "ast-V.json")
        write_ast(ast, [fn(name="a.py:f", params=["a"], vararg="args"),
                        fn(name="a.py:g", params=["a"])])
        dst = str(tmp_path / "V.lean")
        assert run_script(RENDER, ast, dst, "V")[0] == 0
        text = open(dst).read()
        assert 'vararg := some "args"' in text
        assert text.count("vararg") == 1
        assert "kwarg" not in text
