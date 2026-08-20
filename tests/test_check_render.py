"""scripts/check_render.py — is the committed Lean module a render of the committed AST?

This is the only check in the repo that can catch a mutant that reached git, or a module
and an AST that drifted apart. It must be right in *both* directions: it has to pass on a
faithful render and fail on every way the two can disagree.

Each test builds a throwaway repo containing real copies of `check_render.py` and
`render_lean.py`, so it exercises the shipped code rather than a stub.
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys

import pytest

from conftest import fn, make_repo, run_script, seq_chain, write_ast


def check(repo, *mods):
    return run_script(os.path.join(repo, "scripts", "check_render.py"), *mods, cwd=repo)


FUNCS = [
    fn(name="c.py:<module>._DefaultSize.__getitem__", params=["self", "key"],
       body={"k": "ret", "e": {"k": "int", "v": 1}}),
    fn(name="c.py:<module>.f", params=["a"],
       body={"k": "seq",
             "a": {"k": "assign", "x": "b", "e": {"k": "name", "v": "a"}},
             "b": {"k": "ret", "e": {"k": "name", "v": "b"}}}),
]


class TestAgreement:
    def test_a_faithful_render_passes(self, tmp_path):
        repo, _, _ = make_repo(tmp_path, "Cachetools", FUNCS)
        rc, out = check(repo)
        assert rc == 0, out
        assert "1 module(s) match" in out

    def test_it_actually_compared_something(self, tmp_path):
        """A pass must name a module. `check_render: 0 module(s) match` is the silence
        this repo keeps mistaking for success."""
        repo, _, _ = make_repo(tmp_path, "Cachetools", FUNCS)
        rc, out = check(repo)
        assert rc == 0
        assert "0 module(s)" not in out


class TestDisagreement:
    def test_the_mutant_that_reached_git(self, tmp_path):
        """`_DefaultSize.__getitem__` returned 0 where the AST says `int 1`. It survived
        four commits and every proof about it still passed."""
        repo, _, gen = make_repo(tmp_path, "Cachetools", FUNCS)
        text = open(gen).read()
        mutated = text.replace("(.lit (.int 1))", "(.lit (.int 0))", 1)
        assert mutated != text, "the fixture no longer contains the mutated literal"
        open(gen, "w").write(mutated)
        rc, out = check(repo)
        assert rc == 1, out
        assert "is NOT a render of" in out
        assert ".int 0" in out          # the diff must show what changed

    def test_a_module_with_extra_functions(self, tmp_path):
        """238 functions against 208: two pipelines, two ASTs."""
        repo, ast, gen = make_repo(tmp_path, "M", FUNCS)
        write_ast(ast, FUNCS[:1])       # AST shrinks, module does not
        rc, out = check(repo)
        assert rc == 1, out
        assert "differing lines" in out

    def test_whitespace_only_edits_are_caught(self, tmp_path):
        """The module is generated; a hand edit of any kind means it is not the render."""
        repo, _, gen = make_repo(tmp_path, "M", FUNCS)
        open(gen, "a").write("\n-- touched by hand\n")
        rc, out = check(repo)
        assert rc == 1, out

    def test_the_diff_is_bounded(self, tmp_path):
        """A wholly different module must not print a million lines."""
        repo, _, gen = make_repo(tmp_path, "M", FUNCS)
        open(gen, "w").write("\n".join("-- line %d" % i for i in range(5000)))
        rc, out = check(repo)
        assert rc == 1
        assert "more differing lines" in out
        assert len(out.splitlines()) < 60


class TestNothingToCheckIsNotAPass:
    def test_no_modules_at_all_exits_2(self, tmp_path):
        repo, ast, gen = make_repo(tmp_path, "M", FUNCS)
        os.remove(ast)
        os.remove(gen)
        rc, out = check(repo)
        assert rc == 2, out
        assert "no module has both" in out
        assert "match" not in out.replace("no module", "")

    def test_a_module_without_an_ast_is_not_silently_skipped(self, tmp_path):
        """A generated module with no AST is unverifiable. The default sweep can only
        find modules that have both, so an explicit request must fail loudly."""
        repo, ast, gen = make_repo(tmp_path, "M", FUNCS)
        os.remove(ast)
        rc, out = check(repo, "M")
        assert rc != 0, out
        assert "0 module" not in out

    def test_a_render_failure_is_reported_not_swallowed(self, tmp_path):
        repo, ast, gen = make_repo(tmp_path, "M", FUNCS)
        write_ast(ast, [fn(body={"k": "teleport"})])
        rc, out = check(repo)
        assert rc == 1, out
        assert "render failed" in out


class TestRoundTrip:
    def test_render_then_check_holds_for_deep_and_wide_inputs(self, tmp_path):
        funcs = [fn(name="a.py:f%d" % i, params=["x"], body=seq_chain(80))
                 for i in range(30)]
        repo, _, _ = make_repo(tmp_path, "Big", funcs)
        rc, out = check(repo)
        assert rc == 0, out

    def test_unicode_and_control_characters_round_trip(self, tmp_path):
        funcs = [fn(name="a.py:f", body={"k": "ret", "e": {
            "k": "str", "v": "héllo\t\x01  \"quoted\" \\ end"}})]
        repo, _, _ = make_repo(tmp_path, "U", funcs)
        rc, out = check(repo)
        assert rc == 0, out
