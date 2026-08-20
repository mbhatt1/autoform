"""The JSON contract between `cartographer/export_ast.sc` (Scala) and the Python side.

The Scala exporter belongs to another workstream; this file does not test it. It tests
the *contract*: every committed `ast-*.json` must be something `render_lean.py` can turn
into Lean without inventing anything, and the facts the exporter promises about literals,
holes and varargs must hold on the artifacts that are actually in the tree.

Every test here fails loudly when there is nothing to inspect. "No AST files found" is
not a pass.
"""
from __future__ import annotations

import glob
import json
import os
import re

import pytest

from conftest import ROOT

AST_GLOB = os.path.join(ROOT, "ast-*.json")


def ast_paths():
    return sorted(glob.glob(AST_GLOB))


@pytest.fixture(scope="module")
def corpora():
    paths = ast_paths()
    if not paths:
        pytest.fail("no ast-*.json in %s — this suite inspected nothing, which is a "
                    "failure, not a pass. Re-run the exporter or point ROOT at the "
                    "repository." % ROOT)
    return {os.path.basename(p): json.load(open(p)) for p in paths}


def walk(node):
    if isinstance(node, dict):
        yield node
        for v in node.values():
            yield from walk(v)
    elif isinstance(node, list):
        for v in node:
            yield from walk(v)


# ---------------------------------------------------------------------------

class TestTopLevelShape:
    def test_each_ast_is_a_list_of_functions(self, corpora):
        for name, funcs in corpora.items():
            assert isinstance(funcs, list) and funcs, name

    def test_required_fields(self, corpora):
        for name, funcs in corpora.items():
            for f in funcs:
                assert isinstance(f.get("name"), str) and f["name"], name
                assert isinstance(f.get("file"), str), (name, f.get("name"))
                assert isinstance(f.get("params"), list), (name, f["name"])
                assert all(isinstance(p, str) for p in f["params"]), (name, f["name"])
                assert isinstance(f.get("body"), dict), (name, f["name"])

    def test_every_corpus_can_infer_a_dialect(self, corpora, render_lean):
        """An extension the renderer cannot map is a hard stop at render time (by
        design — defaulting gave a `.tsx` file Python's floored division). Catch it at
        the artifact instead of at the next render."""
        for name, funcs in corpora.items():
            try:
                d = render_lean.infer_dialect(funcs)
            except SystemExit as e:
                pytest.fail("%s: %s" % (name, e))
            assert d in (".python", ".cLike"), (name, d)

    @pytest.mark.xfail(strict=True, reason=(
        "KNOWN GAP, reported not hidden: `.cc` is absent from render_lean.DIALECT. "
        "ast-V8Numbers.json is 104 `.cc` files and 53 `.h` files, so the dialect is "
        "decided today by the *headers* alone — the .cc votes are silently discarded. "
        "It happens to come out `.cLike` either way, but a corpus of pure `.cc` would "
        "abort the render. Add `.cc`/`.cxx`/`.hpp`/`.hh` to DIALECT and delete this "
        "xfail (which is strict: it fails the moment the gap is closed)."))
    def test_all_extensions_present_in_the_dialect_table(self, corpora, render_lean):
        for name, funcs in corpora.items():
            exts = {os.path.splitext(f.get("file", ""))[1] for f in funcs}
            unknown = {e for e in exts if e and e not in render_lean.DIALECT}
            assert not unknown, "%s: %s" % (name, sorted(unknown))


class TestLiteralContract:
    def test_ints_are_exact(self, corpora):
        """`v` is a JSON number when |v| <= 2^53 and a decimal *string* beyond it.
        A number past 2^53 means the exporter let a double round the value."""
        seen = 0
        for name, funcs in corpora.items():
            for n in walk(funcs):
                if n.get("k") != "int":
                    continue
                seen += 1
                v = n["v"]
                assert isinstance(v, (int, str)) and not isinstance(v, bool), (name, v)
                if isinstance(v, int):
                    assert abs(v) <= 2 ** 53, (
                        "%s: integer %d is past 2^53 and was carried as a JSON number, "
                        "which is a double — emit it as a string" % (name, v))
                else:
                    assert re.fullmatch(r"-?\d+", v), (name, v)
        assert seen > 0, "no integer literals in any corpus — nothing was checked"

    @pytest.mark.xfail(strict=True, reason=(
        "KNOWN GAP, reported not hidden: the exporter promises `k:int` carries a JSON "
        "number up to 2^53 and a decimal *string* beyond it, but ast-V8Numbers.json "
        "encodes 218 small integers as strings (92 of them plain \"0\"). Nothing is "
        "lost — render_lean.lean_int accepts both and emits the same Lean — but the "
        "artifact is non-canonical, so a byte comparison of two ASTs of the same code "
        "can differ for no semantic reason. Strict xfail: it fails once fixed."))
    def test_int_encoding_is_canonical(self, corpora):
        for name, funcs in corpora.items():
            for n in walk(funcs):
                if n.get("k") == "int" and isinstance(n["v"], str):
                    assert abs(int(n["v"])) > 2 ** 53, (
                        "%s: %s is small enough to be a JSON number" % (name, n["v"]))

    def test_big_ints_render_without_loss(self, corpora, render_lean):
        bigs = [n["v"] for fs in corpora.values() for n in walk(fs)
                if n.get("k") == "int" and isinstance(n["v"], str)]
        for v in bigs:
            assert render_lean.lean_int(v).strip("()") == v.lstrip("-")

    def test_hex_and_suffixed_literals_did_not_become_holes(self, corpora):
        """`0xFFFFFFFF`, `1ULL`, `0b10000`, `0x0010'0000'0000'0000` all used to fall
        through to a `lit:unquoted` hole. If a C-family corpus is present, its
        unquoted-literal holes must not be dominated by plain integers."""
        offenders = []
        for name, funcs in corpora.items():
            for n in walk(funcs):
                if n.get("k") in ("hole", "holeS") and n.get("label") == "lit:unquoted":
                    offenders.append(name)
        # `lit:unquoted` is legitimate for things Core genuinely cannot model (chars,
        # user-defined literals). What must not happen is the count exploding: pin it.
        counts = {k: offenders.count(k) for k in set(offenders)}
        for name, c in counts.items():
            total = sum(1 for _ in walk(corpora[name]))
            assert c < total * 0.02, (
                "%s: %d `lit:unquoted` holes out of %d nodes — the integer-literal "
                "parser has regressed" % (name, c, total))

    def test_bool_literals_are_real_bools(self, corpora):
        for name, funcs in corpora.items():
            for n in walk(funcs):
                if n.get("k") == "bool":
                    assert isinstance(n["v"], bool), name

    def test_string_literals_are_strings(self, corpora):
        for name, funcs in corpora.items():
            for n in walk(funcs):
                if n.get("k") == "str":
                    assert isinstance(n["v"], str), name


class TestHoleContract:
    """A hole is the honest form of "not translated". An *unlabelled* hole is not:
    it makes the gap uncountable, and every downstream ledger counts by label."""

    def test_every_hole_carries_a_nonempty_label(self, corpora):
        seen = 0
        for name, funcs in corpora.items():
            for n in walk(funcs):
                if n.get("k") in ("hole", "holeS"):
                    seen += 1
                    assert isinstance(n.get("label"), str) and n["label"].strip(), name
        assert seen > 0, "no holes anywhere — either 100% translation or a broken walk"

    def test_labels_are_namespaced(self, corpora):
        """`<family>:<detail>` so a ledger can group them. A bare word means somebody
        added a hole without deciding what family it belongs to."""
        bad = set()
        for funcs in corpora.values():
            for n in walk(funcs):
                if n.get("k") in ("hole", "holeS"):
                    if not re.fullmatch(r"[A-Za-z][\w.-]*(:[\w.<>+-]+)+", n["label"]):
                        bad.add(n["label"])
        assert not bad, sorted(bad)

    def test_import_holes_use_the_documented_vocabulary(self, corpora):
        """The import resolver has exactly two honest outcomes it can report as a hole:
        a module *value* it refuses to invent, and a name it could not resolve. A third
        label means somebody widened the resolver without saying so."""
        allowed = {"import:module-value", "import:unresolved"}
        seen = set()
        for funcs in corpora.values():
            for n in walk(funcs):
                lab = n.get("label")
                if isinstance(lab, str) and lab.startswith("import:"):
                    seen.add(lab)
        assert seen <= allowed, sorted(seen - allowed)

    def test_a_resolved_import_is_a_reference_not_a_hole(self, corpora):
        """`from ._cached import _wrapper` names a function of this program; it must
        come out as `fnref`/`closure`. If a Python corpus is present and *every* import
        is a hole, the resolver has stopped resolving."""
        py = {k: v for k, v in corpora.items()
              if any(f.get("file", "").endswith(".py") for f in v)}
        if not py:
            pytest.skip("no Python corpus in the tree")
        refs = sum(1 for fs in py.values() for n in walk(fs)
                   if n.get("k") in ("fnref", "closure"))
        assert refs > 0, ("every import in every Python corpus is a hole; the resolver "
                          "resolved nothing")


class TestRenderability:
    """The strongest contract statement available without running Lean: every node in
    every committed AST is one `render_lean.py` knows how to print."""

    def test_every_node_has_a_shape(self, corpora, render_lean):
        checked = 0
        for name, funcs in corpora.items():
            for f in funcs:
                self._walk_stmt(render_lean, f["body"], name, f["name"])
                checked += 1
        assert checked > 0

    @classmethod
    def _walk_stmt(cls, rl, n, corpus, fname):
        try:
            _, kids = rl.stmt_shape(n)
        except ValueError as e:
            pytest.fail("%s / %s: %s" % (corpus, fname, e))
        cls._kids(rl, kids, corpus, fname)

    @classmethod
    def _walk_expr(cls, rl, n, corpus, fname):
        try:
            _, kids = rl.expr_shape(n)
        except ValueError as e:
            pytest.fail("%s / %s: %s" % (corpus, fname, e))
        cls._kids(rl, kids, corpus, fname)

    @classmethod
    def _kids(cls, rl, kids, corpus, fname):
        for tag, val in kids:
            if tag == "e":
                cls._walk_expr(rl, val, corpus, fname)
            elif tag == "s":
                cls._walk_stmt(rl, val, corpus, fname)
            elif tag == "es":
                for x in val or []:
                    cls._walk_expr(rl, x, corpus, fname)
            elif tag == "ps":
                for p in val or []:
                    assert isinstance(p, list) and len(p) == 2, (corpus, fname)
                    for x in p:
                        cls._walk_expr(rl, x, corpus, fname)

    def test_class_bases_are_modelled(self, corpora, render_lean):
        base_ctor = {"tuple", "list", "dict", "str"}
        for name, funcs in corpora.items():
            for f in funcs:
                for cls, base in (f.get("classBases") or {}).items():
                    assert base in base_ctor, "%s: %s(%s)" % (name, cls, base)
