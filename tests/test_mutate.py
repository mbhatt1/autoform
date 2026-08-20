"""scripts/mutate.py beyond the diagnostic regex.

A mutation gate is only evidence if three things hold: the mutants it generates are real
behavioural perturbations, they are attributed to the right declaration, and a build
failure it cannot attribute is *not* quietly scored as a kill. All three have been wrong
here at some point.
"""
from __future__ import annotations

import re

import pytest


# ---------------------------------------------------------------------------
# declaration map
# ---------------------------------------------------------------------------

SRC = """\
import Foo

namespace X

/-- doc -/
def size (n : Nat) : Nat :=
  if n < 3 then n + 1 else 0

@[simp]
private theorem size_pos (n : Nat) : 0 < size n + 1 := by
  simp [size]

inductive Colour
  | red
  | green

abbrev Two : Nat := 2

instance : Inhabited Nat := ⟨0⟩

lemma two_eq : Two = 2 := rfl

end X
"""


@pytest.fixture
def lines():
    return SRC.splitlines(keepends=True)


class TestDeclParsing:
    def test_kinds_and_names(self, mutate, lines):
        got = [(d.kind, d.name) for d in mutate.parse_decls(lines)]
        assert ("def", "size") in got
        assert ("theorem", "size_pos") in got
        assert ("inductive", "Colour") in got
        assert ("abbrev", "Two") in got
        assert ("lemma", "two_eq") in got
        assert any(k == "instance" for k, _ in got)

    def test_ranges_are_contiguous_and_cover_the_file(self, mutate, lines):
        ds = mutate.parse_decls(lines)
        for a, b in zip(ds, ds[1:]):
            assert a.end == b.start - 1
        assert ds[-1].end == len(lines)

    def test_decl_at_attributes_a_body_line(self, mutate, lines):
        i = next(i for i, l in enumerate(lines, 1) if "if n < 3" in l)
        assert mutate.decl_at(mutate.parse_decls(lines), i).name == "size"

    def test_an_inductive_is_not_misattributed_to_the_previous_def(self, mutate, lines):
        i = next(i for i, l in enumerate(lines, 1) if "| green" in l)
        d = mutate.decl_at(mutate.parse_decls(lines), i)
        assert d.name == "Colour" and d.kind == "inductive"

    def test_specification_kinds_are_not_implementation_kinds(self, mutate):
        """Mutating an `inductive` mutates the thing the theorem is stated against,
        which proves nothing. Keep the three sets disjoint."""
        assert not mutate.DEF_KINDS & mutate.SPEC_KINDS
        assert not mutate.DEF_KINDS & mutate.THEOREM_KINDS
        assert not mutate.THEOREM_KINDS & mutate.SPEC_KINDS


class TestHandWrittenMutants:
    def _ops(self, mutate, lines):
        decls = mutate.parse_decls(lines)
        return {m.op for m in mutate.gen_mutants(lines, decls)}

    def test_theorems_are_never_mutated(self, mutate, lines):
        decls = mutate.parse_decls(lines)
        thms = {d.name for d in decls if d.kind in mutate.THEOREM_KINDS}
        for m in mutate.gen_mutants(lines, decls):
            assert m.decl not in thms, m.diff

    def test_arithmetic_comparison_and_offbyone_operators_fire(self, mutate, lines):
        ops = self._ops(mutate, lines)
        assert any(o.startswith("arith:") for o in ops)
        assert any(o.startswith("cmp:") for o in ops)
        assert any(o.startswith("offbyone:") for o in ops)

    def test_every_mutant_changes_its_line(self, mutate, lines):
        for m in mutate.gen_mutants(lines, mutate.parse_decls(lines)):
            assert m.new != m.old

    def test_identifiers_are_not_rewritten_by_a_token_swap(self, mutate):
        """`_token_mutations` uses space discipline so `a+b` inside a name survives."""
        src = ["def plus_minus : Nat := 1\n"]
        got = mutate.gen_mutants(src, mutate.parse_decls(src))
        assert all("plus_minus" in m.new for m in got)

    def test_negative_literals_are_not_generated(self, mutate):
        src = ["def z : Nat := 0\n"]
        for m in mutate.gen_mutants(src, mutate.parse_decls(src)):
            assert "-1" not in m.new


GENERATED = """\
/-- `f` -/
def f_f : Func :=
  { name := "a.py:f"
  , params := ["self", "key"]
  , body := (.seq
      (.assign "x" (.binop "+" (.name "self") (.int 1)))
      (.seq
        (.expr (.mcall (.name "x") "put" []))
        (.ret (.field (.name "self") "data")))) }
"""


class TestGeneratedMutants:
    @pytest.fixture
    def gen(self, mutate):
        lines = GENERATED.splitlines(keepends=True)
        return mutate.gen_mutants_generated(lines, mutate.parse_decls(lines))

    def test_the_embedded_program_is_what_gets_perturbed(self, gen):
        ops = {m.op.split(":")[0] for m in gen}
        for want in ("ast-binop", "ast-int", "ast-ret->expr", "ast-expr->ret",
                     "ast-name", "ast-assign", "ast-field", "ast-seq-delete"):
            assert want in ops, sorted(ops)

    def test_binop_swaps_stay_inside_their_equivalence_class(self, mutate):
        arith, cmp_, bool_ = set("+-*/%"), {"<", "<=", ">", ">="}, {"&&", "||"}
        for a, b in mutate.AST_BINOP_SWAPS.items():
            for cls in (arith, cmp_, bool_, {"==", "!="}):
                if a in cls:
                    assert b in cls, (a, b)
                    break

    def test_every_mutant_names_the_declaration_it_touched(self, gen):
        assert gen and all(m.decl == "f_f" for m in gen)

    def test_seq_delete_keeps_the_parentheses_balanced(self, mutate, gen):
        lines = GENERATED.splitlines(keepends=True)
        for m in (x for x in gen if x.op == "ast-seq-delete"):
            new = list(lines)
            new[m.line - 1] = m.new
            assert mutate._balanced("".join(new)), m.diff

    def test_a_mutant_is_a_single_line_edit(self, gen):
        for m in gen:
            assert m.old.count("\n") <= 1 and m.new.count("\n") <= 1

    def test_json_record_is_self_describing(self, gen):
        j = gen[0].to_json()
        assert set(j) == {"op", "line", "decl", "before", "after"}
        assert j["before"] != j["after"]


class TestScoringRules:
    """The rules that decide kill/survive/invalid/inconclusive. Getting these wrong is
    how a gate reports 100% while measuring nothing."""

    def test_the_source_says_a_foreign_build_break_is_inconclusive(self, mutate):
        src = open(mutate.__file__).read()
        assert 'rec["verdict"] = "inconclusive"' in src
        assert "foreign" in src
        assert re.search(r"if l\[0\] not in \(base, spec_base\)", src), (
            "the foreign-error filter is the thing that stops an unrelated broken "
            "dependency being credited to a theorem")

    def test_an_ill_typed_mutant_is_invalid_not_a_kill(self, mutate):
        src = open(mutate.__file__).read()
        assert 'rec["verdict"] = "invalid"' in src
        assert "hit_defs and not hit_thms" in src

    def test_the_coarse_fallback_is_counted_and_warned_about(self, mutate):
        """It must never be possible to report a kill rate without saying how much of
        it came from unattributed build failures."""
        src = open(mutate.__file__).read()
        assert 'rec["attribution"] = "coarse"' in src
        assert 'report["coarse_attributions"] = coarse' in src
        assert "WARNING" in src

    def test_the_build_is_retried_before_a_failure_is_believed(self, mutate):
        src = open(mutate.__file__).read()
        assert "if rc == 0 or timed_out or all_error_lines(out):" in src
