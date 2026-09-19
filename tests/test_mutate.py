"""scripts/mutate.py beyond the diagnostic regex.

A mutation gate is only evidence if three things hold: the mutants it generates are real
behavioural perturbations, they are attributed to the right declaration, and a build
failure it cannot attribute is *not* quietly scored as a kill. All three have been wrong
here at some point.
"""
from __future__ import annotations

import re
import json
import os
import signal
import sys
import time
from pathlib import Path

import pytest


@pytest.mark.skipif(os.name != 'posix', reason='process groups require POSIX')
@pytest.mark.parametrize('timeout', [False, True])
def test_build_cleanup_releases_descendant_resources(tmp_path, monkeypatch, mutate, timeout):
    import fcntl
    lake = tmp_path/'lake'
    lake.write_text('#!' + sys.executable + '\n' + '''
import fcntl, os, sys, time
read, write = os.pipe()
pid = os.fork()
if pid == 0:
    os.close(read)
    with open('descendant.lock', 'w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        os.write(write, b'x')
        os.close(write)
        os.close(1)
        os.close(2)
        while True: time.sleep(60)
os.close(write)
assert os.read(read, 1) == b'x'
os.close(read)
with open('descendant.pid', 'w') as result: result.write(str(pid))
if os.environ['STALL'] == '1':
    while True: time.sleep(60)
''')
    lake.chmod(0o755)
    monkeypatch.setattr(mutate, 'lake_env', lambda:dict(os.environ, PATH=str(tmp_path),
                                                      STALL='1' if timeout else '0'))
    start = time.monotonic()
    try:
        rc, _, timed_out = mutate.run_build(tmp_path, 'Check', 1)
        assert timed_out == timeout
        assert (rc == 0) != timeout
        assert time.monotonic() - start < 8
        deadline = time.monotonic() + 2
        with (tmp_path/'descendant.lock').open() as lock:
            while True:
                try:
                    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    break
                except BlockingIOError:
                    if time.monotonic() >= deadline:
                        pytest.fail('compiler descendant remained alive after build cleanup')
                    time.sleep(0.01)
    finally:
        pid = tmp_path/'descendant.pid'
        if pid.exists():
            try:
                os.kill(int(pid.read_text()), signal.SIGKILL)
            except ProcessLookupError:
                pass


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

    def test_comments_and_following_commands_are_not_theorem_bodies(self, mutate):
        source = ['theorem checked : True := by\n', '  trivial\n',
                  '/- theorem fake : False := by\n', '  sorry -/\n',
                  '#guard false\n']
        decls = mutate.parse_decls(source)
        assert not any(d.name == 'fake' for d in decls)
        assert mutate.decl_at(decls, 2).name == 'checked'
        assert mutate.decl_at(decls, 5).kind == 'command'


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
    @pytest.mark.parametrize("operator", ["num:go:i64:+", "num:java:i32:+", "py:/", "js:*"])
    def test_typed_operators_preserve_their_semantics_tag(self, mutate, operator):
        src = ['def f : Func := { body := (.ret (.binop "%s" (.lit (.int 1)) (.lit (.int 2)))) }\n' % operator]
        mutations = mutate.gen_mutants_generated(src, mutate.parse_decls(src))
        swapped = [m for m in mutations if m.op.startswith("ast-binop:")]
        assert len(swapped) == 1
        prefix, _, suffix = operator.rpartition(":")
        assert '"' + prefix + ':' + mutate.AST_BINOP_SWAPS[suffix] + '"' in swapped[0].new

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

    @pytest.mark.parametrize('failure,expected', [
        ((1, '', True), 'inconclusive'),
        ((1, 'lake: internal error', False), 'inconclusive'),
        ((1, 'Other.lean:2:0: error: dependency failed', False), 'inconclusive'),
        ((1, 'Check.lean:1:0: error: type mismatch\nCheck.lean:2:0: error: goal failed', False), 'invalid'),
        ((1, 'Check.lean:2:0: error: goal failed', False), 'killed'),
        ((0, '', False), 'survived'),
    ])
    def test_actual_gate_attributes_only_proof_failures(self, tmp_path, monkeypatch, mutate, failure, expected):
        source = tmp_path / 'Check.lean'
        original = 'def value : Nat := 1\ntheorem checked : value = 1 := rfl\n'
        source.write_text(original)
        (tmp_path / 'lakefile.toml').write_text('name = "test"\n')
        report = tmp_path / 'mutation.json'
        monkeypatch.setattr(mutate, 'run_build', lambda *args:
                            (0, '', False) if source.read_text() == original else failure)
        monkeypatch.setattr('sys.argv', ['mutate.py', str(source), 'Check', '--decls', 'value',
                                       '--subject', 'checked=value', '--max-mutants', '1',
                                       '--json', str(report)])
        code = mutate.main()
        data = json.loads(report.read_text())
        result = data['mutants'][0]['verdict']
        assert (result['checked'] if isinstance(result, dict) else result) == expected
        assert (code == 0) == (expected == 'killed')
        assert data['theorems']['checked']['killed'] == (expected == 'killed')
        assert source.read_text() == original

    def test_failed_restoration_cannot_pass_gate(self, tmp_path, monkeypatch, mutate):
        source = tmp_path / 'Check.lean'
        source.write_text('def value : Nat := 1\ntheorem checked : value = 1 := rfl\n')
        (tmp_path / 'lakefile.toml').write_text('name = "test"\n')
        report = tmp_path / 'mutation.json'
        results = iter([(0, '', False), (1, 'Check.lean:2:0: error: goal failed', False),
                        (1, 'restored build failed', False)])
        monkeypatch.setattr(mutate, 'run_build', lambda *args: next(results))
        monkeypatch.setattr('sys.argv', ['mutate.py', str(source), 'Check', '--decls', 'value',
                                       '--subject', 'checked=value', '--max-mutants', '1',
                                       '--json', str(report)])
        assert mutate.main() != 0
        assert json.loads(report.read_text())['status'] == 'RESTORE_FAILED'

    def test_failed_command_after_theorem_is_not_credited_as_a_kill(self, tmp_path, monkeypatch, mutate):
        source = tmp_path/'Check.lean'
        original = 'def value : Nat := 1\ntheorem checked : value = value := rfl\n#guard value == 1\n'
        source.write_text(original)
        (tmp_path/'lakefile.toml').write_text('name = "test"\n')
        report = tmp_path/'mutation.json'
        monkeypatch.setattr(mutate, 'run_build', lambda *args:
                            (0, '', False) if source.read_text() == original else
                            (1, 'Check.lean:3:0: error: guard failed', False))
        monkeypatch.setattr('sys.argv', ['mutate.py',str(source),'Check','--decls','value',
                                       '--subject','checked=value','--max-mutants','1','--json',str(report)])
        assert mutate.main() != 0
        data = json.loads(report.read_text())
        assert data['mutants'][0]['verdict'] == 'inconclusive'
        assert data['theorems']['checked']['killed'] == 0

    def test_generated_and_spec_with_same_basename_are_distinct(self, tmp_path, monkeypatch, mutate):
        source=tmp_path/'Autoform/Generated/Check.lean'
        spec=tmp_path/'Autoform/SpecsGen/Check.lean'
        source.parent.mkdir(parents=True)
        spec.parent.mkdir(parents=True)
        original='def value : Nat := 1\n'
        source.write_text(original)
        spec.write_text('theorem checked : value = 1 := rfl\n')
        (tmp_path/'lakefile.toml').write_text('name="fixture"\n')
        report=tmp_path/'mutation.json'
        monkeypatch.setattr(mutate,'run_build',lambda *args:(0,'',False) if source.read_text()==original
                            else (1,'error: Autoform/SpecsGen/Check.lean:1:0: unsolved goals',False))
        # Use ordinary Lean operators on this small fixture while retaining the
        # real generated/spec directory layout that exposed the ambiguity.
        monkeypatch.setattr(mutate,'gen_mutants_generated',mutate.gen_mutants)
        monkeypatch.setattr('sys.argv',['mutate.py',str(source),'Autoform.Generated.Check',
            '--spec-file',str(spec),'--spec-module','Autoform.SpecsGen.Check',
            '--decls','value','--subject','checked=value','--max-mutants','1','--json',str(report)])
        assert mutate.main()==0
        data=json.loads(report.read_text())
        assert data['invalid']==0 and data['theorems']['checked']['killed']==1

    def test_the_build_is_retried_before_a_failure_is_believed(self, mutate):
        src = open(mutate.__file__).read()
        assert "if rc == 0 or timed_out or all_error_lines(out):" in src
