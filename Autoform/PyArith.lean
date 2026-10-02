import Autoform.PyArithProgram
import Autoform.PyScoping

/-!
# Python `/`, `//` and `bool`-is-an-`int`, checked against CPython (STRATEGY.md item Q)

Two silent wrong answers, both measured against CPython 3.11 before this change:

* **True division.** `applyBinop .python "/" (.int 7) (.int 2)` was `int 3`; CPython says
  `3.5`, and `6 / 3` is the FLOAT `2.0`. The exporter spelled both `<operator>.division` and
  `<operator>.floorDiv` as `"/"`, and Core floored it. `floorDiv` is now exported as `"//"`
  (floor division on `Int`), and `"/"` on two ints under `.python` is `pyIntTrueDiv`: one
  IEEE division in binary64 when both operands are exact doubles (`|n| ≤ 2^53`), the hole
  `binop:/:int-true-division-beyond-2^53` beyond that -- CPython rounds the quotient once, and
  converting first would round twice -- and `ZeroDivisionError` for a zero divisor.
* **`bool` is an `int`.** `True == 1` was `False`, `True + 1` a hole, `{1: 'a'}[True]` a
  `KeyError`. `Dialect.promotesBool` is now `true` for `.python` (it was `.cLike` only since
  item K): a `bool` is `0`/`1` in arithmetic, comparison and equality, `Val.beq` identifies
  `bool` with the `int`/`float` of the same value (so dict keys, `in` and container equality
  agree), and `bool & bool`, `bool | bool`, `bool ^ bool` stay `bool`.

Section 1 states the rules as kernel-checked theorems; section 2 pins every `case_*` of
`tests/fixtures/pyarith/pyarith_cases.py` (rendered to `Autoform/PyArithProgram.lean`) with
`#guard_msgs`, and `tests/test_pyarith_cpython.py` runs the same functions under CPython and
fails if a pin is not CPython's value -- or, for the three `EXPECTED_HOLES`, not that hole.
-/

namespace Autoform.Core
namespace PyArith

/-! ## 1. The rules -/

/-- `7 / 2` is the float `3.5` (binary64 bits `0x400C000000000000`), not the integer `3`. -/
theorem div_7_2 :
    applyBinop .python "/" (.int 7) (.int 2) = .val (.float ⟨.binary64, 4615063718147915776⟩) := by
  rfl

/-- `-7 / 2` is `-3.5`. -/
theorem div_neg7_2 :
    applyBinop .python "/" (.int (-7)) (.int 2) = .val (.float ⟨.binary64, 13838435755002691584⟩) := by
  rfl

/-- `6 / 3` is the FLOAT `2.0`, not the integer `2`. -/
theorem div_6_3_is_a_float :
    applyBinop .python "/" (.int 6) (.int 3) = .val (.float ⟨.binary64, 4611686018427387904⟩) := by
  rfl

/-- `1 / 0` is `ZeroDivisionError`, for every dividend. -/
theorem div_by_zero (x : Int) :
    applyBinop .python "/" (.int x) (.int 0) = .exn (.str "ZeroDivisionError") := rfl

/-- `7 // 2` is `3`, `-7 // 2` is `-4`: `//` is floor division, and is its own operator. -/
theorem floordiv_7_2 : applyBinop .python "//" (.int 7) (.int 2) = .val (.int 3) := rfl
theorem floordiv_neg7_2 : applyBinop .python "//" (.int (-7)) (.int 2) = .val (.int (-4)) := rfl

/-- Past `2^53` the answer is a NAMED HOLE, never a double-rounded number. -/
theorem div_beyond_2pow53 :
    applyBinop .python "/" (.int 9007199254740993) (.int 2)
      = .hole "binop:/:int-true-division-beyond-2^53" := rfl
theorem div_big_divisor :
    applyBinop .python "/" (.int 1) (.int 9007199254740993)
      = .hole "binop:/:int-true-division-beyond-2^53" := rfl

/-- `True == 1`, both ways round, and `True != 1` is `False`. -/
theorem bool_eq_int :
    applyBinop .python "==" (.bool true) (.int 1) = .val (.bool true) ∧
    applyBinop .python "==" (.int 1) (.bool true) = .val (.bool true) ∧
    applyBinop .python "!=" (.bool true) (.int 1) = .val (.bool false) := ⟨rfl, rfl, rfl⟩

/-- `True + True == 2`, `True + 1 == 2`. -/
theorem bool_add :
    applyBinop .python "+" (.bool true) (.bool true) = .val (.int 2) ∧
    applyBinop .python "+" (.bool true) (.int 1) = .val (.int 2) := ⟨rfl, rfl⟩

/-- `-True == -1`, `~True == -2`. -/
theorem bool_unary :
    applyUnop .python "-" (.bool true) = .val (.int (-1)) ∧
    applyUnop .python "~" (.bool true) = .val (.int (-2)) := ⟨rfl, rfl⟩

/-- `True < 2`. -/
theorem bool_lt : applyBinop .python "<" (.bool true) (.int 2) = .val (.bool true) := rfl

/-- `bool & bool`, `bool | bool`, `bool ^ bool` stay `bool`; `bool & int` is an `int`. -/
theorem bool_bitwise_stays_bool :
    applyBinop .python "&" (.bool true) (.bool true) = .val (.bool true) ∧
    applyBinop .python "|" (.bool true) (.bool false) = .val (.bool true) ∧
    applyBinop .python "^" (.bool true) (.bool true) = .val (.bool false) ∧
    applyBinop .python "&" (.bool true) (.int 3) = .val (.int 1) := ⟨rfl, rfl, rfl, rfl⟩

/-- `True / True` is the float `1.0`: a `bool` follows the integer rule for `/`. -/
theorem bool_div :
    applyBinop .python "/" (.bool true) (.bool true) = .val (.float ⟨.binary64, 4607182418800017408⟩) := by
  rfl

/-- `True` and `1` are the same dictionary key (`{1: 'a'}[True] == 'a'`): `Val.beq` agrees. -/
theorem beq_bool_int : Val.beq (.bool true) (.int 1) = true ∧ Val.beq (.int 0) (.bool false) = true ∧
    Val.beq (.bool true) (.int 2) = false := ⟨rfl, rfl, rfl⟩

/-- `Val.beq` between a `bool` and a `float` is exact, like `int` and `float`. -/
theorem beq_bool_float :
    Val.beq (.bool true) (.float ⟨.binary64, 4607182418800017408⟩) = true := by
  rfl

/-- The `bool` rule is Python's and C's, and JavaScript is untouched: its `==` is loose
equality with its own coercion table (`jsEqE`), still a named hole for `true == 1`. -/
theorem js_unchanged :
    applyBinop .javascript "==" (.bool true) (.int 1) = .hole "js:==:cross-type-coercion" := rfl

/-- The integer rule a `.python` `bool` follows is `applyBinop` on the same integers. -/
theorem pyIntBinop_eq (op : String) (x y : Int) (h : op ∈ pyIntOps) :
    pyIntBinop op x y = applyBinop .python op (.int x) (.int y) := by
  simp only [pyIntOps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## 2. End to end: the exported fixture, pinned, and compared with CPython

`pyRun` prints a result in the canonical text `tests/test_pyarith_cpython.py` produces from
the CPython value, so the comparison is string equality on both sides. -/

open Autoform.Generated.PyArith in
def pyRun (c : String) : String :=
  PyScoping.showR (runMain program 400 moduleInits ("pyarith_cases.py:<module>." ++ c) [])

-- CPython: 2
/-- info: "2" -/
#guard_msgs in #eval pyRun "case_bool_add_bool"

-- CPython: (2, 2)
/-- info: "(2, 2)" -/
#guard_msgs in #eval pyRun "case_bool_add_int"

-- CPython: (True, False, False)
/-- info: "(True, False, False)" -/
#guard_msgs in #eval pyRun "case_bool_and_stays_bool"

-- CPython: (1, 3, 2)
/-- info: "(1, 3, 2)" -/
#guard_msgs in #eval pyRun "case_bool_bitwise_with_int"

-- CPython: ('a', 'b')
/-- info: "('a', 'b')" -/
#guard_msgs in #eval pyRun "case_bool_dict_key_lookup"

-- CPython: (float(bits=4602678819172646912), float(bits=4611686018427387904))
/-- info: "(float(bits=4602678819172646912), float(bits=4611686018427387904))" -/
#guard_msgs in #eval pyRun "case_bool_div"

-- CPython: raise ZeroDivisionError
/-- info: "raise ZeroDivisionError" -/
#guard_msgs in #eval pyRun "case_bool_div_zero"

-- CPython: (True, True)
/-- info: "(True, True)" -/
#guard_msgs in #eval pyRun "case_bool_eq_float"

-- CPython: (True, True, False)
/-- info: "(True, True, False)" -/
#guard_msgs in #eval pyRun "case_bool_eq_int"

-- CPython: (0, 2, 1, 0)
/-- info: "(0, 2, 1, 0)" -/
#guard_msgs in #eval pyRun "case_bool_floordiv_mod"

-- CPython: (True, True, False, True)
/-- info: "(True, True, False, True)" -/
#guard_msgs in #eval pyRun "case_bool_in_list"

-- CPython: (-2, -1)
/-- info: "(-2, -1)" -/
#guard_msgs in #eval pyRun "case_bool_invert"

-- CPython: True
/-- info: "True" -/
#guard_msgs in #eval pyRun "case_bool_list_eq"

-- CPython: (True, True, True, False)
/-- info: "(True, True, True, False)" -/
#guard_msgs in #eval pyRun "case_bool_lt"

-- CPython: (5, 0)
/-- info: "(5, 0)" -/
#guard_msgs in #eval pyRun "case_bool_mul"

-- CPython: (False, True)
/-- info: "(False, True)" -/
#guard_msgs in #eval pyRun "case_bool_ne_int"

-- CPython: -1
/-- info: "-1" -/
#guard_msgs in #eval pyRun "case_bool_neg"

-- CPython: (True, True, False)
/-- info: "(True, True, False)" -/
#guard_msgs in #eval pyRun "case_bool_or_stays_bool"

-- CPython: (float(bits=4612811918334230528), float(bits=4609434218613702656))
/-- info: "(float(bits=4612811918334230528), float(bits=4609434218613702656))" -/
#guard_msgs in #eval pyRun "case_bool_plus_float"

-- CPython: (8, 1)
/-- info: "(8, 1)" -/
#guard_msgs in #eval pyRun "case_bool_shift"

-- CPython: (-1, 1, 0)
/-- info: "(-1, 1, 0)" -/
#guard_msgs in #eval pyRun "case_bool_sub"

-- CPython: (True, False)
/-- info: "(True, False)" -/
#guard_msgs in #eval pyRun "case_bool_tuple_eq"

-- CPython: (False, True, False)
/-- info: "(False, True, False)" -/
#guard_msgs in #eval pyRun "case_bool_xor_stays_bool"

-- CPython: float(bits=4615063718147915776)
/-- info: "float(bits=4615063718147915776)" -/
#guard_msgs in #eval pyRun "case_div_7_2"

-- CPython: float(bits=13838435755002691584)
/-- info: "float(bits=13838435755002691584)" -/
#guard_msgs in #eval pyRun "case_div_7_neg2"

-- CPython: (float(bits=4615063718147915776), 3, 1)
/-- info: "(float(bits=4615063718147915776), 3, 1)" -/
#guard_msgs in #eval pyRun "case_div_and_floordiv_together"

-- CPython: float(bits=4841369599423283200)
/-- info: "hole binop:/:int-true-division-beyond-2^53" -/
#guard_msgs in #eval pyRun "case_div_beyond_2pow53"

-- CPython: float(bits=4368491638549381119)
/-- info: "hole binop:/:int-true-division-beyond-2^53" -/
#guard_msgs in #eval pyRun "case_div_big_divisor"

-- CPython: float(bits=5043144871808901387)
/-- info: "hole binop:/:int-true-division-beyond-2^53" -/
#guard_msgs in #eval pyRun "case_div_big_int"

-- CPython: float(bits=4611686018427387904)
/-- info: "float(bits=4611686018427387904)" -/
#guard_msgs in #eval pyRun "case_div_exact_is_float"

-- CPython: float(bits=4841369599423283200)
/-- info: "float(bits=4841369599423283200)" -/
#guard_msgs in #eval pyRun "case_div_exactly_2pow53"

-- CPython: float(bits=4613937818241073152)
/-- info: "float(bits=4613937818241073152)" -/
#guard_msgs in #eval pyRun "case_div_float_float"

-- CPython: float(bits=4615063718147915776)
/-- info: "float(bits=4615063718147915776)" -/
#guard_msgs in #eval pyRun "case_div_int_float"

-- CPython: float(bits=13838435755002691584)
/-- info: "float(bits=13838435755002691584)" -/
#guard_msgs in #eval pyRun "case_div_neg7_2"

-- CPython: float(bits=4599676419421066581)
/-- info: "float(bits=4599676419421066581)" -/
#guard_msgs in #eval pyRun "case_div_one_third"

-- CPython: raise ZeroDivisionError
/-- info: "raise ZeroDivisionError" -/
#guard_msgs in #eval pyRun "case_div_zero"

-- CPython: float(bits=9223372036854775808)
/-- info: "float(bits=9223372036854775808)" -/
#guard_msgs in #eval pyRun "case_div_zero_numerator_negative_divisor"

-- CPython: (True, True)
/-- info: "(True, True)" -/
#guard_msgs in #eval pyRun "case_false_eq_zero"

-- CPython: 3
/-- info: "3" -/
#guard_msgs in #eval pyRun "case_floordiv_7_2"

-- CPython: -4
/-- info: "-4" -/
#guard_msgs in #eval pyRun "case_floordiv_7_neg2"

-- CPython: -4
/-- info: "-4" -/
#guard_msgs in #eval pyRun "case_floordiv_neg7_2"

-- CPython: raise ZeroDivisionError
/-- info: "raise ZeroDivisionError" -/
#guard_msgs in #eval pyRun "case_floordiv_zero"

-- CPython: 'x'
/-- info: "'x'" -/
#guard_msgs in #eval pyRun "case_int_dict_key_lookup_by_bool_key"

-- CPython: 2
/-- info: "2" -/
#guard_msgs in #eval pyRun "case_mod_neg7_3"

-- CPython: (False, True)
/-- info: "(False, True)" -/
#guard_msgs in #eval pyRun "case_not_bool"


end PyArith
end Autoform.Core
