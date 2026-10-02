import Autoform.CBoolIntProgram

/-!
# C comparison results as integers, checked against `cc`

Under `.cLike` Core produces `Val.bool` for `<`, `==`, `!`, `&&`, ... (Java's `boolean`
and C++'s `bool` need it) and promotes a `bool` to `0`/`1` wherever it meets a number
(`Dialect.promotesBool`, `binopFallback` and `applyUnop` in `Lang/Core/Semantics.lean`).
In C those results are `int` 0/1 to begin with, so before the promotion
`int t = (a < b); if (t == 1) return 7; return 3;` returned 3 here and 7 under `cc`
(`Val.beq (.bool true) (.int 1)` is `false`): the SQLite-sample wrong answer of
`docs/scale.md`.

`Autoform/CBoolIntProgram.lean` is the rendered export of
`tests/fixtures/cboolint/cboolint_cases.c`. Every `case_*` function of it is run here and
pinned with `#guard_msgs`; `tests/test_cboolint_cc.py` compiles the same file with `cc`
and fails if any pin is not `cc`'s value. A pin of `bool true`/`bool false` stands for
`1`/`0` through the return conversion to `int` (the one integer context Core does not
see; `scripts/differential.py`'s `c_return_conversion` applies the same rule).
-/

namespace Autoform.Core
namespace CBoolInt

def showR : EResult → String
  | .val (.int i)   => toString i
  | .val (.bool b)  => if b then "bool true" else "bool false"
  | .val _          => "<non-integer value>"
  | .exn _          => "<exception>"
  | .hole l         => "hole " ++ l
  | .outOfFuel      => "outOfFuel"

open Autoform.Generated.CBoolInt in
def cRun (c : String) : String := showR (runFunc program 400 c [])

/-- info: "7" -/
#guard_msgs in #eval cRun "case_lt_flag_true"

/-- info: "3" -/
#guard_msgs in #eval cRun "case_lt_flag_false"

/-- info: "bool true" -/
#guard_msgs in #eval cRun "case_cmp_eq_one"

/-- info: "1" -/
#guard_msgs in #eval cRun "case_cmp_plus_cmp"

/-- info: "10" -/
#guard_msgs in #eval cRun "case_logical_times"

/-- info: "2" -/
#guard_msgs in #eval cRun "case_not_plus"

/-- info: "-1" -/
#guard_msgs in #eval cRun "case_neg_cmp"

/-- info: "-1" -/
#guard_msgs in #eval cRun "case_bnot_cmp"

/-- info: "3" -/
#guard_msgs in #eval cRun "case_bitand_cmps"

/-- info: "4" -/
#guard_msgs in #eval cRun "case_xor_cmps"

/-- info: "8" -/
#guard_msgs in #eval cRun "case_shift_cmp"

/-- info: "bool true" -/
#guard_msgs in #eval cRun "case_cmp_vs_cmp"

/-- info: "4" -/
#guard_msgs in #eval cRun "case_sum_flags"

/-- info: "1" -/
#guard_msgs in #eval cRun "case_cmp_plus_double"

/-- info: "bool true" -/
#guard_msgs in #eval cRun "case_direct_return"


end CBoolInt
end Autoform.Core
