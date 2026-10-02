import Autoform.CIntWidthProgram

/-!
# Width-typed C integer arithmetic, checked against `cc`

Until item O every `.cLike` integer operation was computed at 32 bits
(`Dialect.toNumConfig .cLike = c32Wrapv`), so `long`, `long long`, `size_t`, `u64` and
every `unsigned` comparison, division and shift were silently wrong or holes. The exporter
now names the C type an operation is performed at (`"*:i64"`, `"<:u32"`, `">>:u64"`;
`Lang/Core/TypedInt.lean`) and converts stores (`cast:<T>`), and Core computes at that
type.

`Autoform/CIntWidthProgram.lean` is the rendered export of
`tests/fixtures/cintwidth/cintwidth_cases.c`. Every `case_*` function of it is run here and
pinned with `#guard_msgs`; `tests/test_cintwidth_cc.py` compiles the same file with
`cc -O0 -fwrapv` and fails if any pin is not `cc`'s value. With the exporter of the
integration head before item O, 4 of these 23 agreed with `cc`, 16 were silent wrong
answers, 2 were holes and 1 ran out of fuel (`docs/scale.md`).
-/

namespace Autoform.Core
namespace CIntWidth

def showR : EResult → String
  | .val (.int i)   => toString i
  | .val (.bool b)  => if b then "bool true" else "bool false"
  | .val _          => "<non-integer value>"
  | .exn _          => "<exception>"
  | .hole l         => "hole " ++ l
  | .outOfFuel      => "outOfFuel"

open Autoform.Generated.CIntWidth in
def cRun (c : String) : String := showR (runFunc program 400 c [])

/-- info: "10000000000" -/
#guard_msgs in #eval cRun "case_long_mul"

/-- info: "1410065408" -/
#guard_msgs in #eval cRun "case_int_mul_wraps"

/-- info: "6000000000" -/
#guard_msgs in #eval cRun "case_mixed_mul"

/-- info: "464269060799999" -/
#guard_msgs in #eval cRun "case_shift_left_64"

/-- info: "7" -/
#guard_msgs in #eval cRun "case_tree_depth"

/-- info: "6000000000" -/
#guard_msgs in #eval cRun "case_long_accumulate"

/-- info: "4294967295" -/
#guard_msgs in #eval cRun "case_unsigned_underflow"

/-- info: "4294967295" -/
#guard_msgs in #eval cRun "case_unsigned_init_widen"

/-- info: "1705032704" -/
#guard_msgs in #eval cRun "case_u32_add_wraps"

/-- info: "18446744073709551614" -/
#guard_msgs in #eval cRun "case_u64_mul_wraps"

/-- info: "1" -/
#guard_msgs in #eval cRun "case_shift_right_u32"

/-- info: "-4" -/
#guard_msgs in #eval cRun "case_shift_right_i32"

/-- info: "15" -/
#guard_msgs in #eval cRun "case_shift_right_u64"

/-- info: "-268435456" -/
#guard_msgs in #eval cRun "case_shift_right_i64"

/-- info: "0" -/
#guard_msgs in #eval cRun "case_mixed_compare"

/-- info: "2147483647" -/
#guard_msgs in #eval cRun "case_unsigned_div"

/-- info: "4294967295" -/
#guard_msgs in #eval cRun "case_unsigned_neg"

/-- info: "18446744073709551615" -/
#guard_msgs in #eval cRun "case_u64_not"

/-- info: "0" -/
#guard_msgs in #eval cRun "case_u8_increment_wraps"

/-- info: "4" -/
#guard_msgs in #eval cRun "case_u8_compound_wraps"

/-- info: "1" -/
#guard_msgs in #eval cRun "case_size_t_underflow"

/-- info: "-3500000000" -/
#guard_msgs in #eval cRun "case_i64_div"

/-- info: "44" -/
#guard_msgs in #eval cRun "case_narrow_signed_char"

end CIntWidth
end Autoform.Core
