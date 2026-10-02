import Autoform.GoIntWidthProgram

/-!
# Width-typed Go integer arithmetic, checked against `go`

Go shared `.cLike` with C, so Go arithmetic was computed at 32 bits whatever the type:
Go `int` is 64-bit on amd64/arm64, so `m := 100000; m * m` is 10000000000 in Go and was
1410065408 in Core (STRATEGY §29 item 5; §63 "Not done"). The exporter now types every
Go integer operator by its operands' type (`"*:g64"` signed, `"-:w08"` unsigned;
`Lang/Core/TypedInt.lean`): operations are performed at the operand type (Go has no integer
promotion), overflow wraps, `MinInt / -1` is `MinInt`, a shift count at or above the width
gives 0 / -1, and division by zero and a negative shift count panic (an exception here).
Integer conversions `T(x)` wrap (`cast:*`); a constant expression is evaluated exactly; a
non-constant shift of an untyped constant (`1 << n`) is a hole, because its type comes from
a context the exporter cannot see.

`Autoform/GoIntWidthProgram.lean` is the rendered export of
`tests/fixtures/gointwidth/cases.go` (gosrc2cpg 4.0.606; see that fixture's
`provenance.json`). Every `case_*` function is pinned here with `#guard_msgs`;
`tests/test_gointwidth_go.py` builds `cases.go` with `main.go` using the `go` toolchain,
runs it, and fails if any pin differs from Go's output (a Go panic is pinned as
`<exception ...>`; the one hole is pinned as a hole and is checked to be a hole).
-/

namespace Autoform.Core
namespace GoIntWidth

def showR : EResult → String
  | .val (.int i)   => toString i
  | .val (.bool b)  => if b then "bool true" else "bool false"
  | .val _          => "<non-integer value>"
  | .exn (.str s)   => "<exception " ++ s ++ ">"
  | .exn _          => "<exception>"
  | .hole l         => "hole " ++ l
  | .outOfFuel      => "outOfFuel"

open Autoform.Generated.GoIntWidth in
def gRun (c : String) : String := showR (runFunc program 400 s!"main.{c}" [])

/-- info: "10000000000" -/
#guard_msgs in #eval gRun "case_int_mul"

/-- info: "-9223372036854775808" -/
#guard_msgs in #eval gRun "case_int_add_wraps"

/-- info: "1410065408" -/
#guard_msgs in #eval gRun "case_int32_mul_wraps"

/-- info: "10000000000" -/
#guard_msgs in #eval gRun "case_int64_mul"

/-- info: "-128" -/
#guard_msgs in #eval gRun "case_int8_add_wraps"

/-- info: "-128" -/
#guard_msgs in #eval gRun "case_int8_incr"

/-- info: "-32767" -/
#guard_msgs in #eval gRun "case_int16_compound"

/-- info: "255" -/
#guard_msgs in #eval gRun "case_uint8_sub_wraps"

/-- info: "144" -/
#guard_msgs in #eval gRun "case_byte_add_wraps"

/-- info: "-2147483648" -/
#guard_msgs in #eval gRun "case_rune_add_wraps"

/-- info: "0" -/
#guard_msgs in #eval gRun "case_uint32_mul_wraps"

/-- info: "0" -/
#guard_msgs in #eval gRun "case_uint64_mul_wraps"

/-- info: "18446744073709551615" -/
#guard_msgs in #eval gRun "case_uint64_sub_wraps"

/-- info: "18446744073709551615" -/
#guard_msgs in #eval gRun "case_uint_sub_wraps"

/-- info: "18446744073709551615" -/
#guard_msgs in #eval gRun "case_uintptr_sub_wraps"

/-- info: "65535" -/
#guard_msgs in #eval gRun "case_uint16_neg"

/-- info: "-9223372036854775808" -/
#guard_msgs in #eval gRun "case_int_neg_min"

/-- info: "250" -/
#guard_msgs in #eval gRun "case_uint8_complement"

/-- info: "-1" -/
#guard_msgs in #eval gRun "case_int64_complement"

/-- info: "240" -/
#guard_msgs in #eval gRun "case_and_not"

/-- info: "-9223372036854775808" -/
#guard_msgs in #eval gRun "case_min_div"

/-- info: "0" -/
#guard_msgs in #eval gRun "case_min_rem"

/-- info: "-128" -/
#guard_msgs in #eval gRun "case_int8_min_div"

/-- info: "-3" -/
#guard_msgs in #eval gRun "case_div_trunc"

/-- info: "-1" -/
#guard_msgs in #eval gRun "case_rem_sign"

/-- info: "2147483647" -/
#guard_msgs in #eval gRun "case_uint32_div"

/-- info: "0" -/
#guard_msgs in #eval gRun "case_shl_over_width"

/-- info: "-2147483648" -/
#guard_msgs in #eval gRun "case_shl_in_width"

/-- info: "-9223372036854775808" -/
#guard_msgs in #eval gRun "case_shl_int64"

/-- info: "-1" -/
#guard_msgs in #eval gRun "case_shr_over_width_neg"

/-- info: "0" -/
#guard_msgs in #eval gRun "case_shr_over_width_pos"

/-- info: "-4" -/
#guard_msgs in #eval gRun "case_shr_arith"

/-- info: "15" -/
#guard_msgs in #eval gRun "case_shr_uint"

/-- info: "128" -/
#guard_msgs in #eval gRun "case_shl_count_type"

/-- info: "4611686018427387904" -/
#guard_msgs in #eval gRun "case_shl_signed_count"

/-- info: "240" -/
#guard_msgs in #eval gRun "case_shl_drops_bits"

/-- info: "bool true" -/
#guard_msgs in #eval gRun "case_uint32_gt"

/-- info: "bool true" -/
#guard_msgs in #eval gRun "case_int8_lt"

/-- info: "78000000000" -/
#guard_msgs in #eval gRun "case_int_accumulate"

/-- info: "1" -/
#guard_msgs in #eval gRun "case_conv_int32_trunc"

/-- info: "44" -/
#guard_msgs in #eval gRun "case_conv_uint8_trunc"

/-- info: "18446744073709551615" -/
#guard_msgs in #eval gRun "case_conv_sign_extend"

/-- info: "-5" -/
#guard_msgs in #eval gRun "case_conv_int64_widen"

/-- info: "hole op:int:untyped-constant-shift" -/
#guard_msgs in #eval gRun "case_untyped_const_shift"

/-- info: "44" -/
#guard_msgs in #eval gRun "case_named_type_wraps"

/-- info: "18446744073709551610" -/
#guard_msgs in #eval gRun "case_untyped_const_operand"

/-- info: "38" -/
#guard_msgs in #eval gRun "case_local_from_conversion"

/-- info: "1099511627783" -/
#guard_msgs in #eval gRun "case_const_expr_exact"

/-- info: "18446744073709551615" -/
#guard_msgs in #eval gRun "case_const_conversion"

/-- info: "64" -/
#guard_msgs in #eval gRun "case_compound_ops"

/-- info: "61680" -/
#guard_msgs in #eval gRun "case_compound_and_not"

/-- info: "0" -/
#guard_msgs in #eval gRun "case_compound_shl_count"

/-- info: "0" -/
#guard_msgs in #eval gRun "case_compound_int64"

/-- info: "<exception panic: integer divide by zero>" -/
#guard_msgs in #eval gRun "case_div_zero"

/-- info: "<exception panic: negative shift amount>" -/
#guard_msgs in #eval gRun "case_neg_shift"

/-- info: "<exception panic: integer divide by zero>" -/
#guard_msgs in #eval gRun "case_rem_zero"

end GoIntWidth
end Autoform.Core
