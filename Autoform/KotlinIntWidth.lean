import Autoform.KotlinIntWidthProgram

/-!
# Width-typed Kotlin integer arithmetic, checked against the Kotlin compiler

Kotlin shared `.cLike` with C, so every Kotlin integer operation ran at 32 bits:
`100000L * 100000L` (`Long`) was 1410065408 where Kotlin gives 10000000000 (STRATEGY §29
item 5; §63 "Not done"). The exporter now types Kotlin integer operators by their
operands' types (`"*:k64"` signed, `"-:q32"` unsigned `UInt`; `Lang/Core/TypedInt.lean`):
`Byte`/`Short` operands promote to `Int`, `Int` meeting `Long` is `Long`, `UInt`/`ULong`
wrap at their width, shift counts are masked, `Int.MIN_VALUE / -1` is `Int.MIN_VALUE`, and
`/` or `%` by zero throws `ArithmeticException`. `x++` on a `Byte`/`Short`/`UByte`/`UShort`
narrows back to the target type (`Byte.inc()` wraps), and the integer conversions
`toInt()`/`toLong()`/`toByte()`/`toUInt()`/... and `inv()` translate.

`Autoform/KotlinIntWidthProgram.lean` is the rendered export of
`tests/fixtures/kotlinintwidth/cases.kt` (kotlin2cpg 4.0.606; see that fixture's
`provenance.json`). Every `case_*` function is pinned here with `#guard_msgs`;
`tests/test_kotlinintwidth_kotlin.py` compiles `cases.kt` with `Main.kt` using a Kotlin
compiler (`kotlinc` on PATH, or `AUTOFORM_KOTLIN_CP`; skipped when neither exists), runs it
and fails if any pin differs from the program's output.
-/

namespace Autoform.Core
namespace KotlinIntWidth

def showR : EResult → String
  | .val (.int i)   => toString i
  | .val (.bool b)  => if b then "bool true" else "bool false"
  | .val _          => "<non-integer value>"
  | .exn (.str s)   => "<exception " ++ s ++ ">"
  | .exn _          => "<exception>"
  | .hole l         => "hole " ++ l
  | .outOfFuel      => "outOfFuel"

open Autoform.Generated.KotlinIntWidth in
/-- Kotlin names a function `name:returnType(params)`; a case is found by its name. -/
def gRun (c : String) : String :=
  match program.funcs.find? (fun f => f.name.startsWith (c ++ ":")) with
  | some f => showR (runFunc program 400 f.name [])
  | none   => "no such function"

/-- info: "1410065408" -/
#guard_msgs in #eval gRun "case_int_mul_wraps"

/-- info: "10000000000" -/
#guard_msgs in #eval gRun "case_long_mul"

/-- info: "6000000000" -/
#guard_msgs in #eval gRun "case_mixed_mul"

/-- info: "6000000000" -/
#guard_msgs in #eval gRun "case_literal_is_long"

/-- info: "-2147483648" -/
#guard_msgs in #eval gRun "case_int_add_wraps"

/-- info: "-9223372036854775808" -/
#guard_msgs in #eval gRun "case_long_add_wraps"

/-- info: "6000000000" -/
#guard_msgs in #eval gRun "case_long_accumulate"

/-- info: "1705032704" -/
#guard_msgs in #eval gRun "case_int_accumulate"

/-- info: "-128" -/
#guard_msgs in #eval gRun "case_byte_incr"

/-- info: "128" -/
#guard_msgs in #eval gRun "case_byte_plus_promotes"

/-- info: "32767" -/
#guard_msgs in #eval gRun "case_short_decr"

/-- info: "0" -/
#guard_msgs in #eval gRun "case_ubyte_incr"

/-- info: "510" -/
#guard_msgs in #eval gRun "case_ubyte_plus_promotes"

/-- info: "2" -/
#guard_msgs in #eval gRun "case_shl_masked_int"

/-- info: "2" -/
#guard_msgs in #eval gRun "case_shl_masked_long"

/-- info: "8589934592" -/
#guard_msgs in #eval gRun "case_shl_long"

/-- info: "-8" -/
#guard_msgs in #eval gRun "case_shr_int"

/-- info: "-268435456" -/
#guard_msgs in #eval gRun "case_shr_long"

/-- info: "15" -/
#guard_msgs in #eval gRun "case_ushr_int"

/-- info: "15" -/
#guard_msgs in #eval gRun "case_ushr_long"

/-- info: "-4" -/
#guard_msgs in #eval gRun "case_shr_assign_style"

/-- info: "4294967295" -/
#guard_msgs in #eval gRun "case_uint_sub_wraps"

/-- info: "18446744073709551615" -/
#guard_msgs in #eval gRun "case_ulong_sub_wraps"

/-- info: "0" -/
#guard_msgs in #eval gRun "case_uint_mul_wraps"

/-- info: "18446744073709551614" -/
#guard_msgs in #eval gRun "case_ulong_mul_wraps"

/-- info: "2147483647" -/
#guard_msgs in #eval gRun "case_uint_div"

/-- info: "5" -/
#guard_msgs in #eval gRun "case_uint_rem"

/-- info: "2147483647" -/
#guard_msgs in #eval gRun "case_uint_shr"

/-- info: "2" -/
#guard_msgs in #eval gRun "case_uint_shl_masked"

/-- info: "15" -/
#guard_msgs in #eval gRun "case_ulong_shr"

/-- info: "-2147483648" -/
#guard_msgs in #eval gRun "case_min_div"

/-- info: "0" -/
#guard_msgs in #eval gRun "case_min_rem"

/-- info: "-9223372036854775808" -/
#guard_msgs in #eval gRun "case_long_min_div"

/-- info: "-3500000000" -/
#guard_msgs in #eval gRun "case_long_div"

/-- info: "-1" -/
#guard_msgs in #eval gRun "case_rem_sign"

/-- info: "-2147483648" -/
#guard_msgs in #eval gRun "case_int_neg_min"

/-- info: "-5" -/
#guard_msgs in #eval gRun "case_long_neg"

/-- info: "<exception ArithmeticException>" -/
#guard_msgs in #eval gRun "case_div_zero"

/-- info: "<exception ArithmeticException>" -/
#guard_msgs in #eval gRun "case_long_rem_zero"

/-- info: "<exception ArithmeticException>" -/
#guard_msgs in #eval gRun "case_uint_div_zero"

/-- info: "-6" -/
#guard_msgs in #eval gRun "case_int_inv"

/-- info: "-1" -/
#guard_msgs in #eval gRun "case_long_inv"

/-- info: "4294967295" -/
#guard_msgs in #eval gRun "case_uint_inv"

/-- info: "250" -/
#guard_msgs in #eval gRun "case_ubyte_inv"

/-- info: "61408" -/
#guard_msgs in #eval gRun "case_and_or_xor"

/-- info: "4294967295" -/
#guard_msgs in #eval gRun "case_long_and"

/-- info: "4294967040" -/
#guard_msgs in #eval gRun "case_uint_xor"

/-- info: "1" -/
#guard_msgs in #eval gRun "case_to_int_trunc"

/-- info: "-5" -/
#guard_msgs in #eval gRun "case_to_long_sign_extends"

/-- info: "44" -/
#guard_msgs in #eval gRun "case_to_byte_trunc"

/-- info: "4294967295" -/
#guard_msgs in #eval gRun "case_to_uint_reinterpret"

/-- info: "18446744073709551615" -/
#guard_msgs in #eval gRun "case_to_ulong_sign_extends"

/-- info: "-1" -/
#guard_msgs in #eval gRun "case_uint_to_int"

/-- info: "4294967295" -/
#guard_msgs in #eval gRun "case_uint_to_long"

/-- info: "4294967295" -/
#guard_msgs in #eval gRun "case_long_to_uint"

/-- info: "bool true" -/
#guard_msgs in #eval gRun "case_uint_gt"

/-- info: "bool true" -/
#guard_msgs in #eval gRun "case_int_long_compare"

/-- info: "10000000000" -/
#guard_msgs in #eval gRun "case_conditional"

/-- info: "-1073741824" -/
#guard_msgs in #eval gRun "case_compound_int"

/-- info: "0" -/
#guard_msgs in #eval gRun "case_compound_long"

/-- info: "112" -/
#guard_msgs in #eval gRun "case_compound_uint"

end KotlinIntWidth
end Autoform.Core
