import Autoform.JavaIntWidthProgram

/-!
# Width-typed Java integer arithmetic, checked against `java`

Java shares `.cLike` with C, so until item O Java `long` arithmetic was computed at 32
bits (STRATEGY §29 item 5: `100000L * 100000L` gave 1410065408). The exporter now types
Java integer operators by binary numeric promotion (`"*:j64"`, `"+:j32"`;
`Lang/Core/TypedInt.lean`: wrapping, shift counts masked, `MIN / -1 = MIN`) and narrows
compound assignments back to `byte`/`short`/`char`/`int` (JLS 15.26.2).

It also reads `>>` and `>>>` from the source token: javasrc2cpg 4.0.606 names `x >>> 28`
`<operator>.arithmeticShiftRight` and `x >> 1` `<operator>.logicalShiftRight`, so each was
translated as the other (`-16 >> 1` gave 2147483640).

`Autoform/JavaIntWidthProgram.lean` is the rendered export of
`tests/fixtures/javaintwidth/JavaIntWidth.java` (javasrc2cpg 4.0.606; see that fixture's
`provenance.json`). Every `case_*` method is pinned here with `#guard_msgs`;
`tests/test_javaintwidth_java.py` compiles and runs the same file with `javac`/`java`
and fails if any pin is not Java's value. With the exporter of the integration head
before item O, 7 of these 22 agreed with Java, 11 were silent wrong answers and 4 were
holes (`docs/scale.md`).
-/

namespace Autoform.Core
namespace JavaIntWidth

def showR : EResult → String
  | .val (.int i)   => toString i
  | .val (.bool b)  => if b then "bool true" else "bool false"
  | .val _          => "<non-integer value>"
  | .exn _          => "<exception>"
  | .hole l         => "hole " ++ l
  | .outOfFuel      => "outOfFuel"

open Autoform.Generated.JavaIntWidth in
def jRun (c : String) : String := showR (runFunc program 400 s!"JavaIntWidth.{c}:long()" [])

/-- info: "10000000000" -/
#guard_msgs in #eval jRun "case_long_mul"

/-- info: "1410065408" -/
#guard_msgs in #eval jRun "case_int_mul_wraps"

/-- info: "6000000000" -/
#guard_msgs in #eval jRun "case_mixed_mul"

/-- info: "6000000000" -/
#guard_msgs in #eval jRun "case_long_accumulate"

/-- info: "-2147483648" -/
#guard_msgs in #eval jRun "case_int_add_wraps"

/-- info: "15" -/
#guard_msgs in #eval jRun "case_ushr_int"

/-- info: "-8" -/
#guard_msgs in #eval jRun "case_shr_int"

/-- info: "15" -/
#guard_msgs in #eval jRun "case_ushr_long"

/-- info: "-268435456" -/
#guard_msgs in #eval jRun "case_shr_long"

/-- info: "-4" -/
#guard_msgs in #eval jRun "case_shr_assign"

/-- info: "2" -/
#guard_msgs in #eval jRun "case_shl_masked_int"

/-- info: "8589934592" -/
#guard_msgs in #eval jRun "case_shl_long"

/-- info: "-128" -/
#guard_msgs in #eval jRun "case_byte_compound"

/-- info: "-128" -/
#guard_msgs in #eval jRun "case_byte_increment"

/-- info: "0" -/
#guard_msgs in #eval jRun "case_char_increment"

/-- info: "1" -/
#guard_msgs in #eval jRun "case_int_compound_long"

/-- info: "-2147483648" -/
#guard_msgs in #eval jRun "case_min_div"

/-- info: "0" -/
#guard_msgs in #eval jRun "case_min_rem"

/-- info: "-3500000000" -/
#guard_msgs in #eval jRun "case_long_div"

/-- info: "-1" -/
#guard_msgs in #eval jRun "case_long_not"

/-- info: "-2147483648" -/
#guard_msgs in #eval jRun "case_int_neg_min"

/-- info: "10000000000" -/
#guard_msgs in #eval jRun "case_boxed_mul"

end JavaIntWidth
end Autoform.Core
