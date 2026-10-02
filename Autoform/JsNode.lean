import Autoform.JsNodeProgram

/-!
# JavaScript `==`/`===`, `>>`/`>>>`, `??` and `null`/`undefined`, checked against Node

jssrc2cpg 4.0.606 erases three distinctions the language makes: `==` and `===` are both
`<operator>.equals` (likewise `!=`/`!==`), `>>` and `>>>` are both
`<operator>.arithmeticShiftRight`, and `a ?? b` is `<operator>.logicalOr`, the operator of
`a || b`. `cartographer/export_ast.sc` recovers the token from the call's source text. Until
item R that was only ever run on synthetic spans: jssrc2cpg was not installed here, so no JS
CPG had been exported by the current exporter (STRATEGY section 64).

`Autoform/JsNodeProgram.lean` is the rendered export of
`tests/fixtures/jsnode/jsnode_cases.js` from a real jssrc2cpg 4.0.606 CPG (see that
fixture's `provenance.json`). Every `case_*` function is run here and pinned with
`#guard_msgs`; `tests/test_jsnode_node.py` runs the same file under Node and fails if any
pin is not Node's value. A string result is shown as `str:<contents>`.

The `null`/`undefined` cases are the ones a single `Val.unit` could not answer
(`null === undefined` was the hole `js:===:null-vs-undefined`): JS `null` is now
`Val.jsnull`, and `Val.unit` is `undefined`.
-/

namespace Autoform.Core
namespace JsNode

def showR : EResult → String
  | .val (.int i)   => toString i
  | .val (.bool b)  => if b then "bool true" else "bool false"
  | .val (.str s)   => "str:" ++ s
  | .val _          => "<other value>"
  | .exn _          => "<exception>"
  | .hole l         => "hole " ++ l
  | .outOfFuel      => "outOfFuel"

open Autoform.Generated.JsNode in
def jRun (c : String) : String := showR (runFunc program 400 s!"jsnode_cases.js::program:{c}" [])

/-- info: "bool false" -/
#guard_msgs in #eval jRun "case_strict_str_vs_num"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_loose_same_type"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_strict_same_type"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_strict_ne_cross"

/-- info: "bool false" -/
#guard_msgs in #eval jRun "case_loose_ne_same"

/-- info: "bool false" -/
#guard_msgs in #eval jRun "case_strict_ne_same"

/-- info: "bool false" -/
#guard_msgs in #eval jRun "case_strict_bool_vs_num"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_single_quote_eq"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_single_quote_ne"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_single_quote_cross"

/-- info: "bool false" -/
#guard_msgs in #eval jRun "case_strict_nan"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_nan_ne"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_inf_strict"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_inf_vs_big"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_strict_negzero"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_strict_int_float"

/-- info: "bool false" -/
#guard_msgs in #eval jRun "case_null_loose_zero"

/-- info: "bool false" -/
#guard_msgs in #eval jRun "case_zero_loose_null"

/-- info: "bool false" -/
#guard_msgs in #eval jRun "case_empty_str_loose_null"

/-- info: "bool false" -/
#guard_msgs in #eval jRun "case_false_loose_null"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_null_loose_null"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_undef_loose_null"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_null_loose_undef"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_null_ne_zero"

/-- info: "bool false" -/
#guard_msgs in #eval jRun "case_null_ne_null"

/-- info: "bool false" -/
#guard_msgs in #eval jRun "case_zero_strict_null"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_null_strict_null"

/-- info: "bool false" -/
#guard_msgs in #eval jRun "case_null_strict_undefined"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_undef_strict_undef"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_null_strict_ne_undefined"

/-- info: "-1" -/
#guard_msgs in #eval jRun "case_sar_neg"

/-- info: "4294967295" -/
#guard_msgs in #eval jRun "case_shr_neg"

/-- info: "-4" -/
#guard_msgs in #eval jRun "case_sar_neg16"

/-- info: "15" -/
#guard_msgs in #eval jRun "case_shr_neg16"

/-- info: "-2147483648" -/
#guard_msgs in #eval jRun "case_shl_sign"

/-- info: "2147483647" -/
#guard_msgs in #eval jRun "case_shr_var"

/-- info: "-1" -/
#guard_msgs in #eval jRun "case_sar_var_call"

/-- info: "0" -/
#guard_msgs in #eval jRun "case_nullish_zero"

/-- info: "str:" -/
#guard_msgs in #eval jRun "case_nullish_empty"

/-- info: "bool false" -/
#guard_msgs in #eval jRun "case_nullish_false"

/-- info: "5" -/
#guard_msgs in #eval jRun "case_nullish_null"

/-- info: "7" -/
#guard_msgs in #eval jRun "case_nullish_undef"

/-- info: "3" -/
#guard_msgs in #eval jRun "case_nullish_chain"

/-- info: "9" -/
#guard_msgs in #eval jRun "case_nullish_value"

/-- info: "str:" -/
#guard_msgs in #eval jRun "case_nullish_single_quote"

/-- info: "str:d" -/
#guard_msgs in #eval jRun "case_nullish_single_quote_null"

/-- info: "0" -/
#guard_msgs in #eval jRun "case_nullish_var_zero"

/-- info: "5" -/
#guard_msgs in #eval jRun "case_nullish_var_null"

/-- info: "0" -/
#guard_msgs in #eval jRun "case_nullish_short_circuit"

/-- info: "18" -/
#guard_msgs in #eval jRun "case_nullish_right_effect"

/-- info: "1" -/
#guard_msgs in #eval jRun "case_nullish_impure_left"

/-- info: "bool true" -/
#guard_msgs in #eval jRun "case_nullish_in_cond"

/-- info: "5" -/
#guard_msgs in #eval jRun "case_or_zero"

/-- info: "0" -/
#guard_msgs in #eval jRun "case_and_zero"

/-- info: "8" -/
#guard_msgs in #eval jRun "case_or_then_nullish"

end JsNode
end Autoform.Core
