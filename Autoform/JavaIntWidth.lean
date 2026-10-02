import Autoform.JavaIntWidthProgram

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

#eval ["case_long_mul", "case_int_mul_wraps", "case_mixed_mul", "case_long_accumulate",
  "case_int_add_wraps", "case_ushr_int", "case_shr_int", "case_ushr_long", "case_shr_long",
  "case_shr_assign", "case_shl_masked_int", "case_shl_long", "case_byte_compound",
  "case_byte_increment", "case_char_increment", "case_int_compound_long", "case_min_div",
  "case_min_rem", "case_long_div", "case_long_not", "case_int_neg_min",
  "case_boxed_mul"].map fun c => (c, jRun c)

end JavaIntWidth
end Autoform.Core
