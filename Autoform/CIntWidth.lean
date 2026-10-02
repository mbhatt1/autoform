import Autoform.CIntWidthProgram

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

#eval ["case_long_mul", "case_int_mul_wraps", "case_mixed_mul", "case_shift_left_64",
  "case_tree_depth", "case_long_accumulate", "case_unsigned_underflow",
  "case_unsigned_init_widen", "case_u32_add_wraps", "case_u64_mul_wraps",
  "case_shift_right_u32", "case_shift_right_i32", "case_shift_right_u64",
  "case_shift_right_i64", "case_mixed_compare", "case_unsigned_div", "case_unsigned_neg",
  "case_u64_not", "case_u8_increment_wraps", "case_u8_compound_wraps",
  "case_size_t_underflow", "case_i64_div", "case_narrow_signed_char"].map fun c => (c, cRun c)

end CIntWidth
end Autoform.Core
