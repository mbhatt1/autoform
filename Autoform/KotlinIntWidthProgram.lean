import Autoform.Lang.Core.Semantics

-- Lean's default `maxRecDepth` (512) is a guard against runaway elaboration, not
-- a statement about reasonable programs. A deep-embedded function body is one
-- term, so the elaborator's recursion depth tracks the *source's* nesting depth:
-- Linux `lib/` hit the limit at two declarations and the whole module failed to
-- type-check. Raising it costs nothing for shallow modules and is the difference
-- between compiling a real codebase and not.
--
-- 8000 was not enough either. The binding constraint is not the nesting depth of
-- any one body (Ansible's deepest is 297) but the `funcs := [...]` list literal,
-- which elaborates as nested cons cells -- one frame or more per function, and
-- Ansible has 5,546. So the limit has to scale with the module's function count,
-- not with how deep its code happens to be.
set_option maxRecDepth 8496

-- Lean's default `maxHeartbeats` (200000) budgets ONE declaration's own
-- elaboration cost, separately from `maxRecDepth` above (which bounds nesting
-- depth, not total work). A single source file whose top-level declarations
-- carry a large static table -- SQLite's `test_vdbecov.c`, whose `<global>`
-- initializer alone is ~5.3M characters of generated Lean -- blows through the
-- default budget on that ONE declaration and fails with a `(deterministic)
-- timeout at isDefEq` error, unrelated to whether the translation is correct.
-- Unlike `maxRecDepth`, this does not scale with function COUNT (Ansible-style
-- corpora with thousands of small functions never hit it); it is one
-- pathologically large declaration, which no per-function-count formula would
-- predict, so this disables the budget outright rather than guessing a bigger
-- number that the next large static table would just exceed again. Scoped to
-- THIS generated file only (`set_option` here does not touch hand-written proof
-- files elsewhere in the project, which keep the default as a real safety net
-- against a genuine runaway elaboration bug while someone is editing them).
set_option maxHeartbeats 0

/-!
# KotlinIntWidth — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.KotlinIntWidth
open Autoform.Core

/-- `case_int_mul_wraps:int()`  (from `cases.kt`) -/
def f_case_int_mul_wraps_int__ : Func :=
  { name := "case_int_mul_wraps:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 100000)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 100000)))
                  (.ret (.binop "*:k32" (.name "a") (.name "b"))))))) }

/-- `case_long_mul:long()`  (from `cases.kt`) -/
def f_case_long_mul_long__ : Func :=
  { name := "case_long_mul:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 100000)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 100000)))
                  (.ret (.binop "*:k64" (.name "a") (.name "b"))))))) }

/-- `case_mixed_mul:long()`  (from `cases.kt`) -/
def f_case_mixed_mul_long__ : Func :=
  { name := "case_mixed_mul:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 3000000000)))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 2))) (.ret (.binop "*:k64" (.name "a") (.name "b"))))))) }

/-- `case_literal_is_long:long()`  (from `cases.kt`) -/
def f_case_literal_is_long_long__ : Func :=
  { name := "case_literal_is_long:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 3000000000)))
              (.ret (.binop "*:k64" (.name "a") (.lit (.int 2)))))) }

/-- `case_int_add_wraps:int()`  (from `cases.kt`) -/
def f_case_int_add_wraps_int__ : Func :=
  { name := "case_int_add_wraps:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 2147483647)))
              (.seq (.assign "x" (.binop "+:k32" (.name "x") (.lit (.int 1)))) (.ret (.name "x"))))) }

/-- `case_long_add_wraps:long()`  (from `cases.kt`) -/
def f_case_long_add_wraps_long__ : Func :=
  { name := "case_long_add_wraps:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 9223372036854775807)))
              (.seq (.assign "x" (.binop "+:k64" (.name "x") (.lit (.int 1)))) (.ret (.name "x"))))) }

/-- `case_long_accumulate:long()`  (from `cases.kt`) -/
def f_case_long_accumulate_long__ : Func :=
  { name := "case_long_accumulate:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "s" (.lit (.int 0)))
              (.seq
                .skip
                (.seq
                  (.assign "i" (.lit (.int 0)))
                  (.seq
                    (.loop
                      (.binop "<" (.name "i") (.lit (.int 3)))
                      (.seq
                        (.assign "s" (.binop "+:k64" (.name "s") (.lit (.int 2000000000))))
                        (.assign "i" (.binop "+:k32" (.name "i") (.lit (.int 1))))))
                    (.ret (.name "s"))))))) }

/-- `case_int_accumulate:int()`  (from `cases.kt`) -/
def f_case_int_accumulate_int__ : Func :=
  { name := "case_int_accumulate:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "s" (.lit (.int 0)))
              (.seq
                .skip
                (.seq
                  (.assign "i" (.lit (.int 0)))
                  (.seq
                    (.loop
                      (.binop "<" (.name "i") (.lit (.int 3)))
                      (.seq
                        (.assign "s" (.binop "+:k32" (.name "s") (.lit (.int 2000000000))))
                        (.assign "i" (.binop "+:k32" (.name "i") (.lit (.int 1))))))
                    (.ret (.name "s"))))))) }

/-- `case_byte_incr:byte()`  (from `cases.kt`) -/
def f_case_byte_incr_byte__ : Func :=
  { name := "case_byte_incr:byte()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "b" (.lit (.int 127)))
              (.seq
                (.assign "b" (.unop "cast:i8" (.binop "+:k32" (.name "b") (.lit (.int 1)))))
                (.ret (.name "b"))))) }

/-- `case_byte_plus_promotes:int()`  (from `cases.kt`) -/
def f_case_byte_plus_promotes_int__ : Func :=
  { name := "case_byte_plus_promotes:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 127)))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 1))) (.ret (.binop "+:k32" (.name "a") (.name "b"))))))) }

/-- `case_short_decr:short()`  (from `cases.kt`) -/
def f_case_short_decr_short__ : Func :=
  { name := "case_short_decr:short()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "s" (.unop "-:k32" (.lit (.int 32768))))
              (.seq
                (.assign "s" (.unop "cast:i16" (.binop "-:k32" (.name "s") (.lit (.int 1)))))
                (.ret (.name "s"))))) }

/-- `case_ubyte_incr:kotlin.UByte()`  (from `cases.kt`) -/
def f_case_ubyte_incr_kotlin_UByte__ : Func :=
  { name := "case_ubyte_incr:kotlin.UByte()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "b" (.lit (.int 255)))
              (.seq
                (.assign "b" (.unop "cast:u8" (.binop "+:q32" (.name "b") (.lit (.int 1)))))
                (.ret (.name "b"))))) }

/-- `case_ubyte_plus_promotes:kotlin.UInt()`  (from `cases.kt`) -/
def f_case_ubyte_plus_promotes_kotlin_UInt__ : Func :=
  { name := "case_ubyte_plus_promotes:kotlin.UInt()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 255)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 255)))
                  (.ret (.binop "+:q32" (.name "a") (.name "b"))))))) }

/-- `case_shl_masked_int:int()`  (from `cases.kt`) -/
def f_case_shl_masked_int_int__ : Func :=
  { name := "case_shl_masked_int:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 1)))
              (.ret (.binop "<<:k32" (.name "x") (.lit (.int 33)))))) }

/-- `case_shl_masked_long:long()`  (from `cases.kt`) -/
def f_case_shl_masked_long_long__ : Func :=
  { name := "case_shl_masked_long:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 1)))
              (.ret (.binop "<<:k64" (.name "x") (.lit (.int 65)))))) }

/-- `case_shl_long:long()`  (from `cases.kt`) -/
def f_case_shl_long_long__ : Func :=
  { name := "case_shl_long:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 1)))
              (.ret (.binop "<<:k64" (.name "x") (.lit (.int 33)))))) }

/-- `case_shr_int:int()`  (from `cases.kt`) -/
def f_case_shr_int_int__ : Func :=
  { name := "case_shr_int:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.unop "-:k32" (.lit (.int 16))))
              (.ret (.binop ">>:k32" (.name "x") (.lit (.int 1)))))) }

/-- `case_shr_long:long()`  (from `cases.kt`) -/
def f_case_shr_long_long__ : Func :=
  { name := "case_shr_long:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.unop "-:k64" (.lit (.int 4294967296))))
              (.ret (.binop ">>:k64" (.name "x") (.lit (.int 4)))))) }

/-- `case_ushr_int:int()`  (from `cases.kt`) -/
def f_case_ushr_int_int__ : Func :=
  { name := "case_ushr_int:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.unop "-:k32" (.lit (.int 1))))
              (.ret (.binop ">>>:k32" (.name "x") (.lit (.int 28)))))) }

/-- `case_ushr_long:long()`  (from `cases.kt`) -/
def f_case_ushr_long_long__ : Func :=
  { name := "case_ushr_long:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.unop "-:k64" (.lit (.int 1))))
              (.ret (.binop ">>>:k64" (.name "x") (.lit (.int 60)))))) }

/-- `case_shr_assign_style:int()`  (from `cases.kt`) -/
def f_case_shr_assign_style_int__ : Func :=
  { name := "case_shr_assign_style:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.unop "-:k32" (.lit (.int 16))))
              (.seq (.assign "x" (.binop ">>:k32" (.name "x") (.lit (.int 2)))) (.ret (.name "x"))))) }

/-- `case_uint_sub_wraps:kotlin.UInt()`  (from `cases.kt`) -/
def f_case_uint_sub_wraps_kotlin_UInt__ : Func :=
  { name := "case_uint_sub_wraps:kotlin.UInt()"
  , params := []
  , body := (.seq
            .skip
            (.seq (.assign "a" (.lit (.int 0))) (.ret (.binop "-:q32" (.name "a") (.lit (.int 1)))))) }

/-- `case_ulong_sub_wraps:kotlin.ULong()`  (from `cases.kt`) -/
def f_case_ulong_sub_wraps_kotlin_ULong__ : Func :=
  { name := "case_ulong_sub_wraps:kotlin.ULong()"
  , params := []
  , body := (.seq
            .skip
            (.seq (.assign "a" (.lit (.int 0))) (.ret (.binop "-:q64" (.name "a") (.lit (.int 1)))))) }

/-- `case_uint_mul_wraps:kotlin.UInt()`  (from `cases.kt`) -/
def f_case_uint_mul_wraps_kotlin_UInt__ : Func :=
  { name := "case_uint_mul_wraps:kotlin.UInt()"
  , params := []
  , body := (.seq
            .skip
            (.seq (.assign "a" (.lit (.int 65536))) (.ret (.binop "*:q32" (.name "a") (.name "a"))))) }

/-- `case_ulong_mul_wraps:kotlin.ULong()`  (from `cases.kt`) -/
def f_case_ulong_mul_wraps_kotlin_ULong__ : Func :=
  { name := "case_ulong_mul_wraps:kotlin.ULong()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 18446744073709551615)))
              (.ret (.binop "*:q64" (.name "a") (.lit (.int 2)))))) }

/-- `case_uint_div:kotlin.UInt()`  (from `cases.kt`) -/
def f_case_uint_div_kotlin_UInt__ : Func :=
  { name := "case_uint_div:kotlin.UInt()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 4294967295)))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 2))) (.ret (.binop "/:q32" (.name "a") (.name "b"))))))) }

/-- `case_uint_rem:kotlin.UInt()`  (from `cases.kt`) -/
def f_case_uint_rem_kotlin_UInt__ : Func :=
  { name := "case_uint_rem:kotlin.UInt()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 4294967295)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 10)))
                  (.ret (.binop "%:q32" (.name "a") (.name "b"))))))) }

/-- `case_uint_shr:kotlin.UInt()`  (from `cases.kt`) -/
def f_case_uint_shr_kotlin_UInt__ : Func :=
  { name := "case_uint_shr:kotlin.UInt()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 4294967295)))
              (.ret (.binop ">>:q32" (.name "a") (.lit (.int 1)))))) }

/-- `case_uint_shl_masked:kotlin.UInt()`  (from `cases.kt`) -/
def f_case_uint_shl_masked_kotlin_UInt__ : Func :=
  { name := "case_uint_shl_masked:kotlin.UInt()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 1)))
              (.ret (.binop "<<:q32" (.name "a") (.lit (.int 33)))))) }

/-- `case_ulong_shr:kotlin.ULong()`  (from `cases.kt`) -/
def f_case_ulong_shr_kotlin_ULong__ : Func :=
  { name := "case_ulong_shr:kotlin.ULong()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 18446744073709551615)))
              (.ret (.binop ">>:q64" (.name "a") (.lit (.int 60)))))) }

/-- `case_min_div:int()`  (from `cases.kt`) -/
def f_case_min_div_int__ : Func :=
  { name := "case_min_div:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign
                "m"
                (.binop "-:k32" (.unop "-:k32" (.lit (.int 2147483647))) (.lit (.int 1))))
              (.seq
                .skip
                (.seq
                  (.assign "d" (.unop "-:k32" (.lit (.int 1))))
                  (.ret (.binop "/:k32" (.name "m") (.name "d"))))))) }

/-- `case_min_rem:int()`  (from `cases.kt`) -/
def f_case_min_rem_int__ : Func :=
  { name := "case_min_rem:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign
                "m"
                (.binop "-:k32" (.unop "-:k32" (.lit (.int 2147483647))) (.lit (.int 1))))
              (.seq
                .skip
                (.seq
                  (.assign "d" (.unop "-:k32" (.lit (.int 1))))
                  (.ret (.binop "%:k32" (.name "m") (.name "d"))))))) }

/-- `case_long_min_div:long()`  (from `cases.kt`) -/
def f_case_long_min_div_long__ : Func :=
  { name := "case_long_min_div:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign
                "m"
                (.binop "-:k64" (.unop "-:k64" (.lit (.int 9223372036854775807))) (.lit (.int 1))))
              (.seq
                .skip
                (.seq
                  (.assign "d" (.unop "-:k64" (.lit (.int 1))))
                  (.ret (.binop "/:k64" (.name "m") (.name "d"))))))) }

/-- `case_long_div:long()`  (from `cases.kt`) -/
def f_case_long_div_long__ : Func :=
  { name := "case_long_div:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "d" (.unop "-:k64" (.lit (.int 7000000000))))
              (.ret (.binop "/:k64" (.name "d") (.lit (.int 2)))))) }

/-- `case_rem_sign:int()`  (from `cases.kt`) -/
def f_case_rem_sign_int__ : Func :=
  { name := "case_rem_sign:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.unop "-:k32" (.lit (.int 7))))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 3))) (.ret (.binop "%:k32" (.name "a") (.name "b"))))))) }

/-- `case_int_neg_min:int()`  (from `cases.kt`) -/
def f_case_int_neg_min_int__ : Func :=
  { name := "case_int_neg_min:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign
                "y"
                (.binop "-:k32" (.unop "-:k32" (.lit (.int 2147483647))) (.lit (.int 1))))
              (.ret (.unop "-:k32" (.name "y"))))) }

/-- `case_long_neg:long()`  (from `cases.kt`) -/
def f_case_long_neg_long__ : Func :=
  { name := "case_long_neg:long()"
  , params := []
  , body := (.seq .skip (.seq (.assign "y" (.lit (.int 5))) (.ret (.unop "-:k64" (.name "y"))))) }

/-- `case_div_zero:int()`  (from `cases.kt`) -/
def f_case_div_zero_int__ : Func :=
  { name := "case_div_zero:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 1)))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 0))) (.ret (.binop "/:k32" (.name "a") (.name "b"))))))) }

/-- `case_long_rem_zero:long()`  (from `cases.kt`) -/
def f_case_long_rem_zero_long__ : Func :=
  { name := "case_long_rem_zero:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 1)))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 0))) (.ret (.binop "%:k64" (.name "a") (.name "b"))))))) }

/-- `case_uint_div_zero:kotlin.UInt()`  (from `cases.kt`) -/
def f_case_uint_div_zero_kotlin_UInt__ : Func :=
  { name := "case_uint_div_zero:kotlin.UInt()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 1)))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 0))) (.ret (.binop "/:q32" (.name "a") (.name "b"))))))) }

/-- `case_int_inv:int()`  (from `cases.kt`) -/
def f_case_int_inv_int__ : Func :=
  { name := "case_int_inv:int()"
  , params := []
  , body := (.seq .skip (.seq (.assign "a" (.lit (.int 5))) (.ret (.unop "~:k32" (.name "a"))))) }

/-- `case_long_inv:long()`  (from `cases.kt`) -/
def f_case_long_inv_long__ : Func :=
  { name := "case_long_inv:long()"
  , params := []
  , body := (.seq .skip (.seq (.assign "a" (.lit (.int 0))) (.ret (.unop "~:k64" (.name "a"))))) }

/-- `case_uint_inv:kotlin.UInt()`  (from `cases.kt`) -/
def f_case_uint_inv_kotlin_UInt__ : Func :=
  { name := "case_uint_inv:kotlin.UInt()"
  , params := []
  , body := (.seq .skip (.seq (.assign "a" (.lit (.int 0))) (.ret (.unop "~:q32" (.name "a"))))) }

/-- `case_ubyte_inv:kotlin.UByte()`  (from `cases.kt`) -/
def f_case_ubyte_inv_kotlin_UByte__ : Func :=
  { name := "case_ubyte_inv:kotlin.UByte()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 5)))
              (.ret (.unop "cast:u8" (.unop "~:q32" (.name "a")))))) }

/-- `case_and_or_xor:int()`  (from `cases.kt`) -/
def f_case_and_or_xor_int__ : Func :=
  { name := "case_and_or_xor:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 12)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 10)))
                  (.ret
                    (.binop
                      "+:k32"
                      (.binop
                        "+:k32"
                        (.binop "&:k32" (.name "a") (.name "b"))
                        (.binop "*:k32" (.binop "|:k32" (.name "a") (.name "b")) (.lit (.int 100))))
                      (.binop "*:k32" (.binop "^:k32" (.name "a") (.name "b")) (.lit (.int 10000))))))))) }

/-- `case_long_and:long()`  (from `cases.kt`) -/
def f_case_long_and_long__ : Func :=
  { name := "case_long_and:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.unop "-:k64" (.lit (.int 1))))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 4294967295)))
                  (.ret (.binop "&:k64" (.name "a") (.name "b"))))))) }

/-- `case_uint_xor:kotlin.UInt()`  (from `cases.kt`) -/
def f_case_uint_xor_kotlin_UInt__ : Func :=
  { name := "case_uint_xor:kotlin.UInt()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 4294967295)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 255)))
                  (.ret (.binop "^:q32" (.name "a") (.name "b"))))))) }

/-- `case_to_int_trunc:int()`  (from `cases.kt`) -/
def f_case_to_int_trunc_int__ : Func :=
  { name := "case_to_int_trunc:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq (.assign "x" (.lit (.int 4294967297))) (.ret (.unop "cast:i32" (.name "x"))))) }

/-- `case_to_long_sign_extends:long()`  (from `cases.kt`) -/
def f_case_to_long_sign_extends_long__ : Func :=
  { name := "case_to_long_sign_extends:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.unop "-:k32" (.lit (.int 5))))
              (.ret (.unop "cast:i64" (.name "x"))))) }

/-- `case_to_byte_trunc:byte()`  (from `cases.kt`) -/
def f_case_to_byte_trunc_byte__ : Func :=
  { name := "case_to_byte_trunc:byte()"
  , params := []
  , body := (.seq .skip (.seq (.assign "x" (.lit (.int 300))) (.ret (.unop "cast:i8" (.name "x"))))) }

/-- `case_to_uint_reinterpret:kotlin.UInt()`  (from `cases.kt`) -/
def f_case_to_uint_reinterpret_kotlin_UInt__ : Func :=
  { name := "case_to_uint_reinterpret:kotlin.UInt()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.unop "-:k32" (.lit (.int 1))))
              (.ret (.unop "cast:u32" (.name "x"))))) }

/-- `case_to_ulong_sign_extends:kotlin.ULong()`  (from `cases.kt`) -/
def f_case_to_ulong_sign_extends_kotlin_ULong__ : Func :=
  { name := "case_to_ulong_sign_extends:kotlin.ULong()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.unop "-:k32" (.lit (.int 1))))
              (.ret (.unop "cast:u64" (.name "x"))))) }

/-- `case_uint_to_int:int()`  (from `cases.kt`) -/
def f_case_uint_to_int_int__ : Func :=
  { name := "case_uint_to_int:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq (.assign "x" (.lit (.int 4294967295))) (.ret (.unop "cast:i32" (.name "x"))))) }

/-- `case_uint_to_long:long()`  (from `cases.kt`) -/
def f_case_uint_to_long_long__ : Func :=
  { name := "case_uint_to_long:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq (.assign "x" (.lit (.int 4294967295))) (.ret (.unop "cast:i64" (.name "x"))))) }

/-- `case_long_to_uint:kotlin.UInt()`  (from `cases.kt`) -/
def f_case_long_to_uint_kotlin_UInt__ : Func :=
  { name := "case_long_to_uint:kotlin.UInt()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.unop "-:k64" (.lit (.int 1))))
              (.ret (.unop "cast:u32" (.name "x"))))) }

/-- `case_uint_gt:boolean()`  (from `cases.kt`) -/
def f_case_uint_gt_boolean__ : Func :=
  { name := "case_uint_gt:boolean()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 4294967295)))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 1))) (.ret (.binop ">" (.name "a") (.name "b"))))))) }

/-- `case_int_long_compare:boolean()`  (from `cases.kt`) -/
def f_case_int_long_compare_boolean__ : Func :=
  { name := "case_int_long_compare:boolean()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 3000000000)))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 1))) (.ret (.binop ">" (.name "a") (.name "b"))))))) }

/-- `case_conditional:long()`  (from `cases.kt`) -/
def f_case_conditional_long__ : Func :=
  { name := "case_conditional:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 100000)))
              (.ret
                (.cond
                  (.binop ">" (.name "a") (.lit (.int 0)))
                  (.binop "*:k64" (.name "a") (.name "a"))
                  (.name "a"))))) }

/-- `case_compound_int:int()`  (from `cases.kt`) -/
def f_case_compound_int_int__ : Func :=
  { name := "case_compound_int:int()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 100)))
              (.seq
                (.assign "x" (.binop "+:k32" (.name "x") (.lit (.int 5))))
                (.seq
                  (.assign "x" (.binop "*:k32" (.name "x") (.lit (.int 2))))
                  (.seq
                    (.assign "x" (.binop "-:k32" (.name "x") (.lit (.int 1))))
                    (.seq
                      (.assign "x" (.binop "/:k32" (.name "x") (.lit (.int 3))))
                      (.seq
                        (.assign "x" (.binop "%:k32" (.name "x") (.lit (.int 7))))
                        (.seq
                          (.assign "x" (.binop "<<:k32" (.name "x") (.lit (.int 29))))
                          (.ret (.name "x")))))))))) }

/-- `case_compound_long:long()`  (from `cases.kt`) -/
def f_case_compound_long_long__ : Func :=
  { name := "case_compound_long:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 4611686018427387904)))
              (.seq
                (.assign "x" (.binop "+:k64" (.name "x") (.name "x")))
                (.seq
                  (.assign "x" (.binop "*:k64" (.name "x") (.lit (.int 2))))
                  (.seq
                    (.assign "x" (.binop "%:k64" (.name "x") (.lit (.int 1000))))
                    (.ret (.name "x"))))))) }

/-- `case_compound_uint:kotlin.UInt()`  (from `cases.kt`) -/
def f_case_compound_uint_kotlin_UInt__ : Func :=
  { name := "case_compound_uint:kotlin.UInt()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 4000000000)))
              (.seq
                (.assign "x" (.binop "+:q32" (.name "x") (.lit (.int 500000000))))
                (.seq
                  (.assign "x" (.binop "*:q32" (.name "x") (.lit (.int 3))))
                  (.seq
                    (.assign "x" (.binop "%:q32" (.name "x") (.lit (.int 1000))))
                    (.ret (.name "x"))))))) }

/-- `cases.kt:<global>.global`  (from `cases.kt`) -/
def f_cases_kt__global__global : Func :=
  { name := "cases.kt:<global>.global"
  , params := []
  , body := (.seq
            (.hole "stmt:METHOD")
            (.seq
              (.hole "stmt:METHOD")
              (.seq
                (.hole "stmt:METHOD")
                (.seq
                  (.hole "stmt:METHOD")
                  (.seq
                    (.hole "stmt:METHOD")
                    (.seq
                      (.hole "stmt:METHOD")
                      (.seq
                        (.hole "stmt:METHOD")
                        (.seq
                          (.hole "stmt:METHOD")
                          (.seq
                            (.hole "stmt:METHOD")
                            (.seq
                              (.hole "stmt:METHOD")
                              (.seq
                                (.hole "stmt:METHOD")
                                (.seq
                                  (.hole "stmt:METHOD")
                                  (.seq
                                    (.hole "stmt:METHOD")
                                    (.seq
                                      (.hole "stmt:METHOD")
                                      (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq
                                        (.hole "stmt:METHOD")
                                        (.seq (.hole "stmt:METHOD") (.hole "stmt:METHOD"))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_case_int_mul_wraps_int__,
  f_case_long_mul_long__,
  f_case_mixed_mul_long__,
  f_case_literal_is_long_long__,
  f_case_int_add_wraps_int__,
  f_case_long_add_wraps_long__,
  f_case_long_accumulate_long__,
  f_case_int_accumulate_int__,
  f_case_byte_incr_byte__,
  f_case_byte_plus_promotes_int__,
  f_case_short_decr_short__,
  f_case_ubyte_incr_kotlin_UByte__,
  f_case_ubyte_plus_promotes_kotlin_UInt__,
  f_case_shl_masked_int_int__,
  f_case_shl_masked_long_long__,
  f_case_shl_long_long__,
  f_case_shr_int_int__,
  f_case_shr_long_long__,
  f_case_ushr_int_int__,
  f_case_ushr_long_long__,
  f_case_shr_assign_style_int__,
  f_case_uint_sub_wraps_kotlin_UInt__,
  f_case_ulong_sub_wraps_kotlin_ULong__,
  f_case_uint_mul_wraps_kotlin_UInt__,
  f_case_ulong_mul_wraps_kotlin_ULong__,
  f_case_uint_div_kotlin_UInt__,
  f_case_uint_rem_kotlin_UInt__,
  f_case_uint_shr_kotlin_UInt__,
  f_case_uint_shl_masked_kotlin_UInt__,
  f_case_ulong_shr_kotlin_ULong__,
  f_case_min_div_int__,
  f_case_min_rem_int__,
  f_case_long_min_div_long__,
  f_case_long_div_long__,
  f_case_rem_sign_int__,
  f_case_int_neg_min_int__,
  f_case_long_neg_long__,
  f_case_div_zero_int__,
  f_case_long_rem_zero_long__,
  f_case_uint_div_zero_kotlin_UInt__,
  f_case_int_inv_int__,
  f_case_long_inv_long__,
  f_case_uint_inv_kotlin_UInt__,
  f_case_ubyte_inv_kotlin_UByte__,
  f_case_and_or_xor_int__,
  f_case_long_and_long__,
  f_case_uint_xor_kotlin_UInt__,
  f_case_to_int_trunc_int__,
  f_case_to_long_sign_extends_long__,
  f_case_to_byte_trunc_byte__,
  f_case_to_uint_reinterpret_kotlin_UInt__,
  f_case_to_ulong_sign_extends_kotlin_ULong__,
  f_case_uint_to_int_int__,
  f_case_uint_to_long_long__,
  f_case_long_to_uint_kotlin_UInt__,
  f_case_uint_gt_boolean__,
  f_case_int_long_compare_boolean__,
  f_case_conditional_long__,
  f_case_compound_int_int__,
  f_case_compound_long_long__,
  f_case_compound_uint_kotlin_UInt__,
  f_cases_kt__global__global
] }

end Autoform.Generated.KotlinIntWidth