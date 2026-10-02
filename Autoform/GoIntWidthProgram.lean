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
set_option maxRecDepth 8456

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
# GoIntWidth — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.GoIntWidth
open Autoform.Core

/-- `main.case_int_mul`  (from `cases.go`) -/
def f_main_case_int_mul : Func :=
  { name := "main.case_int_mul"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "m" (.lit (.int 100000)))
              (.ret (.binop "*:g64" (.name "m") (.name "m"))))) }

/-- `main.case_int_add_wraps`  (from `cases.go`) -/
def f_main_case_int_add_wraps : Func :=
  { name := "main.case_int_add_wraps"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 9223372036854775807)))
              (.seq (.assign "x" (.binop "+:g64" (.name "x") (.lit (.int 1)))) (.ret (.name "x"))))) }

/-- `main.case_int32_mul_wraps`  (from `cases.go`) -/
def f_main_case_int32_mul_wraps : Func :=
  { name := "main.case_int32_mul_wraps"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 100000)))
              (.ret (.binop "*:g32" (.name "a") (.name "a"))))) }

/-- `main.case_int64_mul`  (from `cases.go`) -/
def f_main_case_int64_mul : Func :=
  { name := "main.case_int64_mul"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 100000)))
              (.ret (.binop "*:g64" (.name "a") (.name "a"))))) }

/-- `main.case_int8_add_wraps`  (from `cases.go`) -/
def f_main_case_int8_add_wraps : Func :=
  { name := "main.case_int8_add_wraps"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 127)))
              (.seq (.assign "a" (.binop "+:g08" (.name "a") (.lit (.int 1)))) (.ret (.name "a"))))) }

/-- `main.case_int8_incr`  (from `cases.go`) -/
def f_main_case_int8_incr : Func :=
  { name := "main.case_int8_incr"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 127)))
              (.seq (.assign "a" (.binop "+:g08" (.name "a") (.lit (.int 1)))) (.ret (.name "a"))))) }

/-- `main.case_int16_compound`  (from `cases.go`) -/
def f_main_case_int16_compound : Func :=
  { name := "main.case_int16_compound"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 32767)))
              (.seq (.assign "a" (.binop "+:g16" (.name "a") (.lit (.int 2)))) (.ret (.name "a"))))) }

/-- `main.case_uint8_sub_wraps`  (from `cases.go`) -/
def f_main_case_uint8_sub_wraps : Func :=
  { name := "main.case_uint8_sub_wraps"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 0)))
              (.seq (.assign "a" (.binop "-:w08" (.name "a") (.lit (.int 1)))) (.ret (.name "a"))))) }

/-- `main.case_byte_add_wraps`  (from `cases.go`) -/
def f_main_case_byte_add_wraps : Func :=
  { name := "main.case_byte_add_wraps"
  , params := []
  , body := (.seq
            .skip
            (.seq (.assign "b" (.lit (.int 200))) (.ret (.binop "+:w08" (.name "b") (.name "b"))))) }

/-- `main.case_rune_add_wraps`  (from `cases.go`) -/
def f_main_case_rune_add_wraps : Func :=
  { name := "main.case_rune_add_wraps"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "r" (.lit (.int 2147483647)))
              (.ret (.binop "+:g32" (.name "r") (.lit (.int 1)))))) }

/-- `main.case_uint32_mul_wraps`  (from `cases.go`) -/
def f_main_case_uint32_mul_wraps : Func :=
  { name := "main.case_uint32_mul_wraps"
  , params := []
  , body := (.seq
            .skip
            (.seq (.assign "a" (.lit (.int 65536))) (.ret (.binop "*:w32" (.name "a") (.name "a"))))) }

/-- `main.case_uint64_mul_wraps`  (from `cases.go`) -/
def f_main_case_uint64_mul_wraps : Func :=
  { name := "main.case_uint64_mul_wraps"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 9223372036854775808)))
              (.ret (.binop "*:w64" (.name "a") (.lit (.int 2)))))) }

/-- `main.case_uint64_sub_wraps`  (from `cases.go`) -/
def f_main_case_uint64_sub_wraps : Func :=
  { name := "main.case_uint64_sub_wraps"
  , params := []
  , body := (.seq
            .skip
            (.seq (.assign "a" (.lit (.int 0))) (.ret (.binop "-:w64" (.name "a") (.lit (.int 1)))))) }

/-- `main.case_uint_sub_wraps`  (from `cases.go`) -/
def f_main_case_uint_sub_wraps : Func :=
  { name := "main.case_uint_sub_wraps"
  , params := []
  , body := (.seq
            .skip
            (.seq (.assign "a" (.lit (.int 0))) (.ret (.binop "-:w64" (.name "a") (.lit (.int 1)))))) }

/-- `main.case_uintptr_sub_wraps`  (from `cases.go`) -/
def f_main_case_uintptr_sub_wraps : Func :=
  { name := "main.case_uintptr_sub_wraps"
  , params := []
  , body := (.seq
            .skip
            (.seq (.assign "p" (.lit (.int 0))) (.ret (.binop "-:w64" (.name "p") (.lit (.int 1)))))) }

/-- `main.case_uint16_neg`  (from `cases.go`) -/
def f_main_case_uint16_neg : Func :=
  { name := "main.case_uint16_neg"
  , params := []
  , body := (.seq .skip (.seq (.assign "a" (.lit (.int 1))) (.ret (.unop "-:w16" (.name "a"))))) }

/-- `main.case_int_neg_min`  (from `cases.go`) -/
def f_main_case_int_neg_min : Func :=
  { name := "main.case_int_neg_min"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "y" (.lit (.int (-9223372036854775808))))
              (.ret (.unop "-:g64" (.name "y"))))) }

/-- `main.case_uint8_complement`  (from `cases.go`) -/
def f_main_case_uint8_complement : Func :=
  { name := "main.case_uint8_complement"
  , params := []
  , body := (.seq .skip (.seq (.assign "x" (.lit (.int 5))) (.ret (.unop "~:w08" (.name "x"))))) }

/-- `main.case_int64_complement`  (from `cases.go`) -/
def f_main_case_int64_complement : Func :=
  { name := "main.case_int64_complement"
  , params := []
  , body := (.seq .skip (.seq (.assign "z" (.lit (.int 0))) (.ret (.unop "~:g64" (.name "z"))))) }

/-- `main.case_and_not`  (from `cases.go`) -/
def f_main_case_and_not : Func :=
  { name := "main.case_and_not"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 255)))
              (.seq
                .skip
                (.seq
                  (.assign "y" (.lit (.int 15)))
                  (.ret (.binop "&^:w08" (.name "x") (.name "y"))))))) }

/-- `main.case_min_div`  (from `cases.go`) -/
def f_main_case_min_div : Func :=
  { name := "main.case_min_div"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "m" (.lit (.int (-9223372036854775808))))
              (.seq
                .skip
                (.seq
                  (.assign "d" (.lit (.int (-1))))
                  (.ret (.binop "/:g64" (.name "m") (.name "d"))))))) }

/-- `main.case_min_rem`  (from `cases.go`) -/
def f_main_case_min_rem : Func :=
  { name := "main.case_min_rem"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "m" (.lit (.int (-9223372036854775808))))
              (.seq
                .skip
                (.seq
                  (.assign "d" (.lit (.int (-1))))
                  (.ret (.binop "%:g64" (.name "m") (.name "d"))))))) }

/-- `main.case_int8_min_div`  (from `cases.go`) -/
def f_main_case_int8_min_div : Func :=
  { name := "main.case_int8_min_div"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "m" (.lit (.int (-128))))
              (.seq
                .skip
                (.seq
                  (.assign "d" (.lit (.int (-1))))
                  (.ret (.binop "/:g08" (.name "m") (.name "d"))))))) }

/-- `main.case_div_trunc`  (from `cases.go`) -/
def f_main_case_div_trunc : Func :=
  { name := "main.case_div_trunc"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int (-7))))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 2))) (.ret (.binop "/:g64" (.name "a") (.name "b"))))))) }

/-- `main.case_rem_sign`  (from `cases.go`) -/
def f_main_case_rem_sign : Func :=
  { name := "main.case_rem_sign"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int (-7))))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 3))) (.ret (.binop "%:g64" (.name "a") (.name "b"))))))) }

/-- `main.case_uint32_div`  (from `cases.go`) -/
def f_main_case_uint32_div : Func :=
  { name := "main.case_uint32_div"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 4294967295)))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 2))) (.ret (.binop "/:w32" (.name "a") (.name "b"))))))) }

/-- `main.case_shl_over_width`  (from `cases.go`) -/
def f_main_case_shl_over_width : Func :=
  { name := "main.case_shl_over_width"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 1)))
              (.seq
                .skip
                (.seq
                  (.assign "n" (.lit (.int 33)))
                  (.ret (.binop "<<:g32" (.name "x") (.name "n"))))))) }

/-- `main.case_shl_in_width`  (from `cases.go`) -/
def f_main_case_shl_in_width : Func :=
  { name := "main.case_shl_in_width"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 1)))
              (.seq
                .skip
                (.seq
                  (.assign "n" (.lit (.int 31)))
                  (.ret (.binop "<<:g32" (.name "x") (.name "n"))))))) }

/-- `main.case_shl_int64`  (from `cases.go`) -/
def f_main_case_shl_int64 : Func :=
  { name := "main.case_shl_int64"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 1)))
              (.seq
                .skip
                (.seq
                  (.assign "n" (.lit (.int 63)))
                  (.ret (.binop "<<:g64" (.name "x") (.name "n"))))))) }

/-- `main.case_shr_over_width_neg`  (from `cases.go`) -/
def f_main_case_shr_over_width_neg : Func :=
  { name := "main.case_shr_over_width_neg"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int (-8))))
              (.seq
                .skip
                (.seq
                  (.assign "n" (.lit (.int 40)))
                  (.ret (.binop ">>:g32" (.name "x") (.name "n"))))))) }

/-- `main.case_shr_over_width_pos`  (from `cases.go`) -/
def f_main_case_shr_over_width_pos : Func :=
  { name := "main.case_shr_over_width_pos"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 8)))
              (.seq
                .skip
                (.seq
                  (.assign "n" (.lit (.int 40)))
                  (.ret (.binop ">>:g32" (.name "x") (.name "n"))))))) }

/-- `main.case_shr_arith`  (from `cases.go`) -/
def f_main_case_shr_arith : Func :=
  { name := "main.case_shr_arith"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int (-16))))
              (.seq
                .skip
                (.seq
                  (.assign "n" (.lit (.int 2)))
                  (.ret (.binop ">>:g32" (.name "x") (.name "n"))))))) }

/-- `main.case_shr_uint`  (from `cases.go`) -/
def f_main_case_shr_uint : Func :=
  { name := "main.case_shr_uint"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 4294967295)))
              (.seq
                .skip
                (.seq
                  (.assign "n" (.lit (.int 28)))
                  (.ret (.binop ">>:w32" (.name "x") (.name "n"))))))) }

/-- `main.case_shl_count_type`  (from `cases.go`) -/
def f_main_case_shl_count_type : Func :=
  { name := "main.case_shl_count_type"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 1)))
              (.seq
                .skip
                (.seq
                  (.assign "n" (.lit (.int 7)))
                  (.ret (.binop "<<:w08" (.name "x") (.name "n"))))))) }

/-- `main.case_shl_signed_count`  (from `cases.go`) -/
def f_main_case_shl_signed_count : Func :=
  { name := "main.case_shl_signed_count"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 1)))
              (.seq
                .skip
                (.seq
                  (.assign "n" (.lit (.int 62)))
                  (.ret (.binop "<<:g64" (.name "x") (.name "n"))))))) }

/-- `main.case_shl_drops_bits`  (from `cases.go`) -/
def f_main_case_shl_drops_bits : Func :=
  { name := "main.case_shl_drops_bits"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 255)))
              (.seq
                .skip
                (.seq
                  (.assign "n" (.lit (.int 4)))
                  (.ret (.binop "<<:w08" (.name "x") (.name "n"))))))) }

/-- `main.case_uint32_gt`  (from `cases.go`) -/
def f_main_case_uint32_gt : Func :=
  { name := "main.case_uint32_gt"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 4294967295)))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 1))) (.ret (.binop ">" (.name "a") (.name "b"))))))) }

/-- `main.case_int8_lt`  (from `cases.go`) -/
def f_main_case_int8_lt : Func :=
  { name := "main.case_int8_lt"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int (-1))))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 1))) (.ret (.binop "<" (.name "a") (.name "b"))))))) }

/-- `main.case_int_accumulate`  (from `cases.go`) -/
def f_main_case_int_accumulate : Func :=
  { name := "main.case_int_accumulate"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "s" (.lit (.int 0)))
              (.seq
                (.seq
                  (.seq .skip (.assign "i" (.lit (.int 0))))
                  (.loop
                    (.binop "<" (.name "i") (.lit (.int 3)))
                    (.seq
                      (.seq
                        (.assign "s" (.binop "+:g64" (.name "s") (.lit (.int 2000000000))))
                        (.assign "s" (.binop "*:g64" (.name "s") (.lit (.int 3)))))
                      (.assign "i" (.binop "+:g64" (.name "i") (.lit (.int 1)))))))
                (.ret (.name "s"))))) }

/-- `main.case_conv_int32_trunc`  (from `cases.go`) -/
def f_main_case_conv_int32_trunc : Func :=
  { name := "main.case_conv_int32_trunc"
  , params := []
  , body := (.seq
            .skip
            (.seq (.assign "x" (.lit (.int 4294967297))) (.ret (.unop "cast:i32" (.name "x"))))) }

/-- `main.case_conv_uint8_trunc`  (from `cases.go`) -/
def f_main_case_conv_uint8_trunc : Func :=
  { name := "main.case_conv_uint8_trunc"
  , params := []
  , body := (.seq .skip (.seq (.assign "x" (.lit (.int 300))) (.ret (.unop "cast:u8" (.name "x"))))) }

/-- `main.case_conv_sign_extend`  (from `cases.go`) -/
def f_main_case_conv_sign_extend : Func :=
  { name := "main.case_conv_sign_extend"
  , params := []
  , body := (.seq .skip (.seq (.assign "x" (.lit (.int (-1)))) (.ret (.unop "cast:u64" (.name "x"))))) }

/-- `main.case_conv_int64_widen`  (from `cases.go`) -/
def f_main_case_conv_int64_widen : Func :=
  { name := "main.case_conv_int64_widen"
  , params := []
  , body := (.seq .skip (.seq (.assign "x" (.lit (.int (-5)))) (.ret (.unop "cast:i64" (.name "x"))))) }

/-- `main.case_untyped_const_shift`  (from `cases.go`) -/
def f_main_case_untyped_const_shift : Func :=
  { name := "main.case_untyped_const_shift"
  , params := []
  , body := (.seq
            .skip
            (.seq (.assign "n" (.lit (.int 40))) (.ret (.hole "op:int:untyped-constant-shift")))) }

/-- `main.case_named_type_wraps`  (from `cases.go`) -/
def f_main_case_named_type_wraps : Func :=
  { name := "main.case_named_type_wraps"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "l" (.lit (.int 200)))
              (.ret (.binop "+:w08" (.name "l") (.lit (.int 100)))))) }

/-- `main.case_untyped_const_operand`  (from `cases.go`) -/
def f_main_case_untyped_const_operand : Func :=
  { name := "main.case_untyped_const_operand"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "mask" (.lit (.int 18446744073709551615)))
              (.seq
                .skip
                (.seq
                  (.assign "x" (.lit (.int 5)))
                  (.ret (.binop "^:w64" (.name "x") (.name "mask"))))))) }

/-- `main.case_local_from_conversion`  (from `cases.go`) -/
def f_main_case_local_from_conversion : Func :=
  { name := "main.case_local_from_conversion"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "n" (.lit (.int 300)))
              (.seq
                .skip
                (.seq
                  (.assign "s" (.unop "cast:u8" (.name "n")))
                  (.seq
                    (.assign "s" (.binop "+:w08" (.name "s") (.lit (.int 250))))
                    (.ret (.name "s"))))))) }

/-- `main.case_const_expr_exact`  (from `cases.go`) -/
def f_main_case_const_expr_exact : Func :=
  { name := "main.case_const_expr_exact"
  , params := []
  , body := (.ret (.lit (.int 1099511627783))) }

/-- `main.case_const_conversion`  (from `cases.go`) -/
def f_main_case_const_conversion : Func :=
  { name := "main.case_const_conversion"
  , params := []
  , body := (.ret (.unop "cast:u64" (.lit (.int 18446744073709551615)))) }

/-- `main.case_compound_ops`  (from `cases.go`) -/
def f_main_case_compound_ops : Func :=
  { name := "main.case_compound_ops"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 100)))
              (.seq
                (.assign "x" (.binop "+:w08" (.name "x") (.lit (.int 200))))
                (.seq
                  (.assign "x" (.binop "*:w08" (.name "x") (.lit (.int 3))))
                  (.seq
                    (.assign "x" (.binop "-:w08" (.name "x") (.lit (.int 7))))
                    (.seq
                      (.assign "x" (.binop "/:w08" (.name "x") (.lit (.int 2))))
                      (.seq
                        (.assign "x" (.binop "%:w08" (.name "x") (.lit (.int 50))))
                        (.seq
                          (.assign "x" (.binop "|:w08" (.name "x") (.lit (.int 129))))
                          (.seq
                            (.assign "x" (.binop "&:w08" (.name "x") (.lit (.int 247))))
                            (.seq
                              (.assign "x" (.binop "^:w08" (.name "x") (.lit (.int 85))))
                              (.seq
                                (.assign "x" (.binop "<<:w08" (.name "x") (.lit (.int 3))))
                                (.seq
                                  (.assign "x" (.binop ">>:w08" (.name "x") (.lit (.int 1))))
                                  (.ret (.name "x")))))))))))))) }

/-- `main.case_compound_and_not`  (from `cases.go`) -/
def f_main_case_compound_and_not : Func :=
  { name := "main.case_compound_and_not"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 65535)))
              (.seq
                (.assign "x" (.binop "&^:w16" (.name "x") (.lit (.int 3855))))
                (.ret (.name "x"))))) }

/-- `main.case_compound_shl_count`  (from `cases.go`) -/
def f_main_case_compound_shl_count : Func :=
  { name := "main.case_compound_shl_count"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 1)))
              (.seq
                .skip
                (.seq
                  (.assign "n" (.lit (.int 35)))
                  (.seq (.assign "x" (.binop "<<:g32" (.name "x") (.name "n"))) (.ret (.name "x"))))))) }

/-- `main.case_compound_int64`  (from `cases.go`) -/
def f_main_case_compound_int64 : Func :=
  { name := "main.case_compound_int64"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 4611686018427387904)))
              (.seq
                (.assign "x" (.binop "+:g64" (.name "x") (.name "x")))
                (.seq (.assign "x" (.binop "*:g64" (.name "x") (.lit (.int 2)))) (.ret (.name "x")))))) }

/-- `main.case_div_zero`  (from `cases.go`) -/
def f_main_case_div_zero : Func :=
  { name := "main.case_div_zero"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 1)))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 0))) (.ret (.binop "/:g64" (.name "a") (.name "b"))))))) }

/-- `main.case_neg_shift`  (from `cases.go`) -/
def f_main_case_neg_shift : Func :=
  { name := "main.case_neg_shift"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 1)))
              (.seq
                .skip
                (.seq
                  (.assign "n" (.lit (.int (-1))))
                  (.ret (.binop "<<:g64" (.name "x") (.name "n"))))))) }

/-- `main.case_rem_zero`  (from `cases.go`) -/
def f_main_case_rem_zero : Func :=
  { name := "main.case_rem_zero"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 1)))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 0))) (.ret (.binop "%:w08" (.name "a") (.name "b"))))))) }

/-- `cases.go:main.cases.go`  (from `cases.go`) -/
def f_cases_go_main_cases_go : Func :=
  { name := "cases.go:main.cases.go"
  , params := []
  , body := .skip }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_main_case_int_mul,
  f_main_case_int_add_wraps,
  f_main_case_int32_mul_wraps,
  f_main_case_int64_mul,
  f_main_case_int8_add_wraps,
  f_main_case_int8_incr,
  f_main_case_int16_compound,
  f_main_case_uint8_sub_wraps,
  f_main_case_byte_add_wraps,
  f_main_case_rune_add_wraps,
  f_main_case_uint32_mul_wraps,
  f_main_case_uint64_mul_wraps,
  f_main_case_uint64_sub_wraps,
  f_main_case_uint_sub_wraps,
  f_main_case_uintptr_sub_wraps,
  f_main_case_uint16_neg,
  f_main_case_int_neg_min,
  f_main_case_uint8_complement,
  f_main_case_int64_complement,
  f_main_case_and_not,
  f_main_case_min_div,
  f_main_case_min_rem,
  f_main_case_int8_min_div,
  f_main_case_div_trunc,
  f_main_case_rem_sign,
  f_main_case_uint32_div,
  f_main_case_shl_over_width,
  f_main_case_shl_in_width,
  f_main_case_shl_int64,
  f_main_case_shr_over_width_neg,
  f_main_case_shr_over_width_pos,
  f_main_case_shr_arith,
  f_main_case_shr_uint,
  f_main_case_shl_count_type,
  f_main_case_shl_signed_count,
  f_main_case_shl_drops_bits,
  f_main_case_uint32_gt,
  f_main_case_int8_lt,
  f_main_case_int_accumulate,
  f_main_case_conv_int32_trunc,
  f_main_case_conv_uint8_trunc,
  f_main_case_conv_sign_extend,
  f_main_case_conv_int64_widen,
  f_main_case_untyped_const_shift,
  f_main_case_named_type_wraps,
  f_main_case_untyped_const_operand,
  f_main_case_local_from_conversion,
  f_main_case_const_expr_exact,
  f_main_case_const_conversion,
  f_main_case_compound_ops,
  f_main_case_compound_and_not,
  f_main_case_compound_shl_count,
  f_main_case_compound_int64,
  f_main_case_div_zero,
  f_main_case_neg_shift,
  f_main_case_rem_zero,
  f_cases_go_main_cases_go
] }

end Autoform.Generated.GoIntWidth