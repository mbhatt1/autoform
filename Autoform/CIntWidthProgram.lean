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
set_option maxRecDepth 8192

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
# CIntWidth — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.CIntWidth
open Autoform.Core

/-- `case_long_mul`  (from `cintwidth_cases.c`) -/
def f_case_long_mul : Func :=
  { name := "case_long_mul"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 100000)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 100000)))
                  (.ret (.binop "*:i64" (.name "a") (.name "b"))))))) }

/-- `case_int_mul_wraps`  (from `cintwidth_cases.c`) -/
def f_case_int_mul_wraps : Func :=
  { name := "case_int_mul_wraps"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 100000)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 100000)))
                  (.seq
                    .skip
                    (.seq (.assign "p" (.binop "*:i32" (.name "a") (.name "b"))) (.ret (.name "p")))))))) }

/-- `case_mixed_mul`  (from `cintwidth_cases.c`) -/
def f_case_mixed_mul : Func :=
  { name := "case_mixed_mul"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 3000000000)))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 2))) (.ret (.binop "*:i64" (.name "a") (.name "b"))))))) }

/-- `case_shift_left_64`  (from `cintwidth_cases.c`) -/
def f_case_shift_left_64 : Func :=
  { name := "case_shift_left_64"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "v"
                (.binop
                  "|:i64"
                  (.binop "<<:i64" (.unop "cast:i64" (.lit (.int 108096))) (.lit (.int 32)))
                  (.lit (.int 275971583))))
              (.ret (.name "v")))) }

/-- `case_tree_depth`  (from `cintwidth_cases.c`) -/
def f_case_tree_depth : Func :=
  { name := "case_tree_depth"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "nPMA" (.lit (.int 2147483647)))
              (.seq
                .skip
                (.seq
                  (.assign "nDepth" (.lit (.int 0)))
                  (.seq
                    .skip
                    (.seq
                      (.assign "nDiv" (.lit (.int 16)))
                      (.seq
                        (.loop
                          (.binop "<:i64" (.name "nDiv") (.unop "cast:i64" (.name "nPMA")))
                          (.seq
                            (.assign "nDiv" (.binop "*:i64" (.name "nDiv") (.lit (.int 16))))
                            (.assign "nDepth" (.binop "+:i32" (.name "nDepth") (.lit (.int 1))))))
                        (.ret (.name "nDepth"))))))))) }

/-- `case_long_accumulate`  (from `cintwidth_cases.c`) -/
def f_case_long_accumulate : Func :=
  { name := "case_long_accumulate"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "s" (.lit (.int 0)))
              (.seq
                (.seq
                  (.assign "i" (.lit (.int 0)))
                  (.loop
                    (.binop "<:i32" (.name "i") (.lit (.int 3)))
                    (.seq
                      (.assign "s" (.binop "+:i64" (.name "s") (.lit (.int 2000000000))))
                      (.assign "i" (.binop "+:i32" (.name "i") (.lit (.int 1)))))))
                (.ret (.name "s"))))) }

/-- `case_unsigned_underflow`  (from `cintwidth_cases.c`) -/
def f_case_unsigned_underflow : Func :=
  { name := "case_unsigned_underflow"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "u" (.unop "cast:u32" (.lit (.int 0))))
              (.seq (.assign "u" (.binop "-:u32" (.name "u") (.lit (.int 1)))) (.ret (.name "u"))))) }

/-- `case_unsigned_init_widen`  (from `cintwidth_cases.c`) -/
def f_case_unsigned_init_widen : Func :=
  { name := "case_unsigned_init_widen"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "u" (.unop "cast:u32" (.unop "-:i32" (.lit (.int 1)))))
              (.seq .skip (.seq (.assign "y" (.name "u")) (.ret (.name "y")))))) }

/-- `case_u32_add_wraps`  (from `cintwidth_cases.c`) -/
def f_case_u32_add_wraps : Func :=
  { name := "case_u32_add_wraps"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 3000000000)))
              (.ret (.binop "+:u32" (.name "x") (.name "x"))))) }

/-- `case_u64_mul_wraps`  (from `cintwidth_cases.c`) -/
def f_case_u64_mul_wraps : Func :=
  { name := "case_u64_mul_wraps"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 18446744073709551615)))
              (.ret (.binop "*:u64" (.name "x") (.lit (.int 2)))))) }

/-- `case_shift_right_u32`  (from `cintwidth_cases.c`) -/
def f_case_shift_right_u32 : Func :=
  { name := "case_shift_right_u32"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 2147483648)))
              (.ret (.binop ">>:u32" (.name "x") (.lit (.int 31)))))) }

/-- `case_shift_right_i32`  (from `cintwidth_cases.c`) -/
def f_case_shift_right_i32 : Func :=
  { name := "case_shift_right_i32"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "y" (.unop "-:i32" (.lit (.int 8))))
              (.ret (.binop ">>:i32" (.name "y") (.lit (.int 1)))))) }

/-- `case_shift_right_u64`  (from `cintwidth_cases.c`) -/
def f_case_shift_right_u64 : Func :=
  { name := "case_shift_right_u64"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 17293822569102704640)))
              (.ret (.unop "cast:i64" (.binop ">>:u64" (.name "x") (.lit (.int 60))))))) }

/-- `case_shift_right_i64`  (from `cintwidth_cases.c`) -/
def f_case_shift_right_i64 : Func :=
  { name := "case_shift_right_i64"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.unop "-:i64" (.lit (.int 4294967296))))
              (.ret (.binop ">>:i64" (.name "x") (.lit (.int 4)))))) }

/-- `case_mixed_compare`  (from `cintwidth_cases.c`) -/
def f_case_mixed_compare : Func :=
  { name := "case_mixed_compare"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.unop "-:i32" (.lit (.int 1))))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.unop "cast:u32" (.lit (.int 1))))
                  (.seq
                    .skip
                    (.seq
                      (.assign "r" (.lit (.int 0)))
                      (.seq
                        (.ifte
                          (.binop "<:u32" (.name "a") (.name "b"))
                          (.assign "r" (.lit (.int 1)))
                          .skip)
                        (.ret (.name "r"))))))))) }

/-- `case_unsigned_div`  (from `cintwidth_cases.c`) -/
def f_case_unsigned_div : Func :=
  { name := "case_unsigned_div"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.unop "cast:u32" (.unop "-:i32" (.lit (.int 2)))))
              (.ret (.binop "/:u32" (.name "a") (.lit (.int 2)))))) }

/-- `case_unsigned_neg`  (from `cintwidth_cases.c`) -/
def f_case_unsigned_neg : Func :=
  { name := "case_unsigned_neg"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.unop "cast:u32" (.lit (.int 1))))
              (.ret (.unop "-:u32" (.name "a"))))) }

/-- `case_u64_not`  (from `cintwidth_cases.c`) -/
def f_case_u64_not : Func :=
  { name := "case_u64_not"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "z" (.unop "cast:u64" (.lit (.int 0))))
              (.ret (.unop "~:u64" (.name "z"))))) }

/-- `case_u8_increment_wraps`  (from `cintwidth_cases.c`) -/
def f_case_u8_increment_wraps : Func :=
  { name := "case_u8_increment_wraps"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "c" (.unop "cast:u8" (.lit (.int 255))))
              (.seq
                (.assign "c" (.unop "cast:u8" (.binop "+:i32" (.name "c") (.lit (.int 1)))))
                (.ret (.name "c"))))) }

/-- `case_u8_compound_wraps`  (from `cintwidth_cases.c`) -/
def f_case_u8_compound_wraps : Func :=
  { name := "case_u8_compound_wraps"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "c" (.unop "cast:u8" (.lit (.int 250))))
              (.seq
                (.assign "c" (.unop "cast:u8" (.binop "+:i32" (.name "c") (.lit (.int 10)))))
                (.ret (.name "c"))))) }

/-- `case_size_t_underflow`  (from `cintwidth_cases.c`) -/
def f_case_size_t_underflow : Func :=
  { name := "case_size_t_underflow"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "n" (.unop "cast:u64" (.lit (.int 0))))
              (.seq
                (.assign "n" (.binop "-:u64" (.name "n") (.lit (.int 1))))
                (.seq
                  .skip
                  (.seq
                    (.assign "r" (.lit (.int 0)))
                    (.seq
                      (.ifte
                        (.binop ">:u64" (.name "n") (.lit (.int 4294967296)))
                        (.assign "r" (.lit (.int 1)))
                        .skip)
                      (.ret (.name "r")))))))) }

/-- `case_i64_div`  (from `cintwidth_cases.c`) -/
def f_case_i64_div : Func :=
  { name := "case_i64_div"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.unop "-:i64" (.lit (.int 7000000000))))
              (.ret (.binop "/:i64" (.name "a") (.lit (.int 2)))))) }

/-- `case_narrow_signed_char`  (from `cintwidth_cases.c`) -/
def f_case_narrow_signed_char : Func :=
  { name := "case_narrow_signed_char"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 300)))
              (.seq .skip (.seq (.assign "sc" (.unop "cast:i8" (.name "x"))) (.ret (.name "sc")))))) }

/-- `cintwidth_cases.c:<global>`  (from `cintwidth_cases.c`) -/
def f_cintwidth_cases_c__global_ : Func :=
  { name := "cintwidth_cases.c:<global>"
  , params := []
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := [f_cintwidth_cases_c__global_]

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_case_long_mul,
  f_case_int_mul_wraps,
  f_case_mixed_mul,
  f_case_shift_left_64,
  f_case_tree_depth,
  f_case_long_accumulate,
  f_case_unsigned_underflow,
  f_case_unsigned_init_widen,
  f_case_u32_add_wraps,
  f_case_u64_mul_wraps,
  f_case_shift_right_u32,
  f_case_shift_right_i32,
  f_case_shift_right_u64,
  f_case_shift_right_i64,
  f_case_mixed_compare,
  f_case_unsigned_div,
  f_case_unsigned_neg,
  f_case_u64_not,
  f_case_u8_increment_wraps,
  f_case_u8_compound_wraps,
  f_case_size_t_underflow,
  f_case_i64_div,
  f_case_narrow_signed_char,
  f_cintwidth_cases_c__global_
] }

end Autoform.Generated.CIntWidth