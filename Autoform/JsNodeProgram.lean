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
set_option maxRecDepth 8448

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
# JsNode — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.JsNode
open Autoform.Core

/-- `jsnode_cases.js::program:case_strict_str_vs_num`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_strict_str_vs_num : Func :=
  { name := "jsnode_cases.js::program:case_strict_str_vs_num"
  , params := ["this"]
  , body := (.ret (.binop "===" (.lit (.int 1)) (.lit (.str "1")))) }

/-- `jsnode_cases.js::program`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program : Func :=
  { name := "jsnode_cases.js::program"
  , params := ["this"]
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
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "case_strict_str_vs_num"
                                        (.fnref "jsnode_cases.js::program:case_strict_str_vs_num"))
                                        (.seq
                                        (.assign
                                        "case_loose_same_type"
                                        (.fnref "jsnode_cases.js::program:case_loose_same_type"))
                                        (.seq
                                        (.assign
                                        "case_strict_same_type"
                                        (.fnref "jsnode_cases.js::program:case_strict_same_type"))
                                        (.seq
                                        (.assign
                                        "case_strict_ne_cross"
                                        (.fnref "jsnode_cases.js::program:case_strict_ne_cross"))
                                        (.seq
                                        (.assign
                                        "case_loose_ne_same"
                                        (.fnref "jsnode_cases.js::program:case_loose_ne_same"))
                                        (.seq
                                        (.assign
                                        "case_strict_ne_same"
                                        (.fnref "jsnode_cases.js::program:case_strict_ne_same"))
                                        (.seq
                                        (.assign
                                        "case_strict_bool_vs_num"
                                        (.fnref "jsnode_cases.js::program:case_strict_bool_vs_num"))
                                        (.seq
                                        (.assign
                                        "case_single_quote_eq"
                                        (.fnref "jsnode_cases.js::program:case_single_quote_eq"))
                                        (.seq
                                        (.assign
                                        "case_single_quote_ne"
                                        (.fnref "jsnode_cases.js::program:case_single_quote_ne"))
                                        (.seq
                                        (.assign
                                        "case_single_quote_cross"
                                        (.fnref "jsnode_cases.js::program:case_single_quote_cross"))
                                        (.seq
                                        (.assign
                                        "case_strict_nan"
                                        (.fnref "jsnode_cases.js::program:case_strict_nan"))
                                        (.seq
                                        (.assign
                                        "case_nan_ne"
                                        (.fnref "jsnode_cases.js::program:case_nan_ne"))
                                        (.seq
                                        (.assign
                                        "case_inf_strict"
                                        (.fnref "jsnode_cases.js::program:case_inf_strict"))
                                        (.seq
                                        (.assign
                                        "case_inf_vs_big"
                                        (.fnref "jsnode_cases.js::program:case_inf_vs_big"))
                                        (.seq
                                        (.assign
                                        "case_strict_negzero"
                                        (.fnref "jsnode_cases.js::program:case_strict_negzero"))
                                        (.seq
                                        (.assign
                                        "case_strict_int_float"
                                        (.fnref "jsnode_cases.js::program:case_strict_int_float"))
                                        (.seq
                                        (.assign
                                        "case_null_loose_zero"
                                        (.fnref "jsnode_cases.js::program:case_null_loose_zero"))
                                        (.seq
                                        (.assign
                                        "case_zero_loose_null"
                                        (.fnref "jsnode_cases.js::program:case_zero_loose_null"))
                                        (.seq
                                        (.assign
                                        "case_empty_str_loose_null"
                                        (.fnref
                                        "jsnode_cases.js::program:case_empty_str_loose_null"))
                                        (.seq
                                        (.assign
                                        "case_false_loose_null"
                                        (.fnref "jsnode_cases.js::program:case_false_loose_null"))
                                        (.seq
                                        (.assign
                                        "case_null_loose_null"
                                        (.fnref "jsnode_cases.js::program:case_null_loose_null"))
                                        (.seq
                                        (.assign
                                        "case_undef_loose_null"
                                        (.fnref "jsnode_cases.js::program:case_undef_loose_null"))
                                        (.seq
                                        (.assign
                                        "case_null_loose_undef"
                                        (.fnref "jsnode_cases.js::program:case_null_loose_undef"))
                                        (.seq
                                        (.assign
                                        "case_null_ne_zero"
                                        (.fnref "jsnode_cases.js::program:case_null_ne_zero"))
                                        (.seq
                                        (.assign
                                        "case_null_ne_null"
                                        (.fnref "jsnode_cases.js::program:case_null_ne_null"))
                                        (.seq
                                        (.assign
                                        "case_zero_strict_null"
                                        (.fnref "jsnode_cases.js::program:case_zero_strict_null"))
                                        (.seq
                                        (.assign
                                        "case_null_strict_null"
                                        (.fnref "jsnode_cases.js::program:case_null_strict_null"))
                                        (.seq
                                        (.assign
                                        "case_null_strict_undefined"
                                        (.fnref
                                        "jsnode_cases.js::program:case_null_strict_undefined"))
                                        (.seq
                                        (.assign
                                        "case_undef_strict_undef"
                                        (.fnref "jsnode_cases.js::program:case_undef_strict_undef"))
                                        (.seq
                                        (.assign
                                        "case_null_strict_ne_undefined"
                                        (.fnref
                                        "jsnode_cases.js::program:case_null_strict_ne_undefined"))
                                        (.seq
                                        (.assign
                                        "case_sar_neg"
                                        (.fnref "jsnode_cases.js::program:case_sar_neg"))
                                        (.seq
                                        (.assign
                                        "case_shr_neg"
                                        (.fnref "jsnode_cases.js::program:case_shr_neg"))
                                        (.seq
                                        (.assign
                                        "case_sar_neg16"
                                        (.fnref "jsnode_cases.js::program:case_sar_neg16"))
                                        (.seq
                                        (.assign
                                        "case_shr_neg16"
                                        (.fnref "jsnode_cases.js::program:case_shr_neg16"))
                                        (.seq
                                        (.assign
                                        "case_shl_sign"
                                        (.fnref "jsnode_cases.js::program:case_shl_sign"))
                                        (.seq
                                        (.assign
                                        "case_shr_var"
                                        (.fnref "jsnode_cases.js::program:case_shr_var"))
                                        (.seq
                                        (.assign
                                        "case_sar_var_call"
                                        (.fnref "jsnode_cases.js::program:case_sar_var_call"))
                                        (.seq
                                        (.assign
                                        "case_nullish_zero"
                                        (.fnref "jsnode_cases.js::program:case_nullish_zero"))
                                        (.seq
                                        (.assign
                                        "case_nullish_empty"
                                        (.fnref "jsnode_cases.js::program:case_nullish_empty"))
                                        (.seq
                                        (.assign
                                        "case_nullish_false"
                                        (.fnref "jsnode_cases.js::program:case_nullish_false"))
                                        (.seq
                                        (.assign
                                        "case_nullish_null"
                                        (.fnref "jsnode_cases.js::program:case_nullish_null"))
                                        (.seq
                                        (.assign
                                        "case_nullish_undef"
                                        (.fnref "jsnode_cases.js::program:case_nullish_undef"))
                                        (.seq
                                        (.assign
                                        "case_nullish_chain"
                                        (.fnref "jsnode_cases.js::program:case_nullish_chain"))
                                        (.seq
                                        (.assign
                                        "case_nullish_value"
                                        (.fnref "jsnode_cases.js::program:case_nullish_value"))
                                        (.seq
                                        (.assign
                                        "case_nullish_single_quote"
                                        (.fnref
                                        "jsnode_cases.js::program:case_nullish_single_quote"))
                                        (.seq
                                        (.assign
                                        "case_nullish_single_quote_null"
                                        (.fnref
                                        "jsnode_cases.js::program:case_nullish_single_quote_null"))
                                        (.seq
                                        (.assign
                                        "case_nullish_var_zero"
                                        (.fnref "jsnode_cases.js::program:case_nullish_var_zero"))
                                        (.seq
                                        (.assign
                                        "case_nullish_var_null"
                                        (.fnref "jsnode_cases.js::program:case_nullish_var_null"))
                                        (.seq
                                        (.assign
                                        "case_nullish_short_circuit"
                                        (.fnref
                                        "jsnode_cases.js::program:case_nullish_short_circuit"))
                                        (.seq
                                        (.assign
                                        "case_nullish_right_effect"
                                        (.fnref
                                        "jsnode_cases.js::program:case_nullish_right_effect"))
                                        (.seq
                                        (.assign
                                        "case_nullish_impure_left"
                                        (.fnref "jsnode_cases.js::program:case_nullish_impure_left"))
                                        (.seq
                                        (.assign
                                        "case_nullish_in_cond"
                                        (.fnref "jsnode_cases.js::program:case_nullish_in_cond"))
                                        (.seq
                                        (.assign
                                        "case_or_zero"
                                        (.fnref "jsnode_cases.js::program:case_or_zero"))
                                        (.seq
                                        (.assign
                                        "case_and_zero"
                                        (.fnref "jsnode_cases.js::program:case_and_zero"))
                                        (.assign
                                        "case_or_then_nullish"
                                        (.fnref "jsnode_cases.js::program:case_or_then_nullish"))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) }

/-- `jsnode_cases.js::program:case_loose_same_type`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_loose_same_type : Func :=
  { name := "jsnode_cases.js::program:case_loose_same_type"
  , params := ["this"]
  , body := (.ret (.binop "==" (.lit (.int 2)) (.lit (.int 2)))) }

/-- `jsnode_cases.js::program:case_strict_same_type`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_strict_same_type : Func :=
  { name := "jsnode_cases.js::program:case_strict_same_type"
  , params := ["this"]
  , body := (.ret (.binop "===" (.lit (.int 2)) (.lit (.int 2)))) }

/-- `jsnode_cases.js::program:case_strict_ne_cross`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_strict_ne_cross : Func :=
  { name := "jsnode_cases.js::program:case_strict_ne_cross"
  , params := ["this"]
  , body := (.ret (.binop "!==" (.lit (.int 1)) (.lit (.str "1")))) }

/-- `jsnode_cases.js::program:case_loose_ne_same`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_loose_ne_same : Func :=
  { name := "jsnode_cases.js::program:case_loose_ne_same"
  , params := ["this"]
  , body := (.ret (.binop "!=" (.lit (.int 3)) (.lit (.int 3)))) }

/-- `jsnode_cases.js::program:case_strict_ne_same`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_strict_ne_same : Func :=
  { name := "jsnode_cases.js::program:case_strict_ne_same"
  , params := ["this"]
  , body := (.ret (.binop "!==" (.lit (.str "a")) (.lit (.str "a")))) }

/-- `jsnode_cases.js::program:case_strict_bool_vs_num`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_strict_bool_vs_num : Func :=
  { name := "jsnode_cases.js::program:case_strict_bool_vs_num"
  , params := ["this"]
  , body := (.ret (.binop "===" (.lit (.bool true)) (.lit (.int 1)))) }

/-- `jsnode_cases.js::program:case_single_quote_eq`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_single_quote_eq : Func :=
  { name := "jsnode_cases.js::program:case_single_quote_eq"
  , params := ["this"]
  , body := (.ret (.binop "===" (.lit (.str "a")) (.lit (.str "a")))) }

/-- `jsnode_cases.js::program:case_single_quote_ne`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_single_quote_ne : Func :=
  { name := "jsnode_cases.js::program:case_single_quote_ne"
  , params := ["this"]
  , body := (.ret (.binop "!==" (.lit (.str "a")) (.lit (.str "b")))) }

/-- `jsnode_cases.js::program:case_single_quote_cross`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_single_quote_cross : Func :=
  { name := "jsnode_cases.js::program:case_single_quote_cross"
  , params := ["this"]
  , body := (.ret (.binop "===" (.lit (.str "a")) (.lit (.str "a")))) }

/-- `jsnode_cases.js::program:case_strict_nan`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_strict_nan : Func :=
  { name := "jsnode_cases.js::program:case_strict_nan"
  , params := ["this"]
  , body := (.seq
            .skip
            (.ret
              (.binop
                "==="
                (.lit (.float (Fl.ofBits 9221120237041090560)))
                (.lit (.float (Fl.ofBits 9221120237041090560)))))) }

/-- `jsnode_cases.js::program:case_nan_ne`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_nan_ne : Func :=
  { name := "jsnode_cases.js::program:case_nan_ne"
  , params := ["this"]
  , body := (.seq
            .skip
            (.ret
              (.binop
                "!=="
                (.lit (.float (Fl.ofBits 9221120237041090560)))
                (.lit (.float (Fl.ofBits 9221120237041090560)))))) }

/-- `jsnode_cases.js::program:case_inf_strict`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_inf_strict : Func :=
  { name := "jsnode_cases.js::program:case_inf_strict"
  , params := ["this"]
  , body := (.seq
            .skip
            (.ret
              (.binop
                "==="
                (.lit (.float (Fl.ofBits 9218868437227405312)))
                (.lit (.float (Fl.ofBits 9218868437227405312)))))) }

/-- `jsnode_cases.js::program:case_inf_vs_big`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_inf_vs_big : Func :=
  { name := "jsnode_cases.js::program:case_inf_vs_big"
  , params := ["this"]
  , body := (.seq
            .skip
            (.ret
              (.binop ">" (.lit (.float (Fl.ofBits 9218868437227405312))) (.lit (.int 1000000))))) }

/-- `jsnode_cases.js::program:case_strict_negzero`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_strict_negzero : Func :=
  { name := "jsnode_cases.js::program:case_strict_negzero"
  , params := ["this"]
  , body := (.ret (.binop "===" (.unop "-" (.lit (.int 0))) (.lit (.int 0)))) }

/-- `jsnode_cases.js::program:case_strict_int_float`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_strict_int_float : Func :=
  { name := "jsnode_cases.js::program:case_strict_int_float"
  , params := ["this"]
  , body := (.ret (.binop "===" (.lit (.int 1)) (.lit (.float (Fl.ofBits 4607182418800017408))))) }

/-- `jsnode_cases.js::program:case_null_loose_zero`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_null_loose_zero : Func :=
  { name := "jsnode_cases.js::program:case_null_loose_zero"
  , params := ["this"]
  , body := (.ret (.binop "==" (.lit .jsnull) (.lit (.int 0)))) }

/-- `jsnode_cases.js::program:case_zero_loose_null`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_zero_loose_null : Func :=
  { name := "jsnode_cases.js::program:case_zero_loose_null"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq (.assign "z" (.lit (.int 0))) (.ret (.binop "==" (.name "z") (.lit .jsnull))))) }

/-- `jsnode_cases.js::program:case_empty_str_loose_null`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_empty_str_loose_null : Func :=
  { name := "jsnode_cases.js::program:case_empty_str_loose_null"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq (.assign "s" (.lit (.str ""))) (.ret (.binop "==" (.name "s") (.lit .jsnull))))) }

/-- `jsnode_cases.js::program:case_false_loose_null`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_false_loose_null : Func :=
  { name := "jsnode_cases.js::program:case_false_loose_null"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "f" (.lit (.bool false)))
              (.ret (.binop "==" (.name "f") (.lit .jsnull))))) }

/-- `jsnode_cases.js::program:case_null_loose_null`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_null_loose_null : Func :=
  { name := "jsnode_cases.js::program:case_null_loose_null"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq (.assign "n" (.lit .jsnull)) (.ret (.binop "==" (.name "n") (.lit .jsnull))))) }

/-- `jsnode_cases.js::program:case_undef_loose_null`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_undef_loose_null : Func :=
  { name := "jsnode_cases.js::program:case_undef_loose_null"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq (.assign "u" (.lit .unit)) (.ret (.binop "==" (.name "u") (.lit .jsnull)))))) }

/-- `jsnode_cases.js::program:case_null_loose_undef`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_null_loose_undef : Func :=
  { name := "jsnode_cases.js::program:case_null_loose_undef"
  , params := ["this"]
  , body := (.seq .skip (.ret (.binop "==" (.lit .jsnull) (.lit .unit)))) }

/-- `jsnode_cases.js::program:case_null_ne_zero`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_null_ne_zero : Func :=
  { name := "jsnode_cases.js::program:case_null_ne_zero"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq (.assign "z" (.lit (.int 0))) (.ret (.binop "!=" (.name "z") (.lit .jsnull))))) }

/-- `jsnode_cases.js::program:case_null_ne_null`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_null_ne_null : Func :=
  { name := "jsnode_cases.js::program:case_null_ne_null"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq (.assign "n" (.lit .jsnull)) (.ret (.binop "!=" (.name "n") (.lit .jsnull))))) }

/-- `jsnode_cases.js::program:case_zero_strict_null`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_zero_strict_null : Func :=
  { name := "jsnode_cases.js::program:case_zero_strict_null"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq (.assign "z" (.lit (.int 0))) (.ret (.binop "===" (.name "z") (.lit .jsnull))))) }

/-- `jsnode_cases.js::program:case_null_strict_null`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_null_strict_null : Func :=
  { name := "jsnode_cases.js::program:case_null_strict_null"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq (.assign "n" (.lit .jsnull)) (.ret (.binop "===" (.name "n") (.lit .jsnull))))) }

/-- `jsnode_cases.js::program:case_null_strict_undefined`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_null_strict_undefined : Func :=
  { name := "jsnode_cases.js::program:case_null_strict_undefined"
  , params := ["this"]
  , body := (.seq .skip (.ret (.binop "===" (.lit .jsnull) (.lit .unit)))) }

/-- `jsnode_cases.js::program:case_undef_strict_undef`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_undef_strict_undef : Func :=
  { name := "jsnode_cases.js::program:case_undef_strict_undef"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq (.assign "u" (.lit .unit)) (.ret (.binop "===" (.name "u") (.lit .unit)))))) }

/-- `jsnode_cases.js::program:case_null_strict_ne_undefined`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_null_strict_ne_undefined : Func :=
  { name := "jsnode_cases.js::program:case_null_strict_ne_undefined"
  , params := ["this"]
  , body := (.seq .skip (.ret (.binop "!==" (.lit .jsnull) (.lit .unit)))) }

/-- `jsnode_cases.js::program:case_sar_neg`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_sar_neg : Func :=
  { name := "jsnode_cases.js::program:case_sar_neg"
  , params := ["this"]
  , body := (.ret (.binop ">>" (.unop "-" (.lit (.int 1))) (.lit (.int 0)))) }

/-- `jsnode_cases.js::program:case_shr_neg`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_shr_neg : Func :=
  { name := "jsnode_cases.js::program:case_shr_neg"
  , params := ["this"]
  , body := (.ret (.binop ">>>" (.unop "-" (.lit (.int 1))) (.lit (.int 0)))) }

/-- `jsnode_cases.js::program:case_sar_neg16`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_sar_neg16 : Func :=
  { name := "jsnode_cases.js::program:case_sar_neg16"
  , params := ["this"]
  , body := (.ret (.binop ">>" (.unop "-" (.lit (.int 16))) (.lit (.int 2)))) }

/-- `jsnode_cases.js::program:case_shr_neg16`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_shr_neg16 : Func :=
  { name := "jsnode_cases.js::program:case_shr_neg16"
  , params := ["this"]
  , body := (.ret (.binop ">>>" (.unop "-" (.lit (.int 16))) (.lit (.int 28)))) }

/-- `jsnode_cases.js::program:case_shl_sign`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_shl_sign : Func :=
  { name := "jsnode_cases.js::program:case_shl_sign"
  , params := ["this"]
  , body := (.ret (.binop "<<" (.lit (.int 1)) (.lit (.int 31)))) }

/-- `jsnode_cases.js::program:case_shr_var`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_shr_var : Func :=
  { name := "jsnode_cases.js::program:case_shr_var"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.unop "-" (.lit (.int 2))))
              (.ret (.binop ">>>" (.name "x") (.lit (.int 1)))))) }

/-- `jsnode_cases.js::program:case_sar_var_call`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_sar_var_call : Func :=
  { name := "jsnode_cases.js::program:case_sar_var_call"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.unop "-" (.lit (.int 2))))
              (.ret (.binop ">>" (.name "x") (.lit (.int 1)))))) }

/-- `jsnode_cases.js::program:case_nullish_zero`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_nullish_zero : Func :=
  { name := "jsnode_cases.js::program:case_nullish_zero"
  , params := ["this"]
  , body := (.ret
            (.cond (.binop "==" (.lit (.int 0)) (.lit .jsnull)) (.lit (.int 5)) (.lit (.int 0)))) }

/-- `jsnode_cases.js::program:case_nullish_empty`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_nullish_empty : Func :=
  { name := "jsnode_cases.js::program:case_nullish_empty"
  , params := ["this"]
  , body := (.ret
            (.cond (.binop "==" (.lit (.str "")) (.lit .jsnull)) (.lit (.str "d")) (.lit (.str "")))) }

/-- `jsnode_cases.js::program:case_nullish_false`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_nullish_false : Func :=
  { name := "jsnode_cases.js::program:case_nullish_false"
  , params := ["this"]
  , body := (.ret
            (.cond
              (.binop "==" (.lit (.bool false)) (.lit .jsnull))
              (.lit (.int 5))
              (.lit (.bool false)))) }

/-- `jsnode_cases.js::program:case_nullish_null`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_nullish_null : Func :=
  { name := "jsnode_cases.js::program:case_nullish_null"
  , params := ["this"]
  , body := (.ret (.cond (.binop "==" (.lit .jsnull) (.lit .jsnull)) (.lit (.int 5)) (.lit .jsnull))) }

/-- `jsnode_cases.js::program:case_nullish_undef`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_nullish_undef : Func :=
  { name := "jsnode_cases.js::program:case_nullish_undef"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "u" (.lit .unit))
                (.ret (.cond (.binop "==" (.name "u") (.lit .jsnull)) (.lit (.int 7)) (.name "u")))))) }

/-- `jsnode_cases.js::program:case_nullish_chain`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_nullish_chain : Func :=
  { name := "jsnode_cases.js::program:case_nullish_chain"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.assign "u" (.lit .unit))
                  (.seq
                    (.assign "n" (.lit .jsnull))
                    (.seq
                      (.assign
                        "$exprV$16"
                        (.cond (.binop "==" (.name "u") (.lit .jsnull)) (.name "n") (.name "u")))
                      (.ret
                        (.cond
                          (.binop "==" (.name "$exprV$16") (.lit .jsnull))
                          (.lit (.int 3))
                          (.name "$exprV$16"))))))))) }

/-- `jsnode_cases.js::program:case_nullish_value`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_nullish_value : Func :=
  { name := "jsnode_cases.js::program:case_nullish_value"
  , params := ["this"]
  , body := (.ret
            (.cond (.binop "==" (.lit (.int 9)) (.lit .jsnull)) (.lit (.int 5)) (.lit (.int 9)))) }

/-- `jsnode_cases.js::program:case_nullish_single_quote`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_nullish_single_quote : Func :=
  { name := "jsnode_cases.js::program:case_nullish_single_quote"
  , params := ["this"]
  , body := (.ret
            (.cond (.binop "==" (.lit (.str "")) (.lit .jsnull)) (.lit (.str "d")) (.lit (.str "")))) }

/-- `jsnode_cases.js::program:case_nullish_single_quote_null`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_nullish_single_quote_null : Func :=
  { name := "jsnode_cases.js::program:case_nullish_single_quote_null"
  , params := ["this"]
  , body := (.ret
            (.cond (.binop "==" (.lit .jsnull) (.lit .jsnull)) (.lit (.str "d")) (.lit .jsnull))) }

/-- `jsnode_cases.js::program:case_nullish_var_zero`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_nullish_var_zero : Func :=
  { name := "jsnode_cases.js::program:case_nullish_var_zero"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "a" (.lit (.int 0)))
                (.seq
                  (.assign "b" (.lit (.int 5)))
                  (.ret (.cond (.binop "==" (.name "a") (.lit .jsnull)) (.name "b") (.name "a"))))))) }

/-- `jsnode_cases.js::program:case_nullish_var_null`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_nullish_var_null : Func :=
  { name := "jsnode_cases.js::program:case_nullish_var_null"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "a" (.lit .jsnull))
                (.seq
                  (.assign "b" (.lit (.int 5)))
                  (.ret (.cond (.binop "==" (.name "a") (.lit .jsnull)) (.name "b") (.name "a"))))))) }

/-- `jsnode_cases.js::program:case_nullish_short_circuit`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_nullish_short_circuit : Func :=
  { name := "jsnode_cases.js::program:case_nullish_short_circuit"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "c" (.lit (.int 0)))
                (.seq
                  (.seq
                    (.assign "$exprV$17" (.lit (.int 1)))
                    (.seq
                      (.ifte
                        (.binop "==" (.name "$exprV$17") (.lit .jsnull))
                        (.seq (.assign "c" (.lit (.int 9))) (.assign "$exprV$18" (.name "c")))
                        .skip)
                      (.assign
                        "r"
                        (.cond
                          (.binop "==" (.name "$exprV$17") (.lit .jsnull))
                          (.name "$exprV$18")
                          (.name "$exprV$17")))))
                  (.ret (.name "c")))))) }

/-- `jsnode_cases.js::program:case_nullish_right_effect`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_nullish_right_effect : Func :=
  { name := "jsnode_cases.js::program:case_nullish_right_effect"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "c" (.lit (.int 0)))
                (.seq
                  (.seq
                    (.assign "$exprV$19" (.lit .jsnull))
                    (.seq
                      (.ifte
                        (.binop "==" (.name "$exprV$19") (.lit .jsnull))
                        (.seq (.assign "c" (.lit (.int 9))) (.assign "$exprV$20" (.name "c")))
                        .skip)
                      (.assign
                        "r"
                        (.cond
                          (.binop "==" (.name "$exprV$19") (.lit .jsnull))
                          (.name "$exprV$20")
                          (.name "$exprV$19")))))
                  (.ret (.binop "+" (.name "c") (.name "r"))))))) }

/-- `jsnode_cases.js::program:case_nullish_impure_left`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_nullish_impure_left : Func :=
  { name := "jsnode_cases.js::program:case_nullish_impure_left"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "c" (.lit (.int 0)))
                (.seq
                  (.seq
                    (.assign "$exprV$21" (.name "c"))
                    (.seq
                      (.assign "c" (.binop "+" (.name "c") (.lit (.int 1))))
                      (.seq
                        (.assign "$exprV$22" (.name "$exprV$21"))
                        (.assign
                          "r"
                          (.cond
                            (.binop "==" (.name "$exprV$22") (.lit .jsnull))
                            (.lit (.int 4))
                            (.name "$exprV$22"))))))
                  (.ret (.binop "+" (.binop "*" (.name "r") (.lit (.int 100))) (.name "c"))))))) }

/-- `jsnode_cases.js::program:case_nullish_in_cond`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_nullish_in_cond : Func :=
  { name := "jsnode_cases.js::program:case_nullish_in_cond"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "z" (.lit (.int 0)))
              (.ret
                (.binop
                  "==="
                  (.cond (.binop "==" (.name "z") (.lit .jsnull)) (.lit (.int 5)) (.name "z"))
                  (.lit (.int 0)))))) }

/-- `jsnode_cases.js::program:case_or_zero`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_or_zero : Func :=
  { name := "jsnode_cases.js::program:case_or_zero"
  , params := ["this"]
  , body := (.ret (.binop "||" (.lit (.int 0)) (.lit (.int 5)))) }

/-- `jsnode_cases.js::program:case_and_zero`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_and_zero : Func :=
  { name := "jsnode_cases.js::program:case_and_zero"
  , params := ["this"]
  , body := (.ret (.binop "&&" (.lit (.int 0)) (.lit (.int 5)))) }

/-- `jsnode_cases.js::program:case_or_then_nullish`  (from `jsnode_cases.js`) -/
def f_jsnode_cases_js__program_case_or_then_nullish : Func :=
  { name := "jsnode_cases.js::program:case_or_then_nullish"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "z" (.lit (.int 0)))
              (.seq
                (.assign "$exprV$23" (.binop "||" (.name "z") (.lit (.int 8))))
                (.ret
                  (.cond
                    (.binop "==" (.name "$exprV$23") (.lit .jsnull))
                    (.lit (.int 1))
                    (.name "$exprV$23")))))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.javascript` (integer division/modulo convention). -/
def program : Program := { dialect := .javascript, funcs := [
  f_jsnode_cases_js__program_case_strict_str_vs_num,
  f_jsnode_cases_js__program,
  f_jsnode_cases_js__program_case_loose_same_type,
  f_jsnode_cases_js__program_case_strict_same_type,
  f_jsnode_cases_js__program_case_strict_ne_cross,
  f_jsnode_cases_js__program_case_loose_ne_same,
  f_jsnode_cases_js__program_case_strict_ne_same,
  f_jsnode_cases_js__program_case_strict_bool_vs_num,
  f_jsnode_cases_js__program_case_single_quote_eq,
  f_jsnode_cases_js__program_case_single_quote_ne,
  f_jsnode_cases_js__program_case_single_quote_cross,
  f_jsnode_cases_js__program_case_strict_nan,
  f_jsnode_cases_js__program_case_nan_ne,
  f_jsnode_cases_js__program_case_inf_strict,
  f_jsnode_cases_js__program_case_inf_vs_big,
  f_jsnode_cases_js__program_case_strict_negzero,
  f_jsnode_cases_js__program_case_strict_int_float,
  f_jsnode_cases_js__program_case_null_loose_zero,
  f_jsnode_cases_js__program_case_zero_loose_null,
  f_jsnode_cases_js__program_case_empty_str_loose_null,
  f_jsnode_cases_js__program_case_false_loose_null,
  f_jsnode_cases_js__program_case_null_loose_null,
  f_jsnode_cases_js__program_case_undef_loose_null,
  f_jsnode_cases_js__program_case_null_loose_undef,
  f_jsnode_cases_js__program_case_null_ne_zero,
  f_jsnode_cases_js__program_case_null_ne_null,
  f_jsnode_cases_js__program_case_zero_strict_null,
  f_jsnode_cases_js__program_case_null_strict_null,
  f_jsnode_cases_js__program_case_null_strict_undefined,
  f_jsnode_cases_js__program_case_undef_strict_undef,
  f_jsnode_cases_js__program_case_null_strict_ne_undefined,
  f_jsnode_cases_js__program_case_sar_neg,
  f_jsnode_cases_js__program_case_shr_neg,
  f_jsnode_cases_js__program_case_sar_neg16,
  f_jsnode_cases_js__program_case_shr_neg16,
  f_jsnode_cases_js__program_case_shl_sign,
  f_jsnode_cases_js__program_case_shr_var,
  f_jsnode_cases_js__program_case_sar_var_call,
  f_jsnode_cases_js__program_case_nullish_zero,
  f_jsnode_cases_js__program_case_nullish_empty,
  f_jsnode_cases_js__program_case_nullish_false,
  f_jsnode_cases_js__program_case_nullish_null,
  f_jsnode_cases_js__program_case_nullish_undef,
  f_jsnode_cases_js__program_case_nullish_chain,
  f_jsnode_cases_js__program_case_nullish_value,
  f_jsnode_cases_js__program_case_nullish_single_quote,
  f_jsnode_cases_js__program_case_nullish_single_quote_null,
  f_jsnode_cases_js__program_case_nullish_var_zero,
  f_jsnode_cases_js__program_case_nullish_var_null,
  f_jsnode_cases_js__program_case_nullish_short_circuit,
  f_jsnode_cases_js__program_case_nullish_right_effect,
  f_jsnode_cases_js__program_case_nullish_impure_left,
  f_jsnode_cases_js__program_case_nullish_in_cond,
  f_jsnode_cases_js__program_case_or_zero,
  f_jsnode_cases_js__program_case_and_zero,
  f_jsnode_cases_js__program_case_or_then_nullish
] }

end Autoform.Generated.JsNode