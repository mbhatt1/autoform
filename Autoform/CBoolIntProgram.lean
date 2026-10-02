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
set_option maxRecDepth 8152

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
# CBoolInt — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.CBoolInt
open Autoform.Core

/-- `lt_flag`  (from `cboolint_cases.c`) -/
def f_lt_flag : Func :=
  { name := "lt_flag"
  , params := ["a", "b"]
  , body := (.seq
            .skip
            (.seq
              (.assign "t" (.binop "<:i32" (.name "a") (.name "b")))
              (.seq
                (.ifte (.binop "==:i32" (.name "t") (.lit (.int 1))) (.ret (.lit (.int 7))) .skip)
                (.ret (.lit (.int 3)))))) }

/-- `is_fatal`  (from `cboolint_cases.c`) -/
def f_is_fatal : Func :=
  { name := "is_fatal"
  , params := ["rc"]
  , body := (.ret
            (.binop
              "&&"
              (.binop
                "&&"
                (.binop "!=:i32" (.name "rc") (.lit (.int 0)))
                (.binop "!=:i32" (.name "rc") (.lit (.int 5))))
              (.binop "!=:i32" (.name "rc") (.lit (.int 6))))) }

/-- `both_ways`  (from `cboolint_cases.c`) -/
def f_both_ways : Func :=
  { name := "both_ways"
  , params := ["a", "b"]
  , body := (.ret
            (.binop
              "+:i32"
              (.binop "<:i32" (.name "a") (.name "b"))
              (.binop "<:i32" (.name "b") (.name "a")))) }

/-- `case_lt_flag_true`  (from `cboolint_cases.c`) -/
def f_case_lt_flag_true : Func :=
  { name := "case_lt_flag_true"
  , params := [""]
  , body := (.ret (.call "lt_flag" [(.lit (.int 3)), (.lit (.int 12))])) }

/-- `case_lt_flag_false`  (from `cboolint_cases.c`) -/
def f_case_lt_flag_false : Func :=
  { name := "case_lt_flag_false"
  , params := [""]
  , body := (.ret (.call "lt_flag" [(.lit (.int 12)), (.lit (.int 3))])) }

/-- `case_cmp_eq_one`  (from `cboolint_cases.c`) -/
def f_case_cmp_eq_one : Func :=
  { name := "case_cmp_eq_one"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 3)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 12)))
                  (.ret (.binop "==:i32" (.binop "<:i32" (.name "a") (.name "b")) (.lit (.int 1)))))))) }

/-- `case_cmp_plus_cmp`  (from `cboolint_cases.c`) -/
def f_case_cmp_plus_cmp : Func :=
  { name := "case_cmp_plus_cmp"
  , params := [""]
  , body := (.ret
            (.binop
              "+:i32"
              (.call "both_ways" [(.lit (.int 3)), (.lit (.int 12))])
              (.call "both_ways" [(.lit (.int 5)), (.lit (.int 5))]))) }

/-- `case_logical_times`  (from `cboolint_cases.c`) -/
def f_case_logical_times : Func :=
  { name := "case_logical_times"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.call "is_fatal" [(.lit (.int 4))]))
              (.ret
                (.binop
                  "+:i32"
                  (.binop "*:i32" (.name "x") (.lit (.int 10)))
                  (.call "is_fatal" [(.lit (.int 5))]))))) }

/-- `case_not_plus`  (from `cboolint_cases.c`) -/
def f_case_not_plus : Func :=
  { name := "case_not_plus"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 0)))
              (.ret (.binop "+:i32" (.unop "!" (.name "a")) (.lit (.int 1)))))) }

/-- `case_neg_cmp`  (from `cboolint_cases.c`) -/
def f_case_neg_cmp : Func :=
  { name := "case_neg_cmp"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 1)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 2)))
                  (.ret (.unop "-:i32" (.binop "<:i32" (.name "a") (.name "b")))))))) }

/-- `case_bnot_cmp`  (from `cboolint_cases.c`) -/
def f_case_bnot_cmp : Func :=
  { name := "case_bnot_cmp"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 1)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 2)))
                  (.ret (.unop "~:i32" (.binop ">:i32" (.name "a") (.name "b")))))))) }

/-- `case_bitand_cmps`  (from `cboolint_cases.c`) -/
def f_case_bitand_cmps : Func :=
  { name := "case_bitand_cmps"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 1)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 2)))
                  (.ret
                    (.binop
                      "+:i32"
                      (.binop
                        "&:i32"
                        (.binop "<:i32" (.name "a") (.name "b"))
                        (.binop ">:i32" (.name "b") (.lit (.int 0))))
                      (.lit (.int 2)))))))) }

/-- `case_xor_cmps`  (from `cboolint_cases.c`) -/
def f_case_xor_cmps : Func :=
  { name := "case_xor_cmps"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 1)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 2)))
                  (.ret
                    (.binop
                      "+:i32"
                      (.binop
                        "^:i32"
                        (.binop "<:i32" (.name "a") (.name "b"))
                        (.binop ">:i32" (.name "b") (.lit (.int 0))))
                      (.lit (.int 4)))))))) }

/-- `case_shift_cmp`  (from `cboolint_cases.c`) -/
def f_case_shift_cmp : Func :=
  { name := "case_shift_cmp"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 1)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 2)))
                  (.ret (.binop "<<:i32" (.binop "<:i32" (.name "a") (.name "b")) (.lit (.int 3)))))))) }

/-- `case_cmp_vs_cmp`  (from `cboolint_cases.c`) -/
def f_case_cmp_vs_cmp : Func :=
  { name := "case_cmp_vs_cmp"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 1)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 2)))
                  (.ret
                    (.binop
                      ">:i32"
                      (.binop "<:i32" (.name "a") (.name "b"))
                      (.binop "<:i32" (.name "b") (.name "a")))))))) }

/-- `case_sum_flags`  (from `cboolint_cases.c`) -/
def f_case_sum_flags : Func :=
  { name := "case_sum_flags"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "n" (.lit (.int 0)))
              (.seq
                .skip
                (.seq
                  (.assign "i" (.lit (.int 0)))
                  (.seq
                    (.loop
                      (.binop "<:i32" (.name "i") (.lit (.int 10)))
                      (.seq
                        (.assign
                          "n"
                          (.binop
                            "+:i32"
                            (.name "n")
                            (.binop
                              "==:i32"
                              (.binop "%:i32" (.name "i") (.lit (.int 3)))
                              (.lit (.int 0)))))
                        (.assign "i" (.binop "+:i32" (.name "i") (.lit (.int 1))))))
                    (.ret (.name "n"))))))) }

/-- `case_cmp_plus_double`  (from `cboolint_cases.c`) -/
def f_case_cmp_plus_double : Func :=
  { name := "case_cmp_plus_double"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 1)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 2)))
                  (.seq
                    (.ifte
                      (.binop
                        ">"
                        (.binop
                          "+"
                          (.binop "<:i32" (.name "a") (.name "b"))
                          (.lit (.float (Fl.ofBits 4602678819172646912))))
                        (.lit (.float (Fl.ofBits 4607182418800017408))))
                      (.ret (.lit (.int 1)))
                      .skip)
                    (.ret (.lit (.int 0)))))))) }

/-- `case_direct_return`  (from `cboolint_cases.c`) -/
def f_case_direct_return : Func :=
  { name := "case_direct_return"
  , params := [""]
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 1)))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 2))) (.ret (.binop "<:i32" (.name "a") (.name "b"))))))) }

/-- `cboolint_cases.c:<global>`  (from `cboolint_cases.c`) -/
def f_cboolint_cases_c__global_ : Func :=
  { name := "cboolint_cases.c:<global>"
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
                                    (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := [f_cboolint_cases_c__global_]

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_lt_flag,
  f_is_fatal,
  f_both_ways,
  f_case_lt_flag_true,
  f_case_lt_flag_false,
  f_case_cmp_eq_one,
  f_case_cmp_plus_cmp,
  f_case_logical_times,
  f_case_not_plus,
  f_case_neg_cmp,
  f_case_bnot_cmp,
  f_case_bitand_cmps,
  f_case_xor_cmps,
  f_case_shift_cmp,
  f_case_cmp_vs_cmp,
  f_case_sum_flags,
  f_case_cmp_plus_double,
  f_case_direct_return,
  f_cboolint_cases_c__global_
] }

end Autoform.Generated.CBoolInt