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
set_option maxRecDepth 8184

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
# JavaIntWidth — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.JavaIntWidth
open Autoform.Core

/-- `JavaIntWidth.case_long_mul:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_long_mul_long__ : Func :=
  { name := "JavaIntWidth.case_long_mul:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 100000)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 100000)))
                  (.ret (.binop "*:j64" (.name "a") (.name "b"))))))) }

/-- `JavaIntWidth.case_int_mul_wraps:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_int_mul_wraps_long__ : Func :=
  { name := "JavaIntWidth.case_int_mul_wraps:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 100000)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 100000)))
                  (.ret (.binop "*:j32" (.name "a") (.name "b"))))))) }

/-- `JavaIntWidth.case_mixed_mul:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_mixed_mul_long__ : Func :=
  { name := "JavaIntWidth.case_mixed_mul:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 3000000000)))
              (.seq
                .skip
                (.seq (.assign "b" (.lit (.int 2))) (.ret (.binop "*:j64" (.name "a") (.name "b"))))))) }

/-- `JavaIntWidth.case_long_accumulate:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_long_accumulate_long__ : Func :=
  { name := "JavaIntWidth.case_long_accumulate:long()"
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
                      (.assign "s" (.binop "+:j64" (.name "s") (.lit (.int 2000000000))))
                      (.assign "i" (.binop "+:j32" (.name "i") (.lit (.int 1)))))))
                (.ret (.name "s"))))) }

/-- `JavaIntWidth.case_int_add_wraps:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_int_add_wraps_long__ : Func :=
  { name := "JavaIntWidth.case_int_add_wraps:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 2147483647)))
              (.seq (.assign "x" (.binop "+:j32" (.name "x") (.lit (.int 1)))) (.ret (.name "x"))))) }

/-- `JavaIntWidth.case_ushr_int:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_ushr_int_long__ : Func :=
  { name := "JavaIntWidth.case_ushr_int:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.unop "-:j32" (.lit (.int 1))))
              (.ret (.binop ">>>:j32" (.name "x") (.lit (.int 28)))))) }

/-- `JavaIntWidth.case_shr_int:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_shr_int_long__ : Func :=
  { name := "JavaIntWidth.case_shr_int:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.unop "-:j32" (.lit (.int 16))))
              (.ret (.binop ">>:j32" (.name "x") (.lit (.int 1)))))) }

/-- `JavaIntWidth.case_ushr_long:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_ushr_long_long__ : Func :=
  { name := "JavaIntWidth.case_ushr_long:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.unop "-:j64" (.lit (.int 1))))
              (.ret (.binop ">>>:j64" (.name "x") (.lit (.int 60)))))) }

/-- `JavaIntWidth.case_shr_long:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_shr_long_long__ : Func :=
  { name := "JavaIntWidth.case_shr_long:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.unop "-:j64" (.lit (.int 4294967296))))
              (.ret (.binop ">>:j64" (.name "x") (.lit (.int 4)))))) }

/-- `JavaIntWidth.case_shr_assign:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_shr_assign_long__ : Func :=
  { name := "JavaIntWidth.case_shr_assign:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.unop "-:j32" (.lit (.int 16))))
              (.seq (.assign "x" (.binop ">>:j32" (.name "x") (.lit (.int 2)))) (.ret (.name "x"))))) }

/-- `JavaIntWidth.case_shl_masked_int:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_shl_masked_int_long__ : Func :=
  { name := "JavaIntWidth.case_shl_masked_int:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 1)))
              (.ret (.binop "<<:j32" (.name "x") (.lit (.int 33)))))) }

/-- `JavaIntWidth.case_shl_long:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_shl_long_long__ : Func :=
  { name := "JavaIntWidth.case_shl_long:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 1)))
              (.ret (.binop "<<:j64" (.name "x") (.lit (.int 33)))))) }

/-- `JavaIntWidth.case_byte_compound:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_byte_compound_long__ : Func :=
  { name := "JavaIntWidth.case_byte_compound:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "b" (.lit (.int 127)))
              (.seq
                (.assign "b" (.unop "cast:i8" (.binop "+:j32" (.name "b") (.lit (.int 1)))))
                (.ret (.name "b"))))) }

/-- `JavaIntWidth.case_byte_increment:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_byte_increment_long__ : Func :=
  { name := "JavaIntWidth.case_byte_increment:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "b" (.lit (.int 127)))
              (.seq
                (.assign "b" (.unop "cast:i8" (.binop "+:j32" (.name "b") (.lit (.int 1)))))
                (.ret (.name "b"))))) }

/-- `JavaIntWidth.case_char_increment:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_char_increment_long__ : Func :=
  { name := "JavaIntWidth.case_char_increment:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "c" (.lit (.int 65535)))
              (.seq
                (.assign "c" (.unop "cast:u16" (.binop "+:j32" (.name "c") (.lit (.int 1)))))
                (.ret (.name "c"))))) }

/-- `JavaIntWidth.case_int_compound_long:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_int_compound_long_long__ : Func :=
  { name := "JavaIntWidth.case_int_compound_long:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "x" (.lit (.int 1)))
              (.seq
                .skip
                (.seq
                  (.assign "big" (.lit (.int 4294967296)))
                  (.seq
                    (.assign "x" (.unop "cast:i32" (.binop "+:j64" (.name "x") (.name "big"))))
                    (.ret (.name "x"))))))) }

/-- `JavaIntWidth.case_min_div:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_min_div_long__ : Func :=
  { name := "JavaIntWidth.case_min_div:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "m" (.unop "-:j32" (.lit (.int 2147483648))))
              (.ret (.binop "/:j32" (.name "m") (.unop "-:j32" (.lit (.int 1))))))) }

/-- `JavaIntWidth.case_min_rem:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_min_rem_long__ : Func :=
  { name := "JavaIntWidth.case_min_rem:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "m" (.unop "-:j32" (.lit (.int 2147483648))))
              (.ret (.binop "%:j32" (.name "m") (.unop "-:j32" (.lit (.int 1))))))) }

/-- `JavaIntWidth.case_long_div:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_long_div_long__ : Func :=
  { name := "JavaIntWidth.case_long_div:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "d" (.unop "-:j64" (.lit (.int 7000000000))))
              (.ret (.binop "/:j64" (.name "d") (.lit (.int 2)))))) }

/-- `JavaIntWidth.case_long_not:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_long_not_long__ : Func :=
  { name := "JavaIntWidth.case_long_not:long()"
  , params := []
  , body := (.seq .skip (.seq (.assign "z" (.lit (.int 0))) (.ret (.unop "~:j64" (.name "z"))))) }

/-- `JavaIntWidth.case_int_neg_min:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_int_neg_min_long__ : Func :=
  { name := "JavaIntWidth.case_int_neg_min:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "y" (.unop "-:j32" (.lit (.int 2147483648))))
              (.ret (.unop "-:j32" (.name "y"))))) }

/-- `JavaIntWidth.case_boxed_mul:long()`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_case_boxed_mul_long__ : Func :=
  { name := "JavaIntWidth.case_boxed_mul:long()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.assign "a" (.lit (.int 100000)))
              (.seq
                .skip
                (.seq
                  (.assign "b" (.lit (.int 100000)))
                  (.ret (.binop "*:j64" (.name "a") (.name "b"))))))) }

/-- `JavaIntWidth.main:void(java.lang.String[])`  (from `JavaIntWidth.java`) -/
def f_JavaIntWidth_main_void_java_lang_String___ : Func :=
  { name := "JavaIntWidth.main:void(java.lang.String[])"
  , params := ["args"]
  , body := (.seq
            (.expr
              (.mcall
                (.name "System")
                "out"
                [ (.binop
                    "+"
                    (.lit (.str "case_long_mul "))
                    (.call "JavaIntWidth.case_long_mul:long()" [])) ]))
            (.seq
              (.expr
                (.mcall
                  (.name "System")
                  "out"
                  [ (.binop
                      "+"
                      (.lit (.str "case_int_mul_wraps "))
                      (.call "JavaIntWidth.case_int_mul_wraps:long()" [])) ]))
              (.seq
                (.expr
                  (.mcall
                    (.name "System")
                    "out"
                    [ (.binop
                        "+"
                        (.lit (.str "case_mixed_mul "))
                        (.call "JavaIntWidth.case_mixed_mul:long()" [])) ]))
                (.seq
                  (.expr
                    (.mcall
                      (.name "System")
                      "out"
                      [ (.binop
                          "+"
                          (.lit (.str "case_long_accumulate "))
                          (.call "JavaIntWidth.case_long_accumulate:long()" [])) ]))
                  (.seq
                    (.expr
                      (.mcall
                        (.name "System")
                        "out"
                        [ (.binop
                            "+"
                            (.lit (.str "case_int_add_wraps "))
                            (.call "JavaIntWidth.case_int_add_wraps:long()" [])) ]))
                    (.seq
                      (.expr
                        (.mcall
                          (.name "System")
                          "out"
                          [ (.binop
                              "+"
                              (.lit (.str "case_ushr_int "))
                              (.call "JavaIntWidth.case_ushr_int:long()" [])) ]))
                      (.seq
                        (.expr
                          (.mcall
                            (.name "System")
                            "out"
                            [ (.binop
                                "+"
                                (.lit (.str "case_shr_int "))
                                (.call "JavaIntWidth.case_shr_int:long()" [])) ]))
                        (.seq
                          (.expr
                            (.mcall
                              (.name "System")
                              "out"
                              [ (.binop
                                  "+"
                                  (.lit (.str "case_ushr_long "))
                                  (.call "JavaIntWidth.case_ushr_long:long()" [])) ]))
                          (.seq
                            (.expr
                              (.mcall
                                (.name "System")
                                "out"
                                [ (.binop
                                    "+"
                                    (.lit (.str "case_shr_long "))
                                    (.call "JavaIntWidth.case_shr_long:long()" [])) ]))
                            (.seq
                              (.expr
                                (.mcall
                                  (.name "System")
                                  "out"
                                  [ (.binop
                                      "+"
                                      (.lit (.str "case_shr_assign "))
                                      (.call "JavaIntWidth.case_shr_assign:long()" [])) ]))
                              (.seq
                                (.expr
                                  (.mcall
                                    (.name "System")
                                    "out"
                                    [ (.binop
                                        "+"
                                        (.lit (.str "case_shl_masked_int "))
                                        (.call "JavaIntWidth.case_shl_masked_int:long()" [])) ]))
                                (.seq
                                  (.expr
                                    (.mcall
                                      (.name "System")
                                      "out"
                                      [ (.binop
                                        "+"
                                        (.lit (.str "case_shl_long "))
                                        (.call "JavaIntWidth.case_shl_long:long()" [])) ]))
                                  (.seq
                                    (.expr
                                      (.mcall
                                        (.name "System")
                                        "out"
                                        [ (.binop
                                        "+"
                                        (.lit (.str "case_byte_compound "))
                                        (.call "JavaIntWidth.case_byte_compound:long()" [])) ]))
                                    (.seq
                                      (.expr
                                        (.mcall
                                        (.name "System")
                                        "out"
                                        [ (.binop
                                        "+"
                                        (.lit (.str "case_byte_increment "))
                                        (.call "JavaIntWidth.case_byte_increment:long()" [])) ]))
                                      (.seq
                                        (.expr
                                        (.mcall
                                        (.name "System")
                                        "out"
                                        [ (.binop
                                        "+"
                                        (.lit (.str "case_char_increment "))
                                        (.call "JavaIntWidth.case_char_increment:long()" [])) ]))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.name "System")
                                        "out"
                                        [ (.binop
                                        "+"
                                        (.lit (.str "case_int_compound_long "))
                                        (.call "JavaIntWidth.case_int_compound_long:long()" [])) ]))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.name "System")
                                        "out"
                                        [ (.binop
                                        "+"
                                        (.lit (.str "case_min_div "))
                                        (.call "JavaIntWidth.case_min_div:long()" [])) ]))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.name "System")
                                        "out"
                                        [ (.binop
                                        "+"
                                        (.lit (.str "case_min_rem "))
                                        (.call "JavaIntWidth.case_min_rem:long()" [])) ]))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.name "System")
                                        "out"
                                        [ (.binop
                                        "+"
                                        (.lit (.str "case_long_div "))
                                        (.call "JavaIntWidth.case_long_div:long()" [])) ]))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.name "System")
                                        "out"
                                        [ (.binop
                                        "+"
                                        (.lit (.str "case_long_not "))
                                        (.call "JavaIntWidth.case_long_not:long()" [])) ]))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.name "System")
                                        "out"
                                        [ (.binop
                                        "+"
                                        (.lit (.str "case_int_neg_min "))
                                        (.call "JavaIntWidth.case_int_neg_min:long()" [])) ]))
                                        (.expr
                                        (.mcall
                                        (.name "System")
                                        "out"
                                        [ (.binop
                                        "+"
                                        (.lit (.str "case_boxed_mul "))
                                        (.call "JavaIntWidth.case_boxed_mul:long()" [])) ]))))))))))))))))))))))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_JavaIntWidth_case_long_mul_long__,
  f_JavaIntWidth_case_int_mul_wraps_long__,
  f_JavaIntWidth_case_mixed_mul_long__,
  f_JavaIntWidth_case_long_accumulate_long__,
  f_JavaIntWidth_case_int_add_wraps_long__,
  f_JavaIntWidth_case_ushr_int_long__,
  f_JavaIntWidth_case_shr_int_long__,
  f_JavaIntWidth_case_ushr_long_long__,
  f_JavaIntWidth_case_shr_long_long__,
  f_JavaIntWidth_case_shr_assign_long__,
  f_JavaIntWidth_case_shl_masked_int_long__,
  f_JavaIntWidth_case_shl_long_long__,
  f_JavaIntWidth_case_byte_compound_long__,
  f_JavaIntWidth_case_byte_increment_long__,
  f_JavaIntWidth_case_char_increment_long__,
  f_JavaIntWidth_case_int_compound_long_long__,
  f_JavaIntWidth_case_min_div_long__,
  f_JavaIntWidth_case_min_rem_long__,
  f_JavaIntWidth_case_long_div_long__,
  f_JavaIntWidth_case_long_not_long__,
  f_JavaIntWidth_case_int_neg_min_long__,
  f_JavaIntWidth_case_boxed_mul_long__,
  f_JavaIntWidth_main_void_java_lang_String___
] }

end Autoform.Generated.JavaIntWidth