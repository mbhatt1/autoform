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
set_option maxRecDepth 8376

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
# PyArith — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.PyArith
open Autoform.Core

/-- `pyarith_cases.py:<module>.case_div_7_2`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_div_7_2 : Func :=
  { name := "pyarith_cases.py:<module>.case_div_7_2"
  , params := []
  , body := (.seq
            (.assign "a" (.lit (.int 7)))
            (.seq
              .skip
              (.seq
                (.assign "b" (.lit (.int 2)))
                (.seq .skip (.ret (.binop "/" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_div_neg7_2`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_div_neg7_2 : Func :=
  { name := "pyarith_cases.py:<module>.case_div_neg7_2"
  , params := []
  , body := (.seq
            (.assign "a" (.unop "-" (.lit (.int 7))))
            (.seq
              .skip
              (.seq
                (.assign "b" (.lit (.int 2)))
                (.seq .skip (.ret (.binop "/" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_div_7_neg2`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_div_7_neg2 : Func :=
  { name := "pyarith_cases.py:<module>.case_div_7_neg2"
  , params := []
  , body := (.seq
            (.assign "a" (.lit (.int 7)))
            (.seq
              .skip
              (.seq
                (.assign "b" (.unop "-" (.lit (.int 2))))
                (.seq .skip (.ret (.binop "/" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_div_exact_is_float`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_div_exact_is_float : Func :=
  { name := "pyarith_cases.py:<module>.case_div_exact_is_float"
  , params := []
  , body := (.seq
            (.assign "a" (.lit (.int 6)))
            (.seq
              .skip
              (.seq
                (.assign "b" (.lit (.int 3)))
                (.seq .skip (.ret (.binop "/" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_div_zero`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_div_zero : Func :=
  { name := "pyarith_cases.py:<module>.case_div_zero"
  , params := []
  , body := (.seq
            (.assign "a" (.lit (.int 1)))
            (.seq
              .skip
              (.seq
                (.assign "b" (.lit (.int 0)))
                (.seq .skip (.ret (.binop "/" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_div_zero_numerator_negative_divisor`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_div_zero_numerator_negative_divisor : Func :=
  { name := "pyarith_cases.py:<module>.case_div_zero_numerator_negative_divisor"
  , params := []
  , body := (.seq
            (.assign "a" (.lit (.int 0)))
            (.seq
              .skip
              (.seq
                (.assign "b" (.unop "-" (.lit (.int 3))))
                (.seq .skip (.ret (.binop "/" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_div_one_third`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_div_one_third : Func :=
  { name := "pyarith_cases.py:<module>.case_div_one_third"
  , params := []
  , body := (.seq
            (.assign "a" (.lit (.int 1)))
            (.seq
              .skip
              (.seq
                (.assign "b" (.lit (.int 3)))
                (.seq .skip (.ret (.binop "/" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_div_exactly_2pow53`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_div_exactly_2pow53 : Func :=
  { name := "pyarith_cases.py:<module>.case_div_exactly_2pow53"
  , params := []
  , body := (.seq
            (.assign "a" (.lit (.int 9007199254740992)))
            (.seq
              .skip
              (.seq
                (.assign "b" (.lit (.int 2)))
                (.seq .skip (.ret (.binop "/" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_div_beyond_2pow53`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_div_beyond_2pow53 : Func :=
  { name := "pyarith_cases.py:<module>.case_div_beyond_2pow53"
  , params := []
  , body := (.seq
            (.assign "a" (.lit (.int 9007199254740993)))
            (.seq
              .skip
              (.seq
                (.assign "b" (.lit (.int 2)))
                (.seq .skip (.ret (.binop "/" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_div_big_int`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_div_big_int : Func :=
  { name := "pyarith_cases.py:<module>.case_div_big_int"
  , params := []
  , body := (.seq
            (.assign "a" (.lit (.int 1000000000000000000000000000000)))
            (.seq
              .skip
              (.seq
                (.assign "b" (.lit (.int 7)))
                (.seq .skip (.ret (.binop "/" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_div_big_divisor`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_div_big_divisor : Func :=
  { name := "pyarith_cases.py:<module>.case_div_big_divisor"
  , params := []
  , body := (.seq
            (.assign "a" (.lit (.int 1)))
            (.seq
              .skip
              (.seq
                (.assign "b" (.lit (.int 9007199254740993)))
                (.seq .skip (.ret (.binop "/" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_div_int_float`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_div_int_float : Func :=
  { name := "pyarith_cases.py:<module>.case_div_int_float"
  , params := []
  , body := (.seq
            (.assign "a" (.lit (.int 7)))
            (.seq
              .skip
              (.seq
                (.assign "b" (.lit (.float (Fl.ofBits 4611686018427387904))))
                (.seq .skip (.ret (.binop "/" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_div_float_float`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_div_float_float : Func :=
  { name := "pyarith_cases.py:<module>.case_div_float_float"
  , params := []
  , body := (.seq
            (.assign "a" (.lit (.float (Fl.ofBits 4620130267728707584))))
            (.seq
              .skip
              (.seq
                (.assign "b" (.lit (.float (Fl.ofBits 4612811918334230528))))
                (.seq .skip (.ret (.binop "/" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_floordiv_7_2`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_floordiv_7_2 : Func :=
  { name := "pyarith_cases.py:<module>.case_floordiv_7_2"
  , params := []
  , body := (.seq
            (.assign "a" (.lit (.int 7)))
            (.seq
              .skip
              (.seq
                (.assign "b" (.lit (.int 2)))
                (.seq .skip (.ret (.binop "//" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_floordiv_neg7_2`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_floordiv_neg7_2 : Func :=
  { name := "pyarith_cases.py:<module>.case_floordiv_neg7_2"
  , params := []
  , body := (.seq
            (.assign "a" (.unop "-" (.lit (.int 7))))
            (.seq
              .skip
              (.seq
                (.assign "b" (.lit (.int 2)))
                (.seq .skip (.ret (.binop "//" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_floordiv_7_neg2`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_floordiv_7_neg2 : Func :=
  { name := "pyarith_cases.py:<module>.case_floordiv_7_neg2"
  , params := []
  , body := (.seq
            (.assign "a" (.lit (.int 7)))
            (.seq
              .skip
              (.seq
                (.assign "b" (.unop "-" (.lit (.int 2))))
                (.seq .skip (.ret (.binop "//" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_floordiv_zero`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_floordiv_zero : Func :=
  { name := "pyarith_cases.py:<module>.case_floordiv_zero"
  , params := []
  , body := (.seq
            (.assign "a" (.lit (.int 1)))
            (.seq
              .skip
              (.seq
                (.assign "b" (.lit (.int 0)))
                (.seq .skip (.ret (.binop "//" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_mod_neg7_3`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_mod_neg7_3 : Func :=
  { name := "pyarith_cases.py:<module>.case_mod_neg7_3"
  , params := []
  , body := (.seq
            (.assign "a" (.unop "-" (.lit (.int 7))))
            (.seq
              .skip
              (.seq
                (.assign "b" (.lit (.int 3)))
                (.seq .skip (.ret (.binop "%" (.name "a") (.name "b"))))))) }

/-- `pyarith_cases.py:<module>.case_div_and_floordiv_together`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_div_and_floordiv_together : Func :=
  { name := "pyarith_cases.py:<module>.case_div_and_floordiv_together"
  , params := []
  , body := (.seq
            (.assign "a" (.lit (.int 7)))
            (.seq
              .skip
              (.seq
                (.assign "b" (.lit (.int 2)))
                (.seq
                  .skip
                  (.ret
                    (.tupleE
                      [ (.binop "/" (.name "a") (.name "b"))
                      , (.binop "//" (.name "a") (.name "b"))
                      , (.binop "%" (.name "a") (.name "b")) ])))))) }

/-- `pyarith_cases.py:<module>.case_bool_eq_int`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_eq_int : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_eq_int"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.seq
                (.assign "one" (.lit (.int 1)))
                (.seq
                  .skip
                  (.ret
                    (.tupleE
                      [ (.binop "==" (.name "t") (.name "one"))
                      , (.binop "==" (.name "one") (.name "t"))
                      , (.binop "!=" (.name "t") (.name "one")) ])))))) }

/-- `pyarith_cases.py:<module>.case_bool_ne_int`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_ne_int : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_ne_int"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.seq
                (.assign "two" (.lit (.int 2)))
                (.seq
                  .skip
                  (.ret
                    (.tupleE
                      [ (.binop "==" (.name "t") (.name "two"))
                      , (.binop "!=" (.name "t") (.name "two")) ])))))) }

/-- `pyarith_cases.py:<module>.case_false_eq_zero`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_false_eq_zero : Func :=
  { name := "pyarith_cases.py:<module>.case_false_eq_zero"
  , params := []
  , body := (.seq
            (.assign "f" (.lit (.bool false)))
            (.seq
              .skip
              (.seq
                (.assign "zero" (.lit (.int 0)))
                (.seq
                  .skip
                  (.ret
                    (.tupleE
                      [ (.binop "==" (.name "f") (.name "zero"))
                      , (.binop "==" (.name "zero") (.name "f")) ])))))) }

/-- `pyarith_cases.py:<module>.case_bool_eq_float`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_eq_float : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_eq_float"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.seq
                (.assign "x" (.lit (.float (Fl.ofBits 4607182418800017408))))
                (.seq
                  .skip
                  (.ret
                    (.tupleE
                      [(.binop "==" (.name "t") (.name "x")), (.binop "==" (.name "x") (.name "t"))])))))) }

/-- `pyarith_cases.py:<module>.case_bool_add_int`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_add_int : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_add_int"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.seq
                (.assign "one" (.lit (.int 1)))
                (.seq
                  .skip
                  (.ret
                    (.tupleE
                      [ (.binop "+" (.name "t") (.name "one"))
                      , (.binop "+" (.name "one") (.name "t")) ])))))) }

/-- `pyarith_cases.py:<module>.case_bool_add_bool`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_add_bool : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_add_bool"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq .skip (.ret (.binop "+" (.name "t") (.name "t"))))) }

/-- `pyarith_cases.py:<module>.case_bool_sub`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_sub : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_sub"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.seq
                (.assign "f" (.lit (.bool false)))
                (.seq
                  .skip
                  (.ret
                    (.tupleE
                      [ (.binop "-" (.name "f") (.name "t"))
                      , (.binop "-" (.lit (.int 2)) (.name "t"))
                      , (.binop "-" (.name "t") (.lit (.int 1))) ])))))) }

/-- `pyarith_cases.py:<module>.case_bool_mul`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_mul : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_mul"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.seq
                (.assign "f" (.lit (.bool false)))
                (.seq
                  .skip
                  (.seq
                    (.assign "five" (.lit (.int 5)))
                    (.seq
                      .skip
                      (.ret
                        (.tupleE
                          [ (.binop "*" (.name "t") (.name "five"))
                          , (.binop "*" (.name "five") (.name "f")) ])))))))) }

/-- `pyarith_cases.py:<module>.case_bool_neg`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_neg : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_neg"
  , params := []
  , body := (.seq (.assign "t" (.lit (.bool true))) (.seq .skip (.ret (.unop "-" (.name "t"))))) }

/-- `pyarith_cases.py:<module>.case_bool_invert`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_invert : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_invert"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.seq
                (.assign "f" (.lit (.bool false)))
                (.seq .skip (.ret (.tupleE [(.unop "~" (.name "t")), (.unop "~" (.name "f"))])))))) }

/-- `pyarith_cases.py:<module>.case_bool_lt`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_lt : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_lt"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.seq
                (.assign "two" (.lit (.int 2)))
                (.seq
                  .skip
                  (.ret
                    (.tupleE
                      [ (.binop "<" (.name "t") (.name "two"))
                      , (.binop ">" (.name "two") (.name "t"))
                      , (.binop "<=" (.name "t") (.lit (.int 1)))
                      , (.binop ">=" (.name "t") (.lit (.int 2))) ])))))) }

/-- `pyarith_cases.py:<module>.case_bool_div`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_div : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_div"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.seq
                (.assign "two" (.lit (.int 2)))
                (.seq
                  .skip
                  (.ret
                    (.tupleE
                      [ (.binop "/" (.name "t") (.name "two"))
                      , (.binop "/" (.name "two") (.name "t")) ])))))) }

/-- `pyarith_cases.py:<module>.case_bool_div_zero`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_div_zero : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_div_zero"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.seq
                (.assign "f" (.lit (.bool false)))
                (.seq .skip (.ret (.binop "/" (.name "t") (.name "f"))))))) }

/-- `pyarith_cases.py:<module>.case_bool_floordiv_mod`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_floordiv_mod : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_floordiv_mod"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.seq
                (.assign "two" (.lit (.int 2)))
                (.seq
                  .skip
                  (.ret
                    (.tupleE
                      [ (.binop "//" (.name "t") (.name "two"))
                      , (.binop "//" (.name "two") (.name "t"))
                      , (.binop "%" (.name "t") (.name "two"))
                      , (.binop "%" (.name "two") (.name "t")) ])))))) }

/-- `pyarith_cases.py:<module>.case_bool_shift`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_shift : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_shift"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.seq
                (.assign "three" (.lit (.int 3)))
                (.seq
                  .skip
                  (.ret
                    (.tupleE
                      [ (.binop "<<" (.name "t") (.name "three"))
                      , (.binop ">>" (.name "three") (.name "t")) ])))))) }

/-- `pyarith_cases.py:<module>.case_bool_and_stays_bool`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_and_stays_bool : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_and_stays_bool"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.seq
                (.assign "f" (.lit (.bool false)))
                (.seq
                  .skip
                  (.ret
                    (.tupleE
                      [ (.binop "&" (.name "t") (.name "t"))
                      , (.binop "&" (.name "t") (.name "f"))
                      , (.binop "&" (.name "f") (.name "f")) ])))))) }

/-- `pyarith_cases.py:<module>.case_bool_or_stays_bool`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_or_stays_bool : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_or_stays_bool"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.seq
                (.assign "f" (.lit (.bool false)))
                (.seq
                  .skip
                  (.ret
                    (.tupleE
                      [ (.binop "|" (.name "t") (.name "t"))
                      , (.binop "|" (.name "t") (.name "f"))
                      , (.binop "|" (.name "f") (.name "f")) ])))))) }

/-- `pyarith_cases.py:<module>.case_bool_xor_stays_bool`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_xor_stays_bool : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_xor_stays_bool"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.seq
                (.assign "f" (.lit (.bool false)))
                (.seq
                  .skip
                  (.ret
                    (.tupleE
                      [ (.binop "^" (.name "t") (.name "t"))
                      , (.binop "^" (.name "t") (.name "f"))
                      , (.binop "^" (.name "f") (.name "f")) ])))))) }

/-- `pyarith_cases.py:<module>.case_bool_bitwise_with_int`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_bitwise_with_int : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_bitwise_with_int"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.seq
                (.assign "three" (.lit (.int 3)))
                (.seq
                  .skip
                  (.ret
                    (.tupleE
                      [ (.binop "&" (.name "t") (.name "three"))
                      , (.binop "|" (.name "three") (.name "t"))
                      , (.binop "^" (.name "t") (.name "three")) ])))))) }

/-- `pyarith_cases.py:<module>.case_bool_plus_float`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_plus_float : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_plus_float"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.seq
                (.assign "x" (.lit (.float (Fl.ofBits 4609434218613702656))))
                (.seq
                  .skip
                  (.ret
                    (.tupleE
                      [(.binop "+" (.name "t") (.name "x")), (.binop "*" (.name "x") (.name "t"))])))))) }

/-- `pyarith_cases.py:<module>.case_not_bool`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_not_bool : Func :=
  { name := "pyarith_cases.py:<module>.case_not_bool"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq .skip (.ret (.tupleE [(.unop "!" (.name "t")), (.unop "!" (.lit (.int 0)))])))) }

/-- `pyarith_cases.py:<module>.case_bool_dict_key_lookup`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_dict_key_lookup : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_dict_key_lookup"
  , params := []
  , body := (.seq
            (.seq
              (.assign "tmp0" (.boxContainer (.dictE [])))
              (.seq
                (.setIndex (.name "tmp0") (.lit (.int 1)) (.lit (.str "a")))
                (.seq
                  (.setIndex (.name "tmp0") (.lit (.int 0)) (.lit (.str "b")))
                  (.assign "d" (.name "tmp0")))))
            (.seq
              .skip
              (.seq
                (.assign "t" (.lit (.bool true)))
                (.seq
                  .skip
                  (.seq
                    (.assign "f" (.lit (.bool false)))
                    (.seq
                      .skip
                      (.seq
                        (.ret
                          (.tupleE
                            [(.index (.name "d") (.name "t")), (.index (.name "d") (.name "f"))]))
                        .skip))))))) }

/-- `pyarith_cases.py:<module>.case_int_dict_key_lookup_by_bool_key`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_int_dict_key_lookup_by_bool_key : Func :=
  { name := "pyarith_cases.py:<module>.case_int_dict_key_lookup_by_bool_key"
  , params := []
  , body := (.seq
            (.seq
              (.assign "tmp0" (.boxContainer (.dictE [])))
              (.seq
                (.setIndex (.name "tmp0") (.lit (.bool true)) (.lit (.str "x")))
                (.assign "d" (.name "tmp0"))))
            (.seq
              .skip
              (.seq
                (.assign "one" (.lit (.int 1)))
                (.seq .skip (.seq (.ret (.index (.name "d") (.name "one"))) .skip))))) }

/-- `pyarith_cases.py:<module>.case_bool_in_list`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_in_list : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_in_list"
  , params := []
  , body := (.seq
            (.assign "xs" (.boxContainer (.listE [(.lit (.int 1)), (.lit (.int 2))])))
            (.seq
              .skip
              (.seq
                (.assign "t" (.lit (.bool true)))
                (.seq
                  .skip
                  (.ret
                    (.tupleE
                      [ (.inOp false (.name "t") (.name "xs"))
                      , (.inOp false (.lit (.int 1)) (.boxContainer (.listE [(.name "t")])))
                      , (.inOp false (.lit (.int 2)) (.boxContainer (.listE [(.name "t")])))
                      , (.inOp
                          false
                          (.lit (.bool false))
                          (.boxContainer (.listE [(.lit (.int 0))]))) ])))))) }

/-- `pyarith_cases.py:<module>.case_bool_tuple_eq`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_tuple_eq : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_tuple_eq"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.ret
                (.tupleE
                  [ (.binop
                      "=="
                      (.tupleE [(.name "t"), (.lit (.int 2))])
                      (.tupleE [(.lit (.int 1)), (.lit (.int 2))]))
                  , (.binop
                      "=="
                      (.tupleE [(.lit (.int 1)), (.lit (.int 2))])
                      (.tupleE [(.name "t"), (.lit (.int 3))])) ])))) }

/-- `pyarith_cases.py:<module>.case_bool_list_eq`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module__case_bool_list_eq : Func :=
  { name := "pyarith_cases.py:<module>.case_bool_list_eq"
  , params := []
  , body := (.seq
            (.assign "t" (.lit (.bool true)))
            (.seq
              .skip
              (.ret
                (.binop
                  "=="
                  (.boxContainer (.listE [(.name "t"), (.lit (.int 0))]))
                  (.boxContainer (.listE [(.lit (.int 1)), (.lit (.bool false))])))))) }

/-- `<module-objects>:<module>`  (from ``) -/
def f__module_objects___module_ : Func :=
  { name := "<module-objects>:<module>"
  , params := []
  , body := (.seq
            (.setGlobal "<module>pyarith_cases.py" (.alloc "<module>pyarith_cases.py" []))
            (.seq
              (.setField
                (.name "<module>pyarith_cases.py")
                "case_bool_add_bool"
                (.fnref "pyarith_cases.py:<module>.case_bool_add_bool"))
              (.seq
                (.setField
                  (.name "<module>pyarith_cases.py")
                  "case_bool_add_int"
                  (.fnref "pyarith_cases.py:<module>.case_bool_add_int"))
                (.seq
                  (.setField
                    (.name "<module>pyarith_cases.py")
                    "case_bool_and_stays_bool"
                    (.fnref "pyarith_cases.py:<module>.case_bool_and_stays_bool"))
                  (.seq
                    (.setField
                      (.name "<module>pyarith_cases.py")
                      "case_bool_bitwise_with_int"
                      (.fnref "pyarith_cases.py:<module>.case_bool_bitwise_with_int"))
                    (.seq
                      (.setField
                        (.name "<module>pyarith_cases.py")
                        "case_bool_dict_key_lookup"
                        (.fnref "pyarith_cases.py:<module>.case_bool_dict_key_lookup"))
                      (.seq
                        (.setField
                          (.name "<module>pyarith_cases.py")
                          "case_bool_div"
                          (.fnref "pyarith_cases.py:<module>.case_bool_div"))
                        (.seq
                          (.setField
                            (.name "<module>pyarith_cases.py")
                            "case_bool_div_zero"
                            (.fnref "pyarith_cases.py:<module>.case_bool_div_zero"))
                          (.seq
                            (.setField
                              (.name "<module>pyarith_cases.py")
                              "case_bool_eq_float"
                              (.fnref "pyarith_cases.py:<module>.case_bool_eq_float"))
                            (.seq
                              (.setField
                                (.name "<module>pyarith_cases.py")
                                "case_bool_eq_int"
                                (.fnref "pyarith_cases.py:<module>.case_bool_eq_int"))
                              (.seq
                                (.setField
                                  (.name "<module>pyarith_cases.py")
                                  "case_bool_floordiv_mod"
                                  (.fnref "pyarith_cases.py:<module>.case_bool_floordiv_mod"))
                                (.seq
                                  (.setField
                                    (.name "<module>pyarith_cases.py")
                                    "case_bool_in_list"
                                    (.fnref "pyarith_cases.py:<module>.case_bool_in_list"))
                                  (.seq
                                    (.setField
                                      (.name "<module>pyarith_cases.py")
                                      "case_bool_invert"
                                      (.fnref "pyarith_cases.py:<module>.case_bool_invert"))
                                    (.seq
                                      (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_bool_list_eq"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_list_eq"))
                                      (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_bool_lt"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_lt"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_bool_mul"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_mul"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_bool_ne_int"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_ne_int"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_bool_neg"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_neg"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_bool_or_stays_bool"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_or_stays_bool"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_bool_plus_float"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_plus_float"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_bool_shift"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_shift"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_bool_sub"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_sub"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_bool_tuple_eq"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_tuple_eq"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_bool_xor_stays_bool"
                                        (.fnref
                                        "pyarith_cases.py:<module>.case_bool_xor_stays_bool"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_div_7_2"
                                        (.fnref "pyarith_cases.py:<module>.case_div_7_2"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_div_7_neg2"
                                        (.fnref "pyarith_cases.py:<module>.case_div_7_neg2"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_div_and_floordiv_together"
                                        (.fnref
                                        "pyarith_cases.py:<module>.case_div_and_floordiv_together"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_div_beyond_2pow53"
                                        (.fnref "pyarith_cases.py:<module>.case_div_beyond_2pow53"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_div_big_divisor"
                                        (.fnref "pyarith_cases.py:<module>.case_div_big_divisor"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_div_big_int"
                                        (.fnref "pyarith_cases.py:<module>.case_div_big_int"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_div_exact_is_float"
                                        (.fnref "pyarith_cases.py:<module>.case_div_exact_is_float"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_div_exactly_2pow53"
                                        (.fnref "pyarith_cases.py:<module>.case_div_exactly_2pow53"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_div_float_float"
                                        (.fnref "pyarith_cases.py:<module>.case_div_float_float"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_div_int_float"
                                        (.fnref "pyarith_cases.py:<module>.case_div_int_float"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_div_neg7_2"
                                        (.fnref "pyarith_cases.py:<module>.case_div_neg7_2"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_div_one_third"
                                        (.fnref "pyarith_cases.py:<module>.case_div_one_third"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_div_zero"
                                        (.fnref "pyarith_cases.py:<module>.case_div_zero"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_div_zero_numerator_negative_divisor"
                                        (.fnref
                                        "pyarith_cases.py:<module>.case_div_zero_numerator_negative_divisor"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_false_eq_zero"
                                        (.fnref "pyarith_cases.py:<module>.case_false_eq_zero"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_floordiv_7_2"
                                        (.fnref "pyarith_cases.py:<module>.case_floordiv_7_2"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_floordiv_7_neg2"
                                        (.fnref "pyarith_cases.py:<module>.case_floordiv_7_neg2"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_floordiv_neg7_2"
                                        (.fnref "pyarith_cases.py:<module>.case_floordiv_neg7_2"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_floordiv_zero"
                                        (.fnref "pyarith_cases.py:<module>.case_floordiv_zero"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_int_dict_key_lookup_by_bool_key"
                                        (.fnref
                                        "pyarith_cases.py:<module>.case_int_dict_key_lookup_by_bool_key"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_mod_neg7_3"
                                        (.fnref "pyarith_cases.py:<module>.case_mod_neg7_3"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyarith_cases.py")
                                        "case_not_bool"
                                        (.fnref "pyarith_cases.py:<module>.case_not_bool"))
                                        .skip)))))))))))))))))))))))))))))))))))))))))))))) }

/-- `pyarith_cases.py:<module>`  (from `pyarith_cases.py`) -/
def f_pyarith_cases_py__module_ : Func :=
  { name := "pyarith_cases.py:<module>"
  , params := []
  , body := (.seq
            (.expr
              (.lit
                (.str "Differential fixture for Python `/`, `//` and `bool`-is-an-`int` (STRATEGY.md item Q).\n\nEvery `case_*` function takes no arguments. `tests/test_pyarith_cpython.py` runs each one\nunder CPython and compares the result with the value Core computes for the SAME source\nafter the whole pipeline -- `pysrc2cpg` -> `cartographer/export_ast.sc` ->\n`cartographer/render_lean.py` -> `Autoform/PyArithProgram.lean` -- pinned by\n`#guard_msgs` in `Autoform/PyArith.lean`.\n\nOperands are bound to locals first (`a = 7`) so that no frontend constant-folds the\noperator away, and so the operator under test is the one the exporter emits.\n")))
            (.seq
              (.setGlobal "case_div_7_2" (.fnref "pyarith_cases.py:<module>.case_div_7_2"))
              (.seq
                (.setGlobal "case_div_neg7_2" (.fnref "pyarith_cases.py:<module>.case_div_neg7_2"))
                (.seq
                  (.setGlobal
                    "case_div_7_neg2"
                    (.fnref "pyarith_cases.py:<module>.case_div_7_neg2"))
                  (.seq
                    (.setGlobal
                      "case_div_exact_is_float"
                      (.fnref "pyarith_cases.py:<module>.case_div_exact_is_float"))
                    (.seq
                      (.setGlobal
                        "case_div_zero"
                        (.fnref "pyarith_cases.py:<module>.case_div_zero"))
                      (.seq
                        (.setGlobal
                          "case_div_zero_numerator_negative_divisor"
                          (.fnref
                            "pyarith_cases.py:<module>.case_div_zero_numerator_negative_divisor"))
                        (.seq
                          (.setGlobal
                            "case_div_one_third"
                            (.fnref "pyarith_cases.py:<module>.case_div_one_third"))
                          (.seq
                            (.setGlobal
                              "case_div_exactly_2pow53"
                              (.fnref "pyarith_cases.py:<module>.case_div_exactly_2pow53"))
                            (.seq
                              (.setGlobal
                                "case_div_beyond_2pow53"
                                (.fnref "pyarith_cases.py:<module>.case_div_beyond_2pow53"))
                              (.seq
                                (.setGlobal
                                  "case_div_big_int"
                                  (.fnref "pyarith_cases.py:<module>.case_div_big_int"))
                                (.seq
                                  (.setGlobal
                                    "case_div_big_divisor"
                                    (.fnref "pyarith_cases.py:<module>.case_div_big_divisor"))
                                  (.seq
                                    (.setGlobal
                                      "case_div_int_float"
                                      (.fnref "pyarith_cases.py:<module>.case_div_int_float"))
                                    (.seq
                                      (.setGlobal
                                        "case_div_float_float"
                                        (.fnref "pyarith_cases.py:<module>.case_div_float_float"))
                                      (.seq
                                        (.setGlobal
                                        "case_floordiv_7_2"
                                        (.fnref "pyarith_cases.py:<module>.case_floordiv_7_2"))
                                        (.seq
                                        (.setGlobal
                                        "case_floordiv_neg7_2"
                                        (.fnref "pyarith_cases.py:<module>.case_floordiv_neg7_2"))
                                        (.seq
                                        (.setGlobal
                                        "case_floordiv_7_neg2"
                                        (.fnref "pyarith_cases.py:<module>.case_floordiv_7_neg2"))
                                        (.seq
                                        (.setGlobal
                                        "case_floordiv_zero"
                                        (.fnref "pyarith_cases.py:<module>.case_floordiv_zero"))
                                        (.seq
                                        (.setGlobal
                                        "case_mod_neg7_3"
                                        (.fnref "pyarith_cases.py:<module>.case_mod_neg7_3"))
                                        (.seq
                                        (.setGlobal
                                        "case_div_and_floordiv_together"
                                        (.fnref
                                        "pyarith_cases.py:<module>.case_div_and_floordiv_together"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_eq_int"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_eq_int"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_ne_int"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_ne_int"))
                                        (.seq
                                        (.setGlobal
                                        "case_false_eq_zero"
                                        (.fnref "pyarith_cases.py:<module>.case_false_eq_zero"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_eq_float"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_eq_float"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_add_int"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_add_int"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_add_bool"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_add_bool"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_sub"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_sub"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_mul"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_mul"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_neg"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_neg"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_invert"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_invert"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_lt"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_lt"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_div"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_div"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_div_zero"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_div_zero"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_floordiv_mod"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_floordiv_mod"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_shift"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_shift"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_and_stays_bool"
                                        (.fnref
                                        "pyarith_cases.py:<module>.case_bool_and_stays_bool"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_or_stays_bool"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_or_stays_bool"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_xor_stays_bool"
                                        (.fnref
                                        "pyarith_cases.py:<module>.case_bool_xor_stays_bool"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_bitwise_with_int"
                                        (.fnref
                                        "pyarith_cases.py:<module>.case_bool_bitwise_with_int"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_plus_float"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_plus_float"))
                                        (.seq
                                        (.setGlobal
                                        "case_not_bool"
                                        (.fnref "pyarith_cases.py:<module>.case_not_bool"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_dict_key_lookup"
                                        (.fnref
                                        "pyarith_cases.py:<module>.case_bool_dict_key_lookup"))
                                        (.seq
                                        (.setGlobal
                                        "case_int_dict_key_lookup_by_bool_key"
                                        (.fnref
                                        "pyarith_cases.py:<module>.case_int_dict_key_lookup_by_bool_key"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_in_list"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_in_list"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_tuple_eq"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_tuple_eq"))
                                        (.seq
                                        (.setGlobal
                                        "case_bool_list_eq"
                                        (.fnref "pyarith_cases.py:<module>.case_bool_list_eq"))
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
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := [f__module_objects___module_, f_pyarith_cases_py__module_]

/-- Source dialect: `.python` (integer division/modulo convention).

`pyClasses` is the class table: methods resolve along the C3 MRO, and bare
names by Python scoping (STRATEGY.md §62). -/
def program : Program := { dialect := .python, pyClasses := some [], funcs := [
  f_pyarith_cases_py__module__case_div_7_2,
  f_pyarith_cases_py__module__case_div_neg7_2,
  f_pyarith_cases_py__module__case_div_7_neg2,
  f_pyarith_cases_py__module__case_div_exact_is_float,
  f_pyarith_cases_py__module__case_div_zero,
  f_pyarith_cases_py__module__case_div_zero_numerator_negative_divisor,
  f_pyarith_cases_py__module__case_div_one_third,
  f_pyarith_cases_py__module__case_div_exactly_2pow53,
  f_pyarith_cases_py__module__case_div_beyond_2pow53,
  f_pyarith_cases_py__module__case_div_big_int,
  f_pyarith_cases_py__module__case_div_big_divisor,
  f_pyarith_cases_py__module__case_div_int_float,
  f_pyarith_cases_py__module__case_div_float_float,
  f_pyarith_cases_py__module__case_floordiv_7_2,
  f_pyarith_cases_py__module__case_floordiv_neg7_2,
  f_pyarith_cases_py__module__case_floordiv_7_neg2,
  f_pyarith_cases_py__module__case_floordiv_zero,
  f_pyarith_cases_py__module__case_mod_neg7_3,
  f_pyarith_cases_py__module__case_div_and_floordiv_together,
  f_pyarith_cases_py__module__case_bool_eq_int,
  f_pyarith_cases_py__module__case_bool_ne_int,
  f_pyarith_cases_py__module__case_false_eq_zero,
  f_pyarith_cases_py__module__case_bool_eq_float,
  f_pyarith_cases_py__module__case_bool_add_int,
  f_pyarith_cases_py__module__case_bool_add_bool,
  f_pyarith_cases_py__module__case_bool_sub,
  f_pyarith_cases_py__module__case_bool_mul,
  f_pyarith_cases_py__module__case_bool_neg,
  f_pyarith_cases_py__module__case_bool_invert,
  f_pyarith_cases_py__module__case_bool_lt,
  f_pyarith_cases_py__module__case_bool_div,
  f_pyarith_cases_py__module__case_bool_div_zero,
  f_pyarith_cases_py__module__case_bool_floordiv_mod,
  f_pyarith_cases_py__module__case_bool_shift,
  f_pyarith_cases_py__module__case_bool_and_stays_bool,
  f_pyarith_cases_py__module__case_bool_or_stays_bool,
  f_pyarith_cases_py__module__case_bool_xor_stays_bool,
  f_pyarith_cases_py__module__case_bool_bitwise_with_int,
  f_pyarith_cases_py__module__case_bool_plus_float,
  f_pyarith_cases_py__module__case_not_bool,
  f_pyarith_cases_py__module__case_bool_dict_key_lookup,
  f_pyarith_cases_py__module__case_int_dict_key_lookup_by_bool_key,
  f_pyarith_cases_py__module__case_bool_in_list,
  f_pyarith_cases_py__module__case_bool_tuple_eq,
  f_pyarith_cases_py__module__case_bool_list_eq,
  f__module_objects___module_,
  f_pyarith_cases_py__module_
] }

end Autoform.Generated.PyArith