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
set_option maxRecDepth 8424

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
# PyScoping — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.PyScoping
open Autoform.Core

/-- `pyscoping_cases.py:<module>.dflt_lits`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__dflt_lits : Func :=
  { name := "pyscoping_cases.py:<module>.dflt_lits"
  , params := ["a", "b", "c", "d", "e", "f", "g", "h"]
  , defaults := [("b", (.lit (.int 10))), ("c", (.lit .unit)), ("d", (.lit (.str "s"))), ("e", (.lit (.bool true))), ("f", (.tupleE [])), ("g", (.lit (.int (-3)))), ("h", (.lit (.float (Fl.ofBits 4602678819172646912))))]
  , body := (.ret
            (.tupleE
              [ (.name "a")
              , (.name "b")
              , (.name "c")
              , (.name "d")
              , (.name "e")
              , (.name "f")
              , (.name "g")
              , (.name "h") ])) }

/-- `pyscoping_cases.py:<module>.case_default_all`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_default_all : Func :=
  { name := "pyscoping_cases.py:<module>.case_default_all"
  , params := []
  , body := (.seq (.ret (.call "pyscoping_cases.py:<module>.dflt_lits" [(.lit (.int 1))])) .skip) }

/-- `pyscoping_cases.py:<module>.case_default_some`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_default_some : Func :=
  { name := "pyscoping_cases.py:<module>.case_default_some"
  , params := []
  , body := (.seq
            (.ret
              (.call
                "pyscoping_cases.py:<module>.dflt_lits"
                [(.lit (.int 1)), (.lit (.int 2)), (.kwargE "d" (.lit (.str "t")))]))
            .skip) }

/-- `pyscoping_cases.py:<module>.case_default_by_keyword`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_default_by_keyword : Func :=
  { name := "pyscoping_cases.py:<module>.case_default_by_keyword"
  , params := []
  , body := (.seq
            (.ret
              (.call
                "pyscoping_cases.py:<module>.dflt_lits"
                [(.kwargE "a" (.lit (.int 5))), (.kwargE "g" (.lit (.int 7)))]))
            .skip) }

/-- `pyscoping_cases.py:<module>.dflt_mutable`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__dflt_mutable : Func :=
  { name := "pyscoping_cases.py:<module>.dflt_mutable"
  , params := ["x", "acc"]
  , defaults := [("acc", (.hole "param:default-nonliteral"))]
  , body := (.ret (.binop "+" (.name "acc") (.boxContainer (.listE [(.name "x")])))) }

/-- `pyscoping_cases.py:<module>.case_mutable_default_supplied`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_mutable_default_supplied : Func :=
  { name := "pyscoping_cases.py:<module>.case_mutable_default_supplied"
  , params := []
  , body := (.seq
            (.ret
              (.call
                "pyscoping_cases.py:<module>.dflt_mutable"
                [(.lit (.int 1)), (.boxContainer (.listE [(.lit (.int 0))]))]))
            .skip) }

/-- `pyscoping_cases.py:<module>.case_mutable_default_needed`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_mutable_default_needed : Func :=
  { name := "pyscoping_cases.py:<module>.case_mutable_default_needed"
  , params := []
  , body := (.seq (.ret (.call "pyscoping_cases.py:<module>.dflt_mutable" [(.lit (.int 1))])) .skip) }

/-- `pyscoping_cases.py:<module>.dflt_global`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__dflt_global : Func :=
  { name := "pyscoping_cases.py:<module>.dflt_global"
  , params := ["x", "lim"]
  , defaults := [("lim", (.hole "param:default-unsupported"))]
  , body := (.ret (.tupleE [(.name "x"), (.name "lim")])) }

/-- `pyscoping_cases.py:<module>.case_global_default_supplied`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_global_default_supplied : Func :=
  { name := "pyscoping_cases.py:<module>.case_global_default_supplied"
  , params := []
  , body := (.seq
            (.ret
              (.call "pyscoping_cases.py:<module>.dflt_global" [(.lit (.int 1)), (.lit (.int 2))]))
            .skip) }

/-- `pyscoping_cases.py:<module>.case_global_default_needed`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_global_default_needed : Func :=
  { name := "pyscoping_cases.py:<module>.case_global_default_needed"
  , params := []
  , body := (.seq (.ret (.call "pyscoping_cases.py:<module>.dflt_global" [(.lit (.int 1))])) .skip) }

/-- `pyscoping_cases.py:<module>.case_lambda_default`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_lambda_default : Func :=
  { name := "pyscoping_cases.py:<module>.case_lambda_default"
  , params := []
  , body := (.seq
            (.assign
              "adder_fn"
              (.fnref "pyscoping_cases.py:<module>.case_lambda_default.<lambda>0"))
            (.seq
              (.ret
                (.call
                  "pyscoping_cases.py:<module>.case_lambda_default.<lambda>0"
                  [(.lit (.int 1))]))
              .skip)) }

/-- `pyscoping_cases.py:<module>.case_lambda_default.<lambda>0`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_lambda_default__lambda_0 : Func :=
  { name := "pyscoping_cases.py:<module>.case_lambda_default.<lambda>0"
  , params := ["x", "y"]
  , defaults := [("y", (.lit (.int 2)))]
  , body := (.ret (.binop "+" (.name "x") (.name "y"))) }

/-- `pyscoping_cases.py:<module>.Shelf.get`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__Shelf_get : Func :=
  { name := "pyscoping_cases.py:<module>.Shelf.get"
  , params := ["key", "default", "strict"]
  , kwonly := ["strict"]
  , defaults := [("default", (.lit .unit)), ("strict", (.lit (.bool false)))]
  , body := (.ret (.tupleE [(.name "key"), (.name "default"), (.name "strict")])) }

/-- `pyscoping_cases.py:<module>.case_method_default`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_method_default : Func :=
  { name := "pyscoping_cases.py:<module>.case_method_default"
  , params := []
  , body := (.seq
            (.assign "shelf_obj" (.alloc "Shelf" []))
            (.seq .skip (.seq (.ret (.mcall (.name "shelf_obj") "get" [(.lit (.int 1))])) .skip))) }

/-- `pyscoping_cases.py:<module>.case_method_default_kwonly`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_method_default_kwonly : Func :=
  { name := "pyscoping_cases.py:<module>.case_method_default_kwonly"
  , params := []
  , body := (.seq
            (.assign "shelf_obj" (.alloc "Shelf" []))
            (.seq
              .skip
              (.seq
                (.ret
                  (.mcall
                    (.name "shelf_obj")
                    "get"
                    [(.lit (.int 1)), (.lit (.int 2)), (.kwargE "strict" (.lit (.bool true)))]))
                .skip))) }

/-- `pyscoping_cases.py:<module>._underscored`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module___underscored : Func :=
  { name := "pyscoping_cases.py:<module>._underscored"
  , params := ["_k", "_v"]
  , defaults := [("_v", (.lit (.int 1)))]
  , body := (.ret (.tupleE [(.name "_k"), (.name "_v")])) }

/-- `pyscoping_cases.py:<module>.case_underscored_default`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_underscored_default : Func :=
  { name := "pyscoping_cases.py:<module>.case_underscored_default"
  , params := []
  , body := (.seq (.ret (.call "pyscoping_cases.py:<module>._underscored" [(.lit (.int 0))])) .skip) }

/-- `pyscoping_cases.py:<module>.kwo`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__kwo : Func :=
  { name := "pyscoping_cases.py:<module>.kwo"
  , params := ["a", "b", "c"]
  , kwonly := ["b", "c"]
  , defaults := [("c", (.lit (.int 3)))]
  , body := (.ret (.tupleE [(.name "a"), (.name "b"), (.name "c")])) }

/-- `pyscoping_cases.py:<module>.case_kwonly`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_kwonly : Func :=
  { name := "pyscoping_cases.py:<module>.case_kwonly"
  , params := []
  , body := (.seq
            (.ret
              (.call
                "pyscoping_cases.py:<module>.kwo"
                [(.lit (.int 1)), (.kwargE "b" (.lit (.int 2)))]))
            .skip) }

/-- `pyscoping_cases.py:<module>.case_kwonly_positional_rejected`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_kwonly_positional_rejected : Func :=
  { name := "pyscoping_cases.py:<module>.case_kwonly_positional_rejected"
  , params := []
  , body := (.seq
            (.ret (.call "pyscoping_cases.py:<module>.kwo" [(.lit (.int 1)), (.lit (.int 2))]))
            .skip) }

/-- `pyscoping_cases.py:<module>.kw_after_star`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__kw_after_star : Func :=
  { name := "pyscoping_cases.py:<module>.kw_after_star"
  , params := ["args", "key", "kw"]
  , vararg := some "args"
  , kwarg := some "kw"
  , kwonly := ["key"]
  , defaults := [("key", (.lit .unit))]
  , body := (.ret (.tupleE [(.name "args"), (.name "key"), (.name "kw")])) }

/-- `pyscoping_cases.py:<module>.case_kw_after_varargs`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_kw_after_varargs : Func :=
  { name := "pyscoping_cases.py:<module>.case_kw_after_varargs"
  , params := []
  , body := (.seq
            (.ret
              (.call "pyscoping_cases.py:<module>.kw_after_star" [(.lit (.int 1)), (.lit (.int 2))]))
            .skip) }

/-- `pyscoping_cases.py:<module>.case_kw_after_varargs_named`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_kw_after_varargs_named : Func :=
  { name := "pyscoping_cases.py:<module>.case_kw_after_varargs_named"
  , params := []
  , body := (.seq
            (.ret
              (.call
                "pyscoping_cases.py:<module>.kw_after_star"
                [(.lit (.int 1)), (.kwargE "key" (.lit (.int 5))), (.kwargE "z" (.lit (.int 6)))]))
            .skip) }

/-- `pyscoping_cases.py:<module>.posonly`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__posonly : Func :=
  { name := "pyscoping_cases.py:<module>.posonly"
  , params := ["a", "b", "c"]
  , posonly := ["a", "b"]
  , defaults := [("b", (.lit (.int 2))), ("c", (.lit (.int 3)))]
  , body := (.ret (.tupleE [(.name "a"), (.name "b"), (.name "c")])) }

/-- `pyscoping_cases.py:<module>.case_posonly`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_posonly : Func :=
  { name := "pyscoping_cases.py:<module>.case_posonly"
  , params := []
  , body := (.seq (.ret (.call "pyscoping_cases.py:<module>.posonly" [(.lit (.int 1))])) .skip) }

/-- `pyscoping_cases.py:<module>.case_posonly_keyword_rejected`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_posonly_keyword_rejected : Func :=
  { name := "pyscoping_cases.py:<module>.case_posonly_keyword_rejected"
  , params := []
  , body := (.seq
            (.ret
              (.call
                "pyscoping_cases.py:<module>.posonly"
                [(.lit (.int 1)), (.kwargE "b" (.lit (.int 5)))]))
            .skip) }

/-- `pyscoping_cases.py:<module>.posonly_kw`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__posonly_kw : Func :=
  { name := "pyscoping_cases.py:<module>.posonly_kw"
  , params := ["a", "kw"]
  , kwarg := some "kw"
  , posonly := ["a"]
  , body := (.ret (.tupleE [(.name "a"), (.name "kw")])) }

/-- `pyscoping_cases.py:<module>.case_posonly_name_goes_to_kwargs`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_posonly_name_goes_to_kwargs : Func :=
  { name := "pyscoping_cases.py:<module>.case_posonly_name_goes_to_kwargs"
  , params := []
  , body := (.seq
            (.ret
              (.call
                "pyscoping_cases.py:<module>.posonly_kw"
                [(.lit (.int 1)), (.kwargE "a" (.lit (.int 2)))]))
            .skip) }

/-- `pyscoping_cases.py:<module>.make_counter`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__make_counter : Func :=
  { name := "pyscoping_cases.py:<module>.make_counter"
  , params := []
  , body := (.seq
            (.assign "n" (.boxNew (.lit .unit)))
            (.seq
              (.setField (.name "n") "v" (.lit (.int 0)))
              (.seq
                (.assign "inc" (.closure "pyscoping_cases.py:<module>.make_counter.inc"))
                (.seq
                  (.expr (.call "inc" []))
                  (.seq
                    .skip
                    (.seq
                      (.expr (.call "inc" []))
                      (.seq .skip (.ret (.tupleE [(.field (.name "n") "v"), (.call "inc" [])]))))))))) }

/-- `pyscoping_cases.py:<module>.make_counter.inc`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__make_counter_inc : Func :=
  { name := "pyscoping_cases.py:<module>.make_counter.inc"
  , params := []
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.setField (.name "n") "v" (.binop "+" (.field (.name "n") "v") (.lit (.int 1))))
                (.ret (.field (.name "n") "v"))))) }

/-- `pyscoping_cases.py:<module>.case_nonlocal_counter`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_nonlocal_counter : Func :=
  { name := "pyscoping_cases.py:<module>.case_nonlocal_counter"
  , params := []
  , body := (.seq (.ret (.call "pyscoping_cases.py:<module>.make_counter" [])) .skip) }

/-- `pyscoping_cases.py:<module>.make_pair`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__make_pair : Func :=
  { name := "pyscoping_cases.py:<module>.make_pair"
  , params := ["start"]
  , body := (.seq
            (.assign "start" (.boxNew (.name "start")))
            (.seq
              (.assign "bump_by" (.closure "pyscoping_cases.py:<module>.make_pair.bump_by"))
              (.seq
                (.assign "peek_at" (.closure "pyscoping_cases.py:<module>.make_pair.peek_at"))
                (.seq (.ret (.tupleE [(.name "bump_by"), (.name "peek_at")])) (.seq .skip .skip))))) }

/-- `pyscoping_cases.py:<module>.make_pair.bump_by`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__make_pair_bump_by : Func :=
  { name := "pyscoping_cases.py:<module>.make_pair.bump_by"
  , params := ["k"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.setField
                  (.name "start")
                  "v"
                  (.binop "+" (.field (.name "start") "v") (.name "k")))
                (.ret (.field (.name "start") "v"))))) }

/-- `pyscoping_cases.py:<module>.make_pair.peek_at`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__make_pair_peek_at : Func :=
  { name := "pyscoping_cases.py:<module>.make_pair.peek_at"
  , params := []
  , body := (.seq (.ret (.field (.name "start") "v")) .skip) }

/-- `pyscoping_cases.py:<module>.case_nonlocal_shared_between_closures`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_nonlocal_shared_between_closures : Func :=
  { name := "pyscoping_cases.py:<module>.case_nonlocal_shared_between_closures"
  , params := []
  , body := (.seq
            (.assign "fns" (.call "pyscoping_cases.py:<module>.make_pair" [(.lit (.int 10))]))
            (.seq
              .skip
              (.seq
                (.assign "bumper" (.index (.name "fns") (.lit (.int 0))))
                (.seq
                  .skip
                  (.seq
                    (.assign "peeker" (.index (.name "fns") (.lit (.int 1))))
                    (.seq
                      .skip
                      (.seq
                        (.expr (.call "bumper" [(.lit (.int 5))]))
                        (.seq
                          .skip
                          (.seq
                            (.expr (.call "bumper" [(.lit (.int 1))]))
                            (.ret (.call "peeker" []))))))))))) }

/-- `pyscoping_cases.py:<module>.nonlocal_chain`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__nonlocal_chain : Func :=
  { name := "pyscoping_cases.py:<module>.nonlocal_chain"
  , params := []
  , body := (.seq
            (.assign "x" (.boxNew (.lit .unit)))
            (.seq
              (.setField (.name "x") "v" (.lit (.int 1)))
              (.seq
                (.assign "mid" (.closure "pyscoping_cases.py:<module>.nonlocal_chain.mid"))
                (.seq
                  (.assign "r" (.call "mid" []))
                  (.seq
                    .skip
                    (.seq
                      (.ret (.tupleE [(.name "r"), (.field (.name "x") "v")]))
                      (.seq .skip .skip))))))) }

/-- `pyscoping_cases.py:<module>.nonlocal_chain.mid`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__nonlocal_chain_mid : Func :=
  { name := "pyscoping_cases.py:<module>.nonlocal_chain.mid"
  , params := []
  , body := (.seq
            (.assign "inner" (.closure "pyscoping_cases.py:<module>.nonlocal_chain.mid.inner"))
            (.seq
              (.expr (.call "inner" []))
              (.seq (.ret (.field (.name "x") "v")) (.seq .skip .skip)))) }

/-- `pyscoping_cases.py:<module>.nonlocal_chain.mid.inner`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__nonlocal_chain_mid_inner : Func :=
  { name := "pyscoping_cases.py:<module>.nonlocal_chain.mid.inner"
  , params := []
  , body := (.seq
            .skip
            (.seq
              .skip
              (.setField (.name "x") "v" (.binop "*" (.field (.name "x") "v") (.lit (.int 10)))))) }

/-- `pyscoping_cases.py:<module>.case_nonlocal_through_two_levels`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_nonlocal_through_two_levels : Func :=
  { name := "pyscoping_cases.py:<module>.case_nonlocal_through_two_levels"
  , params := []
  , body := (.seq (.ret (.call "pyscoping_cases.py:<module>.nonlocal_chain" [])) .skip) }

/-- `pyscoping_cases.py:<module>.loop_total`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__loop_total : Func :=
  { name := "pyscoping_cases.py:<module>.loop_total"
  , params := ["xs"]
  , body := (.seq
            (.assign "total" (.boxNew (.lit .unit)))
            (.seq
              (.setField (.name "total") "v" (.lit (.int 0)))
              (.seq
                (.assign "add_one" (.closure "pyscoping_cases.py:<module>.loop_total.add_one"))
                (.seq
                  (.forIn "v" (.name "xs") (.expr (.call "add_one" [(.name "v")])))
                  (.seq
                    .skip
                    (.seq (.ret (.field (.name "total") "v")) (.seq .skip (.seq .skip .skip)))))))) }

/-- `pyscoping_cases.py:<module>.loop_total.add_one`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__loop_total_add_one : Func :=
  { name := "pyscoping_cases.py:<module>.loop_total.add_one"
  , params := ["v"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.setField (.name "total") "v" (.binop "+" (.field (.name "total") "v") (.name "v"))))) }

/-- `pyscoping_cases.py:<module>.case_nonlocal_in_a_loop`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_nonlocal_in_a_loop : Func :=
  { name := "pyscoping_cases.py:<module>.case_nonlocal_in_a_loop"
  , params := []
  , body := (.seq
            (.ret
              (.call
                "pyscoping_cases.py:<module>.loop_total"
                [(.boxContainer (.listE [(.lit (.int 1)), (.lit (.int 2)), (.lit (.int 3))]))]))
            .skip) }

/-- `pyscoping_cases.py:<module>.star_tail`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__star_tail : Func :=
  { name := "pyscoping_cases.py:<module>.star_tail"
  , params := ["xs"]
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "<unpackEx>" [(.name "xs"), (.lit (.int 1)), (.lit (.int 0))]))
              (.seq
                (.assign "a" (.index (.name "tmp0") (.lit (.int 0))))
                (.assign "b" (.index (.name "tmp0") (.lit (.int 1))))))
            (.seq .skip (.seq (.ret (.tupleE [(.name "a"), (.name "b")])) (.seq .skip .skip)))) }

/-- `pyscoping_cases.py:<module>.star_mid`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__star_mid : Func :=
  { name := "pyscoping_cases.py:<module>.star_mid"
  , params := ["xs"]
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "<unpackEx>" [(.name "xs"), (.lit (.int 1)), (.lit (.int 1))]))
              (.seq
                (.assign "p" (.index (.name "tmp0") (.lit (.int 0))))
                (.seq
                  (.assign "q" (.index (.name "tmp0") (.lit (.int 1))))
                  (.assign "r" (.index (.name "tmp0") (.lit (.int (-1))))))))
            (.seq
              .skip
              (.seq
                (.ret (.tupleE [(.name "p"), (.name "q"), (.name "r")]))
                (.seq .skip (.seq .skip .skip))))) }

/-- `pyscoping_cases.py:<module>.star_head`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__star_head : Func :=
  { name := "pyscoping_cases.py:<module>.star_head"
  , params := ["xs"]
  , body := (.seq
            (.seq
              (.assign "tmp0" (.call "<unpackEx>" [(.name "xs"), (.lit (.int 0)), (.lit (.int 1))]))
              (.seq
                (.assign "c" (.index (.name "tmp0") (.lit (.int 0))))
                (.assign "d" (.index (.name "tmp0") (.lit (.int (-1)))))))
            (.seq .skip (.seq (.ret (.tupleE [(.name "c"), (.name "d")])) (.seq .skip .skip)))) }

/-- `pyscoping_cases.py:<module>.case_star_tail_of_tuple_is_a_list`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_star_tail_of_tuple_is_a_list : Func :=
  { name := "pyscoping_cases.py:<module>.case_star_tail_of_tuple_is_a_list"
  , params := []
  , body := (.seq
            (.ret
              (.call
                "pyscoping_cases.py:<module>.star_tail"
                [(.tupleE [(.lit (.int 1)), (.lit (.int 2)), (.lit (.int 3))])]))
            .skip) }

/-- `pyscoping_cases.py:<module>.case_star_tail_empty`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_star_tail_empty : Func :=
  { name := "pyscoping_cases.py:<module>.case_star_tail_empty"
  , params := []
  , body := (.seq
            (.ret
              (.call
                "pyscoping_cases.py:<module>.star_tail"
                [(.boxContainer (.listE [(.lit (.int 1))]))]))
            .skip) }

/-- `pyscoping_cases.py:<module>.case_star_middle_of_str`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_star_middle_of_str : Func :=
  { name := "pyscoping_cases.py:<module>.case_star_middle_of_str"
  , params := []
  , body := (.seq (.ret (.call "pyscoping_cases.py:<module>.star_mid" [(.lit (.str "abcd"))])) .skip) }

/-- `pyscoping_cases.py:<module>.case_star_too_short`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_star_too_short : Func :=
  { name := "pyscoping_cases.py:<module>.case_star_too_short"
  , params := []
  , body := (.seq
            (.ret
              (.call
                "pyscoping_cases.py:<module>.star_mid"
                [(.boxContainer (.listE [(.lit (.int 1))]))]))
            .skip) }

/-- `pyscoping_cases.py:<module>.case_star_head_of_str`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_star_head_of_str : Func :=
  { name := "pyscoping_cases.py:<module>.case_star_head_of_str"
  , params := []
  , body := (.seq (.ret (.call "pyscoping_cases.py:<module>.star_head" [(.lit (.str "xyz"))])) .skip) }

/-- `pyscoping_cases.py:<module>.case_star_noniterable`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module__case_star_noniterable : Func :=
  { name := "pyscoping_cases.py:<module>.case_star_noniterable"
  , params := []
  , body := (.seq (.ret (.call "pyscoping_cases.py:<module>.star_tail" [(.lit (.int 5))])) .skip) }

/-- `<module-objects>:<module>`  (from ``) -/
def f__module_objects___module_ : Func :=
  { name := "<module-objects>:<module>"
  , params := []
  , body := (.seq
            (.setGlobal "<module>pyscoping_cases.py" (.alloc "<module>pyscoping_cases.py" []))
            (.seq
              (.setField
                (.name "<module>pyscoping_cases.py")
                "_underscored"
                (.fnref "pyscoping_cases.py:<module>._underscored"))
              (.seq
                (.setField
                  (.name "<module>pyscoping_cases.py")
                  "case_default_all"
                  (.fnref "pyscoping_cases.py:<module>.case_default_all"))
                (.seq
                  (.setField
                    (.name "<module>pyscoping_cases.py")
                    "case_default_by_keyword"
                    (.fnref "pyscoping_cases.py:<module>.case_default_by_keyword"))
                  (.seq
                    (.setField
                      (.name "<module>pyscoping_cases.py")
                      "case_default_some"
                      (.fnref "pyscoping_cases.py:<module>.case_default_some"))
                    (.seq
                      (.setField
                        (.name "<module>pyscoping_cases.py")
                        "case_global_default_needed"
                        (.fnref "pyscoping_cases.py:<module>.case_global_default_needed"))
                      (.seq
                        (.setField
                          (.name "<module>pyscoping_cases.py")
                          "case_global_default_supplied"
                          (.fnref "pyscoping_cases.py:<module>.case_global_default_supplied"))
                        (.seq
                          (.setField
                            (.name "<module>pyscoping_cases.py")
                            "case_kw_after_varargs"
                            (.fnref "pyscoping_cases.py:<module>.case_kw_after_varargs"))
                          (.seq
                            (.setField
                              (.name "<module>pyscoping_cases.py")
                              "case_kw_after_varargs_named"
                              (.fnref "pyscoping_cases.py:<module>.case_kw_after_varargs_named"))
                            (.seq
                              (.setField
                                (.name "<module>pyscoping_cases.py")
                                "case_kwonly"
                                (.fnref "pyscoping_cases.py:<module>.case_kwonly"))
                              (.seq
                                (.setField
                                  (.name "<module>pyscoping_cases.py")
                                  "case_kwonly_positional_rejected"
                                  (.fnref
                                    "pyscoping_cases.py:<module>.case_kwonly_positional_rejected"))
                                (.seq
                                  (.setField
                                    (.name "<module>pyscoping_cases.py")
                                    "case_lambda_default"
                                    (.fnref "pyscoping_cases.py:<module>.case_lambda_default"))
                                  (.seq
                                    (.setField
                                      (.name "<module>pyscoping_cases.py")
                                      "case_method_default"
                                      (.fnref "pyscoping_cases.py:<module>.case_method_default"))
                                    (.seq
                                      (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "case_method_default_kwonly"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_method_default_kwonly"))
                                      (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "case_mutable_default_needed"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_mutable_default_needed"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "case_mutable_default_supplied"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_mutable_default_supplied"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "case_nonlocal_counter"
                                        (.fnref "pyscoping_cases.py:<module>.case_nonlocal_counter"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "case_nonlocal_in_a_loop"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_nonlocal_in_a_loop"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "case_nonlocal_shared_between_closures"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_nonlocal_shared_between_closures"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "case_nonlocal_through_two_levels"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_nonlocal_through_two_levels"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "case_posonly"
                                        (.fnref "pyscoping_cases.py:<module>.case_posonly"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "case_posonly_keyword_rejected"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_posonly_keyword_rejected"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "case_posonly_name_goes_to_kwargs"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_posonly_name_goes_to_kwargs"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "case_star_head_of_str"
                                        (.fnref "pyscoping_cases.py:<module>.case_star_head_of_str"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "case_star_middle_of_str"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_star_middle_of_str"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "case_star_noniterable"
                                        (.fnref "pyscoping_cases.py:<module>.case_star_noniterable"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "case_star_tail_empty"
                                        (.fnref "pyscoping_cases.py:<module>.case_star_tail_empty"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "case_star_tail_of_tuple_is_a_list"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_star_tail_of_tuple_is_a_list"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "case_star_too_short"
                                        (.fnref "pyscoping_cases.py:<module>.case_star_too_short"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "case_underscored_default"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_underscored_default"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "dflt_global"
                                        (.fnref "pyscoping_cases.py:<module>.dflt_global"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "dflt_lits"
                                        (.fnref "pyscoping_cases.py:<module>.dflt_lits"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "dflt_mutable"
                                        (.fnref "pyscoping_cases.py:<module>.dflt_mutable"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "kw_after_star"
                                        (.fnref "pyscoping_cases.py:<module>.kw_after_star"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "kwo"
                                        (.fnref "pyscoping_cases.py:<module>.kwo"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "loop_total"
                                        (.fnref "pyscoping_cases.py:<module>.loop_total"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "make_counter"
                                        (.fnref "pyscoping_cases.py:<module>.make_counter"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "make_pair"
                                        (.fnref "pyscoping_cases.py:<module>.make_pair"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "nonlocal_chain"
                                        (.fnref "pyscoping_cases.py:<module>.nonlocal_chain"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "posonly"
                                        (.fnref "pyscoping_cases.py:<module>.posonly"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "posonly_kw"
                                        (.fnref "pyscoping_cases.py:<module>.posonly_kw"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "star_head"
                                        (.fnref "pyscoping_cases.py:<module>.star_head"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "star_mid"
                                        (.fnref "pyscoping_cases.py:<module>.star_mid"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "star_tail"
                                        (.fnref "pyscoping_cases.py:<module>.star_tail"))
                                        (.seq
                                        (.setField
                                        (.name "<module>pyscoping_cases.py")
                                        "Shelf"
                                        (.fnref "pyscoping_cases.py:<module>.Shelf<meta>"))
                                        .skip))))))))))))))))))))))))))))))))))))))))))))) }

/-- `pyscoping_cases.py:<module>`  (from `pyscoping_cases.py`) -/
def f_pyscoping_cases_py__module_ : Func :=
  { name := "pyscoping_cases.py:<module>"
  , params := []
  , body := (.seq
            (.expr
              (.lit
                (.str "Differential fixture for Python calling convention and scoping (STRATEGY.md §58).\n\nEvery `case_*` function takes no arguments. `tests/test_pyscoping_cpython.py` runs each one\nunder CPython and compares the result with the value Core computes for the SAME source\nafter the whole pipeline -- `pysrc2cpg` -> `cartographer/export_ast.sc` ->\n`cartographer/render_lean.py` -> `Autoform/PyScopingProgram.lean` -- pinned by\n`#guard_msgs` in `Autoform/PyScoping.lean`.\n\nNames are deliberately distinctive: `Expr.call` resolves a bare name against the whole\nfunction table by suffix before it looks at local variables, so a local called `f` could\nreach an unrelated function `...x.f`. That is a separate, recorded Core rule; this fixture\ndoes not try to test it.\n")))
            (.seq
              (.setGlobal "dflt_lits" (.fnref "pyscoping_cases.py:<module>.dflt_lits"))
              (.seq
                (.setGlobal
                  "case_default_all"
                  (.fnref "pyscoping_cases.py:<module>.case_default_all"))
                (.seq
                  (.setGlobal
                    "case_default_some"
                    (.fnref "pyscoping_cases.py:<module>.case_default_some"))
                  (.seq
                    (.setGlobal
                      "case_default_by_keyword"
                      (.fnref "pyscoping_cases.py:<module>.case_default_by_keyword"))
                    (.seq
                      (.setGlobal
                        "dflt_mutable"
                        (.fnref "pyscoping_cases.py:<module>.dflt_mutable"))
                      (.seq
                        (.setGlobal
                          "case_mutable_default_supplied"
                          (.fnref "pyscoping_cases.py:<module>.case_mutable_default_supplied"))
                        (.seq
                          (.setGlobal
                            "case_mutable_default_needed"
                            (.fnref "pyscoping_cases.py:<module>.case_mutable_default_needed"))
                          (.seq
                            (.setGlobal "GLOBAL_LIMIT" (.lit (.int 4)))
                            (.seq
                              (.setGlobal
                                "dflt_global"
                                (.fnref "pyscoping_cases.py:<module>.dflt_global"))
                              (.seq
                                (.setGlobal
                                  "case_global_default_supplied"
                                  (.fnref
                                    "pyscoping_cases.py:<module>.case_global_default_supplied"))
                                (.seq
                                  (.setGlobal
                                    "case_global_default_needed"
                                    (.fnref
                                      "pyscoping_cases.py:<module>.case_global_default_needed"))
                                  (.seq
                                    (.setGlobal
                                      "case_lambda_default"
                                      (.fnref "pyscoping_cases.py:<module>.case_lambda_default"))
                                    (.seq
                                      (.seq
                                        (.setGlobal
                                        "Shelf"
                                        (.fnref "pyscoping_cases.py:<module>.Shelf<meta>"))
                                        (.expr (.fnref "pyscoping_cases.py:<module>.Shelf<meta>")))
                                      (.seq
                                        (.setGlobal
                                        "case_method_default"
                                        (.fnref "pyscoping_cases.py:<module>.case_method_default"))
                                        (.seq
                                        (.setGlobal
                                        "case_method_default_kwonly"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_method_default_kwonly"))
                                        (.seq
                                        (.setGlobal
                                        "_underscored"
                                        (.fnref "pyscoping_cases.py:<module>._underscored"))
                                        (.seq
                                        (.setGlobal
                                        "case_underscored_default"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_underscored_default"))
                                        (.seq
                                        (.setGlobal
                                        "kwo"
                                        (.fnref "pyscoping_cases.py:<module>.kwo"))
                                        (.seq
                                        (.setGlobal
                                        "case_kwonly"
                                        (.fnref "pyscoping_cases.py:<module>.case_kwonly"))
                                        (.seq
                                        (.setGlobal
                                        "case_kwonly_positional_rejected"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_kwonly_positional_rejected"))
                                        (.seq
                                        (.setGlobal
                                        "kw_after_star"
                                        (.fnref "pyscoping_cases.py:<module>.kw_after_star"))
                                        (.seq
                                        (.setGlobal
                                        "case_kw_after_varargs"
                                        (.fnref "pyscoping_cases.py:<module>.case_kw_after_varargs"))
                                        (.seq
                                        (.setGlobal
                                        "case_kw_after_varargs_named"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_kw_after_varargs_named"))
                                        (.seq
                                        (.setGlobal
                                        "posonly"
                                        (.fnref "pyscoping_cases.py:<module>.posonly"))
                                        (.seq
                                        (.setGlobal
                                        "case_posonly"
                                        (.fnref "pyscoping_cases.py:<module>.case_posonly"))
                                        (.seq
                                        (.setGlobal
                                        "case_posonly_keyword_rejected"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_posonly_keyword_rejected"))
                                        (.seq
                                        (.setGlobal
                                        "posonly_kw"
                                        (.fnref "pyscoping_cases.py:<module>.posonly_kw"))
                                        (.seq
                                        (.setGlobal
                                        "case_posonly_name_goes_to_kwargs"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_posonly_name_goes_to_kwargs"))
                                        (.seq
                                        (.setGlobal
                                        "make_counter"
                                        (.fnref "pyscoping_cases.py:<module>.make_counter"))
                                        (.seq
                                        (.setGlobal
                                        "case_nonlocal_counter"
                                        (.fnref "pyscoping_cases.py:<module>.case_nonlocal_counter"))
                                        (.seq
                                        (.setGlobal
                                        "make_pair"
                                        (.fnref "pyscoping_cases.py:<module>.make_pair"))
                                        (.seq
                                        (.setGlobal
                                        "case_nonlocal_shared_between_closures"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_nonlocal_shared_between_closures"))
                                        (.seq
                                        (.setGlobal
                                        "nonlocal_chain"
                                        (.fnref "pyscoping_cases.py:<module>.nonlocal_chain"))
                                        (.seq
                                        (.setGlobal
                                        "case_nonlocal_through_two_levels"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_nonlocal_through_two_levels"))
                                        (.seq
                                        (.setGlobal
                                        "loop_total"
                                        (.fnref "pyscoping_cases.py:<module>.loop_total"))
                                        (.seq
                                        (.setGlobal
                                        "case_nonlocal_in_a_loop"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_nonlocal_in_a_loop"))
                                        (.seq
                                        (.setGlobal
                                        "star_tail"
                                        (.fnref "pyscoping_cases.py:<module>.star_tail"))
                                        (.seq
                                        (.setGlobal
                                        "star_mid"
                                        (.fnref "pyscoping_cases.py:<module>.star_mid"))
                                        (.seq
                                        (.setGlobal
                                        "star_head"
                                        (.fnref "pyscoping_cases.py:<module>.star_head"))
                                        (.seq
                                        (.setGlobal
                                        "case_star_tail_of_tuple_is_a_list"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_star_tail_of_tuple_is_a_list"))
                                        (.seq
                                        (.setGlobal
                                        "case_star_tail_empty"
                                        (.fnref "pyscoping_cases.py:<module>.case_star_tail_empty"))
                                        (.seq
                                        (.setGlobal
                                        "case_star_middle_of_str"
                                        (.fnref
                                        "pyscoping_cases.py:<module>.case_star_middle_of_str"))
                                        (.seq
                                        (.setGlobal
                                        "case_star_too_short"
                                        (.fnref "pyscoping_cases.py:<module>.case_star_too_short"))
                                        (.seq
                                        (.setGlobal
                                        "case_star_head_of_str"
                                        (.fnref "pyscoping_cases.py:<module>.case_star_head_of_str"))
                                        (.seq
                                        (.setGlobal
                                        "case_star_noniterable"
                                        (.fnref "pyscoping_cases.py:<module>.case_star_noniterable"))
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
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := [f__module_objects___module_, f_pyscoping_cases_py__module_]

/-- Source dialect: `.python` (integer division/modulo convention).

`pyClasses` is the class table: methods resolve along the C3 MRO, and bare
names by Python scoping (STRATEGY.md §62). -/
def program : Program := { dialect := .python, pyClasses := some [{ name := "Shelf", bases := [], attrs := [] }], funcs := [
  f_pyscoping_cases_py__module__dflt_lits,
  f_pyscoping_cases_py__module__case_default_all,
  f_pyscoping_cases_py__module__case_default_some,
  f_pyscoping_cases_py__module__case_default_by_keyword,
  f_pyscoping_cases_py__module__dflt_mutable,
  f_pyscoping_cases_py__module__case_mutable_default_supplied,
  f_pyscoping_cases_py__module__case_mutable_default_needed,
  f_pyscoping_cases_py__module__dflt_global,
  f_pyscoping_cases_py__module__case_global_default_supplied,
  f_pyscoping_cases_py__module__case_global_default_needed,
  f_pyscoping_cases_py__module__case_lambda_default,
  f_pyscoping_cases_py__module__case_lambda_default__lambda_0,
  f_pyscoping_cases_py__module__Shelf_get,
  f_pyscoping_cases_py__module__case_method_default,
  f_pyscoping_cases_py__module__case_method_default_kwonly,
  f_pyscoping_cases_py__module___underscored,
  f_pyscoping_cases_py__module__case_underscored_default,
  f_pyscoping_cases_py__module__kwo,
  f_pyscoping_cases_py__module__case_kwonly,
  f_pyscoping_cases_py__module__case_kwonly_positional_rejected,
  f_pyscoping_cases_py__module__kw_after_star,
  f_pyscoping_cases_py__module__case_kw_after_varargs,
  f_pyscoping_cases_py__module__case_kw_after_varargs_named,
  f_pyscoping_cases_py__module__posonly,
  f_pyscoping_cases_py__module__case_posonly,
  f_pyscoping_cases_py__module__case_posonly_keyword_rejected,
  f_pyscoping_cases_py__module__posonly_kw,
  f_pyscoping_cases_py__module__case_posonly_name_goes_to_kwargs,
  f_pyscoping_cases_py__module__make_counter,
  f_pyscoping_cases_py__module__make_counter_inc,
  f_pyscoping_cases_py__module__case_nonlocal_counter,
  f_pyscoping_cases_py__module__make_pair,
  f_pyscoping_cases_py__module__make_pair_bump_by,
  f_pyscoping_cases_py__module__make_pair_peek_at,
  f_pyscoping_cases_py__module__case_nonlocal_shared_between_closures,
  f_pyscoping_cases_py__module__nonlocal_chain,
  f_pyscoping_cases_py__module__nonlocal_chain_mid,
  f_pyscoping_cases_py__module__nonlocal_chain_mid_inner,
  f_pyscoping_cases_py__module__case_nonlocal_through_two_levels,
  f_pyscoping_cases_py__module__loop_total,
  f_pyscoping_cases_py__module__loop_total_add_one,
  f_pyscoping_cases_py__module__case_nonlocal_in_a_loop,
  f_pyscoping_cases_py__module__star_tail,
  f_pyscoping_cases_py__module__star_mid,
  f_pyscoping_cases_py__module__star_head,
  f_pyscoping_cases_py__module__case_star_tail_of_tuple_is_a_list,
  f_pyscoping_cases_py__module__case_star_tail_empty,
  f_pyscoping_cases_py__module__case_star_middle_of_str,
  f_pyscoping_cases_py__module__case_star_too_short,
  f_pyscoping_cases_py__module__case_star_head_of_str,
  f_pyscoping_cases_py__module__case_star_noniterable,
  f__module_objects___module_,
  f_pyscoping_cases_py__module_
] }

end Autoform.Generated.PyScoping