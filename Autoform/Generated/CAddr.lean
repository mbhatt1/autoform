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
set_option maxRecDepth 8120

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
# CAddr — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated.CAddr
open Autoform.Core

/-- `sum_until`  (from `addr.c`) -/
def f_sum_until : Func :=
  { name := "sum_until"
  , params := ["n"]
  , body := (.seq
            (.assign
              "a"
              (.boxFields
                (((List.range 8).map (fun i => (Expr.lit (Lit.str s!"{i}"), Expr.lit Lit.unit))) ++ [(Expr.lit (Lit.str "$esz"), Expr.lit (Lit.int 4))])))
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      (.assign "s" (.lit (.int 0)))
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            (.seq
                              (.assign "i" (.lit (.int 0)))
                              (.loop
                                (.binop "<" (.name "i") (.lit (.int 8)))
                                (.seq
                                  (.setDerefIref
                                    (.irefIndex (.name "a") (.name "i"))
                                    (.binop "+" (.name "i") (.lit (.int 1))))
                                  (.assign "i" (.binop "+" (.name "i") (.lit (.int 1)))))))
                            (.seq
                              (.ifte
                                (.binop
                                  "||"
                                  (.binop "<" (.name "n") (.lit (.int 0)))
                                  (.binop ">" (.name "n") (.lit (.int 8))))
                                (.ret (.unop "-" (.lit (.int 1))))
                                .skip)
                              (.seq
                                (.assign "p" (.irefIndex (.name "a") (.lit (.int 0))))
                                (.seq
                                  (.assign "end" (.irefIndex (.name "a") (.name "n")))
                                  (.seq
                                    (.loop
                                      (.ptrOp "<" 0 (.name "p") (.name "end"))
                                      (.seq
                                        (.assign
                                        "s"
                                        (.binop "+" (.name "s") (.derefIref (.name "p"))))
                                        (.assign "p" (.binop "+" (.name "p") (.lit (.int 1))))))
                                    (.ret (.name "s"))))))))))))))) }

/-- `cmp_ptrs`  (from `addr.c`) -/
def f_cmp_ptrs : Func :=
  { name := "cmp_ptrs"
  , params := ["x", "y"]
  , body := (.seq
            (.ifte (.ptrOp "==" 0 (.name "x") (.name "y")) (.ret (.lit (.int 0))) .skip)
            (.seq
              (.ifte
                (.ptrOp "<" 0 (.name "x") (.name "y"))
                (.ret (.unop "-" (.lit (.int 1))))
                .skip)
              (.ret (.lit (.int 1))))) }

/-- `cmp_field_elems`  (from `addr.c`) -/
def f_cmp_field_elems : Func :=
  { name := "cmp_field_elems"
  , params := ["b", "i", "j"]
  , body := (.ret
            (.call
              "cmp_ptrs"
              [ (.ptrOp "+" 1 (.field (.name "b") "a") (.name "i"))
              , (.ptrOp "+" 1 (.field (.name "b") "a") (.name "j")) ])) }

/-- `field_order`  (from `addr.c`) -/
def f_field_order : Func :=
  { name := "field_order"
  , params := ["i", "j"]
  , body := (.seq
            (.assign
              "buf"
              (.boxFields
                (((List.range 8).map (fun i => (Expr.lit (Lit.str s!"{i}"), Expr.lit Lit.unit))) ++ [(Expr.lit (Lit.str "$esz"), Expr.lit (Lit.int 1))])))
            (.seq
              (.assign
                "b"
                (.boxFields [((.lit (.str "a")), (.lit .unit)), ((.lit (.str "n")), (.lit .unit))]))
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      (.ifte
                        (.binop
                          "||"
                          (.binop
                            "||"
                            (.binop
                              "||"
                              (.binop "<" (.name "i") (.lit (.int 0)))
                              (.binop ">" (.name "i") (.lit (.int 8))))
                            (.binop "<" (.name "j") (.lit (.int 0))))
                          (.binop ">" (.name "j") (.lit (.int 8))))
                        (.ret (.lit (.int 9)))
                        .skip)
                      (.seq
                        (.setField (.name "b") "a" (.irefIndex (.name "buf") (.lit (.int 0))))
                        (.seq
                          (.setField (.name "b") "n" (.lit (.int 8)))
                          (.ret (.call "cmp_field_elems" [(.name "b"), (.name "i"), (.name "j")])))))))))) }

/-- `eq_field_elems`  (from `addr.c`) -/
def f_eq_field_elems : Func :=
  { name := "eq_field_elems"
  , params := ["b", "i", "j"]
  , body := (.ret
            (.cond
              (.ptrOp
                "=="
                0
                (.ptrOp "+" 1 (.field (.name "b") "a") (.name "i"))
                (.ptrOp "+" 1 (.field (.name "b") "a") (.name "j")))
              (.lit (.int 1))
              (.lit (.int 0)))) }

/-- `field_eq`  (from `addr.c`) -/
def f_field_eq : Func :=
  { name := "field_eq"
  , params := ["i", "j"]
  , body := (.seq
            (.assign
              "buf"
              (.boxFields
                (((List.range 8).map (fun i => (Expr.lit (Lit.str s!"{i}"), Expr.lit Lit.unit))) ++ [(Expr.lit (Lit.str "$esz"), Expr.lit (Lit.int 1))])))
            (.seq
              (.assign
                "b"
                (.boxFields [((.lit (.str "a")), (.lit .unit)), ((.lit (.str "n")), (.lit .unit))]))
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      (.ifte
                        (.binop
                          "||"
                          (.binop
                            "||"
                            (.binop
                              "||"
                              (.binop "<" (.name "i") (.lit (.int 0)))
                              (.binop ">" (.name "i") (.lit (.int 8))))
                            (.binop "<" (.name "j") (.lit (.int 0))))
                          (.binop ">" (.name "j") (.lit (.int 8))))
                        (.ret (.lit (.int 9)))
                        .skip)
                      (.seq
                        (.setField (.name "b") "a" (.irefIndex (.name "buf") (.lit (.int 0))))
                        (.seq
                          (.setField (.name "b") "n" (.lit (.int 8)))
                          (.ret (.call "eq_field_elems" [(.name "b"), (.name "i"), (.name "j")])))))))))) }

/-- `span`  (from `addr.c`) -/
def f_span : Func :=
  { name := "span"
  , params := ["from", "to"]
  , body := (.seq
            .skip
            (.seq
              (.assign "k" (.lit (.int 0)))
              (.seq
                (.loop
                  (.ptrOp "<" 0 (.name "from") (.name "to"))
                  (.seq
                    (.assign "from" (.ptrOp "+" 1 (.name "from") (.lit (.int 1))))
                    (.assign "k" (.binop "+" (.name "k") (.lit (.int 1))))))
                (.ret (.name "k"))))) }

/-- `walk_span`  (from `addr.c`) -/
def f_walk_span : Func :=
  { name := "walk_span"
  , params := ["i", "j"]
  , body := (.seq
            (.assign
              "buf"
              (.boxFields
                (((List.range 8).map (fun i => (Expr.lit (Lit.str s!"{i}"), Expr.lit Lit.unit))) ++ [(Expr.lit (Lit.str "$esz"), Expr.lit (Lit.int 1))])))
            (.seq
              (.assign
                "b"
                (.boxFields [((.lit (.str "a")), (.lit .unit)), ((.lit (.str "n")), (.lit .unit))]))
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      (.ifte
                        (.binop
                          "||"
                          (.binop
                            "||"
                            (.binop
                              "||"
                              (.binop "<" (.name "i") (.lit (.int 0)))
                              (.binop ">" (.name "i") (.lit (.int 8))))
                            (.binop "<" (.name "j") (.lit (.int 0))))
                          (.binop ">" (.name "j") (.lit (.int 8))))
                        (.ret (.unop "-" (.lit (.int 1))))
                        .skip)
                      (.seq
                        (.setField (.name "b") "a" (.irefIndex (.name "buf") (.lit (.int 0))))
                        (.ret
                          (.call
                            "span"
                            [ (.ptrOp "+" 1 (.field (.name "b") "a") (.name "i"))
                            , (.ptrOp "+" 1 (.field (.name "b") "a") (.name "j")) ]))))))))) }

/-- `oob_order`  (from `addr.c`) -/
def f_oob_order : Func :=
  { name := "oob_order"
  , params := ["i"]
  , body := (.seq
            (.assign
              "buf"
              (.boxFields
                (((List.range 4).map (fun i => (Expr.lit (Lit.str s!"{i}"), Expr.lit Lit.unit))) ++ [(Expr.lit (Lit.str "$esz"), Expr.lit (Lit.int 1))])))
            (.seq
              (.assign
                "b"
                (.boxFields [((.lit (.str "a")), (.lit .unit)), ((.lit (.str "n")), (.lit .unit))]))
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      (.setField (.name "b") "a" (.irefIndex (.name "buf") (.lit (.int 0))))
                      (.ret
                        (.call
                          "cmp_ptrs"
                          [ (.ptrOp "+" 1 (.field (.name "b") "a") (.lit (.int 0)))
                          , (.ptrOp "+" 1 (.field (.name "b") "a") (.name "i")) ])))))))) }

/-- `past_end`  (from `addr.c`) -/
def f_past_end : Func :=
  { name := "past_end"
  , params := ["k"]
  , body := (.seq
            (.assign
              "x"
              (.boxFields
                (((List.range 4).map (fun i => (Expr.lit (Lit.str s!"{i}"), Expr.lit Lit.unit))) ++ [(Expr.lit (Lit.str "$esz"), Expr.lit (Lit.int 1))])))
            (.seq
              (.assign
                "y"
                (.boxFields
                  (((List.range 4).map (fun i => (Expr.lit (Lit.str s!"{i}"), Expr.lit Lit.unit))) ++ [(Expr.lit (Lit.str "$esz"), Expr.lit (Lit.int 1))])))
              (.seq
                (.assign
                  "bx"
                  (.boxFields
                    [((.lit (.str "a")), (.lit .unit)), ((.lit (.str "n")), (.lit .unit))]))
                (.seq
                  (.assign
                    "by"
                    (.boxFields
                      [((.lit (.str "a")), (.lit .unit)), ((.lit (.str "n")), (.lit .unit))]))
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
                                (.setField
                                  (.name "bx")
                                  "a"
                                  (.irefIndex (.name "x") (.lit (.int 0))))
                                (.seq
                                  (.setField
                                    (.name "by")
                                    "a"
                                    (.irefIndex (.name "y") (.lit (.int 0))))
                                  (.seq
                                    (.ifte
                                      (.binop "==" (.name "k") (.lit (.int 0)))
                                      (.ret
                                        (.cond
                                        (.ptrOp
                                        "=="
                                        0
                                        (.ptrOp "+" 1 (.field (.name "bx") "a") (.lit (.int 4)))
                                        (.ptrOp "+" 1 (.field (.name "by") "a") (.lit (.int 0))))
                                        (.lit (.int 1))
                                        (.lit (.int 0))))
                                      .skip)
                                    (.ret
                                      (.cond
                                        (.ptrOp
                                        "=="
                                        0
                                        (.ptrOp "+" 1 (.field (.name "bx") "a") (.lit (.int 4)))
                                        (.ptrOp "+" 1 (.field (.name "bx") "a") (.lit (.int 0))))
                                        (.lit (.int 1))
                                        (.lit (.int 0))))))))))))))))) }

/-- `char_gap`  (from `addr.c`) -/
def f_char_gap : Func :=
  { name := "char_gap"
  , params := ["b", "i", "j"]
  , body := (.seq
            .skip
            (.seq
              (.assign "from" (.ptrOp "+" 1 (.field (.name "b") "c") (.name "i")))
              (.seq
                .skip
                (.seq
                  (.assign "to" (.ptrOp "+" 1 (.field (.name "b") "c") (.name "j")))
                  (.ret (.unop "cast:i32" (.ptrOp "diff" 1 (.name "to") (.name "from")))))))) }

/-- `gap`  (from `addr.c`) -/
def f_gap : Func :=
  { name := "gap"
  , params := ["i", "j"]
  , body := (.seq
            (.assign
              "buf"
              (.boxFields
                (((List.range 8).map (fun i => (Expr.lit (Lit.str s!"{i}"), Expr.lit Lit.unit))) ++ [(Expr.lit (Lit.str "$esz"), Expr.lit (Lit.int 1))])))
            (.seq
              (.assign "b" (.boxFields [((.lit (.str "c")), (.lit .unit))]))
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      (.ifte
                        (.binop
                          "||"
                          (.binop
                            "||"
                            (.binop
                              "||"
                              (.binop "<" (.name "i") (.lit (.int 0)))
                              (.binop ">" (.name "i") (.lit (.int 8))))
                            (.binop "<" (.name "j") (.lit (.int 0))))
                          (.binop ">" (.name "j") (.lit (.int 8))))
                        (.ret (.unop "-" (.lit (.int 99))))
                        .skip)
                      (.seq
                        (.setField (.name "b") "c" (.irefIndex (.name "buf") (.lit (.int 0))))
                        (.ret (.call "char_gap" [(.name "b"), (.name "i"), (.name "j")]))))))))) }

/-- `back`  (from `addr.c`) -/
def f_back : Func :=
  { name := "back"
  , params := ["p", "n"]
  , body := (.ret (.ptrOp "-" 1 (.name "p") (.name "n"))) }

/-- `back_eq`  (from `addr.c`) -/
def f_back_eq : Func :=
  { name := "back_eq"
  , params := ["i", "n"]
  , body := (.seq
            (.assign
              "buf"
              (.boxFields
                (((List.range 8).map (fun i => (Expr.lit (Lit.str s!"{i}"), Expr.lit Lit.unit))) ++ [(Expr.lit (Lit.str "$esz"), Expr.lit (Lit.int 1))])))
            (.seq
              (.assign "b" (.boxFields [((.lit (.str "c")), (.lit .unit))]))
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      (.ifte
                        (.binop
                          "||"
                          (.binop
                            "||"
                            (.binop
                              "||"
                              (.binop "<" (.name "i") (.lit (.int 0)))
                              (.binop ">" (.name "i") (.lit (.int 8))))
                            (.binop "<" (.name "n") (.lit (.int 0))))
                          (.binop ">" (.name "n") (.name "i")))
                        (.ret (.unop "-" (.lit (.int 1))))
                        .skip)
                      (.seq
                        (.setField (.name "b") "c" (.irefIndex (.name "buf") (.lit (.int 0))))
                        (.ret
                          (.cond
                            (.ptrOp
                              "=="
                              0
                              (.call
                                "back"
                                [(.ptrOp "+" 1 (.field (.name "b") "c") (.name "i")), (.name "n")])
                              (.ptrOp
                                "+"
                                1
                                (.field (.name "b") "c")
                                (.binop "-" (.name "i") (.name "n"))))
                            (.lit (.int 1))
                            (.lit (.int 0))))))))))) }

/-- `addr.c:<global>`  (from `addr.c`) -/
def f_addr_c__global_ : Func :=
  { name := "addr.c:<global>"
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
                                  (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := [f_addr_c__global_]

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_sum_until,
  f_cmp_ptrs,
  f_cmp_field_elems,
  f_field_order,
  f_eq_field_elems,
  f_field_eq,
  f_span,
  f_walk_span,
  f_oob_order,
  f_past_end,
  f_char_gap,
  f_gap,
  f_back,
  f_back_eq,
  f_addr_c__global_
] }

end Autoform.Generated.CAddr