import Autoform.Lang.Core.Semantics

/-!
# LangJS — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated
open Autoform.Core

/-- `index.js::program:pMap:<lambda>0:signalListener`  (from `index.js`) -/
def f_index_js__program_pMap__lambda_0_signalListener : Func :=
  { name := "index.js::program:pMap:<lambda>0:signalListener"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.expr
                (.call
                  "index.js::program:pMap:<lambda>0:reject"
                  [(.field (.name "signal") "reason")])))) }

/-- `index.js::program:pMap:<lambda>0`  (from `index.js`) -/
def f_index_js__program_pMap__lambda_0 : Func :=
  { name := "index.js::program:pMap:<lambda>0"
  , params := ["this", "resolve_", "reject_"]
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
                                                                    (.ifte
                                                                      (.binop
                                                                        "&&"
                                                                        (.binop
                                                                          "=="
                                                                          (.index
                                                                            (.name "iterable")
                                                                            (.field
                                                                              (.name "Symbol")
                                                                              "iterator"))
                                                                          (.name "undefined"))
                                                                        (.binop
                                                                          "=="
                                                                          (.index
                                                                            (.name "iterable")
                                                                            (.field
                                                                              (.name "Symbol")
                                                                              "asyncIterator"))
                                                                          (.name "undefined")))
                                                                      (.hole "control:THROW")
                                                                      .skip)
                                                                    (.seq
                                                                      (.ifte
                                                                        (.binop
                                                                          "!="
                                                                          (.hole "op:instanceOf")
                                                                          (.lit (.str "function")))
                                                                        (.hole "control:THROW")
                                                                        .skip)
                                                                      (.seq
                                                                        (.ifte
                                                                          (.unop
                                                                            "!"
                                                                            (.binop
                                                                              "||"
                                                                              (.binop
                                                                                "&&"
                                                                                (.call
                                                                                  "isSafeInteger"
                                                                                  [ (.name
                                                                                      "concurrency") ])
                                                                                (.binop
                                                                                  ">="
                                                                                  (.name
                                                                                    "concurrency")
                                                                                  (.lit (.int 1))))
                                                                              (.binop
                                                                                "=="
                                                                                (.name
                                                                                  "concurrency")
                                                                                (.field
                                                                                  (.name "Number")
                                                                                  "POSITIVE_INFINITY"))))
                                                                          (.hole "control:THROW")
                                                                          .skip)
                                                                        (.seq
                                                                          (.assign
                                                                            "result"
                                                                            (.call
                                                                              "__ecma.Array.factory"
                                                                              []))
                                                                          (.seq
                                                                            (.assign
                                                                              "errors"
                                                                              (.call
                                                                                "__ecma.Array.factory"
                                                                                []))
                                                                            (.seq
                                                                              (.seq
                                                                                .skip
                                                                                (.seq
                                                                                  (.assign
                                                                                    "_tmp_6"
                                                                                    (.hole
                                                                                      "op:alloc"))
                                                                                  (.seq
                                                                                    (.expr
                                                                                      (.call
                                                                                        "<operator>.new"
                                                                                        []))
                                                                                    (.assign
                                                                                      "skippedIndexesMap"
                                                                                      (.name
                                                                                        "_tmp_6")))))
                                                                              (.seq
                                                                                (.assign
                                                                                  "isRejected"
                                                                                  (.lit
                                                                                    (.bool false)))
                                                                                (.seq
                                                                                  (.assign
                                                                                    "isResolved"
                                                                                    (.lit
                                                                                      (.bool false)))
                                                                                  (.seq
                                                                                    (.assign
                                                                                      "isIterableDone"
                                                                                      (.lit
                                                                                        (.bool false)))
                                                                                    (.seq
                                                                                      (.assign
                                                                                        "resolvingCount"
                                                                                        (.lit
                                                                                          (.int 0)))
                                                                                      (.seq
                                                                                        (.assign
                                                                                          "currentIndex"
                                                                                          (.lit
                                                                                            (.int 0)))
                                                                                        (.seq
                                                                                          (.assign
                                                                                            "iterator"
                                                                                            (.cond
                                                                                              (.binop
                                                                                                "=="
                                                                                                (.index
                                                                                                  (.name
                                                                                                    "iterable")
                                                                                                  (.field
                                                                                                    (.name
                                                                                                      "Symbol")
                                                                                                    "iterator"))
                                                                                                (.name
                                                                                                  "undefined"))
                                                                                              (.call
                                                                                                "Symbol.asyncIterator"
                                                                                                [])
                                                                                              (.call
                                                                                                "Symbol.iterator"
                                                                                                [])))
                                                                                          (.seq
                                                                                            (.assign
                                                                                              "signalListener"
                                                                                              (.fnref
                                                                                                "index.js::program:pMap:<lambda>0:signalListener"))
                                                                                            (.seq
                                                                                              (.assign
                                                                                                "cleanup"
                                                                                                (.fnref
                                                                                                  "index.js::program:pMap:<lambda>0:cleanup"))
                                                                                              (.seq
                                                                                                (.assign
                                                                                                  "resolve"
                                                                                                  (.fnref
                                                                                                    "index.js::program:pMap:<lambda>0:resolve"))
                                                                                                (.seq
                                                                                                  (.assign
                                                                                                    "reject"
                                                                                                    (.fnref
                                                                                                      "index.js::program:pMap:<lambda>0:reject"))
                                                                                                  (.seq
                                                                                                    (.ifte
                                                                                                      (.name
                                                                                                        "signal")
                                                                                                      (.seq
                                                                                                        (.ifte
                                                                                                          (.field
                                                                                                            (.name
                                                                                                              "signal")
                                                                                                            "aborted")
                                                                                                          (.seq
                                                                                                            (.expr
                                                                                                              (.call
                                                                                                                "index.js::program:pMap:<lambda>0:reject"
                                                                                                                [ (.field
                                                                                                                    (.name
                                                                                                                      "signal")
                                                                                                                    "reason") ]))
                                                                                                            (.ret
                                                                                                              (.lit
                                                                                                                .unit)))
                                                                                                          .skip)
                                                                                                        (.expr
                                                                                                          (.mcall
                                                                                                            (.name
                                                                                                              "signal")
                                                                                                            "addEventListener"
                                                                                                            [ (.lit
                                                                                                                (.str "abort"))
                                                                                                            , (.name
                                                                                                                "signalListener")
                                                                                                            , (.hole
                                                                                                                "expr:BLOCK-prelude") ])))
                                                                                                      .skip)
                                                                                                    (.seq
                                                                                                      (.assign
                                                                                                        "next"
                                                                                                        (.fnref
                                                                                                          "index.js::program:pMap:<lambda>0:next"))
                                                                                                      (.expr
                                                                                                        (.call
                                                                                                          "index.js::program:pMap:<lambda>0:<lambda>7"
                                                                                                          [])))))))))))))))))))))))))))))))))))))))))))))))) }

/-- `index.js::program:pMap:<lambda>0:cleanup`  (from `index.js`) -/
def f_index_js__program_pMap__lambda_0_cleanup : Func :=
  { name := "index.js::program:pMap:<lambda>0:cleanup"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.expr
                (.mcall
                  (.name "signal")
                  "removeEventListener"
                  [(.lit (.str "abort")), (.name "signalListener")])))) }

/-- `index.js::program:pMap:<lambda>0:resolve`  (from `index.js`) -/
def f_index_js__program_pMap__lambda_0_resolve : Func :=
  { name := "index.js::program:pMap:<lambda>0:resolve"
  , params := ["this", "value"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.expr (.call "resolve_" [(.name "value")]))
                (.expr (.call "index.js::program:pMap:<lambda>0:cleanup" []))))) }

/-- `index.js::program:pMap:<lambda>0:reject`  (from `index.js`) -/
def f_index_js__program_pMap__lambda_0_reject : Func :=
  { name := "index.js::program:pMap:<lambda>0:reject"
  , params := ["this", "reason"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    (.assign "isRejected" (.lit (.bool true)))
                    (.seq
                      (.assign "isResolved" (.lit (.bool true)))
                      (.seq
                        (.expr (.call "reject_" [(.name "reason")]))
                        (.expr (.call "index.js::program:pMap:<lambda>0:cleanup" []))))))))) }

/-- `index.js::program:pMap:<lambda>0:<lambda>5:<lambda>6`  (from `index.js`) -/
def f_index_js__program_pMap__lambda_0__lambda_5__lambda_6 : Func :=
  { name := "index.js::program:pMap:<lambda>0:<lambda>5:<lambda>6"
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
                                    (.tryCatch
                                      (.seq
                                        .skip
                                        (.seq
                                          .skip
                                          (.seq
                                            (.assign "element" (.hole "op:await"))
                                            (.seq
                                              (.ifte (.name "isResolved") (.ret (.lit .unit)) .skip)
                                              (.seq
                                                (.assign "value" (.hole "op:await"))
                                                (.seq
                                                  (.ifte
                                                    (.binop "==" (.name "value") (.name "pMapSkip"))
                                                    (.expr
                                                      (.mcall
                                                        (.name "skippedIndexesMap")
                                                        "set"
                                                        [(.name "index"), (.name "value")]))
                                                    .skip)
                                                  (.seq
                                                    (.setIndex
                                                      (.name "result")
                                                      (.name "index")
                                                      (.name "value"))
                                                    (.seq
                                                      (.expr (.hole "op:postIncrement"))
                                                      (.expr (.hole "op:await"))))))))))
                                      "__exc"
                                      (.seq
                                        (.expr (.name "error"))
                                        (.ifte
                                          (.name "stopOnError")
                                          (.expr
                                            (.call
                                              "index.js::program:pMap:<lambda>0:reject"
                                              [(.name "error")]))
                                          (.seq
                                            (.expr
                                              (.mcall (.name "errors") "push" [(.name "error")]))
                                            (.seq
                                              (.expr (.hole "op:postIncrement"))
                                              (.tryCatch
                                                (.expr (.hole "op:await"))
                                                "__exc"
                                                (.seq
                                                  (.expr (.name "error"))
                                                  (.expr
                                                    (.call
                                                      "index.js::program:pMap:<lambda>0:reject"
                                                      [(.name "error")])))))))))))))))))))))) }

/-- `index.js::program:pMap:<lambda>0:next`  (from `index.js`) -/
def f_index_js__program_pMap__lambda_0_next : Func :=
  { name := "index.js::program:pMap:<lambda>0:next"
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
                                                      (.ifte
                                                        (.name "isResolved")
                                                        (.ret (.lit .unit))
                                                        .skip)
                                                      (.seq
                                                        (.assign "nextItem" (.hole "op:await"))
                                                        (.seq
                                                          (.assign "index" (.name "currentIndex"))
                                                          (.seq
                                                            (.expr (.hole "op:postIncrement"))
                                                            (.seq
                                                              (.ifte
                                                                (.field (.name "nextItem") "done")
                                                                (.seq
                                                                  (.assign
                                                                    "isIterableDone"
                                                                    (.lit (.bool true)))
                                                                  (.seq
                                                                    (.ifte
                                                                      (.binop
                                                                        "&&"
                                                                        (.binop
                                                                          "=="
                                                                          (.name "resolvingCount")
                                                                          (.lit (.int 0)))
                                                                        (.unop
                                                                          "!"
                                                                          (.name "isResolved")))
                                                                      (.seq
                                                                        .skip
                                                                        (.seq
                                                                          (.ifte
                                                                            (.binop
                                                                              "&&"
                                                                              (.unop
                                                                                "!"
                                                                                (.name
                                                                                  "stopOnError"))
                                                                              (.binop
                                                                                ">"
                                                                                (.field
                                                                                  (.name "errors")
                                                                                  "length")
                                                                                (.lit (.int 0))))
                                                                            (.seq
                                                                              (.expr
                                                                                (.call
                                                                                  "index.js::program:pMap:<lambda>0:reject"
                                                                                  [ (.hole
                                                                                      "expr:BLOCK-impure") ]))
                                                                              (.ret (.lit .unit)))
                                                                            .skip)
                                                                          (.seq
                                                                            (.assign
                                                                              "isResolved"
                                                                              (.lit (.bool true)))
                                                                            (.seq
                                                                              (.ifte
                                                                                (.binop
                                                                                  "=="
                                                                                  (.field
                                                                                    (.name
                                                                                      "skippedIndexesMap")
                                                                                    "size")
                                                                                  (.lit (.int 0)))
                                                                                (.seq
                                                                                  (.expr
                                                                                    (.call
                                                                                      "index.js::program:pMap:<lambda>0:resolve"
                                                                                      [ (.name
                                                                                          "result") ]))
                                                                                  (.ret
                                                                                    (.lit .unit)))
                                                                                .skip)
                                                                              (.seq
                                                                                (.assign
                                                                                  "pureResult"
                                                                                  (.call
                                                                                    "__ecma.Array.factory"
                                                                                    []))
                                                                                (.seq
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
                                                                                              "_iterator_0"
                                                                                              (.hole
                                                                                                "op:iterator"))
                                                                                            (.seq
                                                                                              (.expr
                                                                                                (.name
                                                                                                  "_result_0"))
                                                                                              (.seq
                                                                                                (.expr
                                                                                                  (.name
                                                                                                    "index"))
                                                                                                (.seq
                                                                                                  (.expr
                                                                                                    (.name
                                                                                                      "value"))
                                                                                                  (.loop
                                                                                                    (.unop
                                                                                                      "!"
                                                                                                      (.field
                                                                                                        (.hole
                                                                                                          "op:assignment")
                                                                                                        "done"))
                                                                                                    (.seq
                                                                                                      (.assign
                                                                                                        "index"
                                                                                                        (.index
                                                                                                          (.field
                                                                                                            (.name
                                                                                                              "_result_0")
                                                                                                            "value")
                                                                                                          (.lit
                                                                                                            (.int 0))))
                                                                                                      (.seq
                                                                                                        (.assign
                                                                                                          "value"
                                                                                                          (.index
                                                                                                            (.field
                                                                                                              (.name
                                                                                                                "_result_0")
                                                                                                              "value")
                                                                                                            (.lit
                                                                                                              (.int 1))))
                                                                                                        (.seq
                                                                                                          (.ifte
                                                                                                            (.binop
                                                                                                              "=="
                                                                                                              (.mcall
                                                                                                                (.name
                                                                                                                  "skippedIndexesMap")
                                                                                                                "get"
                                                                                                                [ (.name
                                                                                                                    "index") ])
                                                                                                              (.name
                                                                                                                "pMapSkip"))
                                                                                                            .cont
                                                                                                            .skip)
                                                                                                          (.expr
                                                                                                            (.mcall
                                                                                                              (.name
                                                                                                                "pureResult")
                                                                                                              "push"
                                                                                                              [ (.name
                                                                                                                  "value") ]))))))))))))))
                                                                                  (.expr
                                                                                    (.call
                                                                                      "index.js::program:pMap:<lambda>0:resolve"
                                                                                      [ (.name
                                                                                          "pureResult") ]))))))))
                                                                      .skip)
                                                                    (.ret (.lit .unit))))
                                                                .skip)
                                                              (.seq
                                                                (.expr (.hole "op:postIncrement"))
                                                                (.expr
                                                                  (.call
                                                                    "index.js::program:pMap:<lambda>0:<lambda>5:<lambda>6"
                                                                    []))))))))))))))))))))))))))))) }

/-- `index.js::program:pMap:<lambda>0:<lambda>7`  (from `index.js`) -/
def f_index_js__program_pMap__lambda_0__lambda_7 : Func :=
  { name := "index.js::program:pMap:<lambda>0:<lambda>7"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.hole "control:FOR")))))))) }

/-- `index.js::program:pMap`  (from `index.js`) -/
def f_index_js__program_pMap : Func :=
  { name := "index.js::program:pMap"
  , params := ["this", "iterable", "mapper", "param3_0"]
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
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              (.assign
                                "_tmp_1"
                                (.cond
                                  (.binop "==" (.name "param3_0") (.hole "op:void"))
                                  (.name "_tmp_0")
                                  (.name "param3_0")))
                              (.seq
                                (.assign
                                  "concurrency"
                                  (.cond
                                    (.binop
                                      "=="
                                      (.field (.name "_tmp_1") "concurrency")
                                      (.hole "op:void"))
                                    (.field (.name "Number") "POSITIVE_INFINITY")
                                    (.field (.name "_tmp_1") "concurrency")))
                                (.seq
                                  (.assign
                                    "stopOnError"
                                    (.cond
                                      (.binop
                                        "=="
                                        (.field (.name "_tmp_1") "stopOnError")
                                        (.hole "op:void"))
                                      (.lit (.bool true))
                                      (.field (.name "_tmp_1") "stopOnError")))
                                  (.seq
                                    (.assign "signal" (.field (.name "_tmp_1") "signal"))
                                    (.expr (.name "_tmp_1"))))))))
                        (.seq
                          .skip
                          (.seq
                            (.assign "_tmp_2" (.hole "op:alloc"))
                            (.seq
                              (.expr
                                (.call
                                  "<operator>.new"
                                  [(.fnref "index.js::program:pMap:<lambda>0")]))
                              (.ret (.name "_tmp_2")))))))))))) }

/-- `index.js::program`  (from `index.js`) -/
def f_index_js__program : Func :=
  { name := "index.js::program"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.seq
                    (.assign "pMap" (.fnref "index.js::program:pMap"))
                    (.setIndex (.name "exports") (.lit (.str "default")) (.name "pMap")))
                  (.seq
                    (.seq
                      (.assign "pMapIterable" (.fnref "index.js::program:pMapIterable"))
                      (.setField (.name "exports") "pMapIterable" (.name "pMapIterable")))
                    (.seq
                      (.assign "pMapSkip" (.call "Symbol" [(.lit (.str "skip"))]))
                      (.setField (.name "exports") "pMapSkip" (.name "pMapSkip")))))))) }

/-- `index.js::program:pMapIterable:_computed_object_method_0:trySpawn:<lambda>8`  (from `index.js`) -/
def f_index_js__program_pMapIterable__computed_object_method_0_trySpawn__lambda_8 : Func :=
  { name := "index.js::program:pMapIterable:_computed_object_method_0:trySpawn:<lambda>8"
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
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign "_tmp_16" (.hole "op:await"))
                                        (.seq
                                          (.assign "done" (.field (.name "_tmp_16") "done"))
                                          (.seq
                                            (.assign "value" (.field (.name "_tmp_16") "value"))
                                            (.expr (.name "_tmp_16"))))))))
                                (.seq
                                  (.ifte
                                    (.name "done")
                                    (.seq
                                      (.expr (.hole "op:postIncrement"))
                                      (.seq
                                        .skip
                                        (.seq
                                          (.setField (.name "_tmp_17") "done" (.lit (.bool true)))
                                          (.ret (.name "_tmp_17")))))
                                    .skip)
                                  (.seq
                                    (.expr
                                      (.call
                                        "index.js::program:pMapIterable:_computed_object_method_0:trySpawn"
                                        []))
                                    (.tryCatch
                                      (.seq
                                        .skip
                                        (.seq
                                          .skip
                                          (.seq
                                            (.assign "currentIndex" (.hole "op:postIncrement"))
                                            (.seq
                                              (.assign "returnValue" (.hole "op:await"))
                                              (.seq
                                                (.expr (.hole "op:postIncrement"))
                                                (.seq
                                                  (.ifte
                                                    (.binop
                                                      "=="
                                                      (.name "returnValue")
                                                      (.name "pMapSkip"))
                                                    (.seq
                                                      .skip
                                                      (.seq
                                                        (.assign
                                                          "index"
                                                          (.mcall
                                                            (.name "promises")
                                                            "indexOf"
                                                            [(.name "promise")]))
                                                        (.ifte
                                                          (.binop
                                                            ">"
                                                            (.name "index")
                                                            (.lit (.int 0)))
                                                          (.expr
                                                            (.mcall
                                                              (.name "promises")
                                                              "splice"
                                                              [(.name "index"), (.lit (.int 1))]))
                                                          .skip)))
                                                    .skip)
                                                  (.seq
                                                    (.expr
                                                      (.call
                                                        "index.js::program:pMapIterable:_computed_object_method_0:trySpawn"
                                                        []))
                                                    (.seq
                                                      .skip
                                                      (.seq
                                                        (.setField
                                                          (.name "_tmp_18")
                                                          "done"
                                                          (.lit (.bool false)))
                                                        (.seq
                                                          (.setField
                                                            (.name "_tmp_18")
                                                            "value"
                                                            (.name "returnValue"))
                                                          (.ret (.name "_tmp_18"))))))))))))
                                      "__exc"
                                      (.seq
                                        (.expr (.name "error"))
                                        (.seq
                                          (.expr (.hole "op:postIncrement"))
                                          (.seq
                                            (.assign "isDone" (.lit (.bool true)))
                                            (.seq
                                              .skip
                                              (.seq
                                                (.setField
                                                  (.name "_tmp_19")
                                                  "error"
                                                  (.name "error"))
                                                (.ret (.name "_tmp_19"))))))))))))))))))))) }

/-- `index.js::program:pMapIterable:_computed_object_method_0:trySpawn`  (from `index.js`) -/
def f_index_js__program_pMapIterable__computed_object_method_0_trySpawn : Func :=
  { name := "index.js::program:pMapIterable:_computed_object_method_0:trySpawn"
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
                                  (.ifte
                                    (.binop
                                      "||"
                                      (.name "isDone")
                                      (.unop
                                        "!"
                                        (.binop
                                          "&&"
                                          (.binop
                                            "<"
                                            (.name "pendingPromisesCount")
                                            (.name "concurrency"))
                                          (.binop
                                            "<"
                                            (.field (.name "promises") "length")
                                            (.name "backpressure")))))
                                    (.ret (.lit .unit))
                                    .skip)
                                  (.seq
                                    (.expr (.hole "op:postIncrement"))
                                    (.seq
                                      (.assign
                                        "promise"
                                        (.call
                                          "index.js::program:pMapIterable:_computed_object_method_0:trySpawn:<lambda>8"
                                          []))
                                      (.expr (.mcall (.name "promises") "push" [(.name "promise")])))))))))))))))) }

/-- `index.js::program:pMapIterable:_computed_object_method_0`  (from `index.js`) -/
def f_index_js__program_pMapIterable__computed_object_method_0 : Func :=
  { name := "index.js::program:pMapIterable:_computed_object_method_0"
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
                                  (.assign
                                    "trySpawn"
                                    (.fnref
                                      "index.js::program:pMapIterable:_computed_object_method_0:trySpawn"))
                                  (.seq
                                    (.assign
                                      "iterator"
                                      (.cond
                                        (.binop
                                          "=="
                                          (.index
                                            (.name "iterable")
                                            (.field (.name "Symbol") "asyncIterator"))
                                          (.name "undefined"))
                                        (.call "Symbol.iterator" [])
                                        (.call "Symbol.asyncIterator" [])))
                                    (.seq
                                      (.assign "promises" (.call "__ecma.Array.factory" []))
                                      (.seq
                                        (.assign "pendingPromisesCount" (.lit (.int 0)))
                                        (.seq
                                          (.assign "isDone" (.lit (.bool false)))
                                          (.seq
                                            (.assign "index" (.lit (.int 0)))
                                            (.seq
                                              (.expr
                                                (.call
                                                  "index.js::program:pMapIterable:_computed_object_method_0:trySpawn"
                                                  []))
                                              (.loop
                                                (.binop
                                                  ">"
                                                  (.field (.name "promises") "length")
                                                  (.lit (.int 0)))
                                                (.seq
                                                  .skip
                                                  (.seq
                                                    (.seq
                                                      .skip
                                                      (.seq
                                                        .skip
                                                        (.seq
                                                          .skip
                                                          (.seq
                                                            .skip
                                                            (.seq
                                                              (.assign "_tmp_20" (.hole "op:await"))
                                                              (.seq
                                                                (.assign
                                                                  "error"
                                                                  (.field (.name "_tmp_20") "error"))
                                                                (.seq
                                                                  (.assign
                                                                    "done"
                                                                    (.field
                                                                      (.name "_tmp_20")
                                                                      "done"))
                                                                  (.seq
                                                                    (.assign
                                                                      "value"
                                                                      (.field
                                                                        (.name "_tmp_20")
                                                                        "value"))
                                                                    (.expr (.name "_tmp_20"))))))))))
                                                    (.seq
                                                      (.expr (.mcall (.name "promises") "shift" []))
                                                      (.seq
                                                        (.ifte
                                                          (.name "error")
                                                          (.hole "control:THROW")
                                                          .skip)
                                                        (.seq
                                                          (.ifte
                                                            (.name "done")
                                                            (.ret (.lit .unit))
                                                            .skip)
                                                          (.seq
                                                            (.expr
                                                              (.call
                                                                "index.js::program:pMapIterable:_computed_object_method_0:trySpawn"
                                                                []))
                                                            (.seq
                                                              (.ifte
                                                                (.binop
                                                                  "=="
                                                                  (.name "value")
                                                                  (.name "pMapSkip"))
                                                                .cont
                                                                .skip)
                                                              (.ret (.name "value")))))))))))))))))))))))))))) }

/-- `index.js::program:pMapIterable`  (from `index.js`) -/
def f_index_js__program_pMapIterable : Func :=
  { name := "index.js::program:pMapIterable"
  , params := ["this", "iterable", "mapper", "param3_1"]
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
                                  (.seq
                                    .skip
                                    (.seq
                                      (.assign
                                        "_tmp_10"
                                        (.cond
                                          (.binop "==" (.name "param3_1") (.hole "op:void"))
                                          (.name "_tmp_9")
                                          (.name "param3_1")))
                                      (.seq
                                        (.assign
                                          "concurrency"
                                          (.cond
                                            (.binop
                                              "=="
                                              (.field (.name "_tmp_10") "concurrency")
                                              (.hole "op:void"))
                                            (.field (.name "Number") "POSITIVE_INFINITY")
                                            (.field (.name "_tmp_10") "concurrency")))
                                        (.seq
                                          (.assign
                                            "backpressure"
                                            (.cond
                                              (.binop
                                                "=="
                                                (.field (.name "_tmp_10") "backpressure")
                                                (.hole "op:void"))
                                              (.name "concurrency")
                                              (.field (.name "_tmp_10") "backpressure")))
                                          (.expr (.name "_tmp_10"))))))
                                  (.seq
                                    (.ifte
                                      (.binop
                                        "&&"
                                        (.binop
                                          "=="
                                          (.index
                                            (.name "iterable")
                                            (.field (.name "Symbol") "iterator"))
                                          (.name "undefined"))
                                        (.binop
                                          "=="
                                          (.index
                                            (.name "iterable")
                                            (.field (.name "Symbol") "asyncIterator"))
                                          (.name "undefined")))
                                      (.hole "control:THROW")
                                      .skip)
                                    (.seq
                                      (.ifte
                                        (.binop
                                          "!="
                                          (.hole "op:instanceOf")
                                          (.lit (.str "function")))
                                        (.hole "control:THROW")
                                        .skip)
                                      (.seq
                                        (.ifte
                                          (.unop
                                            "!"
                                            (.binop
                                              "||"
                                              (.binop
                                                "&&"
                                                (.call "isSafeInteger" [(.name "concurrency")])
                                                (.binop ">=" (.name "concurrency") (.lit (.int 1))))
                                              (.binop
                                                "=="
                                                (.name "concurrency")
                                                (.field (.name "Number") "POSITIVE_INFINITY"))))
                                          (.hole "control:THROW")
                                          .skip)
                                        (.seq
                                          (.ifte
                                            (.unop
                                              "!"
                                              (.binop
                                                "||"
                                                (.binop
                                                  "&&"
                                                  (.call "isSafeInteger" [(.name "backpressure")])
                                                  (.binop
                                                    ">="
                                                    (.name "backpressure")
                                                    (.name "concurrency")))
                                                (.binop
                                                  "=="
                                                  (.name "backpressure")
                                                  (.field (.name "Number") "POSITIVE_INFINITY"))))
                                            (.hole "control:THROW")
                                            .skip)
                                          (.seq
                                            .skip
                                            (.seq
                                              (.setIndex
                                                (.name "_tmp_15")
                                                (.hole "lit:unquoted")
                                                (.fnref
                                                  "index.js::program:pMapIterable:_computed_object_method_0"))
                                              (.ret (.name "_tmp_15")))))))))))))))))))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_index_js__program_pMap__lambda_0_signalListener,
  f_index_js__program_pMap__lambda_0,
  f_index_js__program_pMap__lambda_0_cleanup,
  f_index_js__program_pMap__lambda_0_resolve,
  f_index_js__program_pMap__lambda_0_reject,
  f_index_js__program_pMap__lambda_0__lambda_5__lambda_6,
  f_index_js__program_pMap__lambda_0_next,
  f_index_js__program_pMap__lambda_0__lambda_7,
  f_index_js__program_pMap,
  f_index_js__program,
  f_index_js__program_pMapIterable__computed_object_method_0_trySpawn__lambda_8,
  f_index_js__program_pMapIterable__computed_object_method_0_trySpawn,
  f_index_js__program_pMapIterable__computed_object_method_0,
  f_index_js__program_pMapIterable
] }

end Autoform.Generated