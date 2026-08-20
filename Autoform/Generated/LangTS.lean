import Autoform.Lang.Core.Semantics

-- Lean's default `maxRecDepth` (512) is a guard against runaway elaboration, not
-- a statement about reasonable programs. A deep-embedded function body is one
-- term, so the elaborator's recursion depth tracks the *source's* nesting depth:
-- Linux `lib/` hit the limit at two declarations and the whole module failed to
-- type-check. Raising it costs nothing for shallow modules and is the difference
-- between compiling a real codebase and not.
set_option maxRecDepth 8000

/-!
# LangTS — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated
open Autoform.Core

/-- `index.ts::program`  (from `index.ts`) -/
def f_index_ts__program : Func :=
  { name := "index.ts::program"
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
                                        (.assign
                                        "EventEmitter"
                                        (.field
                                        (.call "require" [(.lit (.str "eventemitter3"))])
                                        "EventEmitter"))
                                        (.seq
                                        (.assign
                                        "pTimeout"
                                        (.call "require" [(.lit (.str "p-timeout"))]))
                                        (.seq
                                        (.seq
                                        (.assign
                                        "Queue"
                                        (.field
                                        (.call "require" [(.lit (.str "./queue.js"))])
                                        "Queue"))
                                        (.assign
                                        "RunFunction"
                                        (.field
                                        (.call "require" [(.lit (.str "./queue.js"))])
                                        "RunFunction")))
                                        (.seq
                                        (.assign
                                        "PriorityQueue"
                                        (.call "require" [(.lit (.str "./priority-queue.js"))]))
                                        (.seq
                                        (.seq
                                        (.assign
                                        "QueueAddOptions"
                                        (.field
                                        (.call "require" [(.lit (.str "./options.js"))])
                                        "QueueAddOptions"))
                                        (.seq
                                        (.assign
                                        "Options"
                                        (.field
                                        (.call "require" [(.lit (.str "./options.js"))])
                                        "Options"))
                                        (.assign
                                        "TaskOptions"
                                        (.field
                                        (.call "require" [(.lit (.str "./options.js"))])
                                        "TaskOptions"))))
                                        (.seq
                                        (.seq
                                        (.seq
                                        .skip
                                        (.assign
                                        "PQueue"
                                        (.fnref "index.ts::program:PQueue:<init>")))
                                        (.setIndex
                                        (.name "exports")
                                        (.lit (.str "default"))
                                        (.name "PQueue")))
                                        (.seq
                                        (.seq
                                        (.assign
                                        "_queue.js"
                                        (.call "require" [(.lit (.str "./queue.js"))]))
                                        (.setField
                                        (.name "exports")
                                        "Queue"
                                        (.field (.name "_queue.js") "Queue")))
                                        (.seq
                                        (.seq
                                        (.assign
                                        "_priority-queue.js"
                                        (.call "require" [(.lit (.str "./priority-queue.js"))]))
                                        (.setField
                                        (.name "exports")
                                        "PriorityQueue"
                                        (.field (.name "_priority-queue.js") "default")))
                                        (.seq
                                        (.seq
                                        (.assign
                                        "_options.js"
                                        (.call "require" [(.lit (.str "./options.js"))]))
                                        (.seq
                                        (.setField
                                        (.name "exports")
                                        "QueueAddOptions"
                                        (.field (.name "_options.js") "QueueAddOptions"))
                                        (.setField
                                        (.name "exports")
                                        "Options"
                                        (.field (.name "_options.js") "Options"))))
                                        (.seq
                                        (.seq
                                        (.assign
                                        "_p-timeout"
                                        (.call "require" [(.lit (.str "p-timeout"))]))
                                        (.setField
                                        (.name "exports")
                                        "TimeoutError"
                                        (.field (.name "_p-timeout") "TimeoutError")))
                                        (.seq (.hole "stmt:TYPE_DECL") (.hole "stmt:TYPE_DECL"))))))))))))))))))))))))))) }

/-- `index.ts::program:PQueue:<init>`  (from `index.ts`) -/
def f_index_ts__program_PQueue__init_ : Func :=
  { name := "index.ts::program:PQueue:<init>"
  , params := ["this", "options"]
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
                                        (.assign "intervalCount" (.lit (.int 0)))
                                        (.seq
                                        (.assign "rateLimitedInInterval" (.lit (.bool false)))
                                        (.seq
                                        (.assign "rateLimitFlushScheduled" (.lit (.bool false)))
                                        (.seq
                                        (.assign "intervalEnd" (.lit (.int 0)))
                                        (.seq
                                        (.assign "strictTicks" (.call "__ecma.Array.factory" []))
                                        (.seq
                                        (.assign "strictTicksStartIndex" (.lit (.int 0)))
                                        (.seq
                                        (.assign "pending" (.lit (.int 0)))
                                        (.seq
                                        (.assign "idAssigner" (.hole "lit:unquoted"))
                                        (.seq
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "_tmp_7" (.hole "op:alloc"))
                                        (.seq
                                        (.expr (.call "<operator>.new" []))
                                        (.assign "runningTasks" (.name "_tmp_7")))))
                                        (.seq
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "_tmp_8" (.hole "op:alloc"))
                                        (.seq
                                        (.expr (.call "<operator>.new" []))
                                        (.assign
                                        "queueAbortListenerCleanupFunctions"
                                        (.name "_tmp_8")))))
                                        (.seq
                                        (.expr (.call "super" []))
                                        (.seq
                                        (.assign "options" (.hole "op:cast"))
                                        (.seq
                                        (.ifte
                                        (.unop
                                        "!"
                                        (.binop
                                        "&&"
                                        (.binop "==" (.hole "op:instanceOf") (.lit (.str "number")))
                                        (.binop
                                        ">="
                                        (.field (.name "options") "intervalCap")
                                        (.lit (.int 1)))))
                                        (.hole "control:THROW")
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "||"
                                        (.binop
                                        "=="
                                        (.field (.name "options") "interval")
                                        (.name "undefined"))
                                        (.unop
                                        "!"
                                        (.binop
                                        "&&"
                                        (.mcall
                                        (.name "options")
                                        "interval"
                                        [(.field (.name "options") "interval")])
                                        (.binop
                                        ">="
                                        (.field (.name "options") "interval")
                                        (.lit (.int 0))))))
                                        (.hole "control:THROW")
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.field (.name "options") "strict")
                                        (.binop
                                        "=="
                                        (.field (.name "options") "interval")
                                        (.lit (.int 0))))
                                        (.hole "control:THROW")
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.field (.name "options") "strict")
                                        (.binop
                                        "=="
                                        (.field (.name "options") "intervalCap")
                                        (.field (.name "Number") "POSITIVE_INFINITY")))
                                        (.hole "control:THROW")
                                        .skip)
                                        (.seq
                                        (.setField
                                        (.name "this")
                                        "#carryoverIntervalCount"
                                        (.binop
                                        "||"
                                        (.binop
                                        "||"
                                        (.field (.name "options") "carryoverIntervalCount")
                                        (.field (.name "options") "carryoverConcurrencyCount"))
                                        (.lit (.bool false))))
                                        (.seq
                                        (.setField
                                        (.name "this")
                                        "#isIntervalIgnored"
                                        (.binop
                                        "||"
                                        (.binop
                                        "=="
                                        (.field (.name "options") "intervalCap")
                                        (.field (.name "Number") "POSITIVE_INFINITY"))
                                        (.binop
                                        "=="
                                        (.field (.name "options") "interval")
                                        (.lit (.int 0)))))
                                        (.seq
                                        (.setField
                                        (.name "this")
                                        "#intervalCap"
                                        (.field (.name "options") "intervalCap"))
                                        (.seq
                                        (.setField
                                        (.name "this")
                                        "#interval"
                                        (.field (.name "options") "interval"))
                                        (.seq
                                        (.setField
                                        (.name "this")
                                        "#strict"
                                        (.hole "op:notNullAssert"))
                                        (.seq
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "_tmp_5" (.hole "op:alloc"))
                                        (.seq
                                        (.expr (.call "<operator>.new" []))
                                        (.setField (.name "this") "#queue" (.name "_tmp_5")))))
                                        (.seq
                                        (.setField
                                        (.name "this")
                                        "#queueClass"
                                        (.hole "op:notNullAssert"))
                                        (.seq
                                        (.setField
                                        (.name "this")
                                        "concurrency"
                                        (.hole "op:notNullAssert"))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.binop
                                        "!="
                                        (.field (.name "options") "timeout")
                                        (.name "undefined"))
                                        (.unop
                                        "!"
                                        (.binop
                                        "&&"
                                        (.mcall
                                        (.name "options")
                                        "timeout"
                                        [(.field (.name "options") "timeout")])
                                        (.binop
                                        ">"
                                        (.field (.name "options") "timeout")
                                        (.lit (.int 0))))))
                                        (.hole "control:THROW")
                                        .skip)
                                        (.seq
                                        (.setField
                                        (.name "this")
                                        "timeout"
                                        (.field (.name "options") "timeout"))
                                        (.seq
                                        (.setField
                                        (.name "this")
                                        "#isPaused"
                                        (.binop
                                        "=="
                                        (.field (.name "options") "autoStart")
                                        (.lit (.bool false))))
                                        (.expr (.mcall (.name "this") "#setupRateLimitTracking" []))))))))))))))))))))))))))))))))))))))))))))))))))))) }

/-- `index.ts::program:PQueue:#cleanupStrictTicks`  (from `index.ts`) -/
def f_index_ts__program_PQueue__cleanupStrictTicks : Func :=
  { name := "index.ts::program:PQueue:#cleanupStrictTicks"
  , params := ["this", "now"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.loop
                    (.binop
                      "<"
                      (.field (.name "this") "#strictTicksStartIndex")
                      (.field (.field (.name "this") "#strictTicks") "length"))
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "oldestTick"
                          (.index
                            (.field (.name "this") "#strictTicks")
                            (.field (.name "this") "#strictTicksStartIndex")))
                        (.ifte
                          (.binop
                            "&&"
                            (.binop "!=" (.name "oldestTick") (.name "undefined"))
                            (.binop
                              ">="
                              (.binop "-" (.name "now") (.name "oldestTick"))
                              (.field (.name "this") "#interval")))
                          (.expr (.hole "op:postIncrement"))
                          .brk))))
                  (.seq
                    (.assign
                      "shouldCompact"
                      (.binop
                        "||"
                        (.binop
                          "&&"
                          (.binop
                            ">"
                            (.field (.name "this") "#strictTicksStartIndex")
                            (.lit (.int 100)))
                          (.binop
                            ">"
                            (.field (.name "this") "#strictTicksStartIndex")
                            (.binop
                              "/"
                              (.field (.field (.name "this") "#strictTicks") "length")
                              (.lit (.int 2)))))
                        (.binop
                          "=="
                          (.field (.name "this") "#strictTicksStartIndex")
                          (.field (.field (.name "this") "#strictTicks") "length"))))
                    (.ifte
                      (.name "shouldCompact")
                      (.seq
                        (.setField
                          (.name "this")
                          "#strictTicks"
                          (.mcall
                            (.hole "op:assignment")
                            "slice"
                            [(.field (.name "this") "#strictTicksStartIndex")]))
                        (.setField (.name "this") "#strictTicksStartIndex" (.lit (.int 0))))
                      .skip)))))) }

/-- `index.ts::program:PQueue:#consumeIntervalSlot`  (from `index.ts`) -/
def f_index_ts__program_PQueue__consumeIntervalSlot : Func :=
  { name := "index.ts::program:PQueue:#consumeIntervalSlot"
  , params := ["this", "now"]
  , body := (.seq
            .skip
            (.ifte
              (.field (.name "this") "#strict")
              (.expr (.mcall (.hole "op:assignment") "push" [(.name "now")]))
              (.expr (.hole "op:postIncrement")))) }

/-- `index.ts::program:PQueue:#rollbackIntervalSlot`  (from `index.ts`) -/
def f_index_ts__program_PQueue__rollbackIntervalSlot : Func :=
  { name := "index.ts::program:PQueue:#rollbackIntervalSlot"
  , params := ["this"]
  , body := (.seq
            .skip
            (.ifte
              (.field (.name "this") "#strict")
              (.ifte
                (.binop
                  ">"
                  (.field (.field (.name "this") "#strictTicks") "length")
                  (.field (.name "this") "#strictTicksStartIndex"))
                (.expr (.mcall (.hole "op:assignment") "pop" []))
                .skip)
              (.ifte
                (.binop ">" (.field (.name "this") "#intervalCount") (.lit (.int 0)))
                (.expr (.hole "op:postIncrement"))
                .skip))) }

/-- `index.ts::program:PQueue:#getActiveTicksCount`  (from `index.ts`) -/
def f_index_ts__program_PQueue__getActiveTicksCount : Func :=
  { name := "index.ts::program:PQueue:#getActiveTicksCount"
  , params := ["this"]
  , body := (.ret
            (.binop
              "-"
              (.field (.field (.name "this") "#strictTicks") "length")
              (.field (.name "this") "#strictTicksStartIndex"))) }

/-- `index.ts::program:PQueue:#doesIntervalAllowAnother`  (from `index.ts`) -/
def f_index_ts__program_PQueue__doesIntervalAllowAnother : Func :=
  { name := "index.ts::program:PQueue:#doesIntervalAllowAnother"
  , params := ["this"]
  , body := (.seq
            (.ifte (.field (.name "this") "#isIntervalIgnored") (.ret (.lit (.bool true))) .skip)
            (.seq
              (.ifte
                (.field (.name "this") "#strict")
                (.ret
                  (.binop
                    "<"
                    (.mcall (.name "this") "#getActiveTicksCount" [])
                    (.field (.name "this") "#intervalCap")))
                .skip)
              (.ret
                (.binop
                  "<"
                  (.field (.name "this") "#intervalCount")
                  (.field (.name "this") "#intervalCap"))))) }

/-- `index.ts::program:PQueue:#doesConcurrentAllowAnother`  (from `index.ts`) -/
def f_index_ts__program_PQueue__doesConcurrentAllowAnother : Func :=
  { name := "index.ts::program:PQueue:#doesConcurrentAllowAnother"
  , params := ["this"]
  , body := (.ret
            (.binop "<" (.field (.name "this") "#pending") (.field (.name "this") "#concurrency"))) }

/-- `index.ts::program:PQueue:#next`  (from `index.ts`) -/
def f_index_ts__program_PQueue__next : Func :=
  { name := "index.ts::program:PQueue:#next"
  , params := ["this"]
  , body := (.seq
            (.expr (.hole "op:postIncrement"))
            (.seq
              (.ifte
                (.binop "==" (.field (.name "this") "#pending") (.lit (.int 0)))
                (.expr (.mcall (.name "this") "emit" [(.lit (.str "pendingZero"))]))
                .skip)
              (.seq
                (.expr (.mcall (.name "this") "#tryToStartAnother" []))
                (.expr (.mcall (.name "this") "emit" [(.lit (.str "next"))]))))) }

/-- `index.ts::program:PQueue:#onResumeInterval`  (from `index.ts`) -/
def f_index_ts__program_PQueue__onResumeInterval : Func :=
  { name := "index.ts::program:PQueue:#onResumeInterval"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.setField (.name "this") "#timeoutId" (.name "undefined"))
              (.seq
                (.expr (.mcall (.name "this") "#onInterval" []))
                (.expr (.mcall (.name "this") "#initializeIntervalIfNeeded" []))))) }

/-- `index.ts::program:PQueue:#isIntervalPausedAt`  (from `index.ts`) -/
def f_index_ts__program_PQueue__isIntervalPausedAt : Func :=
  { name := "index.ts::program:PQueue:#isIntervalPausedAt"
  , params := ["this", "now"]
  , body := (.seq
            .skip
            (.seq
              (.ifte
                (.field (.name "this") "#strict")
                (.seq
                  .skip
                  (.seq
                    (.expr (.mcall (.name "this") "#cleanupStrictTicks" [(.name "now")]))
                    (.seq
                      (.assign "activeTicksCount" (.mcall (.name "this") "#getActiveTicksCount" []))
                      (.seq
                        (.ifte
                          (.binop
                            ">="
                            (.name "activeTicksCount")
                            (.field (.name "this") "#intervalCap"))
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                (.assign "oldestTick" (.hole "op:notNullAssert"))
                                (.seq
                                  (.assign
                                    "delay"
                                    (.binop
                                      "-"
                                      (.field (.name "this") "#interval")
                                      (.binop "-" (.name "now") (.name "oldestTick"))))
                                  (.seq
                                    (.expr
                                      (.mcall
                                        (.name "this")
                                        "#createIntervalTimeout"
                                        [(.name "delay")]))
                                    (.ret (.lit (.bool true))))))))
                          .skip)
                        (.ret (.lit (.bool false)))))))
                .skip)
              (.seq
                (.ifte
                  (.binop "==" (.field (.name "this") "#intervalId") (.name "undefined"))
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "delay"
                        (.binop "-" (.field (.name "this") "#intervalEnd") (.name "now")))
                      (.ifte
                        (.binop "<" (.name "delay") (.lit (.int 0)))
                        (.setField
                          (.name "this")
                          "#intervalCount"
                          (.cond
                            (.field (.name "this") "#carryoverIntervalCount")
                            (.field (.name "this") "#pending")
                            (.lit (.int 0))))
                        (.seq
                          (.expr (.mcall (.name "this") "#createIntervalTimeout" [(.name "delay")]))
                          (.ret (.lit (.bool true)))))))
                  .skip)
                (.ret (.lit (.bool false)))))) }

/-- `index.ts::program:PQueue:#createIntervalTimeout:<lambda>0`  (from `index.ts`) -/
def f_index_ts__program_PQueue__createIntervalTimeout__lambda_0 : Func :=
  { name := "index.ts::program:PQueue:#createIntervalTimeout:<lambda>0"
  , params := ["this"]
  , body := (.expr (.mcall (.name "this") "#onResumeInterval" [])) }

/-- `index.ts::program:PQueue:#createIntervalTimeout`  (from `index.ts`) -/
def f_index_ts__program_PQueue__createIntervalTimeout : Func :=
  { name := "index.ts::program:PQueue:#createIntervalTimeout"
  , params := ["this", "delay"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.ifte
                  (.binop "!=" (.field (.name "this") "#timeoutId") (.name "undefined"))
                  (.ret (.lit .unit))
                  .skip)
                (.setField
                  (.name "this")
                  "#timeoutId"
                  (.call
                    "setTimeout"
                    [ (.fnref "index.ts::program:PQueue:#createIntervalTimeout:<lambda>0")
                    , (.name "delay") ]))))) }

/-- `index.ts::program:PQueue:#clearIntervalTimer`  (from `index.ts`) -/
def f_index_ts__program_PQueue__clearIntervalTimer : Func :=
  { name := "index.ts::program:PQueue:#clearIntervalTimer"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.ifte
                (.field (.name "this") "#intervalId")
                (.seq
                  (.expr (.call "clearInterval" [(.field (.name "this") "#intervalId")]))
                  (.setField (.name "this") "#intervalId" (.name "undefined")))
                .skip))) }

/-- `index.ts::program:PQueue:#clearTimeoutTimer`  (from `index.ts`) -/
def f_index_ts__program_PQueue__clearTimeoutTimer : Func :=
  { name := "index.ts::program:PQueue:#clearTimeoutTimer"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.ifte
                (.field (.name "this") "#timeoutId")
                (.seq
                  (.expr (.call "clearTimeout" [(.field (.name "this") "#timeoutId")]))
                  (.setField (.name "this") "#timeoutId" (.name "undefined")))
                .skip))) }

/-- `index.ts::program:PQueue:#tryToStartAnother`  (from `index.ts`) -/
def f_index_ts__program_PQueue__tryToStartAnother : Func :=
  { name := "index.ts::program:PQueue:#tryToStartAnother"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.ifte
                    (.binop "==" (.field (.field (.name "this") "#queue") "size") (.lit (.int 0)))
                    (.seq
                      (.expr (.mcall (.name "this") "#clearIntervalTimer" []))
                      (.seq
                        (.expr (.mcall (.name "this") "emit" [(.lit (.str "empty"))]))
                        (.seq
                          (.ifte
                            (.binop "==" (.field (.name "this") "#pending") (.lit (.int 0)))
                            (.seq
                              (.expr (.mcall (.name "this") "#clearTimeoutTimer" []))
                              (.seq
                                (.ifte
                                  (.binop
                                    "&&"
                                    (.field (.name "this") "#strict")
                                    (.binop
                                      ">"
                                      (.field (.name "this") "#strictTicksStartIndex")
                                      (.lit (.int 0))))
                                  (.seq
                                    .skip
                                    (.seq
                                      (.assign "now" (.mcall (.name "Date") "now" []))
                                      (.expr
                                        (.mcall
                                        (.name "this")
                                        "#cleanupStrictTicks"
                                        [(.name "now")]))))
                                  .skip)
                                (.expr (.mcall (.name "this") "emit" [(.lit (.str "idle"))]))))
                            .skip)
                          (.ret (.lit (.bool false))))))
                    .skip)
                  (.seq
                    (.assign "taskStarted" (.lit (.bool false)))
                    (.seq
                      (.ifte
                        (.unop "!" (.field (.name "this") "#isPaused"))
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              (.assign "now" (.mcall (.name "Date") "now" []))
                              (.seq
                                (.assign
                                  "canInitializeInterval"
                                  (.unop
                                    "!"
                                    (.mcall (.name "this") "#isIntervalPausedAt" [(.name "now")])))
                                (.ifte
                                  (.binop
                                    "&&"
                                    (.field (.name "this") "#doesIntervalAllowAnother")
                                    (.field (.name "this") "#doesConcurrentAllowAnother"))
                                  (.seq
                                    .skip
                                    (.seq
                                      (.assign "job" (.hole "op:notNullAssert"))
                                      (.seq
                                        (.ifte
                                        (.unop "!" (.field (.name "this") "#isIntervalIgnored"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.name "this")
                                        "#consumeIntervalSlot"
                                        [(.name "now")]))
                                        (.expr
                                        (.mcall (.name "this") "#scheduleRateLimitUpdate" [])))
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.name "canInitializeInterval")
                                        (.expr
                                        (.mcall (.name "this") "#initializeIntervalIfNeeded" []))
                                        .skip)
                                        (.seq
                                        (.expr
                                        (.mcall (.name "this") "emit" [(.lit (.str "active"))]))
                                        (.seq
                                        (.expr (.call "job" []))
                                        (.assign "taskStarted" (.lit (.bool true)))))))))
                                  .skip)))))
                        .skip)
                      (.ret (.name "taskStarted")))))))) }

/-- `index.ts::program:PQueue:#initializeIntervalIfNeeded:<lambda>1`  (from `index.ts`) -/
def f_index_ts__program_PQueue__initializeIntervalIfNeeded__lambda_1 : Func :=
  { name := "index.ts::program:PQueue:#initializeIntervalIfNeeded:<lambda>1"
  , params := ["this"]
  , body := (.expr (.mcall (.name "this") "#onInterval" [])) }

/-- `index.ts::program:PQueue:#initializeIntervalIfNeeded`  (from `index.ts`) -/
def f_index_ts__program_PQueue__initializeIntervalIfNeeded : Func :=
  { name := "index.ts::program:PQueue:#initializeIntervalIfNeeded"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.ifte
                    (.binop
                      "||"
                      (.field (.name "this") "#isIntervalIgnored")
                      (.binop "!=" (.field (.name "this") "#intervalId") (.name "undefined")))
                    (.ret (.lit .unit))
                    .skip)
                  (.seq
                    (.ifte (.field (.name "this") "#strict") (.ret (.lit .unit)) .skip)
                    (.seq
                      (.setField
                        (.name "this")
                        "#intervalId"
                        (.call
                          "setInterval"
                          [ (.fnref
                              "index.ts::program:PQueue:#initializeIntervalIfNeeded:<lambda>1")
                          , (.field (.name "this") "#interval") ]))
                      (.setField
                        (.name "this")
                        "#intervalEnd"
                        (.binop
                          "+"
                          (.mcall (.name "Date") "now" [])
                          (.field (.name "this") "#interval"))))))))) }

/-- `index.ts::program:PQueue:#onInterval`  (from `index.ts`) -/
def f_index_ts__program_PQueue__onInterval : Func :=
  { name := "index.ts::program:PQueue:#onInterval"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.ifte
                  (.unop "!" (.field (.name "this") "#strict"))
                  (.seq
                    (.ifte
                      (.binop "!=" (.field (.name "this") "#intervalId") (.name "undefined"))
                      (.ifte
                        (.binop
                          "&&"
                          (.binop "==" (.field (.name "this") "#intervalCount") (.lit (.int 0)))
                          (.binop "==" (.field (.name "this") "#pending") (.lit (.int 0))))
                        (.expr (.mcall (.name "this") "#clearIntervalTimer" []))
                        (.setField
                          (.name "this")
                          "#intervalEnd"
                          (.binop
                            "+"
                            (.mcall (.name "Date") "now" [])
                            (.field (.name "this") "#interval"))))
                      .skip)
                    (.setField
                      (.name "this")
                      "#intervalCount"
                      (.cond
                        (.field (.name "this") "#carryoverIntervalCount")
                        (.field (.name "this") "#pending")
                        (.lit (.int 0)))))
                  .skip)
                (.seq
                  (.expr (.mcall (.name "this") "#processQueue" []))
                  (.expr (.mcall (.name "this") "#scheduleRateLimitUpdate" [])))))) }

/-- `index.ts::program:PQueue:#processQueue`  (from `index.ts`) -/
def f_index_ts__program_PQueue__processQueue : Func :=
  { name := "index.ts::program:PQueue:#processQueue"
  , params := ["this"]
  , body := (.loop (.mcall (.name "this") "#tryToStartAnother" []) .skip) }

/-- `index.ts::program:PQueue:concurrency`  (from `index.ts`) -/
def f_index_ts__program_PQueue_concurrency : Func :=
  { name := "index.ts::program:PQueue:concurrency"
  , params := ["this"]
  , body := (.ret (.field (.name "this") "#concurrency")) }

/-- `index.ts::program:PQueue:concurrency1`  (from `index.ts`) -/
def f_index_ts__program_PQueue_concurrency1 : Func :=
  { name := "index.ts::program:PQueue:concurrency1"
  , params := ["this", "newConcurrency"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.ifte
                  (.unop
                    "!"
                    (.binop
                      "&&"
                      (.binop "==" (.hole "op:instanceOf") (.lit (.str "number")))
                      (.binop ">=" (.name "newConcurrency") (.lit (.int 1)))))
                  (.hole "control:THROW")
                  .skip)
                (.seq
                  (.setField (.name "this") "#concurrency" (.name "newConcurrency"))
                  (.expr (.mcall (.name "this") "#processQueue" [])))))) }

/-- `index.ts::program:PQueue:setPriority`  (from `index.ts`) -/
def f_index_ts__program_PQueue_setPriority : Func :=
  { name := "index.ts::program:PQueue:setPriority"
  , params := ["this", "id", "priority"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.ifte
                    (.binop
                      "||"
                      (.binop "!=" (.hole "op:instanceOf") (.lit (.str "number")))
                      (.unop "!" (.call "isFinite" [(.name "priority")])))
                    (.hole "control:THROW")
                    .skip)
                  (.expr
                    (.mcall
                      (.hole "op:assignment")
                      "setPriority"
                      [(.name "id"), (.name "priority")])))))) }

/-- `index.ts::program:PQueue:add`  (from `index.ts`) -/
def f_index_ts__program_PQueue_add : Func :=
  { name := "index.ts::program:PQueue:add"
  , params := ["this", "function_", "options"]
  , body := .skip }

/-- `index.ts::program:PQueue:add1:<lambda>2:<lambda>3`  (from `index.ts`) -/
def f_index_ts__program_PQueue_add1__lambda_2__lambda_3 : Func :=
  { name := "index.ts::program:PQueue:add1:<lambda>2:<lambda>3"
  , params := ["this"]
  , body := (.seq .skip (.ret (.name "undefined"))) }

/-- `index.ts::program:PQueue:add1:<lambda>2`  (from `index.ts`) -/
def f_index_ts__program_PQueue_add1__lambda_2 : Func :=
  { name := "index.ts::program:PQueue:add1:<lambda>2"
  , params := ["this", "resolve", "reject"]
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
                                (.assign "taskSymbol" (.call "Symbol" [(.hole "op:formatString")]))
                                (.seq
                                  (.assign
                                    "cleanupQueueAbortHandler"
                                    (.fnref "index.ts::program:PQueue:add1:<lambda>2:<lambda>3"))
                                  (.seq
                                    (.assign
                                      "run"
                                      (.fnref "index.ts::program:PQueue:add1:<lambda>2:run"))
                                    (.seq
                                      (.expr
                                        (.mcall
                                        (.hole "op:assignment")
                                        "enqueue"
                                        [(.name "run"), (.name "options")]))
                                      (.seq
                                        (.assign
                                        "removeQueuedTask"
                                        (.fnref
                                        "index.ts::program:PQueue:add1:<lambda>2:removeQueuedTask"))
                                        (.seq
                                        (.ifte
                                        (.field (.name "options") "signal")
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
                                        (.assign "_tmp_34" (.name "options"))
                                        (.seq
                                        (.assign "signal" (.field (.name "_tmp_34") "signal"))
                                        (.expr (.name "_tmp_34"))))))
                                        (.seq
                                        (.assign
                                        "queueAbortHandler"
                                        (.fnref
                                        "index.ts::program:PQueue:add1:<lambda>2:queueAbortHandler"))
                                        (.seq
                                        (.assign
                                        "cleanupQueueAbortHandler"
                                        (.fnref
                                        "index.ts::program:PQueue:add1:<lambda>2:<lambda>10"))
                                        (.seq
                                        (.ifte
                                        (.field (.name "signal") "aborted")
                                        (.seq
                                        (.expr
                                        (.call
                                        "index.ts::program:PQueue:add1:<lambda>2:queueAbortHandler"
                                        []))
                                        (.ret (.lit .unit)))
                                        .skip)
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.name "signal")
                                        "addEventListener"
                                        [ (.lit (.str "abort"))
                                        , (.name "queueAbortHandler")
                                        , (.hole "expr:BLOCK-prelude") ]))
                                        (.expr
                                        (.mcall
                                        (.hole "op:assignment")
                                        "add"
                                        [(.name "cleanupQueueAbortHandler")])))))))))
                                        .skip)
                                        (.seq
                                        (.expr (.mcall (.name "this") "emit" [(.lit (.str "add"))]))
                                        (.expr (.mcall (.name "this") "#tryToStartAnother" []))))))))))))))))))) }

/-- `index.ts::program:PQueue:add1:<lambda>2:<lambda>4:<lambda>5:<lambda>6`  (from `index.ts`) -/
def f_index_ts__program_PQueue_add1__lambda_2__lambda_4__lambda_5__lambda_6 : Func :=
  { name := "index.ts::program:PQueue:add1:<lambda>2:<lambda>4:<lambda>5:<lambda>6"
  , params := ["this"]
  , body := (.seq .skip (.seq .skip (.expr (.call "reject" [(.field (.name "signal") "reason")])))) }

/-- `index.ts::program:PQueue:add1:<lambda>2:<lambda>4:<lambda>5`  (from `index.ts`) -/
def f_index_ts__program_PQueue_add1__lambda_2__lambda_4__lambda_5 : Func :=
  { name := "index.ts::program:PQueue:add1:<lambda>2:<lambda>4:<lambda>5"
  , params := ["this", "_resolve", "reject"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign
                  "eventListener"
                  (.fnref "index.ts::program:PQueue:add1:<lambda>2:<lambda>4:<lambda>5:<lambda>6"))
                (.expr
                  (.mcall
                    (.name "signal")
                    "addEventListener"
                    [(.lit (.str "abort")), (.name "eventListener"), (.hole "expr:BLOCK-prelude")]))))) }

/-- `index.ts::program:PQueue:add1:<lambda>2:run`  (from `index.ts`) -/
def f_index_ts__program_PQueue_add1__lambda_2_run : Func :=
  { name := "index.ts::program:PQueue:add1:<lambda>2:run"
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
                                        (.expr (.call "cleanupQueueAbortHandler" []))
                                        (.seq
                                        (.expr (.hole "op:postIncrement"))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.hole "op:assignment")
                                        "set"
                                        [(.name "taskSymbol"), (.hole "expr:BLOCK-prelude")]))
                                        (.tryFinally
                                        (.tryCatch
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        (.tryCatch
                                        (.expr
                                        (.mcall
                                        (.field (.name "options") "signal")
                                        "throwIfAborted"
                                        []))
                                        "__exc"
                                        (.seq
                                        (.expr (.name "error"))
                                        (.seq
                                        (.expr
                                        (.mcall (.name "this") "#rollbackIntervalConsumption" []))
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.hole "op:assignment")
                                        "delete"
                                        [(.name "taskSymbol")]))
                                        (.hole "control:THROW")))))
                                        (.seq
                                        (.assign
                                        "operation"
                                        (.call "function_" [(.hole "expr:BLOCK-prelude")]))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "options") "timeout")
                                        (.name "undefined"))
                                        (.assign
                                        "operation"
                                        (.call
                                        "pTimeout"
                                        [ (.call "resolve" [(.name "operation")])
                                        , (.hole "expr:BLOCK-prelude") ]))
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.field (.name "options") "signal")
                                        (.seq
                                        .skip
                                        (.seq
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "_tmp_26" (.name "options"))
                                        (.seq
                                        (.assign "signal" (.field (.name "_tmp_26") "signal"))
                                        (.expr (.name "_tmp_26"))))))
                                        (.assign
                                        "operation"
                                        (.call "race" [(.hole "expr:BLOCK-impure")]))))
                                        .skip)
                                        (.seq
                                        (.assign "result" (.hole "op:await"))
                                        (.seq
                                        (.expr (.call "resolve" [(.name "result")]))
                                        (.expr
                                        (.mcall
                                        (.name "this")
                                        "emit"
                                        [(.lit (.str "completed")), (.name "result")]))))))))))
                                        "__exc"
                                        (.seq
                                        (.expr (.name "error"))
                                        (.seq
                                        (.expr (.call "reject" [(.name "error")]))
                                        (.expr
                                        (.mcall
                                        (.name "this")
                                        "emit"
                                        [(.lit (.str "error")), (.name "error")])))))
                                        (.seq
                                        (.ifte
                                        (.name "eventListener")
                                        (.expr
                                        (.mcall
                                        (.field (.name "options") "signal")
                                        "removeEventListener"
                                        [(.lit (.str "abort")), (.name "eventListener")]))
                                        .skip)
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.hole "op:assignment")
                                        "delete"
                                        [(.name "taskSymbol")]))
                                        (.expr
                                        (.call
                                        "queueMicrotask"
                                        [ (.fnref
                                        "index.ts::program:PQueue:add1:<lambda>2:<lambda>4:<lambda>7") ])))))))))))))))))))))))))) }

/-- `index.ts::program:PQueue:add1:<lambda>2:<lambda>4:<lambda>7`  (from `index.ts`) -/
def f_index_ts__program_PQueue_add1__lambda_2__lambda_4__lambda_7 : Func :=
  { name := "index.ts::program:PQueue:add1:<lambda>2:<lambda>4:<lambda>7"
  , params := ["this"]
  , body := (.expr (.mcall (.name "this") "#next" [])) }

/-- `index.ts::program:PQueue:add1:<lambda>2:removeQueuedTask`  (from `index.ts`) -/
def f_index_ts__program_PQueue_add1__lambda_2_removeQueuedTask : Func :=
  { name := "index.ts::program:PQueue:add1:<lambda>2:removeQueuedTask"
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
                      (.ifte
                        (.hole "op:instanceOf")
                        (.seq
                          (.expr (.mcall (.hole "op:assignment") "remove" [(.name "run")]))
                          (.ret (.lit .unit)))
                        .skip)
                      (.expr (.mcall (.hole "op:assignment") "remove" [(.hole "op:notNullAssert")])))))))) }

/-- `index.ts::program:PQueue:add1:<lambda>2:queueAbortHandler`  (from `index.ts`) -/
def f_index_ts__program_PQueue_add1__lambda_2_queueAbortHandler : Func :=
  { name := "index.ts::program:PQueue:add1:<lambda>2:queueAbortHandler"
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
                    (.expr (.call "cleanupQueueAbortHandler" []))
                    (.seq
                      (.expr (.call "index.ts::program:PQueue:add1:<lambda>2:removeQueuedTask" []))
                      (.seq
                        (.expr (.call "reject" [(.field (.name "signal") "reason")]))
                        (.seq
                          (.expr (.mcall (.name "this") "#tryToStartAnother" []))
                          (.expr (.mcall (.name "this") "emit" [(.lit (.str "next"))])))))))))) }

/-- `index.ts::program:PQueue:add1:<lambda>2:<lambda>10`  (from `index.ts`) -/
def f_index_ts__program_PQueue_add1__lambda_2__lambda_10 : Func :=
  { name := "index.ts::program:PQueue:add1:<lambda>2:<lambda>10"
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
                    (.expr
                      (.mcall
                        (.name "signal")
                        "removeEventListener"
                        [(.lit (.str "abort")), (.name "queueAbortHandler")]))
                    (.expr
                      (.mcall (.hole "op:assignment") "delete" [(.name "cleanupQueueAbortHandler")]))))))) }

/-- `index.ts::program:PQueue:add1`  (from `index.ts`) -/
def f_index_ts__program_PQueue_add1 : Func :=
  { name := "index.ts::program:PQueue:add1"
  , params := ["this", "function_", "options: Partial<EnqueueOptionsType>"]
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
                              (.assign
                                "options"
                                (.cond
                                  (.binop "==" (.name "options") (.hole "op:void"))
                                  (.name "_tmp_16")
                                  (.name "options")))
                              (.seq
                                (.seq
                                  .skip
                                  (.seq
                                    (.setField
                                      (.name "_tmp_17")
                                      "timeout"
                                      (.field (.name "this") "timeout"))
                                    (.seq
                                      (.expr (.hole "op:spread"))
                                      (.seq
                                        (.setField
                                        (.name "_tmp_17")
                                        "id"
                                        (.binop
                                        "||"
                                        (.field (.name "options") "id")
                                        (.mcall (.hole "op:assignment") "toString" [])))
                                        (.assign "options" (.name "_tmp_17"))))))
                                (.seq
                                  (.ifte
                                    (.binop
                                      "&&"
                                      (.binop
                                        "!="
                                        (.field (.name "options") "timeout")
                                        (.name "undefined"))
                                      (.unop
                                        "!"
                                        (.binop
                                        "&&"
                                        (.mcall
                                        (.name "options")
                                        "timeout"
                                        [(.field (.name "options") "timeout")])
                                        (.binop
                                        ">"
                                        (.field (.name "options") "timeout")
                                        (.lit (.int 0))))))
                                    (.hole "control:THROW")
                                    .skip)
                                  (.seq
                                    .skip
                                    (.seq
                                      (.assign "_tmp_20" (.hole "op:alloc"))
                                      (.seq
                                        (.expr
                                        (.call
                                        "<operator>.new"
                                        [(.fnref "index.ts::program:PQueue:add1:<lambda>2")]))
                                        (.ret (.name "_tmp_20"))))))))))))))))) }

/-- `index.ts::program:PQueue:addAll`  (from `index.ts`) -/
def f_index_ts__program_PQueue_addAll : Func :=
  { name := "index.ts::program:PQueue:addAll"
  , params := ["this", "functions", "options"]
  , body := .skip }

/-- `index.ts::program:PQueue:addAll1:<lambda>11`  (from `index.ts`) -/
def f_index_ts__program_PQueue_addAll1__lambda_11 : Func :=
  { name := "index.ts::program:PQueue:addAll1:<lambda>11"
  , params := ["this", "function_"]
  , body := (.seq .skip (.ret (.mcall (.name "this") "add" [(.name "function_"), (.name "options")]))) }

/-- `index.ts::program:PQueue:addAll1`  (from `index.ts`) -/
def f_index_ts__program_PQueue_addAll1 : Func :=
  { name := "index.ts::program:PQueue:addAll1"
  , params := ["this", "functions", "options"]
  , body := (.ret
            (.call
              "all"
              [ (.mcall
                  (.name "functions")
                  "map"
                  [(.fnref "index.ts::program:PQueue:addAll1:<lambda>11")]) ])) }

/-- `index.ts::program:PQueue:start`  (from `index.ts`) -/
def f_index_ts__program_PQueue_start : Func :=
  { name := "index.ts::program:PQueue:start"
  , params := ["this"]
  , body := (.seq
            (.ifte (.unop "!" (.field (.name "this") "#isPaused")) (.ret (.name "this")) .skip)
            (.seq
              (.setField (.name "this") "#isPaused" (.lit (.bool false)))
              (.seq (.expr (.mcall (.name "this") "#processQueue" [])) (.ret (.name "this"))))) }

/-- `index.ts::program:PQueue:pause`  (from `index.ts`) -/
def f_index_ts__program_PQueue_pause : Func :=
  { name := "index.ts::program:PQueue:pause"
  , params := ["this"]
  , body := (.setField (.name "this") "#isPaused" (.lit (.bool true))) }

/-- `index.ts::program:PQueue:clear`  (from `index.ts`) -/
def f_index_ts__program_PQueue_clear : Func :=
  { name := "index.ts::program:PQueue:clear"
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
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            (.assign "_iterator_0" (.hole "op:iterator"))
                            (.seq
                              (.expr (.name "_result_0"))
                              (.seq
                                (.expr (.name "cleanupQueueAbortHandler"))
                                (.loop
                                  (.unop "!" (.field (.hole "op:assignment") "done"))
                                  (.seq
                                    (.assign
                                      "cleanupQueueAbortHandler"
                                      (.field (.name "_result_0") "value"))
                                    (.expr (.call "cleanupQueueAbortHandler" []))))))))))
                    (.seq
                      (.seq
                        .skip
                        (.seq
                          (.assign "_tmp_38" (.hole "op:alloc"))
                          (.seq
                            (.expr (.mcall (.name "this") "#queueClass" []))
                            (.setField (.name "this") "#queue" (.name "_tmp_38")))))
                      (.seq
                        (.expr (.mcall (.name "this") "#clearIntervalTimer" []))
                        (.seq
                          (.expr (.mcall (.name "this") "#updateRateLimitState" []))
                          (.seq
                            (.expr (.mcall (.name "this") "emit" [(.lit (.str "empty"))]))
                            (.seq
                              (.ifte
                                (.binop "==" (.field (.name "this") "#pending") (.lit (.int 0)))
                                (.seq
                                  (.expr (.mcall (.name "this") "#clearTimeoutTimer" []))
                                  (.expr (.mcall (.name "this") "emit" [(.lit (.str "idle"))])))
                                .skip)
                              (.expr (.mcall (.name "this") "emit" [(.lit (.str "next"))])))))))))))) }

/-- `index.ts::program:PQueue:onEmpty`  (from `index.ts`) -/
def f_index_ts__program_PQueue_onEmpty : Func :=
  { name := "index.ts::program:PQueue:onEmpty"
  , params := ["this"]
  , body := (.seq
            (.ifte
              (.binop "==" (.field (.field (.name "this") "#queue") "size") (.lit (.int 0)))
              (.ret (.lit .unit))
              .skip)
            (.expr (.hole "op:await"))) }

/-- `index.ts::program:PQueue:onSizeLessThan:<lambda>12`  (from `index.ts`) -/
def f_index_ts__program_PQueue_onSizeLessThan__lambda_12 : Func :=
  { name := "index.ts::program:PQueue:onSizeLessThan:<lambda>12"
  , params := ["this"]
  , body := (.seq
            .skip
            (.ret (.binop "<" (.field (.field (.name "this") "#queue") "size") (.name "limit")))) }

/-- `index.ts::program:PQueue:onSizeLessThan`  (from `index.ts`) -/
def f_index_ts__program_PQueue_onSizeLessThan : Func :=
  { name := "index.ts::program:PQueue:onSizeLessThan"
  , params := ["this", "limit"]
  , body := (.seq
            .skip
            (.seq
              (.ifte
                (.binop "<" (.field (.field (.name "this") "#queue") "size") (.name "limit"))
                (.ret (.lit .unit))
                .skip)
              (.expr (.hole "op:await")))) }

/-- `index.ts::program:PQueue:onIdle`  (from `index.ts`) -/
def f_index_ts__program_PQueue_onIdle : Func :=
  { name := "index.ts::program:PQueue:onIdle"
  , params := ["this"]
  , body := (.seq
            (.ifte
              (.binop
                "&&"
                (.binop "==" (.field (.name "this") "#pending") (.lit (.int 0)))
                (.binop "==" (.field (.field (.name "this") "#queue") "size") (.lit (.int 0))))
              (.ret (.lit .unit))
              .skip)
            (.expr (.hole "op:await"))) }

/-- `index.ts::program:PQueue:onPendingZero`  (from `index.ts`) -/
def f_index_ts__program_PQueue_onPendingZero : Func :=
  { name := "index.ts::program:PQueue:onPendingZero"
  , params := ["this"]
  , body := (.seq
            (.ifte
              (.binop "==" (.field (.name "this") "#pending") (.lit (.int 0)))
              (.ret (.lit .unit))
              .skip)
            (.expr (.hole "op:await"))) }

/-- `index.ts::program:PQueue:onRateLimit`  (from `index.ts`) -/
def f_index_ts__program_PQueue_onRateLimit : Func :=
  { name := "index.ts::program:PQueue:onRateLimit"
  , params := ["this"]
  , body := (.seq
            (.ifte (.field (.name "this") "isRateLimited") (.ret (.lit .unit)) .skip)
            (.expr (.hole "op:await"))) }

/-- `index.ts::program:PQueue:onRateLimitCleared`  (from `index.ts`) -/
def f_index_ts__program_PQueue_onRateLimitCleared : Func :=
  { name := "index.ts::program:PQueue:onRateLimitCleared"
  , params := ["this"]
  , body := (.seq
            (.ifte (.unop "!" (.field (.name "this") "isRateLimited")) (.ret (.lit .unit)) .skip)
            (.expr (.hole "op:await"))) }

/-- `index.ts::program:PQueue:onError:<lambda>13:handleError`  (from `index.ts`) -/
def f_index_ts__program_PQueue_onError__lambda_13_handleError : Func :=
  { name := "index.ts::program:PQueue:onError:<lambda>13:handleError"
  , params := ["this", "error"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.expr (.mcall (.name "this") "off" [(.lit (.str "error")), (.name "handleError")]))
                (.expr (.call "reject" [(.name "error")]))))) }

/-- `index.ts::program:PQueue:onError:<lambda>13`  (from `index.ts`) -/
def f_index_ts__program_PQueue_onError__lambda_13 : Func :=
  { name := "index.ts::program:PQueue:onError:<lambda>13"
  , params := ["this", "_resolve", "reject"]
  , body := (.seq
            .skip
            (.seq
              (.assign
                "handleError"
                (.fnref "index.ts::program:PQueue:onError:<lambda>13:handleError"))
              (.expr (.mcall (.name "this") "on" [(.lit (.str "error")), (.name "handleError")])))) }

/-- `index.ts::program:PQueue:onError`  (from `index.ts`) -/
def f_index_ts__program_PQueue_onError : Func :=
  { name := "index.ts::program:PQueue:onError"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.assign "_tmp_40" (.hole "op:alloc"))
                  (.seq
                    (.expr
                      (.call
                        "<operator>.new"
                        [(.fnref "index.ts::program:PQueue:onError:<lambda>13")]))
                    (.ret (.name "_tmp_40"))))))) }

/-- `index.ts::program:PQueue:#onEvent:<lambda>15:listener`  (from `index.ts`) -/
def f_index_ts__program_PQueue__onEvent__lambda_15_listener : Func :=
  { name := "index.ts::program:PQueue:#onEvent:<lambda>15:listener"
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
                          (.ifte
                            (.binop "&&" (.name "filter") (.unop "!" (.call "filter" [])))
                            (.ret (.lit .unit))
                            .skip)
                          (.seq
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "_iterator_1" (.hole "op:iterator"))
                                    (.seq
                                      (.expr (.name "_result_1"))
                                      (.seq
                                        (.expr (.name "event"))
                                        (.loop
                                        (.unop "!" (.field (.hole "op:assignment") "done"))
                                        (.seq
                                        (.assign "event" (.field (.name "_result_1") "value"))
                                        (.expr
                                        (.mcall
                                        (.name "this")
                                        "off"
                                        [(.name "event"), (.name "listener")]))))))))))
                            (.expr (.call "resolve" []))))))))))) }

/-- `index.ts::program:PQueue:#onEvent:<lambda>15`  (from `index.ts`) -/
def f_index_ts__program_PQueue__onEvent__lambda_15 : Func :=
  { name := "index.ts::program:PQueue:#onEvent:<lambda>15"
  , params := ["this", "resolve"]
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
                        (.assign
                          "listener"
                          (.fnref "index.ts::program:PQueue:#onEvent:<lambda>15:listener"))
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                (.assign "_iterator_2" (.hole "op:iterator"))
                                (.seq
                                  (.expr (.name "_result_2"))
                                  (.seq
                                    (.expr (.name "event"))
                                    (.loop
                                      (.unop "!" (.field (.hole "op:assignment") "done"))
                                      (.seq
                                        (.assign "event" (.field (.name "_result_2") "value"))
                                        (.expr
                                        (.mcall
                                        (.name "this")
                                        "on"
                                        [(.name "event"), (.name "listener")]))))))))))))))))) }

/-- `index.ts::program:PQueue:#onEvent`  (from `index.ts`) -/
def f_index_ts__program_PQueue__onEvent : Func :=
  { name := "index.ts::program:PQueue:#onEvent"
  , params := ["this", "events", "filter"]
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
                      (.assign
                        "eventList"
                        (.cond
                          (.mcall (.name "Array") "isArray" [(.name "events")])
                          (.name "events")
                          (.hole "expr:BLOCK-impure")))
                      (.seq
                        .skip
                        (.seq
                          (.assign "_tmp_42" (.hole "op:alloc"))
                          (.seq
                            (.expr
                              (.call
                                "<operator>.new"
                                [(.fnref "index.ts::program:PQueue:#onEvent:<lambda>15")]))
                            (.ret (.name "_tmp_42"))))))))))) }

/-- `index.ts::program:PQueue:size`  (from `index.ts`) -/
def f_index_ts__program_PQueue_size : Func :=
  { name := "index.ts::program:PQueue:size"
  , params := ["this"]
  , body := (.ret (.field (.field (.name "this") "#queue") "size")) }

/-- `index.ts::program:PQueue:sizeBy`  (from `index.ts`) -/
def f_index_ts__program_PQueue_sizeBy : Func :=
  { name := "index.ts::program:PQueue:sizeBy"
  , params := ["this", "options"]
  , body := (.seq
            .skip
            (.ret (.field (.mcall (.hole "op:assignment") "filter" [(.name "options")]) "length"))) }

/-- `index.ts::program:PQueue:pending`  (from `index.ts`) -/
def f_index_ts__program_PQueue_pending : Func :=
  { name := "index.ts::program:PQueue:pending"
  , params := ["this"]
  , body := (.ret (.field (.name "this") "#pending")) }

/-- `index.ts::program:PQueue:isPaused`  (from `index.ts`) -/
def f_index_ts__program_PQueue_isPaused : Func :=
  { name := "index.ts::program:PQueue:isPaused"
  , params := ["this"]
  , body := (.ret (.field (.name "this") "#isPaused")) }

/-- `index.ts::program:PQueue:#setupRateLimitTracking:<lambda>17`  (from `index.ts`) -/
def f_index_ts__program_PQueue__setupRateLimitTracking__lambda_17 : Func :=
  { name := "index.ts::program:PQueue:#setupRateLimitTracking:<lambda>17"
  , params := ["this"]
  , body := (.ifte
            (.binop ">" (.field (.field (.name "this") "#queue") "size") (.lit (.int 0)))
            (.expr (.mcall (.name "this") "#scheduleRateLimitUpdate" []))
            .skip) }

/-- `index.ts::program:PQueue:#setupRateLimitTracking`  (from `index.ts`) -/
def f_index_ts__program_PQueue__setupRateLimitTracking : Func :=
  { name := "index.ts::program:PQueue:#setupRateLimitTracking"
  , params := ["this"]
  , body := (.seq
            (.ifte (.field (.name "this") "#isIntervalIgnored") (.ret (.lit .unit)) .skip)
            (.seq
              (.expr
                (.mcall
                  (.name "this")
                  "on"
                  [ (.lit (.str "add"))
                  , (.fnref "index.ts::program:PQueue:#setupRateLimitTracking:<lambda>17") ]))
              (.expr
                (.mcall
                  (.name "this")
                  "on"
                  [ (.lit (.str "next"))
                  , (.fnref "index.ts::program:PQueue:#setupRateLimitTracking:<lambda>18") ])))) }

/-- `index.ts::program:PQueue:#setupRateLimitTracking:<lambda>18`  (from `index.ts`) -/
def f_index_ts__program_PQueue__setupRateLimitTracking__lambda_18 : Func :=
  { name := "index.ts::program:PQueue:#setupRateLimitTracking:<lambda>18"
  , params := ["this"]
  , body := (.expr (.mcall (.name "this") "#scheduleRateLimitUpdate" [])) }

/-- `index.ts::program:PQueue:#scheduleRateLimitUpdate:<lambda>19`  (from `index.ts`) -/
def f_index_ts__program_PQueue__scheduleRateLimitUpdate__lambda_19 : Func :=
  { name := "index.ts::program:PQueue:#scheduleRateLimitUpdate:<lambda>19"
  , params := ["this"]
  , body := (.seq
            (.setField (.name "this") "#rateLimitFlushScheduled" (.lit (.bool false)))
            (.expr (.mcall (.name "this") "#updateRateLimitState" []))) }

/-- `index.ts::program:PQueue:#scheduleRateLimitUpdate`  (from `index.ts`) -/
def f_index_ts__program_PQueue__scheduleRateLimitUpdate : Func :=
  { name := "index.ts::program:PQueue:#scheduleRateLimitUpdate"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.ifte
                (.binop
                  "||"
                  (.field (.name "this") "#isIntervalIgnored")
                  (.field (.name "this") "#rateLimitFlushScheduled"))
                (.ret (.lit .unit))
                .skip)
              (.seq
                (.setField (.name "this") "#rateLimitFlushScheduled" (.lit (.bool true)))
                (.expr
                  (.call
                    "queueMicrotask"
                    [(.fnref "index.ts::program:PQueue:#scheduleRateLimitUpdate:<lambda>19")]))))) }

/-- `index.ts::program:PQueue:#rollbackIntervalConsumption`  (from `index.ts`) -/
def f_index_ts__program_PQueue__rollbackIntervalConsumption : Func :=
  { name := "index.ts::program:PQueue:#rollbackIntervalConsumption"
  , params := ["this"]
  , body := (.seq
            (.ifte (.field (.name "this") "#isIntervalIgnored") (.ret (.lit .unit)) .skip)
            (.seq
              (.expr (.mcall (.name "this") "#rollbackIntervalSlot" []))
              (.expr (.mcall (.name "this") "#scheduleRateLimitUpdate" [])))) }

/-- `index.ts::program:PQueue:#updateRateLimitState`  (from `index.ts`) -/
def f_index_ts__program_PQueue__updateRateLimitState : Func :=
  { name := "index.ts::program:PQueue:#updateRateLimitState"
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
                    (.assign "previous" (.field (.name "this") "#rateLimitedInInterval"))
                    (.seq
                      (.ifte
                        (.binop
                          "||"
                          (.field (.name "this") "#isIntervalIgnored")
                          (.binop
                            "=="
                            (.field (.field (.name "this") "#queue") "size")
                            (.lit (.int 0))))
                        (.seq
                          (.ifte
                            (.name "previous")
                            (.seq
                              (.setField
                                (.name "this")
                                "#rateLimitedInInterval"
                                (.lit (.bool false)))
                              (.expr
                                (.mcall (.name "this") "emit" [(.lit (.str "rateLimitCleared"))])))
                            .skip)
                          (.ret (.lit .unit)))
                        .skip)
                      (.seq
                        (.ifte
                          (.field (.name "this") "#strict")
                          (.seq
                            .skip
                            (.seq
                              (.assign "now" (.mcall (.name "Date") "now" []))
                              (.seq
                                (.expr
                                  (.mcall (.name "this") "#cleanupStrictTicks" [(.name "now")]))
                                (.assign "count" (.mcall (.name "this") "#getActiveTicksCount" [])))))
                          (.assign "count" (.field (.name "this") "#intervalCount")))
                        (.seq
                          (.assign
                            "shouldBeRateLimited"
                            (.binop ">=" (.name "count") (.field (.name "this") "#intervalCap")))
                          (.ifte
                            (.binop "!=" (.name "shouldBeRateLimited") (.name "previous"))
                            (.seq
                              (.setField
                                (.name "this")
                                "#rateLimitedInInterval"
                                (.name "shouldBeRateLimited"))
                              (.expr
                                (.mcall
                                  (.name "this")
                                  "emit"
                                  [ (.cond
                                      (.name "shouldBeRateLimited")
                                      (.lit (.str "rateLimit"))
                                      (.lit (.str "rateLimitCleared"))) ])))
                            .skip))))))))) }

/-- `index.ts::program:PQueue:isRateLimited`  (from `index.ts`) -/
def f_index_ts__program_PQueue_isRateLimited : Func :=
  { name := "index.ts::program:PQueue:isRateLimited"
  , params := ["this"]
  , body := (.ret (.field (.name "this") "#rateLimitedInInterval")) }

/-- `index.ts::program:PQueue:isSaturated`  (from `index.ts`) -/
def f_index_ts__program_PQueue_isSaturated : Func :=
  { name := "index.ts::program:PQueue:isSaturated"
  , params := ["this"]
  , body := (.ret
            (.binop
              "||"
              (.binop
                "&&"
                (.binop
                  "=="
                  (.field (.name "this") "#pending")
                  (.field (.name "this") "#concurrency"))
                (.binop ">" (.field (.field (.name "this") "#queue") "size") (.lit (.int 0))))
              (.binop
                "&&"
                (.field (.name "this") "isRateLimited")
                (.binop ">" (.field (.field (.name "this") "#queue") "size") (.lit (.int 0)))))) }

/-- `index.ts::program:PQueue:runningTasks:<lambda>20`  (from `index.ts`) -/
def f_index_ts__program_PQueue_runningTasks__lambda_20 : Func :=
  { name := "index.ts::program:PQueue:runningTasks:<lambda>20"
  , params := ["this", "task"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    (.expr (.hole "op:spread"))
                    (.seq
                      (.setField
                        (.name "_tmp_47")
                        "timeoutRemaining"
                        (.cond
                          (.field (.name "task") "timeout")
                          (.mcall
                            (.name "Math")
                            "max"
                            [ (.lit (.int 0))
                            , (.binop
                                "-"
                                (.binop
                                  "+"
                                  (.field (.name "task") "startTime")
                                  (.field (.name "task") "timeout"))
                                (.mcall (.name "Date") "now" [])) ])
                          (.name "undefined")))
                      (.ret (.name "_tmp_47")))))))) }

/-- `index.ts::program:PQueue:runningTasks`  (from `index.ts`) -/
def f_index_ts__program_PQueue_runningTasks : Func :=
  { name := "index.ts::program:PQueue:runningTasks"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.ret
                  (.mcall
                    (.hole "op:assignment")
                    "map"
                    [(.fnref "index.ts::program:PQueue:runningTasks:<lambda>20")]))))) }

/-- `lower-bound.ts::program:lowerBound`  (from `lower-bound.ts`) -/
def f_lower_bound_ts__program_lowerBound : Func :=
  { name := "lower-bound.ts::program:lowerBound"
  , params := ["this", "array", "value", "comparator"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.assign "first" (.lit (.int 0)))
                  (.seq
                    (.assign "count" (.field (.name "array") "length"))
                    (.seq
                      (.loop
                        (.binop ">" (.name "count") (.lit (.int 0)))
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              (.assign
                                "step"
                                (.mcall
                                  (.name "Math")
                                  "trunc"
                                  [(.binop "/" (.name "count") (.lit (.int 2)))]))
                              (.seq
                                (.assign "it" (.binop "+" (.name "first") (.name "step")))
                                (.ifte
                                  (.binop
                                    "<="
                                    (.call
                                      "comparator"
                                      [(.hole "op:notNullAssert"), (.name "value")])
                                    (.lit (.int 0)))
                                  (.seq
                                    (.assign "first" (.hole "op:preIncrement"))
                                    (.assign
                                      "count"
                                      (.binop
                                        "-"
                                        (.name "count")
                                        (.binop "+" (.name "step") (.lit (.int 1))))))
                                  (.assign "count" (.name "step"))))))))
                      (.ret (.name "first")))))))) }

/-- `lower-bound.ts::program`  (from `lower-bound.ts`) -/
def f_lower_bound_ts__program : Func :=
  { name := "lower-bound.ts::program"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.assign "lowerBound" (.fnref "lower-bound.ts::program:lowerBound"))
              (.setIndex (.name "exports") (.lit (.str "default")) (.name "lowerBound")))) }

/-- `options.ts::program`  (from `options.ts`) -/
def f_options_ts__program : Func :=
  { name := "options.ts::program"
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
                      (.seq
                        (.assign
                          "Queue"
                          (.field (.call "require" [(.lit (.str "./queue.js"))]) "Queue"))
                        (.assign
                          "RunFunction"
                          (.field (.call "require" [(.lit (.str "./queue.js"))]) "RunFunction")))
                      (.seq
                        (.seq
                          (.hole "stmt:TYPE_DECL")
                          (.setField (.name "exports") "Options" (.name "Options")))
                        (.seq
                          (.seq
                            (.hole "stmt:TYPE_DECL")
                            (.setField
                              (.name "exports")
                              "QueueAddOptions"
                              (.name "QueueAddOptions")))
                          (.seq
                            (.seq
                              (.hole "stmt:TYPE_DECL")
                              (.setField (.name "exports") "TaskOptions" (.name "TaskOptions")))
                            (.hole "stmt:TYPE_DECL")))))))))) }

/-- `priority-queue.ts::program`  (from `priority-queue.ts`) -/
def f_priority_queue_ts__program : Func :=
  { name := "priority-queue.ts::program"
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
                          (.seq
                            (.assign
                              "Queue"
                              (.field (.call "require" [(.lit (.str "./queue.js"))]) "Queue"))
                            (.assign
                              "RunFunction"
                              (.field (.call "require" [(.lit (.str "./queue.js"))]) "RunFunction")))
                          (.seq
                            (.assign
                              "lowerBound"
                              (.call "require" [(.lit (.str "./lower-bound.js"))]))
                            (.seq
                              (.assign
                                "QueueAddOptions"
                                (.field
                                  (.call "require" [(.lit (.str "./options.js"))])
                                  "QueueAddOptions"))
                              (.seq
                                (.assign "compactionThreshold" (.lit (.int 100)))
                                (.seq
                                  (.seq
                                    (.hole "stmt:TYPE_DECL")
                                    (.setField
                                      (.name "exports")
                                      "PriorityQueueOptions"
                                      (.name "PriorityQueueOptions")))
                                  (.seq
                                    (.seq
                                      .skip
                                      (.assign
                                        "PriorityQueue"
                                        (.fnref "priority-queue.ts::program:PriorityQueue:<init>")))
                                    (.setIndex
                                      (.name "exports")
                                      (.lit (.str "default"))
                                      (.name "PriorityQueue"))))))))))))))) }

/-- `priority-queue.ts::program:PriorityQueue:<init>`  (from `priority-queue.ts`) -/
def f_priority_queue_ts__program_PriorityQueue__init_ : Func :=
  { name := "priority-queue.ts::program:PriorityQueue:<init>"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "queue" (.call "__ecma.Array.factory" []))
                (.assign "head" (.lit (.int 0)))))) }

/-- `priority-queue.ts::program:PriorityQueue:enqueue:<lambda>0`  (from `priority-queue.ts`) -/
def f_priority_queue_ts__program_PriorityQueue_enqueue__lambda_0 : Func :=
  { name := "priority-queue.ts::program:PriorityQueue:enqueue:<lambda>0"
  , params := ["this", "a", "b"]
  , body := (.ret (.binop "-" (.hole "op:notNullAssert") (.hole "op:notNullAssert"))) }

/-- `priority-queue.ts::program:PriorityQueue:enqueue`  (from `priority-queue.ts`) -/
def f_priority_queue_ts__program_PriorityQueue_enqueue : Func :=
  { name := "priority-queue.ts::program:PriorityQueue:enqueue"
  , params := ["this", "run", "options"]
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
                                      (.assign
                                        "_tmp_1"
                                        (.binop "||" (.name "options") (.name "_tmp_0")))
                                      (.seq
                                        (.assign
                                        "priority"
                                        (.cond
                                        (.binop
                                        "=="
                                        (.field (.name "_tmp_1") "priority")
                                        (.hole "op:void"))
                                        (.lit (.int 0))
                                        (.field (.name "_tmp_1") "priority")))
                                        (.seq
                                        (.assign "id" (.field (.name "_tmp_1") "id"))
                                        (.expr (.name "_tmp_1")))))))
                                (.seq
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign "_tmp_2" (.name "this"))
                                        (.seq
                                        (.assign "size" (.field (.name "_tmp_2") "size"))
                                        (.expr (.name "_tmp_2"))))))
                                  (.seq
                                    (.seq
                                      .skip
                                      (.seq
                                        (.setField (.name "_tmp_3") "priority" (.name "priority"))
                                        (.seq
                                        (.setField (.name "_tmp_3") "id" (.name "id"))
                                        (.seq
                                        (.setField (.name "_tmp_3") "run" (.name "run"))
                                        (.assign "element" (.name "_tmp_3"))))))
                                    (.seq
                                      (.ifte
                                        (.binop "==" (.name "size") (.lit (.int 0)))
                                        (.seq
                                        (.setField
                                        (.field (.name "this") "#queue")
                                        "length"
                                        (.lit (.int 0)))
                                        (.seq
                                        (.setField (.name "this") "#head" (.lit (.int 0)))
                                        (.seq
                                        (.expr
                                        (.mcall (.hole "op:assignment") "push" [(.name "element")]))
                                        (.ret (.lit .unit)))))
                                        .skip)
                                      (.seq
                                        (.ifte
                                        (.binop ">=" (.hole "op:notNullAssert") (.name "priority"))
                                        (.seq
                                        (.expr
                                        (.mcall (.hole "op:assignment") "push" [(.name "element")]))
                                        (.ret (.lit .unit)))
                                        .skip)
                                        (.seq
                                        (.expr (.mcall (.name "this") "#compact" []))
                                        (.seq
                                        (.assign
                                        "index"
                                        (.call
                                        "lowerBound"
                                        [ (.field (.name "this") "#queue")
                                        , (.name "element")
                                        , (.fnref
                                        "priority-queue.ts::program:PriorityQueue:enqueue:<lambda>0") ]))
                                        (.expr
                                        (.mcall
                                        (.hole "op:assignment")
                                        "splice"
                                        [(.name "index"), (.lit (.int 0)), (.name "element")]))))))))))))))))))) }

/-- `priority-queue.ts::program:PriorityQueue:setPriority:<lambda>1`  (from `priority-queue.ts`) -/
def f_priority_queue_ts__program_PriorityQueue_setPriority__lambda_1 : Func :=
  { name := "priority-queue.ts::program:PriorityQueue:setPriority:<lambda>1"
  , params := ["this", "element", "index"]
  , body := (.seq
            .skip
            (.ret
              (.binop
                "&&"
                (.binop ">=" (.name "index") (.field (.name "this") "#head"))
                (.binop "==" (.field (.name "element") "id") (.name "id"))))) }

/-- `priority-queue.ts::program:PriorityQueue:setPriority`  (from `priority-queue.ts`) -/
def f_priority_queue_ts__program_PriorityQueue_setPriority : Func :=
  { name := "priority-queue.ts::program:PriorityQueue:setPriority"
  , params := ["this", "id", "priority"]
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
                        (.assign
                          "index"
                          (.mcall
                            (.hole "op:assignment")
                            "findIndex"
                            [ (.fnref
                                "priority-queue.ts::program:PriorityQueue:setPriority:<lambda>1") ]))
                        (.seq
                          (.ifte
                            (.binop "==" (.name "index") (.unop "-" (.lit (.int 1))))
                            (.hole "control:THROW")
                            .skip)
                          (.seq
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  (.assign
                                    "_tmp_11"
                                    (.mcall
                                      (.hole "op:assignment")
                                      "splice"
                                      [(.name "index"), (.lit (.int 1))]))
                                  (.seq
                                    (.assign "item" (.index (.name "_tmp_11") (.lit (.int 0))))
                                    (.expr (.name "_tmp_11"))))))
                            (.expr
                              (.mcall
                                (.name "this")
                                "enqueue"
                                [ (.field (.hole "op:notNullAssert") "run")
                                , (.hole "expr:BLOCK-prelude") ]))))))))))) }

/-- `priority-queue.ts::program:PriorityQueue:remove`  (from `priority-queue.ts`) -/
def f_priority_queue_ts__program_PriorityQueue_remove : Func :=
  { name := "priority-queue.ts::program:PriorityQueue:remove"
  , params := ["this", "id"]
  , body := .skip }

/-- `priority-queue.ts::program:PriorityQueue:remove1`  (from `priority-queue.ts`) -/
def f_priority_queue_ts__program_PriorityQueue_remove1 : Func :=
  { name := "priority-queue.ts::program:PriorityQueue:remove1"
  , params := ["this", "run"]
  , body := .skip }

/-- `priority-queue.ts::program:PriorityQueue:remove2:<lambda>2`  (from `priority-queue.ts`) -/
def f_priority_queue_ts__program_PriorityQueue_remove2__lambda_2 : Func :=
  { name := "priority-queue.ts::program:PriorityQueue:remove2:<lambda>2"
  , params := ["this", "element", "index"]
  , body := (.seq
            .skip
            (.seq
              (.ifte
                (.binop "<" (.name "index") (.field (.name "this") "#head"))
                (.ret (.lit (.bool false)))
                .skip)
              (.seq
                (.ifte
                  (.binop "==" (.hole "op:instanceOf") (.lit (.str "string")))
                  (.ret (.binop "==" (.field (.name "element") "id") (.name "idOrRun")))
                  .skip)
                (.ret (.binop "==" (.field (.name "element") "run") (.name "idOrRun")))))) }

/-- `priority-queue.ts::program:PriorityQueue:remove2`  (from `priority-queue.ts`) -/
def f_priority_queue_ts__program_PriorityQueue_remove2 : Func :=
  { name := "priority-queue.ts::program:PriorityQueue:remove2"
  , params := ["this", "idOrRun"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.assign
                    "index"
                    (.mcall
                      (.hole "op:assignment")
                      "findIndex"
                      [(.fnref "priority-queue.ts::program:PriorityQueue:remove2:<lambda>2")]))
                  (.ifte
                    (.binop "!=" (.name "index") (.unop "-" (.lit (.int 1))))
                    (.expr
                      (.mcall (.hole "op:assignment") "splice" [(.name "index"), (.lit (.int 1))]))
                    .skip))))) }

/-- `priority-queue.ts::program:PriorityQueue:dequeue`  (from `priority-queue.ts`) -/
def f_priority_queue_ts__program_PriorityQueue_dequeue : Func :=
  { name := "priority-queue.ts::program:PriorityQueue:dequeue"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.ifte
                    (.binop
                      "=="
                      (.field (.name "this") "#head")
                      (.field (.field (.name "this") "#queue") "length"))
                    (.ret (.name "undefined"))
                    .skip)
                  (.seq
                    (.assign
                      "item"
                      (.index (.field (.name "this") "#queue") (.field (.name "this") "#head")))
                    (.seq
                      (.expr (.hole "op:postIncrement"))
                      (.seq
                        (.ifte
                          (.binop
                            "=="
                            (.field (.name "this") "#head")
                            (.field (.field (.name "this") "#queue") "length"))
                          (.seq
                            (.setField (.field (.name "this") "#queue") "length" (.lit (.int 0)))
                            (.setField (.name "this") "#head" (.lit (.int 0))))
                          (.ifte
                            (.binop
                              "&&"
                              (.binop
                                ">"
                                (.field (.name "this") "#head")
                                (.name "compactionThreshold"))
                              (.binop
                                ">"
                                (.field (.name "this") "#head")
                                (.binop
                                  "/"
                                  (.field (.field (.name "this") "#queue") "length")
                                  (.lit (.int 2)))))
                            (.expr (.mcall (.name "this") "#compact" []))
                            .skip))
                        (.ret (.field (.name "item") "run"))))))))) }

/-- `priority-queue.ts::program:PriorityQueue:filter`  (from `priority-queue.ts`) -/
def f_priority_queue_ts__program_PriorityQueue_filter : Func :=
  { name := "priority-queue.ts::program:PriorityQueue:filter"
  , params := ["this", "options"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "result" (.call "__ecma.Array.factory" []))
                (.seq (.hole "control:FOR") (.ret (.name "result")))))) }

/-- `priority-queue.ts::program:PriorityQueue:size`  (from `priority-queue.ts`) -/
def f_priority_queue_ts__program_PriorityQueue_size : Func :=
  { name := "priority-queue.ts::program:PriorityQueue:size"
  , params := ["this"]
  , body := (.ret
            (.binop
              "-"
              (.field (.field (.name "this") "#queue") "length")
              (.field (.name "this") "#head"))) }

/-- `priority-queue.ts::program:PriorityQueue:#compact`  (from `priority-queue.ts`) -/
def f_priority_queue_ts__program_PriorityQueue__compact : Func :=
  { name := "priority-queue.ts::program:PriorityQueue:#compact"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              (.ifte
                (.binop "==" (.field (.name "this") "#head") (.lit (.int 0)))
                (.ret (.lit .unit))
                .skip)
              (.seq
                (.expr
                  (.mcall
                    (.hole "op:assignment")
                    "splice"
                    [(.lit (.int 0)), (.field (.name "this") "#head")]))
                (.setField (.name "this") "#head" (.lit (.int 0)))))) }

/-- `queue.ts::program`  (from `queue.ts`) -/
def f_queue_ts__program : Func :=
  { name := "queue.ts::program"
  , params := ["this"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.seq
                  (.hole "stmt:TYPE_DECL")
                  (.setField (.name "exports") "RunFunction" (.name "RunFunction")))
                (.seq
                  (.hole "stmt:TYPE_DECL")
                  (.setField (.name "exports") "Queue" (.name "Queue")))))) }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := []

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_index_ts__program,
  f_index_ts__program_PQueue__init_,
  f_index_ts__program_PQueue__cleanupStrictTicks,
  f_index_ts__program_PQueue__consumeIntervalSlot,
  f_index_ts__program_PQueue__rollbackIntervalSlot,
  f_index_ts__program_PQueue__getActiveTicksCount,
  f_index_ts__program_PQueue__doesIntervalAllowAnother,
  f_index_ts__program_PQueue__doesConcurrentAllowAnother,
  f_index_ts__program_PQueue__next,
  f_index_ts__program_PQueue__onResumeInterval,
  f_index_ts__program_PQueue__isIntervalPausedAt,
  f_index_ts__program_PQueue__createIntervalTimeout__lambda_0,
  f_index_ts__program_PQueue__createIntervalTimeout,
  f_index_ts__program_PQueue__clearIntervalTimer,
  f_index_ts__program_PQueue__clearTimeoutTimer,
  f_index_ts__program_PQueue__tryToStartAnother,
  f_index_ts__program_PQueue__initializeIntervalIfNeeded__lambda_1,
  f_index_ts__program_PQueue__initializeIntervalIfNeeded,
  f_index_ts__program_PQueue__onInterval,
  f_index_ts__program_PQueue__processQueue,
  f_index_ts__program_PQueue_concurrency,
  f_index_ts__program_PQueue_concurrency1,
  f_index_ts__program_PQueue_setPriority,
  f_index_ts__program_PQueue_add,
  f_index_ts__program_PQueue_add1__lambda_2__lambda_3,
  f_index_ts__program_PQueue_add1__lambda_2,
  f_index_ts__program_PQueue_add1__lambda_2__lambda_4__lambda_5__lambda_6,
  f_index_ts__program_PQueue_add1__lambda_2__lambda_4__lambda_5,
  f_index_ts__program_PQueue_add1__lambda_2_run,
  f_index_ts__program_PQueue_add1__lambda_2__lambda_4__lambda_7,
  f_index_ts__program_PQueue_add1__lambda_2_removeQueuedTask,
  f_index_ts__program_PQueue_add1__lambda_2_queueAbortHandler,
  f_index_ts__program_PQueue_add1__lambda_2__lambda_10,
  f_index_ts__program_PQueue_add1,
  f_index_ts__program_PQueue_addAll,
  f_index_ts__program_PQueue_addAll1__lambda_11,
  f_index_ts__program_PQueue_addAll1,
  f_index_ts__program_PQueue_start,
  f_index_ts__program_PQueue_pause,
  f_index_ts__program_PQueue_clear,
  f_index_ts__program_PQueue_onEmpty,
  f_index_ts__program_PQueue_onSizeLessThan__lambda_12,
  f_index_ts__program_PQueue_onSizeLessThan,
  f_index_ts__program_PQueue_onIdle,
  f_index_ts__program_PQueue_onPendingZero,
  f_index_ts__program_PQueue_onRateLimit,
  f_index_ts__program_PQueue_onRateLimitCleared,
  f_index_ts__program_PQueue_onError__lambda_13_handleError,
  f_index_ts__program_PQueue_onError__lambda_13,
  f_index_ts__program_PQueue_onError,
  f_index_ts__program_PQueue__onEvent__lambda_15_listener,
  f_index_ts__program_PQueue__onEvent__lambda_15,
  f_index_ts__program_PQueue__onEvent,
  f_index_ts__program_PQueue_size,
  f_index_ts__program_PQueue_sizeBy,
  f_index_ts__program_PQueue_pending,
  f_index_ts__program_PQueue_isPaused,
  f_index_ts__program_PQueue__setupRateLimitTracking__lambda_17,
  f_index_ts__program_PQueue__setupRateLimitTracking,
  f_index_ts__program_PQueue__setupRateLimitTracking__lambda_18,
  f_index_ts__program_PQueue__scheduleRateLimitUpdate__lambda_19,
  f_index_ts__program_PQueue__scheduleRateLimitUpdate,
  f_index_ts__program_PQueue__rollbackIntervalConsumption,
  f_index_ts__program_PQueue__updateRateLimitState,
  f_index_ts__program_PQueue_isRateLimited,
  f_index_ts__program_PQueue_isSaturated,
  f_index_ts__program_PQueue_runningTasks__lambda_20,
  f_index_ts__program_PQueue_runningTasks,
  f_lower_bound_ts__program_lowerBound,
  f_lower_bound_ts__program,
  f_options_ts__program,
  f_priority_queue_ts__program,
  f_priority_queue_ts__program_PriorityQueue__init_,
  f_priority_queue_ts__program_PriorityQueue_enqueue__lambda_0,
  f_priority_queue_ts__program_PriorityQueue_enqueue,
  f_priority_queue_ts__program_PriorityQueue_setPriority__lambda_1,
  f_priority_queue_ts__program_PriorityQueue_setPriority,
  f_priority_queue_ts__program_PriorityQueue_remove,
  f_priority_queue_ts__program_PriorityQueue_remove1,
  f_priority_queue_ts__program_PriorityQueue_remove2__lambda_2,
  f_priority_queue_ts__program_PriorityQueue_remove2,
  f_priority_queue_ts__program_PriorityQueue_dequeue,
  f_priority_queue_ts__program_PriorityQueue_filter,
  f_priority_queue_ts__program_PriorityQueue_size,
  f_priority_queue_ts__program_PriorityQueue__compact,
  f_queue_ts__program
] }

end Autoform.Generated