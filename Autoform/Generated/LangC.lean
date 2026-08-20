import Autoform.Lang.Core.Semantics

-- Lean's default `maxRecDepth` (512) is a guard against runaway elaboration, not
-- a statement about reasonable programs. A deep-embedded function body is one
-- term, so the elaborator's recursion depth tracks the *source's* nesting depth:
-- Linux `lib/` hit the limit at two declarations and the whole module failed to
-- type-check. Raising it costs nothing for shallow modules and is the difference
-- between compiling a real codebase and not.
set_option maxRecDepth 8000

/-!
# LangC — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated
open Autoform.Core

/-- `sdsHdrSize`  (from `sds.c`) -/
def f_sdsHdrSize : Func :=
  { name := "sdsHdrSize"
  , params := ["type"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq .skip (.seq .skip (.seq (.hole "control:SWITCH") (.ret (.lit (.int 0))))))))) }

/-- `sdsReqType`  (from `sds.c`) -/
def f_sdsReqType : Func :=
  { name := "sdsReqType"
  , params := ["string_size"]
  , body := (.seq
            (.ifte
              (.binop "<" (.name "string_size") (.hole "op:shiftLeft"))
              (.ret (.call "SDS_TYPE_5" [(.lit (.int 0))]))
              .skip)
            (.seq
              (.ifte
                (.binop "<" (.name "string_size") (.hole "op:shiftLeft"))
                (.ret (.call "SDS_TYPE_8" [(.lit (.int 1))]))
                .skip)
              (.seq
                (.ifte
                  (.binop "<" (.name "string_size") (.hole "op:shiftLeft"))
                  (.ret (.call "SDS_TYPE_16" [(.lit (.int 2))]))
                  .skip)
                (.seq
                  (.ifte
                    (.binop "<" (.name "string_size") (.hole "op:shiftLeft"))
                    (.ret (.call "SDS_TYPE_32" [(.lit (.int 3))]))
                    .skip)
                  (.ret (.call "SDS_TYPE_64" [(.lit (.int 4))])))))) }

/-- `sdsnewlen`  (from `sds.c`) -/
def f_sdsnewlen : Func :=
  { name := "sdsnewlen"
  , params := ["init", "initlen"]
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
                              (.assign "type" (.call "sdsReqType" [(.name "initlen")]))
                              (.seq
                                (.ifte
                                  (.binop
                                    "&&"
                                    (.binop
                                      "=="
                                      (.name "type")
                                      (.call "SDS_TYPE_5" [(.lit (.int 0))]))
                                    (.binop "==" (.name "initlen") (.lit (.int 0))))
                                  (.assign "type" (.call "SDS_TYPE_8" [(.lit (.int 1))]))
                                  .skip)
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "hdrlen" (.call "sdsHdrSize" [(.name "type")]))
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign
                                        "sh"
                                        (.call
                                        "s_malloc"
                                        [ (.call
                                        "malloc"
                                        [ (.binop
                                        "+"
                                        (.binop "+" (.name "hdrlen") (.name "initlen"))
                                        (.lit (.int 1))) ]) ]))
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.name "sh") (.name "NULL"))
                                        (.ret (.name "NULL"))
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.hole "cstr:address-equality")
                                        (.assign "init" (.name "NULL"))
                                        (.ifte
                                        (.unop "!" (.name "init"))
                                        (.expr
                                        (.call
                                        "memset"
                                        [ (.name "sh")
                                        , (.lit (.int 0))
                                        , (.binop
                                        "+"
                                        (.binop "+" (.name "hdrlen") (.name "initlen"))
                                        (.lit (.int 1))) ]))
                                        .skip))
                                        (.seq
                                        (.assign
                                        "s"
                                        (.binop "+" (.hole "op:cast") (.name "hdrlen")))
                                        (.seq
                                        (.assign
                                        "fp"
                                        (.binop "-" (.hole "op:cast") (.lit (.int 1))))
                                        (.seq
                                        (.hole "control:SWITCH")
                                        (.seq
                                        (.ifte
                                        (.binop "&&" (.name "initlen") (.name "init"))
                                        (.expr
                                        (.call
                                        "memcpy"
                                        [(.name "s"), (.name "init"), (.name "initlen")]))
                                        .skip)
                                        (.seq
                                        (.hole "assign:lhs:indirectIndexAccess")
                                        (.ret (.name "s")))))))))))))))))))))))) }

/-- `sdsempty`  (from `sds.c`) -/
def f_sdsempty : Func :=
  { name := "sdsempty"
  , params := [""]
  , body := (.ret (.call "sdsnewlen" [(.lit (.str "")), (.lit (.int 0))])) }

/-- `sdsnew`  (from `sds.c`) -/
def f_sdsnew : Func :=
  { name := "sdsnew"
  , params := ["init"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign
                  "initlen"
                  (.cond
                    (.hole "cstr:address-equality")
                    (.lit (.int 0))
                    (.call "strlen" [(.name "init")])))
                (.ret (.call "sdsnewlen" [(.name "init"), (.name "initlen")]))))) }

/-- `sdsdup`  (from `sds.c`) -/
def f_sdsdup : Func :=
  { name := "sdsdup"
  , params := ["s"]
  , body := (.ret (.call "sdsnewlen" [(.name "s"), (.call "sdslen" [(.name "s")])])) }

/-- `sdsfree`  (from `sds.c`) -/
def f_sdsfree : Func :=
  { name := "sdsfree"
  , params := ["s"]
  , body := (.seq
            .skip
            (.seq
              (.ifte (.binop "==" (.name "s") (.name "NULL")) (.ret (.lit .unit)) .skip)
              (.expr
                (.call
                  "s_free"
                  [ (.call
                      "free"
                      [ (.binop
                          "-"
                          (.hole "op:cast")
                          (.call "sdsHdrSize" [(.hole "op:indirectIndexAccess")])) ]) ])))) }

/-- `sdsupdatelen`  (from `sds.c`) -/
def f_sdsupdatelen : Func :=
  { name := "sdsupdatelen"
  , params := ["s"]
  , body := (.seq
            .skip
            (.seq
              (.assign "reallen" (.call "strlen" [(.name "s")]))
              (.expr (.call "sdssetlen" [(.name "s"), (.name "reallen")])))) }

/-- `sdsclear`  (from `sds.c`) -/
def f_sdsclear : Func :=
  { name := "sdsclear"
  , params := ["s"]
  , body := (.seq
            (.expr (.call "sdssetlen" [(.name "s"), (.lit (.int 0))]))
            (.hole "assign:lhs:indirectIndexAccess")) }

/-- `sdsMakeRoomFor`  (from `sds.c`) -/
def f_sdsMakeRoomFor : Func :=
  { name := "sdsMakeRoomFor"
  , params := ["s", "addlen"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    (.assign "avail" (.call "sdsavail" [(.name "s")]))
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                (.assign "oldtype" (.hole "op:and"))
                                (.seq
                                  .skip
                                  (.seq
                                    (.ifte
                                      (.binop ">=" (.name "avail") (.name "addlen"))
                                      (.ret (.name "s"))
                                      .skip)
                                    (.seq
                                      (.assign "len" (.call "sdslen" [(.name "s")]))
                                      (.seq
                                        (.assign
                                        "sh"
                                        (.binop
                                        "-"
                                        (.hole "op:cast")
                                        (.call "sdsHdrSize" [(.name "oldtype")])))
                                        (.seq
                                        (.assign "reqlen" (.hole "op:assignment"))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "<"
                                        (.name "newlen")
                                        (.call
                                        "SDS_MAX_PREALLOC"
                                        [(.binop "*" (.lit (.int 1024)) (.lit (.int 1024)))]))
                                        (.expr (.hole "op:assignmentMultiplication"))
                                        (.assign
                                        "newlen"
                                        (.binop
                                        "+"
                                        (.name "newlen")
                                        (.call
                                        "SDS_MAX_PREALLOC"
                                        [(.binop "*" (.lit (.int 1024)) (.lit (.int 1024)))]))))
                                        (.seq
                                        (.assign "type" (.call "sdsReqType" [(.name "newlen")]))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.name "type")
                                        (.call "SDS_TYPE_5" [(.lit (.int 0))]))
                                        (.assign "type" (.call "SDS_TYPE_8" [(.lit (.int 1))]))
                                        .skip)
                                        (.seq
                                        (.assign "hdrlen" (.call "sdsHdrSize" [(.name "type")]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "assert"
                                        [ (.binop
                                        ">"
                                        (.binop
                                        "+"
                                        (.binop "+" (.name "hdrlen") (.name "newlen"))
                                        (.lit (.int 1)))
                                        (.name "reqlen")) ]))
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.name "oldtype") (.name "type"))
                                        (.seq
                                        (.assign
                                        "newsh"
                                        (.call
                                        "s_realloc"
                                        [ (.call
                                        "realloc"
                                        [ (.name "sh")
                                        , (.binop
                                        "+"
                                        (.binop "+" (.name "hdrlen") (.name "newlen"))
                                        (.lit (.int 1))) ]) ]))
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.name "newsh") (.name "NULL"))
                                        (.ret (.name "NULL"))
                                        .skip)
                                        (.assign
                                        "s"
                                        (.binop "+" (.hole "op:cast") (.name "hdrlen")))))
                                        (.seq
                                        (.assign
                                        "newsh"
                                        (.call
                                        "s_malloc"
                                        [ (.call
                                        "malloc"
                                        [ (.binop
                                        "+"
                                        (.binop "+" (.name "hdrlen") (.name "newlen"))
                                        (.lit (.int 1))) ]) ]))
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.name "newsh") (.name "NULL"))
                                        (.ret (.name "NULL"))
                                        .skip)
                                        (.seq
                                        (.expr
                                        (.call
                                        "memcpy"
                                        [ (.binop "+" (.hole "op:cast") (.name "hdrlen"))
                                        , (.name "s")
                                        , (.binop "+" (.name "len") (.lit (.int 1))) ]))
                                        (.seq
                                        (.expr (.call "s_free" [(.call "free" [(.name "sh")])]))
                                        (.seq
                                        (.assign
                                        "s"
                                        (.binop "+" (.hole "op:cast") (.name "hdrlen")))
                                        (.seq
                                        (.hole "assign:lhs:indirectIndexAccess")
                                        (.expr (.call "sdssetlen" [(.name "s"), (.name "len")])))))))))
                                        (.seq
                                        (.expr
                                        (.call "sdssetalloc" [(.name "s"), (.name "newlen")]))
                                        (.ret (.name "s"))))))))))))))))))))))))) }

/-- `sdsRemoveFreeSpace`  (from `sds.c`) -/
def f_sdsRemoveFreeSpace : Func :=
  { name := "sdsRemoveFreeSpace"
  , params := ["s"]
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
                      (.assign "oldtype" (.hole "op:and"))
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            (.assign "oldhdrlen" (.call "sdsHdrSize" [(.name "oldtype")]))
                            (.seq
                              .skip
                              (.seq
                                (.assign "len" (.call "sdslen" [(.name "s")]))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "avail" (.call "sdsavail" [(.name "s")]))
                                    (.seq
                                      (.assign
                                        "sh"
                                        (.binop "-" (.hole "op:cast") (.name "oldhdrlen")))
                                      (.seq
                                        (.ifte
                                        (.binop "==" (.name "avail") (.lit (.int 0)))
                                        (.ret (.name "s"))
                                        .skip)
                                        (.seq
                                        (.assign "type" (.call "sdsReqType" [(.name "len")]))
                                        (.seq
                                        (.assign "hdrlen" (.call "sdsHdrSize" [(.name "type")]))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "||"
                                        (.binop "==" (.name "oldtype") (.name "type"))
                                        (.binop
                                        ">"
                                        (.name "type")
                                        (.call "SDS_TYPE_8" [(.lit (.int 1))])))
                                        (.seq
                                        (.assign
                                        "newsh"
                                        (.call
                                        "s_realloc"
                                        [ (.call
                                        "realloc"
                                        [ (.name "sh")
                                        , (.binop
                                        "+"
                                        (.binop "+" (.name "oldhdrlen") (.name "len"))
                                        (.lit (.int 1))) ]) ]))
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.name "newsh") (.name "NULL"))
                                        (.ret (.name "NULL"))
                                        .skip)
                                        (.assign
                                        "s"
                                        (.binop "+" (.hole "op:cast") (.name "oldhdrlen")))))
                                        (.seq
                                        (.assign
                                        "newsh"
                                        (.call
                                        "s_malloc"
                                        [ (.call
                                        "malloc"
                                        [ (.binop
                                        "+"
                                        (.binop "+" (.name "hdrlen") (.name "len"))
                                        (.lit (.int 1))) ]) ]))
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.name "newsh") (.name "NULL"))
                                        (.ret (.name "NULL"))
                                        .skip)
                                        (.seq
                                        (.expr
                                        (.call
                                        "memcpy"
                                        [ (.binop "+" (.hole "op:cast") (.name "hdrlen"))
                                        , (.name "s")
                                        , (.binop "+" (.name "len") (.lit (.int 1))) ]))
                                        (.seq
                                        (.expr (.call "s_free" [(.call "free" [(.name "sh")])]))
                                        (.seq
                                        (.assign
                                        "s"
                                        (.binop "+" (.hole "op:cast") (.name "hdrlen")))
                                        (.seq
                                        (.hole "assign:lhs:indirectIndexAccess")
                                        (.expr (.call "sdssetlen" [(.name "s"), (.name "len")])))))))))
                                        (.seq
                                        (.expr (.call "sdssetalloc" [(.name "s"), (.name "len")]))
                                        (.ret (.name "s"))))))))))))))))))))) }

/-- `sdsAllocSize`  (from `sds.c`) -/
def f_sdsAllocSize : Func :=
  { name := "sdsAllocSize"
  , params := ["s"]
  , body := (.seq
            .skip
            (.seq
              (.assign "alloc" (.call "sdsalloc" [(.name "s")]))
              (.ret
                (.binop
                  "+"
                  (.binop
                    "+"
                    (.call "sdsHdrSize" [(.hole "op:indirectIndexAccess")])
                    (.name "alloc"))
                  (.lit (.int 1)))))) }

/-- `sdsAllocPtr`  (from `sds.c`) -/
def f_sdsAllocPtr : Func :=
  { name := "sdsAllocPtr"
  , params := ["s"]
  , body := (.ret (.hole "op:cast")) }

/-- `sdsIncrLen`  (from `sds.c`) -/
def f_sdsIncrLen : Func :=
  { name := "sdsIncrLen"
  , params := ["s", "incr"]
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
                        (.assign "flags" (.hole "op:indirectIndexAccess"))
                        (.seq
                          .skip
                          (.seq (.hole "control:SWITCH") (.hole "assign:lhs:indirectIndexAccess")))))))))) }

/-- `sdsgrowzero`  (from `sds.c`) -/
def f_sdsgrowzero : Func :=
  { name := "sdsgrowzero"
  , params := ["s", "len"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "curlen" (.call "sdslen" [(.name "s")]))
                (.seq
                  (.ifte (.binop "<=" (.name "len") (.name "curlen")) (.ret (.name "s")) .skip)
                  (.seq
                    (.assign
                      "s"
                      (.call
                        "sdsMakeRoomFor"
                        [(.name "s"), (.binop "-" (.name "len") (.name "curlen"))]))
                    (.seq
                      (.ifte (.binop "==" (.name "s") (.name "NULL")) (.ret (.name "NULL")) .skip)
                      (.seq
                        (.expr
                          (.call
                            "memset"
                            [ (.binop "+" (.name "s") (.name "curlen"))
                            , (.lit (.int 0))
                            , (.binop
                                "+"
                                (.binop "-" (.name "len") (.name "curlen"))
                                (.lit (.int 1))) ]))
                        (.seq
                          (.expr (.call "sdssetlen" [(.name "s"), (.name "len")]))
                          (.ret (.name "s")))))))))) }

/-- `sdscatlen`  (from `sds.c`) -/
def f_sdscatlen : Func :=
  { name := "sdscatlen"
  , params := ["s", "t", "len"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "curlen" (.call "sdslen" [(.name "s")]))
                (.seq
                  (.assign "s" (.call "sdsMakeRoomFor" [(.name "s"), (.name "len")]))
                  (.seq
                    (.ifte (.binop "==" (.name "s") (.name "NULL")) (.ret (.name "NULL")) .skip)
                    (.seq
                      (.expr
                        (.call
                          "memcpy"
                          [(.binop "+" (.name "s") (.name "curlen")), (.name "t"), (.name "len")]))
                      (.seq
                        (.expr
                          (.call
                            "sdssetlen"
                            [(.name "s"), (.binop "+" (.name "curlen") (.name "len"))]))
                        (.seq (.hole "assign:lhs:indirectIndexAccess") (.ret (.name "s")))))))))) }

/-- `sdscat`  (from `sds.c`) -/
def f_sdscat : Func :=
  { name := "sdscat"
  , params := ["s", "t"]
  , body := (.ret (.call "sdscatlen" [(.name "s"), (.name "t"), (.call "strlen" [(.name "t")])])) }

/-- `sdscatsds`  (from `sds.c`) -/
def f_sdscatsds : Func :=
  { name := "sdscatsds"
  , params := ["s", "t"]
  , body := (.ret (.call "sdscatlen" [(.name "s"), (.name "t"), (.call "sdslen" [(.name "t")])])) }

/-- `sdscpylen`  (from `sds.c`) -/
def f_sdscpylen : Func :=
  { name := "sdscpylen"
  , params := ["s", "t", "len"]
  , body := (.seq
            .skip
            (.seq
              (.ifte
                (.binop "<" (.call "sdsalloc" [(.name "s")]) (.name "len"))
                (.seq
                  (.assign
                    "s"
                    (.call
                      "sdsMakeRoomFor"
                      [(.name "s"), (.binop "-" (.name "len") (.call "sdslen" [(.name "s")]))]))
                  (.ifte (.binop "==" (.name "s") (.name "NULL")) (.ret (.name "NULL")) .skip))
                .skip)
              (.seq
                (.expr (.call "memcpy" [(.name "s"), (.name "t"), (.name "len")]))
                (.seq
                  (.hole "assign:lhs:indirectIndexAccess")
                  (.seq (.expr (.call "sdssetlen" [(.name "s"), (.name "len")])) (.ret (.name "s"))))))) }

/-- `sdscpy`  (from `sds.c`) -/
def f_sdscpy : Func :=
  { name := "sdscpy"
  , params := ["s", "t"]
  , body := (.ret (.call "sdscpylen" [(.name "s"), (.name "t"), (.call "strlen" [(.name "t")])])) }

/-- `sdsll2str`  (from `sds.c`) -/
def f_sdsll2str : Func :=
  { name := "sdsll2str"
  , params := ["s", "value"]
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
                        (.ifte
                          (.binop "<" (.name "value") (.lit (.int 0)))
                          (.ifte
                            (.binop "!=" (.name "value") (.name "LLONG_MIN"))
                            (.assign "v" (.unop "-" (.name "value")))
                            (.assign "v" (.binop "+" (.hole "op:cast") (.lit (.int 1)))))
                          (.assign "v" (.name "value")))
                        (.seq
                          (.assign "p" (.name "s"))
                          (.seq
                            (.loop
                              (.hole "expr:BLOCK-prelude")
                              (.expr (.binop "!=" (.name "v") (.lit (.int 0)))))
                            (.seq
                              (.ifte
                                (.binop "<" (.name "value") (.lit (.int 0)))
                                (.hole "assign:lhs:indirection")
                                .skip)
                              (.seq
                                (.assign "l" (.hole "cstr:pointer-arith"))
                                (.seq
                                  (.hole "assign:lhs:indirection")
                                  (.seq
                                    (.expr (.hole "op:postDecrement"))
                                    (.seq
                                      (.loop
                                        (.hole "cstr:address-compare")
                                        (.seq
                                        (.assign "aux" (.hole "op:indirection"))
                                        (.seq
                                        (.hole "assign:lhs:indirection")
                                        (.seq
                                        (.hole "assign:lhs:indirection")
                                        (.seq
                                        (.expr (.hole "op:postIncrement"))
                                        (.expr (.hole "op:postDecrement")))))))
                                      (.ret (.name "l")))))))))))))))) }

/-- `sdsull2str`  (from `sds.c`) -/
def f_sdsull2str : Func :=
  { name := "sdsull2str"
  , params := ["s", "v"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.assign "p" (.name "s"))
                  (.seq
                    (.loop
                      (.hole "expr:BLOCK-prelude")
                      (.expr (.binop "!=" (.name "v") (.lit (.int 0)))))
                    (.seq
                      (.assign "l" (.hole "cstr:pointer-arith"))
                      (.seq
                        (.hole "assign:lhs:indirection")
                        (.seq
                          (.expr (.hole "op:postDecrement"))
                          (.seq
                            (.loop
                              (.hole "cstr:address-compare")
                              (.seq
                                (.assign "aux" (.hole "op:indirection"))
                                (.seq
                                  (.hole "assign:lhs:indirection")
                                  (.seq
                                    (.hole "assign:lhs:indirection")
                                    (.seq
                                      (.expr (.hole "op:postIncrement"))
                                      (.expr (.hole "op:postDecrement")))))))
                            (.ret (.name "l"))))))))))) }

/-- `sdsfromlonglong`  (from `sds.c`) -/
def f_sdsfromlonglong : Func :=
  { name := "sdsfromlonglong"
  , params := ["value"]
  , body := (.seq
            .skip
            (.seq
              (.assign "buf" (.hole "op:alloc"))
              (.seq
                .skip
                (.seq
                  (.assign "len" (.call "sdsll2str" [(.name "buf"), (.name "value")]))
                  (.ret (.call "sdsnewlen" [(.name "buf"), (.name "len")])))))) }

/-- `sdscatvprintf`  (from `sds.c`) -/
def f_sdscatvprintf : Func :=
  { name := "sdscatvprintf"
  , params := ["s", "fmt", "ap"]
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
                      (.assign "staticbuf" (.hole "op:alloc"))
                      (.seq
                        (.assign "buf" (.name "staticbuf"))
                        (.seq
                          .skip
                          (.seq
                            (.assign
                              "buflen"
                              (.binop "*" (.call "strlen" [(.name "fmt")]) (.lit (.int 2))))
                            (.seq
                              .skip
                              (.seq
                                (.ifte
                                  (.binop ">" (.name "buflen") (.hole "op:sizeOf"))
                                  (.seq
                                    (.assign
                                      "buf"
                                      (.call "s_malloc" [(.call "malloc" [(.name "buflen")])]))
                                    (.ifte
                                      (.hole "cstr:address-equality")
                                      (.ret (.name "NULL"))
                                      .skip))
                                  (.assign "buflen" (.hole "op:sizeOf")))
                                (.seq
                                  (.loop
                                    (.lit (.int 1))
                                    (.seq
                                      (.expr (.call "va_copy" [(.name "cpy"), (.name "ap")]))
                                      (.seq
                                        (.assign
                                        "bufstrlen"
                                        (.call
                                        "vsnprintf"
                                        [ (.name "buf")
                                        , (.name "buflen")
                                        , (.name "fmt")
                                        , (.name "cpy") ]))
                                        (.seq
                                        (.expr (.call "va_end" [(.name "cpy")]))
                                        (.seq
                                        (.ifte
                                        (.binop "<" (.name "bufstrlen") (.lit (.int 0)))
                                        (.seq
                                        (.ifte
                                        (.hole "cstr:address-equality")
                                        (.expr (.call "s_free" [(.call "free" [(.name "buf")])]))
                                        .skip)
                                        (.ret (.name "NULL")))
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.binop ">=" (.hole "op:cast") (.name "buflen"))
                                        (.seq
                                        (.ifte
                                        (.hole "cstr:address-equality")
                                        (.expr (.call "s_free" [(.call "free" [(.name "buf")])]))
                                        .skip)
                                        (.seq
                                        (.assign
                                        "buflen"
                                        (.binop "+" (.hole "op:cast") (.lit (.int 1))))
                                        (.seq
                                        (.assign
                                        "buf"
                                        (.call "s_malloc" [(.call "malloc" [(.name "buflen")])]))
                                        (.seq
                                        (.ifte
                                        (.hole "cstr:address-equality")
                                        (.ret (.name "NULL"))
                                        .skip)
                                        .cont))))
                                        .skip)
                                        .brk))))))
                                  (.seq
                                    (.assign
                                      "t"
                                      (.call
                                        "sdscatlen"
                                        [(.name "s"), (.name "buf"), (.name "bufstrlen")]))
                                    (.seq
                                      (.ifte
                                        (.hole "cstr:address-equality")
                                        (.expr (.call "s_free" [(.call "free" [(.name "buf")])]))
                                        .skip)
                                      (.ret (.name "t")))))))))))))))) }

/-- `sdscatprintf`  (from `sds.c`) -/
def f_sdscatprintf : Func :=
  { name := "sdscatprintf"
  , params := ["s", "fmt", "<param>3"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.expr (.call "va_start" [(.name "ap"), (.name "fmt")]))
                (.seq
                  (.assign "t" (.call "sdscatvprintf" [(.name "s"), (.name "fmt"), (.name "ap")]))
                  (.seq (.expr (.call "va_end" [(.name "ap")])) (.ret (.name "t"))))))) }

/-- `sdscatfmt`  (from `sds.c`) -/
def f_sdscatfmt : Func :=
  { name := "sdscatfmt"
  , params := ["s", "fmt", "<param>3"]
  , body := (.seq
            .skip
            (.seq
              (.assign "initlen" (.call "sdslen" [(.name "s")]))
              (.seq
                .skip
                (.seq
                  (.assign "f" (.name "fmt"))
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq
                        (.assign
                          "s"
                          (.call
                            "sdsMakeRoomFor"
                            [ (.name "s")
                            , (.binop
                                "+"
                                (.name "initlen")
                                (.binop "*" (.call "strlen" [(.name "fmt")]) (.lit (.int 2)))) ]))
                        (.seq
                          (.expr (.call "va_start" [(.name "ap"), (.name "fmt")]))
                          (.seq
                            (.assign "f" (.name "fmt"))
                            (.seq
                              (.assign "i" (.name "initlen"))
                              (.seq
                                (.loop
                                  (.hole "op:indirection")
                                  (.seq
                                    .skip
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
                                        "=="
                                        (.call "sdsavail" [(.name "s")])
                                        (.lit (.int 0)))
                                        (.assign
                                        "s"
                                        (.call "sdsMakeRoomFor" [(.name "s"), (.lit (.int 1))]))
                                        .skip)
                                        (.seq
                                        (.hole "control:SWITCH")
                                        (.expr (.hole "op:postIncrement"))))))))))
                                (.seq
                                  (.expr (.call "va_end" [(.name "ap")]))
                                  (.seq (.hole "assign:lhs:indirectIndexAccess") (.ret (.name "s"))))))))))))))) }

/-- `sdstrim`  (from `sds.c`) -/
def f_sdstrim : Func :=
  { name := "sdstrim"
  , params := ["s", "cset"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    (.assign "sp" (.name "s"))
                    (.seq
                      (.assign "ep" (.hole "op:assignment"))
                      (.seq
                        (.loop
                          (.binop
                            "&&"
                            (.hole "cstr:address-compare")
                            (.call "strchr" [(.name "cset"), (.hole "op:indirection")]))
                          (.expr (.hole "op:postIncrement")))
                        (.seq
                          (.loop
                            (.binop
                              "&&"
                              (.hole "cstr:address-compare")
                              (.call "strchr" [(.name "cset"), (.hole "op:indirection")]))
                            (.expr (.hole "op:postDecrement")))
                          (.seq
                            (.assign
                              "len"
                              (.binop "+" (.hole "cstr:pointer-arith") (.lit (.int 1))))
                            (.seq
                              (.ifte
                                (.hole "cstr:address-equality")
                                (.expr (.call "memmove" [(.name "s"), (.name "sp"), (.name "len")]))
                                .skip)
                              (.seq
                                (.hole "assign:lhs:indirectIndexAccess")
                                (.seq
                                  (.expr (.call "sdssetlen" [(.name "s"), (.name "len")]))
                                  (.ret (.name "s")))))))))))))) }

/-- `sdsrange`  (from `sds.c`) -/
def f_sdsrange : Func :=
  { name := "sdsrange"
  , params := ["s", "start", "end"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "len" (.call "sdslen" [(.name "s")]))
                (.seq
                  (.ifte (.binop "==" (.name "len") (.lit (.int 0))) (.ret (.lit .unit)) .skip)
                  (.seq
                    (.ifte
                      (.binop "<" (.name "start") (.lit (.int 0)))
                      (.seq
                        (.assign "start" (.binop "+" (.name "len") (.name "start")))
                        (.ifte
                          (.binop "<" (.name "start") (.lit (.int 0)))
                          (.assign "start" (.lit (.int 0)))
                          .skip))
                      .skip)
                    (.seq
                      (.ifte
                        (.binop "<" (.name "end") (.lit (.int 0)))
                        (.seq
                          (.assign "end" (.binop "+" (.name "len") (.name "end")))
                          (.ifte
                            (.binop "<" (.name "end") (.lit (.int 0)))
                            (.assign "end" (.lit (.int 0)))
                            .skip))
                        .skip)
                      (.seq
                        (.assign
                          "newlen"
                          (.cond
                            (.binop ">" (.name "start") (.name "end"))
                            (.lit (.int 0))
                            (.binop "+" (.binop "-" (.name "end") (.name "start")) (.lit (.int 1)))))
                        (.seq
                          (.ifte
                            (.binop "!=" (.name "newlen") (.lit (.int 0)))
                            (.ifte
                              (.binop ">=" (.name "start") (.hole "op:cast"))
                              (.assign "newlen" (.lit (.int 0)))
                              (.ifte
                                (.binop ">=" (.name "end") (.hole "op:cast"))
                                (.seq
                                  (.assign "end" (.binop "-" (.name "len") (.lit (.int 1))))
                                  (.assign
                                    "newlen"
                                    (.binop
                                      "+"
                                      (.binop "-" (.name "end") (.name "start"))
                                      (.lit (.int 1)))))
                                .skip))
                            .skip)
                          (.seq
                            (.ifte
                              (.binop "&&" (.name "start") (.name "newlen"))
                              (.expr
                                (.call
                                  "memmove"
                                  [ (.name "s")
                                  , (.binop "+" (.name "s") (.name "start"))
                                  , (.name "newlen") ]))
                              .skip)
                            (.seq
                              (.hole "assign:lhs:indirectIndexAccess")
                              (.expr (.call "sdssetlen" [(.name "s"), (.name "newlen")])))))))))))) }

/-- `sdstolower`  (from `sds.c`) -/
def f_sdstolower : Func :=
  { name := "sdstolower"
  , params := ["s"]
  , body := (.seq
            .skip
            (.seq .skip (.seq (.assign "len" (.call "sdslen" [(.name "s")])) (.hole "control:FOR")))) }

/-- `sdstoupper`  (from `sds.c`) -/
def f_sdstoupper : Func :=
  { name := "sdstoupper"
  , params := ["s"]
  , body := (.seq
            .skip
            (.seq .skip (.seq (.assign "len" (.call "sdslen" [(.name "s")])) (.hole "control:FOR")))) }

/-- `sdscmp`  (from `sds.c`) -/
def f_sdscmp : Func :=
  { name := "sdscmp"
  , params := ["s1", "s2"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    (.assign "l1" (.call "sdslen" [(.name "s1")]))
                    (.seq
                      (.assign "l2" (.call "sdslen" [(.name "s2")]))
                      (.seq
                        (.assign
                          "minlen"
                          (.cond (.binop "<" (.name "l1") (.name "l2")) (.name "l1") (.name "l2")))
                        (.seq
                          (.assign
                            "cmp"
                            (.call "memcmp" [(.name "s1"), (.name "s2"), (.name "minlen")]))
                          (.seq
                            (.ifte
                              (.binop "==" (.name "cmp") (.lit (.int 0)))
                              (.ret
                                (.cond
                                  (.binop ">" (.name "l1") (.name "l2"))
                                  (.lit (.int 1))
                                  (.cond
                                    (.binop "<" (.name "l1") (.name "l2"))
                                    (.unop "-" (.lit (.int 1)))
                                    (.lit (.int 0)))))
                              .skip)
                            (.ret (.name "cmp"))))))))))) }

/-- `sdssplitlen`  (from `sds.c`) -/
def f_sdssplitlen : Func :=
  { name := "sdssplitlen"
  , params := ["s", "len", "sep", "seplen", "count"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    (.assign "elements" (.lit (.int 0)))
                    (.seq
                      (.assign "slots" (.lit (.int 5)))
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            (.assign "start" (.lit (.int 0)))
                            (.seq
                              .skip
                              (.seq
                                (.ifte
                                  (.binop
                                    "||"
                                    (.binop "<" (.name "seplen") (.lit (.int 1)))
                                    (.binop "<=" (.name "len") (.lit (.int 0))))
                                  (.seq (.hole "assign:lhs:indirection") (.ret (.name "NULL")))
                                  .skip)
                                (.seq
                                  (.assign
                                    "tokens"
                                    (.call
                                      "s_malloc"
                                      [ (.call
                                        "malloc"
                                        [(.binop "*" (.hole "op:sizeOf") (.name "slots"))]) ]))
                                  (.seq
                                    (.ifte
                                      (.binop "==" (.name "tokens") (.name "NULL"))
                                      (.ret (.name "NULL"))
                                      .skip)
                                    (.seq
                                      (.hole "control:FOR")
                                      (.seq
                                        (.hole "assign:lhs:indirectIndexAccess")
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.hole "op:indirectIndexAccess")
                                        (.name "NULL"))
                                        (.hole "control:GOTO")
                                        .skip)
                                        (.seq
                                        (.expr (.hole "op:postIncrement"))
                                        (.seq
                                        (.hole "assign:lhs:indirection")
                                        (.seq
                                        (.ret (.name "tokens"))
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        (.hole "control:FOR")
                                        (.seq
                                        (.expr (.call "s_free" [(.call "free" [(.name "tokens")])]))
                                        (.seq
                                        (.hole "assign:lhs:indirection")
                                        (.ret (.name "NULL")))))))))))))))))))))))))) }

/-- `sdsfreesplitres`  (from `sds.c`) -/
def f_sdsfreesplitres : Func :=
  { name := "sdsfreesplitres"
  , params := ["tokens", "count"]
  , body := (.seq
            (.ifte (.unop "!" (.name "tokens")) (.ret (.lit .unit)) .skip)
            (.seq
              (.loop
                (.hole "op:postDecrement")
                (.expr (.call "sdsfree" [(.hole "op:indirectIndexAccess")])))
              (.expr (.call "s_free" [(.call "free" [(.name "tokens")])])))) }

/-- `sdscatrepr`  (from `sds.c`) -/
def f_sdscatrepr : Func :=
  { name := "sdscatrepr"
  , params := ["s", "p", "len"]
  , body := (.seq
            (.assign "s" (.call "sdscatlen" [(.name "s"), (.lit (.str "\\\"")), (.lit (.int 1))]))
            (.seq
              (.loop
                (.hole "op:postDecrement")
                (.seq (.hole "control:SWITCH") (.expr (.hole "op:postIncrement"))))
              (.ret (.call "sdscatlen" [(.name "s"), (.lit (.str "\\\"")), (.lit (.int 1))])))) }

/-- `is_hex_digit`  (from `sds.c`) -/
def f_is_hex_digit : Func :=
  { name := "is_hex_digit"
  , params := ["c"]
  , body := (.ret
            (.binop
              "||"
              (.binop
                "||"
                (.binop
                  "&&"
                  (.binop ">=" (.name "c") (.lit (.str "0")))
                  (.binop "<=" (.name "c") (.lit (.str "9"))))
                (.binop
                  "&&"
                  (.binop ">=" (.name "c") (.lit (.str "a")))
                  (.binop "<=" (.name "c") (.lit (.str "f")))))
              (.binop
                "&&"
                (.binop ">=" (.name "c") (.lit (.str "A")))
                (.binop "<=" (.name "c") (.lit (.str "F")))))) }

/-- `hex_digit_to_int`  (from `sds.c`) -/
def f_hex_digit_to_int : Func :=
  { name := "hex_digit_to_int"
  , params := ["c"]
  , body := (.hole "control:SWITCH") }

/-- `sdssplitargs`  (from `sds.c`) -/
def f_sdssplitargs : Func :=
  { name := "sdssplitargs"
  , params := ["line", "argc"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    (.assign "p" (.name "line"))
                    (.seq
                      .skip
                      (.seq
                        (.assign "current" (.name "NULL"))
                        (.seq
                          .skip
                          (.seq
                            (.assign "vector" (.name "NULL"))
                            (.seq
                              (.hole "assign:lhs:indirection")
                              (.seq
                                (.loop
                                  (.lit (.int 1))
                                  (.seq
                                    (.loop
                                      (.binop
                                        "&&"
                                        (.hole "op:indirection")
                                        (.call "isspace" [(.hole "op:indirection")]))
                                      (.expr (.hole "op:postIncrement")))
                                    (.ifte
                                      (.hole "op:indirection")
                                      (.seq
                                        .skip
                                        (.seq
                                        (.assign "inq" (.lit (.int 0)))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "insq" (.lit (.int 0)))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "done" (.lit (.int 0)))
                                        (.seq
                                        (.ifte
                                        (.hole "cstr:address-equality")
                                        (.assign "current" (.call "sdsempty" []))
                                        .skip)
                                        (.seq
                                        (.loop
                                        (.unop "!" (.name "done"))
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.name "inq") (.lit (.int 0)))
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.binop
                                        "&&"
                                        (.binop
                                        "&&"
                                        (.binop "==" (.hole "op:indirection") (.lit (.str "\\\\")))
                                        (.binop "==" (.hole "op:indirection") (.lit (.str "x"))))
                                        (.call "is_hex_digit" [(.hole "op:indirection")]))
                                        (.call "is_hex_digit" [(.hole "op:indirection")]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "byte"
                                        (.binop
                                        "+"
                                        (.binop
                                        "*"
                                        (.call "hex_digit_to_int" [(.hole "op:indirection")])
                                        (.lit (.int 16)))
                                        (.call "hex_digit_to_int" [(.hole "op:indirection")])))
                                        (.seq
                                        (.assign
                                        "current"
                                        (.call
                                        "sdscatlen"
                                        [(.name "current"), (.hole "op:cast"), (.lit (.int 1))]))
                                        (.hole "cstr:pointer-arith"))))
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.binop "==" (.hole "op:indirection") (.lit (.str "\\\\")))
                                        (.hole "op:indirection"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.expr (.hole "op:postIncrement"))
                                        (.seq
                                        (.hole "control:SWITCH")
                                        (.assign
                                        "current"
                                        (.call
                                        "sdscatlen"
                                        [(.name "current"), (.hole "op:addressOf"), (.lit (.int 1))])))))
                                        (.ifte
                                        (.binop "==" (.hole "op:indirection") (.lit (.str "\"")))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.hole "op:indirection")
                                        (.unop "!" (.call "isspace" [(.hole "op:indirection")])))
                                        (.hole "control:GOTO")
                                        .skip)
                                        (.assign "done" (.lit (.int 1))))
                                        (.ifte
                                        (.unop "!" (.hole "op:indirection"))
                                        (.hole "control:GOTO")
                                        (.assign
                                        "current"
                                        (.call
                                        "sdscatlen"
                                        [(.name "current"), (.name "p"), (.lit (.int 1))]))))))
                                        (.ifte
                                        (.binop "!=" (.name "insq") (.lit (.int 0)))
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.binop "==" (.hole "op:indirection") (.lit (.str "\\\\")))
                                        (.binop "==" (.hole "op:indirection") (.lit (.str "\\'"))))
                                        (.seq
                                        (.expr (.hole "op:postIncrement"))
                                        (.assign
                                        "current"
                                        (.call
                                        "sdscatlen"
                                        [(.name "current"), (.lit (.str "'")), (.lit (.int 1))])))
                                        (.ifte
                                        (.binop "==" (.hole "op:indirection") (.lit (.str "\\'")))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.hole "op:indirection")
                                        (.unop "!" (.call "isspace" [(.hole "op:indirection")])))
                                        (.hole "control:GOTO")
                                        .skip)
                                        (.assign "done" (.lit (.int 1))))
                                        (.ifte
                                        (.unop "!" (.hole "op:indirection"))
                                        (.hole "control:GOTO")
                                        (.assign
                                        "current"
                                        (.call
                                        "sdscatlen"
                                        [(.name "current"), (.name "p"), (.lit (.int 1))])))))
                                        (.hole "control:SWITCH")))
                                        (.ifte
                                        (.hole "op:indirection")
                                        (.expr (.hole "op:postIncrement"))
                                        .skip)))
                                        (.seq
                                        (.assign
                                        "vector"
                                        (.call
                                        "s_realloc"
                                        [ (.call
                                        "realloc"
                                        [ (.name "vector")
                                        , (.binop
                                        "*"
                                        (.binop "+" (.hole "op:indirection") (.lit (.int 1)))
                                        (.hole "op:sizeOf")) ]) ]))
                                        (.seq
                                        (.hole "assign:lhs:indirectIndexAccess")
                                        (.seq
                                        (.expr (.hole "op:postIncrement"))
                                        (.assign "current" (.name "NULL")))))))))))))
                                      (.seq
                                        (.ifte
                                        (.hole "cstr:address-equality")
                                        (.assign
                                        "vector"
                                        (.call "s_malloc" [(.call "malloc" [(.hole "op:sizeOf")])]))
                                        .skip)
                                        (.ret (.name "vector"))))))
                                (.seq
                                  .skip
                                  (.seq
                                    (.loop
                                      (.hole "op:postDecrement")
                                      (.expr (.call "sdsfree" [(.hole "op:indirectIndexAccess")])))
                                    (.seq
                                      (.expr (.call "s_free" [(.call "free" [(.name "vector")])]))
                                      (.seq
                                        (.ifte
                                        (.hole "cstr:address-equality")
                                        (.expr (.call "sdsfree" [(.name "current")]))
                                        .skip)
                                        (.seq
                                        (.hole "assign:lhs:indirection")
                                        (.ret (.name "NULL")))))))))))))))))) }

/-- `sdsmapchars`  (from `sds.c`) -/
def f_sdsmapchars : Func :=
  { name := "sdsmapchars"
  , params := ["s", "from", "to", "setlen"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.assign "l" (.call "sdslen" [(.name "s")]))
                  (.seq (.hole "control:FOR") (.ret (.name "s"))))))) }

/-- `sdsjoin`  (from `sds.c`) -/
def f_sdsjoin : Func :=
  { name := "sdsjoin"
  , params := ["argv", "argc", "sep"]
  , body := (.seq
            .skip
            (.seq
              (.assign "join" (.call "sdsempty" []))
              (.seq .skip (.seq (.hole "control:FOR") (.ret (.name "join")))))) }

/-- `sdsjoinsds`  (from `sds.c`) -/
def f_sdsjoinsds : Func :=
  { name := "sdsjoinsds"
  , params := ["argv", "argc", "sep", "seplen"]
  , body := (.seq
            .skip
            (.seq
              (.assign "join" (.call "sdsempty" []))
              (.seq .skip (.seq (.hole "control:FOR") (.ret (.name "join")))))) }

/-- `sds_malloc`  (from `sds.c`) -/
def f_sds_malloc : Func :=
  { name := "sds_malloc"
  , params := ["size"]
  , body := (.ret (.call "s_malloc" [(.call "malloc" [(.name "size")])])) }

/-- `sds_realloc`  (from `sds.c`) -/
def f_sds_realloc : Func :=
  { name := "sds_realloc"
  , params := ["ptr", "size"]
  , body := (.ret (.call "s_realloc" [(.call "realloc" [(.name "ptr"), (.name "size")])])) }

/-- `sds_free`  (from `sds.c`) -/
def f_sds_free : Func :=
  { name := "sds_free"
  , params := ["ptr"]
  , body := (.expr (.call "s_free" [(.call "free" [(.name "ptr")])])) }

/-- `sdsTest`  (from `sds.c`) -/
def f_sdsTest : Func :=
  { name := "sdsTest"
  , params := [""]
  , body := .skip }

/-- `main`  (from `sds.c`) -/
def f_main : Func :=
  { name := "main"
  , params := [""]
  , body := .skip }

/-- `sdshdr5.<clinit>:sdshdr5()`  (from `sds.h`) -/
def f_sdshdr5__clinit__sdshdr5__ : Func :=
  { name := "sdshdr5.<clinit>:sdshdr5()"
  , params := []
  , body := (.expr (.hole "op:arrayInitializer")) }

/-- `sdshdr8.<clinit>:sdshdr8()`  (from `sds.h`) -/
def f_sdshdr8__clinit__sdshdr8__ : Func :=
  { name := "sdshdr8.<clinit>:sdshdr8()"
  , params := []
  , body := (.expr (.hole "op:arrayInitializer")) }

/-- `sdshdr16.<clinit>:sdshdr16()`  (from `sds.h`) -/
def f_sdshdr16__clinit__sdshdr16__ : Func :=
  { name := "sdshdr16.<clinit>:sdshdr16()"
  , params := []
  , body := (.expr (.hole "op:arrayInitializer")) }

/-- `sdshdr32.<clinit>:sdshdr32()`  (from `sds.h`) -/
def f_sdshdr32__clinit__sdshdr32__ : Func :=
  { name := "sdshdr32.<clinit>:sdshdr32()"
  , params := []
  , body := (.expr (.hole "op:arrayInitializer")) }

/-- `sdshdr64.<clinit>:sdshdr64()`  (from `sds.h`) -/
def f_sdshdr64__clinit__sdshdr64__ : Func :=
  { name := "sdshdr64.<clinit>:sdshdr64()"
  , params := []
  , body := (.expr (.hole "op:arrayInitializer")) }

/-- `sdslen`  (from `sds.h`) -/
def f_sdslen : Func :=
  { name := "sdslen"
  , params := ["s"]
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
                      (.assign "flags" (.hole "op:indirectIndexAccess"))
                      (.seq (.hole "control:SWITCH") (.ret (.lit (.int 0)))))))))) }

/-- `sdsavail`  (from `sds.h`) -/
def f_sdsavail : Func :=
  { name := "sdsavail"
  , params := ["s"]
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
                      (.assign "flags" (.hole "op:indirectIndexAccess"))
                      (.seq (.hole "control:SWITCH") (.ret (.lit (.int 0)))))))))) }

/-- `sdssetlen`  (from `sds.h`) -/
def f_sdssetlen : Func :=
  { name := "sdssetlen"
  , params := ["s", "newlen"]
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
                      (.assign "flags" (.hole "op:indirectIndexAccess"))
                      (.hole "control:SWITCH"))))))) }

/-- `sdsinclen`  (from `sds.h`) -/
def f_sdsinclen : Func :=
  { name := "sdsinclen"
  , params := ["s", "inc"]
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
                      (.assign "flags" (.hole "op:indirectIndexAccess"))
                      (.hole "control:SWITCH"))))))) }

/-- `sdsalloc`  (from `sds.h`) -/
def f_sdsalloc : Func :=
  { name := "sdsalloc"
  , params := ["s"]
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
                      (.assign "flags" (.hole "op:indirectIndexAccess"))
                      (.seq (.hole "control:SWITCH") (.ret (.lit (.int 0)))))))))) }

/-- `sdssetalloc`  (from `sds.h`) -/
def f_sdssetalloc : Func :=
  { name := "sdssetalloc"
  , params := ["s", "newlen"]
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
                      (.assign "flags" (.hole "op:indirectIndexAccess"))
                      (.hole "control:SWITCH"))))))) }

/-- `sds.c:<global>`  (from `sds.c`) -/
def f_sds_c__global_ : Func :=
  { name := "sds.c:<global>"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.setGlobal "SDS_NOINIT" (.lit (.str "SDS_NOINIT")))
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              .skip
                              (.seq
                                .skip
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))))))))))))))))))))))))))))))))))))) }

/-- `sds.h:<global>`  (from `sds.h`) -/
def f_sds_h__global_ : Func :=
  { name := "sds.h:<global>"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.hole "stmt:TYPE_DECL")
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    .skip
                    (.seq
                      .skip
                      (.seq
                        .skip
                        (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))))))))))) }

/-- `sdsalloc.h:<global>`  (from `sdsalloc.h`) -/
def f_sdsalloc_h__global_ : Func :=
  { name := "sdsalloc.h:<global>"
  , params := []
  , body := .skip }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := [f_sds_c__global_, f_sds_h__global_, f_sdsalloc_h__global_]

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_sdsHdrSize,
  f_sdsReqType,
  f_sdsnewlen,
  f_sdsempty,
  f_sdsnew,
  f_sdsdup,
  f_sdsfree,
  f_sdsupdatelen,
  f_sdsclear,
  f_sdsMakeRoomFor,
  f_sdsRemoveFreeSpace,
  f_sdsAllocSize,
  f_sdsAllocPtr,
  f_sdsIncrLen,
  f_sdsgrowzero,
  f_sdscatlen,
  f_sdscat,
  f_sdscatsds,
  f_sdscpylen,
  f_sdscpy,
  f_sdsll2str,
  f_sdsull2str,
  f_sdsfromlonglong,
  f_sdscatvprintf,
  f_sdscatprintf,
  f_sdscatfmt,
  f_sdstrim,
  f_sdsrange,
  f_sdstolower,
  f_sdstoupper,
  f_sdscmp,
  f_sdssplitlen,
  f_sdsfreesplitres,
  f_sdscatrepr,
  f_is_hex_digit,
  f_hex_digit_to_int,
  f_sdssplitargs,
  f_sdsmapchars,
  f_sdsjoin,
  f_sdsjoinsds,
  f_sds_malloc,
  f_sds_realloc,
  f_sds_free,
  f_sdsTest,
  f_main,
  f_sdshdr5__clinit__sdshdr5__,
  f_sdshdr8__clinit__sdshdr8__,
  f_sdshdr16__clinit__sdshdr16__,
  f_sdshdr32__clinit__sdshdr32__,
  f_sdshdr64__clinit__sdshdr64__,
  f_sdslen,
  f_sdsavail,
  f_sdssetlen,
  f_sdsinclen,
  f_sdsalloc,
  f_sdssetalloc,
  f_sds_c__global_,
  f_sds_h__global_,
  f_sdsalloc_h__global_
] }

end Autoform.Generated