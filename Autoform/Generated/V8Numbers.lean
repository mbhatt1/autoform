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
set_option maxRecDepth 9256

/-!
# V8Numbers — machine-generated

Emitted by `cartographer/render_lean.py` from a Joern code property graph.
Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the
transpiler did not translate, tagged with the CPG node label responsible.
-/

namespace Autoform.Generated
open Autoform.Core

/-- `v8.internal.Convert2Digits:void(uint8_t,char*)`  (from `conversions.cc`) -/
def f_v8_internal_Convert2Digits_void_uint8_t_char__ : Func :=
  { name := "v8.internal.Convert2Digits:void(uint8_t,char*)"
  , params := ["n", "buffer"]
  , body := (.seq
            .skip
            (.seq
              (.expr
                (.call "DCHECK_LT" [(.name "n"), (.binop "/" (.hole "op:sizeOf") (.lit (.int 2)))]))
              (.expr
                (.call "MemCopy" [(.name "buffer"), (.hole "cstr:pointer-arith"), (.lit (.int 2))])))) }

/-- `v8.internal.ConvertHeadDigits:uint8_t(uint8_t,char*)`  (from `conversions.cc`) -/
def f_v8_internal_ConvertHeadDigits_uint8_t_uint8_t_char__ : Func :=
  { name := "v8.internal.ConvertHeadDigits:uint8_t(uint8_t,char*)"
  , params := ["n", "buffer"]
  , body := (.seq
            .skip
            (.seq
              (.expr
                (.call "DCHECK_LT" [(.name "n"), (.binop "/" (.hole "op:sizeOf") (.lit (.int 2)))]))
              (.seq
                .skip
                (.seq
                  (.assign
                    "digit_count"
                    (.binop "+" (.lit (.int 1)) (.binop ">=" (.name "n") (.lit (.int 10)))))
                  (.seq
                    (.expr (.call "DCHECK_LE" [(.name "digit_count"), (.lit (.int 2))]))
                    (.seq
                      (.expr
                        (.call
                          "MemCopy"
                          [(.name "buffer"), (.hole "cstr:pointer-arith"), (.name "digit_count")]))
                      (.ret (.name "digit_count")))))))) }

/-- `v8.internal.Convert8Digits:void(uint32_t,char*)`  (from `conversions.cc`) -/
def f_v8_internal_Convert8Digits_void_uint32_t_char__ : Func :=
  { name := "v8.internal.Convert8Digits:void(uint32_t,char*)"
  , params := ["n", "buffer"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "kUint32Mask" (.name "kMaxUInt32"))
                (.seq
                  .skip
                  (.seq
                    (.assign "prod" (.binop "*" (.name "n") (.lit (.int 281474978))))
                    (.seq
                      (.expr
                        (.call
                          "<operators>.assignmentArithmeticShiftRight"
                          [(.name "prod"), (.lit (.int 16))]))
                      (.seq
                        (.assign "prod" (.binop "+" (.name "prod") (.lit (.int 1))))
                        (.seq
                          (.expr
                            (.call
                              "Convert2Digits"
                              [ (.unop "cast:u8" (.hole "op:arithmeticShiftRight"))
                              , (.name "buffer") ]))
                          (.seq
                            (.assign "prod" (.binop "*" (.hole "op:and") (.lit (.int 100))))
                            (.seq
                              (.expr
                                (.call
                                  "Convert2Digits"
                                  [ (.unop "cast:u8" (.hole "op:arithmeticShiftRight"))
                                  , (.hole "cstr:pointer-arith") ]))
                              (.seq
                                (.assign "prod" (.binop "*" (.hole "op:and") (.lit (.int 100))))
                                (.seq
                                  (.expr
                                    (.call
                                      "Convert2Digits"
                                      [ (.unop "cast:u8" (.hole "op:arithmeticShiftRight"))
                                      , (.hole "cstr:pointer-arith") ]))
                                  (.seq
                                    (.assign "prod" (.binop "*" (.hole "op:and") (.lit (.int 100))))
                                    (.expr
                                      (.call
                                        "Convert2Digits"
                                        [ (.unop "cast:u8" (.hole "op:arithmeticShiftRight"))
                                        , (.hole "cstr:pointer-arith") ]))))))))))))))) }

/-- `v8.internal.ConvertUpTo9Digits:uint8_t(uint32_t,char*)`  (from `conversions.cc`) -/
def f_v8_internal_ConvertUpTo9Digits_uint8_t_uint32_t_char__ : Func :=
  { name := "v8.internal.ConvertUpTo9Digits:uint8_t(uint32_t,char*)"
  , params := ["n", "buffer"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "kUint32Mask" (.name "kMaxUInt32"))
                (.seq
                  (.ifte
                    (.binop ">=" (.name "n") (.lit (.int 100000000)))
                    (.seq
                      .skip
                      (.seq
                        (.assign "prod" (.binop "*" (.name "n") (.lit (.int 1441151882))))
                        (.seq
                          (.expr
                            (.call
                              "<operators>.assignmentArithmeticShiftRight"
                              [(.name "prod"), (.lit (.int 25))]))
                          (.seq
                            .skip
                            (.seq
                              (.assign
                                "head_digit"
                                (.unop "cast:u8" (.hole "op:arithmeticShiftRight")))
                              (.seq
                                (.expr (.call "DCHECK_LT" [(.name "head_digit"), (.lit (.int 10))]))
                                (.seq
                                  (.hole "assign:lhs:indirection")
                                  (.seq
                                    (.assign "prod" (.binop "*" (.hole "op:and") (.lit (.int 100))))
                                    (.seq
                                      (.expr
                                        (.call
                                        "Convert2Digits"
                                        [ (.unop "cast:u8" (.hole "op:arithmeticShiftRight"))
                                        , (.hole "cstr:pointer-arith") ]))
                                      (.seq
                                        (.assign
                                        "prod"
                                        (.binop "*" (.hole "op:and") (.lit (.int 100))))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Convert2Digits"
                                        [ (.unop "cast:u8" (.hole "op:arithmeticShiftRight"))
                                        , (.hole "cstr:pointer-arith") ]))
                                        (.seq
                                        (.assign
                                        "prod"
                                        (.binop "*" (.hole "op:and") (.lit (.int 100))))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Convert2Digits"
                                        [ (.unop "cast:u8" (.hole "op:arithmeticShiftRight"))
                                        , (.hole "cstr:pointer-arith") ]))
                                        (.seq
                                        (.assign
                                        "prod"
                                        (.binop "*" (.hole "op:and") (.lit (.int 100))))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Convert2Digits"
                                        [ (.unop "cast:u8" (.hole "op:arithmeticShiftRight"))
                                        , (.hole "cstr:pointer-arith") ]))
                                        (.ret (.lit (.int 9))))))))))))))))))
                    .skip)
                  (.seq
                    (.ifte
                      (.binop ">=" (.name "n") (.lit (.int 1000000)))
                      (.seq
                        .skip
                        (.seq
                          (.assign "prod" (.binop "*" (.name "n") (.lit (.int 281474978))))
                          (.seq
                            (.expr
                              (.call
                                "<operators>.assignmentArithmeticShiftRight"
                                [(.name "prod"), (.lit (.int 16))]))
                            (.seq
                              .skip
                              (.seq
                                (.assign
                                  "head_digits"
                                  (.unop "cast:u8" (.hole "op:arithmeticShiftRight")))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign
                                      "head_digit_count"
                                      (.call
                                        "ConvertHeadDigits"
                                        [(.name "head_digits"), (.name "buffer")]))
                                    (.seq
                                      (.hole "cstr:pointer-arith")
                                      (.seq
                                        (.assign
                                        "prod"
                                        (.binop "*" (.hole "op:and") (.lit (.int 100))))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Convert2Digits"
                                        [ (.unop "cast:u8" (.hole "op:arithmeticShiftRight"))
                                        , (.name "buffer") ]))
                                        (.seq
                                        (.assign
                                        "prod"
                                        (.binop "*" (.hole "op:and") (.lit (.int 100))))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Convert2Digits"
                                        [ (.unop "cast:u8" (.hole "op:arithmeticShiftRight"))
                                        , (.hole "cstr:pointer-arith") ]))
                                        (.seq
                                        (.assign
                                        "prod"
                                        (.binop "*" (.hole "op:and") (.lit (.int 100))))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Convert2Digits"
                                        [ (.unop "cast:u8" (.hole "op:arithmeticShiftRight"))
                                        , (.hole "cstr:pointer-arith") ]))
                                        (.ret
                                        (.binop "+" (.lit (.int 6)) (.name "head_digit_count")))))))))))))))))
                      .skip)
                    (.seq
                      (.ifte
                        (.binop ">=" (.name "n") (.lit (.int 10000)))
                        (.seq
                          .skip
                          (.seq
                            (.assign "prod" (.binop "*" (.name "n") (.lit (.int 429497))))
                            (.seq
                              .skip
                              (.seq
                                (.assign
                                  "head_digits"
                                  (.unop "cast:u8" (.hole "op:arithmeticShiftRight")))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign
                                      "head_digit_count"
                                      (.call
                                        "ConvertHeadDigits"
                                        [(.name "head_digits"), (.name "buffer")]))
                                    (.seq
                                      (.hole "cstr:pointer-arith")
                                      (.seq
                                        (.assign
                                        "prod"
                                        (.binop "*" (.hole "op:and") (.lit (.int 100))))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Convert2Digits"
                                        [ (.unop "cast:u8" (.hole "op:arithmeticShiftRight"))
                                        , (.name "buffer") ]))
                                        (.seq
                                        (.assign
                                        "prod"
                                        (.binop "*" (.hole "op:and") (.lit (.int 100))))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Convert2Digits"
                                        [ (.unop "cast:u8" (.hole "op:arithmeticShiftRight"))
                                        , (.hole "cstr:pointer-arith") ]))
                                        (.ret
                                        (.binop "+" (.lit (.int 4)) (.name "head_digit_count"))))))))))))))
                        .skip)
                      (.seq
                        (.ifte
                          (.binop ">=" (.name "n") (.lit (.int 100)))
                          (.seq
                            .skip
                            (.seq
                              (.assign "prod" (.binop "*" (.name "n") (.lit (.int 42949673))))
                              (.seq
                                .skip
                                (.seq
                                  (.assign
                                    "head_digits"
                                    (.unop "cast:u8" (.hole "op:arithmeticShiftRight")))
                                  (.seq
                                    .skip
                                    (.seq
                                      (.assign
                                        "head_digit_count"
                                        (.call
                                        "ConvertHeadDigits"
                                        [(.name "head_digits"), (.name "buffer")]))
                                      (.seq
                                        (.hole "cstr:pointer-arith")
                                        (.seq
                                        (.assign
                                        "prod"
                                        (.binop "*" (.hole "op:and") (.lit (.int 100))))
                                        (.seq
                                        (.expr
                                        (.call
                                        "Convert2Digits"
                                        [ (.unop "cast:u8" (.hole "op:arithmeticShiftRight"))
                                        , (.name "buffer") ]))
                                        (.ret
                                        (.binop "+" (.lit (.int 2)) (.name "head_digit_count"))))))))))))
                          .skip)
                        (.ret (.call "ConvertHeadDigits" [(.name "n"), (.name "buffer")]))))))))) }

/-- `v8.internal.SignificandToChars:uint8_t(uint64_t,char*)`  (from `conversions.cc`) -/
def f_v8_internal_SignificandToChars_uint8_t_uint64_t_char__ : Func :=
  { name := "v8.internal.SignificandToChars:uint8_t(uint64_t,char*)"
  , params := ["n", "buffer"]
  , body := (.seq
            (.expr (.call "DCHECK_LT" [(.name "n"), (.lit (.int 99999999999999999))]))
            (.ifte
              (.binop ">=" (.name "n") (.lit (.int 100000000)))
              (.seq
                .skip
                (.seq
                  (.assign
                    "first_block"
                    (.unop "cast:u32" (.binop "/" (.name "n") (.lit (.int 100000000)))))
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "second_block"
                        (.unop "cast:u32" (.binop "%" (.name "n") (.lit (.int 100000000)))))
                      (.seq
                        .skip
                        (.seq
                          (.assign
                            "first_block_digits"
                            (.call "ConvertUpTo9Digits" [(.name "first_block"), (.name "buffer")]))
                          (.seq
                            (.expr
                              (.call
                                "Convert8Digits"
                                [(.name "second_block"), (.hole "cstr:pointer-arith")]))
                            (.ret (.binop "+" (.name "first_block_digits") (.lit (.int 8)))))))))))
              (.ret (.call "ConvertUpTo9Digits" [(.unop "cast:u32" (.name "n")), (.name "buffer")])))) }

/-- `v8.internal.SimpleStringBuilder.<clinit>:v8.internal.SimpleStringBuilder()`  (from `conversions.cc`) -/
def f_v8_internal_SimpleStringBuilder__clinit__v8_internal_SimpleStringBuilder__ : Func :=
  { name := "v8.internal.SimpleStringBuilder.<clinit>:v8.internal.SimpleStringBuilder()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "<tmp>0" (.hole "op:alloc:ctor-unresolved-class"))
                (.seq (.expr (.call "ANY" [])) (.assign "buffer_" (.name "<tmp>0")))))) }

/-- `v8.internal.SimpleStringBuilder.__init__`  (from `conversions.cc`) -/
def f_v8_internal_SimpleStringBuilder___init__ : Func :=
  { name := "v8.internal.SimpleStringBuilder.__init__"
  , params := ["size"]
  , body := (.seq
            (.setField (.name "self") "buffer_" (.call "New" [(.name "size")]))
            (.setField (.name "self") "cursor_" (.mcall (.name "self") "buffer_" []))) }

/-- `v8.internal.SimpleStringBuilder.__init__`  (from `conversions.cc`) -/
def f_v8_internal_SimpleStringBuilder___init__' : Func :=
  { name := "v8.internal.SimpleStringBuilder.__init__"
  , params := ["buffer", "size"]
  , body := (.seq
            (.setField (.name "self") "buffer_" (.name "buffer"))
            (.setField (.name "self") "cursor_" (.name "buffer"))) }

/-- `v8.internal.SimpleStringBuilder.~SimpleStringBuilder:ANY()`  (from `conversions.cc`) -/
def f_v8_internal_SimpleStringBuilder__SimpleStringBuilder_ANY__ : Func :=
  { name := "v8.internal.SimpleStringBuilder.~SimpleStringBuilder:ANY()"
  , params := []
  , body := (.ifte
            (.call "V8_UNLIKELY" [(.unop "!" (.call "is_finalized" []))])
            (.expr (.call "v8.internal.SimpleStringBuilder.Finalize:char*()" []))
            .skip) }

/-- `v8.internal.SimpleStringBuilder.position:size_t()<const>`  (from `conversions.cc`) -/
def f_v8_internal_SimpleStringBuilder_position_size_t___const_ : Func :=
  { name := "v8.internal.SimpleStringBuilder.position:size_t()<const>"
  , params := []
  , body := (.seq
            (.expr (.call "DCHECK" [(.unop "!" (.call "is_finalized" []))]))
            (.ret (.hole "cstr:pointer-arith"))) }

/-- `v8.internal.SimpleStringBuilder.AddCharacter:void(char)`  (from `conversions.cc`) -/
def f_v8_internal_SimpleStringBuilder_AddCharacter_void_char_ : Func :=
  { name := "v8.internal.SimpleStringBuilder.AddCharacter:void(char)"
  , params := ["c"]
  , body := (.seq
            (.expr (.call "DCHECK_NE" [(.name "c"), (.lit (.str "\\0"))]))
            (.seq
              (.expr (.call "DCHECK" [(.unop "!" (.call "is_finalized" []))]))
              (.seq
                (.expr
                  (.call "DCHECK_LT" [(.call "position" []), (.mcall (.name "self") "buffer_" [])]))
                (.hole "assign:lhs:indirection")))) }

/-- `v8.internal.SimpleStringBuilder.AddString:void(char*,size_t)`  (from `conversions.cc`) -/
def f_v8_internal_SimpleStringBuilder_AddString_void_char__size_t_ : Func :=
  { name := "v8.internal.SimpleStringBuilder.AddString:void(char*,size_t)"
  , params := ["s", "len"]
  , body := (.seq
            (.expr (.call "DCHECK_EQ" [(.name "len"), (.call "strlen" [(.name "s")])]))
            (.expr (.call "AddSubstring" [(.name "s"), (.name "len")]))) }

/-- `v8.internal.SimpleStringBuilder.AddSubstring:void(char*,size_t)`  (from `conversions.cc`) -/
def f_v8_internal_SimpleStringBuilder_AddSubstring_void_char__size_t_ : Func :=
  { name := "v8.internal.SimpleStringBuilder.AddSubstring:void(char*,size_t)"
  , params := ["s", "n"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.call "DCHECK" [(.unop "!" (.call "is_finalized" []))]))
              (.seq
                (.expr
                  (.call
                    "DCHECK_LE"
                    [ (.binop "+" (.call "position" []) (.name "n"))
                    , (.mcall (.name "self") "buffer_" []) ]))
                (.seq
                  (.expr (.call "DCHECK_LE" [(.name "n"), (.call "strlen" [(.name "s")])]))
                  (.seq
                    (.expr
                      (.mcall
                        (.name "self")
                        "cursor_"
                        [ (.field (.name "self") "cursor_")
                        , (.name "s")
                        , (.binop "*" (.name "n") (.name "kCharSize")) ]))
                    (.hole "cstr:pointer-arith")))))) }

/-- `v8.internal.SimpleStringBuilder.AddPadding:void(char,int)`  (from `conversions.cc`) -/
def f_v8_internal_SimpleStringBuilder_AddPadding_void_char_int_ : Func :=
  { name := "v8.internal.SimpleStringBuilder.AddPadding:void(char,int)"
  , params := ["c", "count"]
  , body := (.seq
            (.expr (.call "DCHECK" [(.unop "!" (.call "is_finalized" []))]))
            (.seq
              (.expr
                (.call
                  "DCHECK_LE"
                  [ (.binop
                      "+"
                      (.call "position" [])
                      (.call "max" [(.lit (.int 0)), (.name "count")]))
                  , (.mcall (.name "self") "buffer_" []) ]))
              (.setField
                (.name "self")
                "cursor_"
                (.mcall
                  (.name "self")
                  "cursor_"
                  [(.field (.name "self") "cursor_"), (.name "count"), (.name "c")])))) }

/-- `v8.internal.SimpleStringBuilder.AddExponent:void(int)`  (from `conversions.cc`) -/
def f_v8_internal_SimpleStringBuilder_AddExponent_void_int_ : Func :=
  { name := "v8.internal.SimpleStringBuilder.AddExponent:void(int)"
  , params := ["value"]
  , body := (.seq
            (.expr (.call "DCHECK" [(.unop "!" (.call "is_finalized" []))]))
            (.seq
              (.expr (.call "DCHECK_GE" [(.name "value"), (.lit (.int 0))]))
              (.seq
                (.expr (.call "DCHECK_LE" [(.name "value"), (.lit (.int 999))]))
                (.ifte
                  (.binop ">=" (.name "value") (.lit (.int 100)))
                  (.seq
                    .skip
                    (.seq
                      (.assign "d1" (.hole "op:arithmeticShiftRight"))
                      (.seq
                        .skip
                        (.seq
                          (.assign
                            "d2"
                            (.binop
                              "-"
                              (.unop "cast:u32" (.name "value"))
                              (.binop "*" (.lit (.int 10)) (.name "d1"))))
                          (.seq
                            (.expr
                              (.call
                                "DCHECK_LT"
                                [ (.binop "+" (.call "position" []) (.lit (.int 2)))
                                , (.mcall (.name "self") "buffer_" []) ]))
                            (.seq
                              (.expr
                                (.call
                                  "Convert2Digits"
                                  [(.name "d1"), (.field (.name "self") "cursor_")]))
                              (.seq
                                (.hole "cstr:pointer-arith")
                                (.expr
                                  (.call "AddCharacter" [(.binop "+" (.lit (.int 0)) (.name "d2"))])))))))))
                  (.ifte
                    (.binop ">=" (.name "value") (.lit (.int 10)))
                    (.seq
                      (.expr
                        (.call
                          "DCHECK_LT"
                          [ (.binop "+" (.call "position" []) (.lit (.int 2)))
                          , (.mcall (.name "self") "buffer_" []) ]))
                      (.seq
                        (.expr
                          (.call
                            "Convert2Digits"
                            [(.name "value"), (.field (.name "self") "cursor_")]))
                        (.hole "cstr:pointer-arith")))
                    (.seq
                      (.expr (.call "DCHECK_LT" [(.name "value"), (.lit (.int 10))]))
                      (.expr
                        (.call
                          "v8.internal.SimpleStringBuilder.AddCharacter:void(char)"
                          [(.binop "+" (.lit (.int 0)) (.name "value"))])))))))) }

/-- `v8.internal.SimpleStringBuilder.Finalize:char*()`  (from `conversions.cc`) -/
def f_v8_internal_SimpleStringBuilder_Finalize_char___ : Func :=
  { name := "v8.internal.SimpleStringBuilder.Finalize:char*()"
  , params := []
  , body := (.seq
            (.expr (.call "DCHECK" [(.unop "!" (.call "is_finalized" []))]))
            (.seq
              (.expr
                (.call "DCHECK_LE" [(.call "position" []), (.mcall (.name "self") "buffer_" [])]))
              (.seq
                .skip
                (.seq
                  (.assign "ret" (.field (.name "self") "cursor_"))
                  (.seq
                    (.setField (.name "self") "cursor_" (.lit .unit))
                    (.seq (.expr (.call "DCHECK" [(.call "is_finalized" [])])) (.ret (.name "ret")))))))) }

/-- `v8.internal.SimpleStringBuilder.is_finalized:bool()<const>`  (from `conversions.cc`) -/
def f_v8_internal_SimpleStringBuilder_is_finalized_bool___const_ : Func :=
  { name := "v8.internal.SimpleStringBuilder.is_finalized:bool()<const>"
  , params := []
  , body := (.ret (.hole "cstr:address-equality")) }

/-- `v8.internal.JunkStringValue:double()`  (from `conversions.cc`) -/
def f_v8_internal_JunkStringValue_double__ : Func :=
  { name := "v8.internal.JunkStringValue:double()"
  , params := []
  , body := (.seq .skip (.ret (.call "bit_cast" [(.name "kQuietNaNMask")]))) }

/-- `v8.internal.SignedZero:double(bool)`  (from `conversions.cc`) -/
def f_v8_internal_SignedZero_double_bool_ : Func :=
  { name := "v8.internal.SignedZero:double(bool)"
  , params := ["negative"]
  , body := (.seq
            .skip
            (.ret
              (.cond
                (.name "negative")
                (.mcall
                  (.field (.name "base") "Double")
                  "kSignMask"
                  [(.field (.field (.name "base") "Double") "kSignMask")])
                (.hole "lit:float")))) }

/-- `v8.internal.isDigit:bool(int,int)`  (from `conversions.cc`) -/
def f_v8_internal_isDigit_bool_int_int_ : Func :=
  { name := "v8.internal.isDigit:bool(int,int)"
  , params := ["x", "radix"]
  , body := (.ret
            (.binop
              "||"
              (.binop
                "||"
                (.binop
                  "&&"
                  (.binop
                    "&&"
                    (.binop ">=" (.name "x") (.lit (.int 0)))
                    (.binop "<=" (.name "x") (.lit (.int 9))))
                  (.binop "<" (.name "x") (.binop "+" (.lit (.int 0)) (.name "radix"))))
                (.binop
                  "&&"
                  (.binop
                    "&&"
                    (.binop ">" (.name "radix") (.lit (.int 10)))
                    (.binop ">=" (.name "x") (.lit (.str "a"))))
                  (.binop
                    "<"
                    (.name "x")
                    (.binop "-" (.binop "+" (.lit (.str "a")) (.name "radix")) (.lit (.int 10))))))
              (.binop
                "&&"
                (.binop
                  "&&"
                  (.binop ">" (.name "radix") (.lit (.int 10)))
                  (.binop ">=" (.name "x") (.lit (.str "A"))))
                (.binop
                  "<"
                  (.name "x")
                  (.binop "-" (.binop "+" (.lit (.str "A")) (.name "radix")) (.lit (.int 10))))))) }

/-- `v8.internal.isBinaryDigit:bool(int)`  (from `conversions.cc`) -/
def f_v8_internal_isBinaryDigit_bool_int_ : Func :=
  { name := "v8.internal.isBinaryDigit:bool(int)"
  , params := ["x"]
  , body := (.ret
            (.binop
              "||"
              (.binop "==" (.name "x") (.lit (.int 0)))
              (.binop "==" (.name "x") (.lit (.int 1))))) }

/-- `v8.internal.SubStringEquals:bool(Char**,Char*,char*)`  (from `conversions.cc`) -/
def f_v8_internal_SubStringEquals_bool_Char___Char__char__ : Func :=
  { name := "v8.internal.SubStringEquals:bool(Char**,Char*,char*)"
  , params := ["current", "end", "substring"]
  , body := (.seq
            (.expr
              (.call
                "DCHECK"
                [(.binop "==" (.hole "op:indirection:pointer") (.hole "op:indirection:pointer"))]))
            (.seq
              (.hole "control:FOR")
              (.seq (.hole "op:preIncrement:pointer") (.ret (.lit (.bool true)))))) }

/-- `v8.internal.AdvanceToNonspace:bool(Char**,Char*)`  (from `conversions.cc`) -/
def f_v8_internal_AdvanceToNonspace_bool_Char___Char__ : Func :=
  { name := "v8.internal.AdvanceToNonspace:bool(Char**,Char*)"
  , params := ["current", "end"]
  , body := (.seq
            (.loop
              (.binop "!=" (.hole "op:indirection:pointer") (.name "end"))
              (.seq
                (.ifte
                  (.unop
                    "!"
                    (.call "IsWhiteSpaceOrLineTerminator" [(.hole "op:indirection:pointer")]))
                  (.ret (.lit (.bool true)))
                  .skip)
                (.hole "op:preIncrement:pointer")))
            (.ret (.lit (.bool false)))) }

/-- `v8.internal.InternalStringToIntDouble:double(Char*,Char*,bool,bool)`  (from `conversions.cc`) -/
def f_v8_internal_InternalStringToIntDouble_double_Char__Char__bool_bool_ : Func :=
  { name := "v8.internal.InternalStringToIntDouble:double(Char*,Char*,bool,bool)"
  , params := ["start", "end", "negative", "allow_trailing_junk"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.assign "current" (.name "start"))
                  (.seq
                    (.expr (.call "DCHECK_NE" [(.name "current"), (.name "end")]))
                    (.seq
                      (.loop
                        (.binop "==" (.hole "op:indirection:pointer") (.lit (.int 0)))
                        (.seq
                          (.hole "op:preIncrement:pointer")
                          (.ifte
                            (.binop "==" (.name "current") (.name "end"))
                            (.ret
                              (.call "v8.internal.SignedZero:double(bool)" [(.name "negative")]))
                            .skip)))
                      (.seq
                        .skip
                        (.seq
                          (.assign "number" (.lit (.int 0)))
                          (.seq
                            .skip
                            (.seq
                              (.assign "exponent" (.lit (.int 0)))
                              (.seq
                                .skip
                                (.seq
                                  (.assign "radix" (.hole "op:shiftLeft"))
                                  (.seq
                                    .skip
                                    (.seq
                                      (.assign
                                        "lim_0"
                                        (.binop
                                        "+"
                                        (.lit (.int 0))
                                        (.cond
                                        (.binop "<" (.name "radix") (.lit (.int 10)))
                                        (.name "radix")
                                        (.lit (.int 10)))))
                                      (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "lim_a"
                                        (.binop
                                        "+"
                                        (.lit (.str "a"))
                                        (.binop "-" (.name "radix") (.lit (.int 10)))))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "lim_A"
                                        (.binop
                                        "+"
                                        (.lit (.str "A"))
                                        (.binop "-" (.name "radix") (.lit (.int 10)))))
                                        (.seq
                                        (.loop
                                        (.hole "expr:BLOCK-prelude")
                                        (.expr (.binop "!=" (.name "current") (.name "end"))))
                                        (.seq
                                        (.expr
                                        (.call
                                        "DCHECK"
                                        [(.binop "<" (.name "number") (.hole "op:shiftLeft"))]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "DCHECK"
                                        [ (.binop
                                        "=="
                                        (.unop "cast:i64" (.hole "op:cast:scalar"))
                                        (.name "number")) ]))
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.name "exponent") (.lit (.int 0)))
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.name "negative") (.lit (.int 0)))
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.name "number") (.lit (.int 0)))
                                        (.ret (.unop "-" (.hole "lit:float")))
                                        .skip)
                                        (.assign "number" (.unop "-" (.name "number"))))
                                        .skip)
                                        (.ret (.hole "op:cast:scalar")))
                                        .skip)
                                        (.seq
                                        (.expr
                                        (.call "DCHECK_NE" [(.name "number"), (.lit (.int 0))]))
                                        (.ret
                                        (.call
                                        "ldexp"
                                        [(.hole "op:cast:scalar"), (.name "exponent")]))))))))))))))))))))))))) }

/-- `v8.internal.StringToIntHelper.<clinit>:v8.internal.StringToIntHelper()`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper__clinit__v8_internal_StringToIntHelper__ : Func :=
  { name := "v8.internal.StringToIntHelper.<clinit>:v8.internal.StringToIntHelper()"
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
                                        (.seq
                                        (.assign "<tmp>0" (.hole "op:alloc:ctor-unresolved-class"))
                                        (.seq
                                        (.expr (.call "ANY" []))
                                        (.assign "subject_" (.name "<tmp>0"))))
                                        (.seq
                                        (.assign "raw_one_byte_subject_" (.lit .unit))
                                        (.seq
                                        (.assign "raw_two_byte_subject_" (.lit .unit))
                                        (.seq
                                        (.assign "radix_" (.lit (.int 0)))
                                        (.seq
                                        (.assign "cursor_" (.lit (.int 0)))
                                        (.seq
                                        (.assign "length_" (.lit (.int 0)))
                                        (.seq
                                        (.assign "sign_" (.field (.name "Sign") "kNone"))
                                        (.seq
                                        (.assign "leading_zero_" (.lit (.bool false)))
                                        (.seq
                                        (.assign
                                        "allow_binary_and_octal_prefixes_"
                                        (.lit (.bool false)))
                                        (.seq
                                        (.assign "allow_trailing_junk_" (.lit (.bool true)))
                                        (.assign "state_" (.field (.name "State") "kRunning")))))))))))))))))))))))))) }

/-- `v8.internal.StringToIntHelper.__init__`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper___init__ : Func :=
  { name := "v8.internal.StringToIntHelper.__init__"
  , params := ["subject", "radix"]
  , body := (.seq
            (.expr (.call "DCHECK" [(.call "IsFlat" [])]))
            (.seq
              (.setField (.name "self") "subject_" (.name "subject"))
              (.setField (.name "self") "radix_" (.name "radix")))) }

/-- `v8.internal.StringToIntHelper.__init__`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper___init__' : Func :=
  { name := "v8.internal.StringToIntHelper.__init__"
  , params := ["subject", "radix", "length"]
  , body := (.seq
            (.setField (.name "self") "raw_one_byte_subject_" (.name "subject"))
            (.seq
              (.setField (.name "self") "radix_" (.name "radix"))
              (.setField (.name "self") "length_" (.name "length")))) }

/-- `v8.internal.StringToIntHelper.__init__`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper___init__'' : Func :=
  { name := "v8.internal.StringToIntHelper.__init__"
  , params := ["subject", "radix", "length"]
  , body := (.seq
            (.setField (.name "self") "raw_two_byte_subject_" (.name "subject"))
            (.seq
              (.setField (.name "self") "radix_" (.name "radix"))
              (.setField (.name "self") "length_" (.name "length")))) }

/-- `v8.internal.StringToIntHelper.__init__`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper___init__''' : Func :=
  { name := "v8.internal.StringToIntHelper.__init__"
  , params := ["subject"]
  , body := (.seq
            (.expr (.call "DCHECK" [(.call "IsFlat" [])]))
            (.setField (.name "self") "subject_" (.name "subject"))) }

/-- `v8.internal.StringToIntHelper.__init__`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper___init__'''' : Func :=
  { name := "v8.internal.StringToIntHelper.__init__"
  , params := ["subject", "length"]
  , body := (.seq
            (.setField (.name "self") "raw_one_byte_subject_" (.name "subject"))
            (.setField (.name "self") "length_" (.name "length"))) }

/-- `v8.internal.StringToIntHelper.~StringToIntHelper:ANY()`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper__StringToIntHelper_ANY__ : Func :=
  { name := "v8.internal.StringToIntHelper.~StringToIntHelper:ANY()"
  , params := []
  , body := .skip }

/-- `v8.internal.StringToIntHelper.set_allow_binary_and_octal_prefixes:void()`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper_set_allow_binary_and_octal_prefixes_void__ : Func :=
  { name := "v8.internal.StringToIntHelper.set_allow_binary_and_octal_prefixes:void()"
  , params := []
  , body := (.setField (.name "self") "allow_binary_and_octal_prefixes_" (.lit (.bool true))) }

/-- `v8.internal.StringToIntHelper.set_disallow_trailing_junk:void()`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper_set_disallow_trailing_junk_void__ : Func :=
  { name := "v8.internal.StringToIntHelper.set_disallow_trailing_junk:void()"
  , params := []
  , body := (.setField (.name "self") "allow_trailing_junk_" (.lit (.bool false))) }

/-- `v8.internal.StringToIntHelper.allow_trailing_junk:bool()`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper_allow_trailing_junk_bool__ : Func :=
  { name := "v8.internal.StringToIntHelper.allow_trailing_junk:bool()"
  , params := []
  , body := (.ret (.field (.name "self") "allow_trailing_junk_")) }

/-- `v8.internal.StringToIntHelper.IsOneByte:bool()<const>`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper_IsOneByte_bool___const_ : Func :=
  { name := "v8.internal.StringToIntHelper.IsOneByte:bool()<const>"
  , params := []
  , body := (.seq
            (.ifte
              (.binop "!=" (.field (.name "self") "raw_two_byte_subject_") (.lit .unit))
              (.ret (.lit (.bool false)))
              .skip)
            (.ret
              (.binop
                "||"
                (.binop "!=" (.field (.name "self") "raw_one_byte_subject_") (.lit .unit))
                (.call "IsOneByteRepresentationUnderneath" [(.hole "op:indirection:opaque-type")])))) }

/-- `v8.internal.StringToIntHelper.radix:int()`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper_radix_int__ : Func :=
  { name := "v8.internal.StringToIntHelper.radix:int()"
  , params := []
  , body := (.ret (.field (.name "self") "radix_")) }

/-- `v8.internal.StringToIntHelper.cursor:size_t()`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper_cursor_size_t__ : Func :=
  { name := "v8.internal.StringToIntHelper.cursor:size_t()"
  , params := []
  , body := (.ret (.field (.name "self") "cursor_")) }

/-- `v8.internal.StringToIntHelper.length:size_t()`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper_length_size_t__ : Func :=
  { name := "v8.internal.StringToIntHelper.length:size_t()"
  , params := []
  , body := (.ret (.field (.name "self") "length_")) }

/-- `v8.internal.StringToIntHelper.negative:bool()`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper_negative_bool__ : Func :=
  { name := "v8.internal.StringToIntHelper.negative:bool()"
  , params := []
  , body := (.seq
            .skip
            (.ret (.binop "==" (.field (.name "self") "sign_") (.field (.name "Sign") "kNegative")))) }

/-- `v8.internal.StringToIntHelper.sign:v8.internal..Sign()`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper_sign_v8_internal__Sign__ : Func :=
  { name := "v8.internal.StringToIntHelper.sign:v8.internal..Sign()"
  , params := []
  , body := (.ret (.field (.name "self") "sign_")) }

/-- `v8.internal.StringToIntHelper.state:v8.internal..State()`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper_state_v8_internal__State__ : Func :=
  { name := "v8.internal.StringToIntHelper.state:v8.internal..State()"
  , params := []
  , body := (.ret (.field (.name "self") "state_")) }

/-- `v8.internal.StringToIntHelper.set_state:void(v8.internal.State)`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper_set_state_void_v8_internal_State_ : Func :=
  { name := "v8.internal.StringToIntHelper.set_state:void(v8.internal.State)"
  , params := ["state"]
  , body := (.setField (.name "self") "state_" (.name "state")) }

/-- `v8.internal.StringToIntHelper.ParseInt:void()`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper_ParseInt_void__ : Func :=
  { name := "v8.internal.StringToIntHelper.ParseInt:void()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              .skip
              (.ifte
                (.call "IsOneByte" [])
                (.seq
                  .skip
                  (.seq
                    (.assign "vector" (.call "GetOneByteVector" [(.name "no_gc")]))
                    (.seq
                      (.expr (.call "DetectRadixInternal" [(.call "begin" []), (.call "size" [])]))
                      (.seq
                        (.ifte
                          (.binop
                            "!="
                            (.field (.name "self") "state_")
                            (.field (.name "State") "kRunning"))
                          (.ret (.lit .unit))
                          .skip)
                        (.expr (.call "ParseOneByte" [(.call "begin" [])]))))))
                (.seq
                  .skip
                  (.seq
                    (.assign "vector" (.call "GetTwoByteVector" [(.name "no_gc")]))
                    (.seq
                      (.expr (.call "DetectRadixInternal" [(.call "begin" []), (.call "size" [])]))
                      (.seq
                        (.ifte
                          (.binop
                            "!="
                            (.field (.name "self") "state_")
                            (.field (.name "State") "kRunning"))
                          (.ret (.lit .unit))
                          .skip)
                        (.expr (.call "ParseTwoByte" [(.call "begin" [])]))))))))) }

/-- `v8.internal.StringToIntHelper.DetectRadixInternal:void(Char*,size_t)`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper_DetectRadixInternal_void_Char__size_t_ : Func :=
  { name := "v8.internal.StringToIntHelper.DetectRadixInternal:void(Char*,size_t)"
  , params := ["current", "length"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.assign "start" (.name "current"))
                  (.seq
                    (.setField (.name "self") "length_" (.name "length"))
                    (.seq
                      .skip
                      (.seq
                        (.assign "end" (.binop "+" (.name "start") (.name "length")))
                        (.seq
                          (.ifte
                            (.unop
                              "!"
                              (.call
                                "AdvanceToNonspace"
                                [(.hole "op:addressOf:local:pointer"), (.name "end")]))
                            (.ret
                              (.mcall (.name "State") "kEmpty" [(.field (.name "State") "kEmpty")]))
                            .skip)
                          (.seq
                            (.ifte
                              (.binop "==" (.hole "op:indirection:pointer") (.lit (.str "+")))
                              (.seq
                                (.hole "op:preIncrement:pointer")
                                (.seq
                                  (.ifte
                                    (.binop "==" (.name "current") (.name "end"))
                                    (.ret
                                      (.mcall
                                        (.name "State")
                                        "kJunk"
                                        [(.field (.name "State") "kJunk")]))
                                    .skip)
                                  (.setField
                                    (.name "self")
                                    "sign_"
                                    (.field (.name "Sign") "kPositive"))))
                              (.ifte
                                (.binop "==" (.hole "op:indirection:pointer") (.lit (.str "-")))
                                (.seq
                                  (.hole "op:preIncrement:pointer")
                                  (.seq
                                    (.ifte
                                      (.binop "==" (.name "current") (.name "end"))
                                      (.ret
                                        (.mcall
                                        (.name "State")
                                        "kJunk"
                                        [(.field (.name "State") "kJunk")]))
                                      .skip)
                                    (.setField
                                      (.name "self")
                                      "sign_"
                                      (.field (.name "Sign") "kNegative"))))
                                .skip))
                            (.seq
                              (.ifte
                                (.binop "==" (.field (.name "self") "radix_") (.lit (.int 0)))
                                (.seq
                                  (.setField (.name "self") "radix_" (.lit (.int 10)))
                                  (.ifte
                                    (.binop "==" (.hole "op:indirection:pointer") (.lit (.int 0)))
                                    (.seq
                                      (.hole "op:preIncrement:pointer")
                                      (.seq
                                        (.ifte
                                        (.binop "==" (.name "current") (.name "end"))
                                        (.ret
                                        (.mcall
                                        (.name "State")
                                        "kZero"
                                        [(.field (.name "State") "kZero")]))
                                        .skip)
                                        (.ifte
                                        (.binop
                                        "||"
                                        (.binop
                                        "=="
                                        (.hole "op:indirection:pointer")
                                        (.lit (.str "x")))
                                        (.binop
                                        "=="
                                        (.hole "op:indirection:pointer")
                                        (.lit (.str "X"))))
                                        (.seq
                                        (.setField (.name "self") "radix_" (.lit (.int 16)))
                                        (.seq
                                        (.hole "op:preIncrement:pointer")
                                        (.ifte
                                        (.binop "==" (.name "current") (.name "end"))
                                        (.ret
                                        (.mcall
                                        (.name "State")
                                        "kJunk"
                                        [(.field (.name "State") "kJunk")]))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.field (.name "self") "allow_binary_and_octal_prefixes_")
                                        (.binop
                                        "||"
                                        (.binop
                                        "=="
                                        (.hole "op:indirection:pointer")
                                        (.lit (.str "o")))
                                        (.binop
                                        "=="
                                        (.hole "op:indirection:pointer")
                                        (.lit (.str "O")))))
                                        (.seq
                                        (.setField (.name "self") "radix_" (.lit (.int 8)))
                                        (.seq
                                        (.hole "op:preIncrement:pointer")
                                        (.ifte
                                        (.binop "==" (.name "current") (.name "end"))
                                        (.ret
                                        (.mcall
                                        (.name "State")
                                        "kJunk"
                                        [(.field (.name "State") "kJunk")]))
                                        .skip)))
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.field (.name "self") "allow_binary_and_octal_prefixes_")
                                        (.binop
                                        "||"
                                        (.binop
                                        "=="
                                        (.hole "op:indirection:pointer")
                                        (.lit (.str "b")))
                                        (.binop
                                        "=="
                                        (.hole "op:indirection:pointer")
                                        (.lit (.str "B")))))
                                        (.seq
                                        (.setField (.name "self") "radix_" (.lit (.int 2)))
                                        (.seq
                                        (.hole "op:preIncrement:pointer")
                                        (.ifte
                                        (.binop "==" (.name "current") (.name "end"))
                                        (.ret
                                        (.mcall
                                        (.name "State")
                                        "kJunk"
                                        [(.field (.name "State") "kJunk")]))
                                        .skip)))
                                        (.setField
                                        (.name "self")
                                        "leading_zero_"
                                        (.lit (.bool true))))))))
                                    .skip))
                                (.ifte
                                  (.binop "==" (.field (.name "self") "radix_") (.lit (.int 16)))
                                  (.ifte
                                    (.binop "==" (.hole "op:indirection:pointer") (.lit (.int 0)))
                                    (.seq
                                      (.hole "op:preIncrement:pointer")
                                      (.seq
                                        (.ifte
                                        (.binop "==" (.name "current") (.name "end"))
                                        (.ret
                                        (.mcall
                                        (.name "State")
                                        "kZero"
                                        [(.field (.name "State") "kZero")]))
                                        .skip)
                                        (.ifte
                                        (.binop
                                        "||"
                                        (.binop
                                        "=="
                                        (.hole "op:indirection:pointer")
                                        (.lit (.str "x")))
                                        (.binop
                                        "=="
                                        (.hole "op:indirection:pointer")
                                        (.lit (.str "X"))))
                                        (.seq
                                        (.hole "op:preIncrement:pointer")
                                        (.ifte
                                        (.binop "==" (.name "current") (.name "end"))
                                        (.ret
                                        (.mcall
                                        (.name "State")
                                        "kJunk"
                                        [(.field (.name "State") "kJunk")]))
                                        .skip))
                                        (.setField
                                        (.name "self")
                                        "leading_zero_"
                                        (.lit (.bool true))))))
                                    .skip)
                                  .skip))
                              (.seq
                                (.loop
                                  (.binop "==" (.hole "op:indirection:pointer") (.lit (.int 0)))
                                  (.seq
                                    (.setField (.name "self") "leading_zero_" (.lit (.bool true)))
                                    (.seq
                                      (.hole "op:preIncrement:pointer")
                                      (.ifte
                                        (.binop "==" (.name "current") (.name "end"))
                                        (.ret
                                        (.mcall
                                        (.name "State")
                                        "kZero"
                                        [(.field (.name "State") "kZero")]))
                                        .skip))))
                                (.seq
                                  (.ifte
                                    (.binop
                                      "&&"
                                      (.binop
                                        "&&"
                                        (.field (.name "self") "leading_zero_")
                                        (.field (.name "self") "allow_trailing_junk_"))
                                      (.unop
                                        "!"
                                        (.call
                                        "isDigit"
                                        [ (.hole "op:indirection:pointer")
                                        , (.field (.name "self") "radix_") ])))
                                    (.ret
                                      (.mcall
                                        (.name "State")
                                        "kZero"
                                        [(.field (.name "State") "kZero")]))
                                    .skip)
                                  (.seq
                                    (.ifte
                                      (.binop
                                        "&&"
                                        (.unop "!" (.field (.name "self") "leading_zero_"))
                                        (.unop
                                        "!"
                                        (.call
                                        "isDigit"
                                        [ (.hole "op:indirection:pointer")
                                        , (.field (.name "self") "radix_") ])))
                                      (.ret
                                        (.mcall
                                        (.name "State")
                                        "kJunk"
                                        [(.field (.name "State") "kJunk")]))
                                      .skip)
                                    (.seq
                                      (.expr
                                        (.call
                                        "DCHECK"
                                        [ (.binop
                                        "&&"
                                        (.binop
                                        ">="
                                        (.field (.name "self") "radix_")
                                        (.lit (.int 2)))
                                        (.binop
                                        "<="
                                        (.field (.name "self") "radix_")
                                        (.lit (.int 36)))) ]))
                                      (.setField
                                        (.name "self")
                                        "cursor_"
                                        (.binop "-" (.name "current") (.name "start"))))))))))))))))) }

/-- `v8.internal.NumberParseIntHelper.<clinit>:v8.internal.NumberParseIntHelper()`  (from `conversions.cc`) -/
def f_v8_internal_NumberParseIntHelper__clinit__v8_internal_NumberParseIntHelper__ : Func :=
  { name := "v8.internal.NumberParseIntHelper.<clinit>:v8.internal.NumberParseIntHelper()"
  , params := []
  , body := (.seq .skip (.assign "result_" (.lit (.int 0)))) }

/-- `v8.internal.NumberParseIntHelper.__init__`  (from `conversions.cc`) -/
def f_v8_internal_NumberParseIntHelper___init__ : Func :=
  { name := "v8.internal.NumberParseIntHelper.__init__"
  , params := ["string", "radix"]
  , body := (.setField (.name "self") "StringToIntHelper" (.name "string")) }

/-- `v8.internal.NumberParseIntHelper.__init__`  (from `conversions.cc`) -/
def f_v8_internal_NumberParseIntHelper___init__' : Func :=
  { name := "v8.internal.NumberParseIntHelper.__init__"
  , params := ["string", "radix", "length"]
  , body := (.setField (.name "self") "StringToIntHelper" (.name "string")) }

/-- `v8.internal.NumberParseIntHelper.__init__`  (from `conversions.cc`) -/
def f_v8_internal_NumberParseIntHelper___init__'' : Func :=
  { name := "v8.internal.NumberParseIntHelper.__init__"
  , params := ["string", "radix", "length"]
  , body := (.setField (.name "self") "StringToIntHelper" (.name "string")) }

/-- `v8.internal.NumberParseIntHelper.ParseInternal:void(Char*)`  (from `conversions.cc`) -/
def f_v8_internal_NumberParseIntHelper_ParseInternal_void_Char__ : Func :=
  { name := "v8.internal.NumberParseIntHelper.ParseInternal:void(Char*)"
  , params := ["start"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "current" (.binop "+" (.name "start") (.call "cursor" [])))
                (.seq
                  .skip
                  (.seq
                    (.assign "end" (.binop "+" (.name "start") (.call "length" [])))
                    (.seq
                      (.ifte
                        (.binop
                          "=="
                          (.call "v8.internal.StringToIntHelper.radix:int()" [])
                          (.lit (.int 10)))
                        (.ret (.call "HandleBaseTenCase" [(.name "current"), (.name "end")]))
                        .skip)
                      (.seq
                        (.ifte
                          (.call
                            "IsPowerOfTwo"
                            [(.call "v8.internal.StringToIntHelper.radix:int()" [])])
                          (.seq
                            (.setField
                              (.name "self")
                              "result_"
                              (.call "HandlePowerOfTwoCase" [(.name "current"), (.name "end")]))
                            (.seq
                              (.expr
                                (.mcall (.name "State") "kDone" [(.field (.name "State") "kDone")]))
                              (.ret (.lit .unit))))
                          .skip)
                        (.ret (.call "HandleGenericCase" [(.name "current"), (.name "end")]))))))))) }

/-- `v8.internal.NumberParseIntHelper.ParseOneByte:void(uint8_t*)`  (from `conversions.cc`) -/
def f_v8_internal_NumberParseIntHelper_ParseOneByte_void_uint8_t__ : Func :=
  { name := "v8.internal.NumberParseIntHelper.ParseOneByte:void(uint8_t*)"
  , params := ["start"]
  , body := (.ret (.call "ParseInternal" [(.name "start")])) }

/-- `v8.internal.NumberParseIntHelper.ParseTwoByte:void(base.uc16*)`  (from `conversions.cc`) -/
def f_v8_internal_NumberParseIntHelper_ParseTwoByte_void_base_uc16__ : Func :=
  { name := "v8.internal.NumberParseIntHelper.ParseTwoByte:void(base.uc16*)"
  , params := ["start"]
  , body := (.ret (.call "ParseInternal" [(.name "start")])) }

/-- `v8.internal.NumberParseIntHelper.GetResult:double()`  (from `conversions.cc`) -/
def f_v8_internal_NumberParseIntHelper_GetResult_double__ : Func :=
  { name := "v8.internal.NumberParseIntHelper.GetResult:double()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              (.expr (.call "v8.internal.StringToIntHelper.ParseInt:void()" []))
              (.seq (.hole "control:SWITCH") (.expr (.call "UNREACHABLE" []))))) }

/-- `v8.internal.NumberParseIntHelper.HandlePowerOfTwoCase:double(Char*,Char*)`  (from `conversions.cc`) -/
def f_v8_internal_NumberParseIntHelper_HandlePowerOfTwoCase_double_Char__Char__ : Func :=
  { name := "v8.internal.NumberParseIntHelper.HandlePowerOfTwoCase:double(Char*,Char*)"
  , params := ["current", "end"]
  , body := (.seq
            .skip
            (.seq
              (.assign "allow_trailing_junk" (.lit (.bool true)))
              (.seq .skip (.seq (.assign "negative" (.lit (.bool false))) (.hole "control:SWITCH"))))) }

/-- `v8.internal.NumberParseIntHelper.HandleBaseTenCase:void(Char*,Char*)`  (from `conversions.cc`) -/
def f_v8_internal_NumberParseIntHelper_HandleBaseTenCase_void_Char__Char__ : Func :=
  { name := "v8.internal.NumberParseIntHelper.HandleBaseTenCase:void(Char*,Char*)"
  , params := ["current", "end"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.assign "kMaxSignificantDigits" (.lit (.int 309)))
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "kBufferSize"
                        (.binop "+" (.name "kMaxSignificantDigits") (.lit (.int 2))))
                      (.seq
                        .skip
                        (.seq
                          (.assign "buffer" (.hole "op:alloc:array-decl"))
                          (.seq
                            .skip
                            (.seq
                              (.assign "buffer_pos" (.lit (.int 0)))
                              (.seq
                                (.loop
                                  (.binop
                                    "&&"
                                    (.binop ">=" (.hole "op:indirection:pointer") (.lit (.int 0)))
                                    (.binop "<=" (.hole "op:indirection:pointer") (.lit (.int 9))))
                                  (.seq
                                    (.ifte
                                      (.binop
                                        "<="
                                        (.name "buffer_pos")
                                        (.name "kMaxSignificantDigits"))
                                      (.seq
                                        (.expr (.lit .unit))
                                        (.setIndex
                                        (.name "buffer")
                                        (.hole "op:postIncrement:value")
                                        (.hole "op:cast:scalar")))
                                      .skip)
                                    (.seq
                                      (.hole "op:preIncrement:pointer")
                                      (.ifte
                                        (.binop "==" (.name "current") (.name "end"))
                                        .brk
                                        .skip))))
                                (.seq
                                  (.expr
                                    (.call
                                      "SLOW_DCHECK"
                                      [(.binop "<" (.name "buffer_pos") (.name "kBufferSize"))]))
                                  (.seq
                                    (.setIndex
                                      (.name "buffer")
                                      (.name "buffer_pos")
                                      (.lit (.str "\\0")))
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign
                                        "buffer_vector"
                                        (.alloc "Vector" [(.name "buffer"), (.name "buffer_pos")]))
                                        (.seq
                                        (.setField
                                        (.name "self")
                                        "result_"
                                        (.call "Strtod" [(.name "buffer_vector"), (.lit (.int 0))]))
                                        (.expr
                                        (.mcall
                                        (.name "State")
                                        "kDone"
                                        [(.field (.name "State") "kDone")])))))))))))))))))) }

/-- `v8.internal.NumberParseIntHelper.HandleGenericCase:void(Char*,Char*)`  (from `conversions.cc`) -/
def f_v8_internal_NumberParseIntHelper_HandleGenericCase_void_Char__Char__ : Func :=
  { name := "v8.internal.NumberParseIntHelper.HandleGenericCase:void(Char*,Char*)"
  , params := ["current", "end"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.assign
                    "lim_0"
                    (.binop
                      "+"
                      (.lit (.int 0))
                      (.cond
                        (.binop
                          "<"
                          (.call "v8.internal.StringToIntHelper.radix:int()" [])
                          (.lit (.int 10)))
                        (.call "v8.internal.StringToIntHelper.radix:int()" [])
                        (.lit (.int 10)))))
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "lim_a"
                        (.binop
                          "+"
                          (.lit (.str "a"))
                          (.binop
                            "-"
                            (.call "v8.internal.StringToIntHelper.radix:int()" [])
                            (.lit (.int 10)))))
                      (.seq
                        .skip
                        (.seq
                          (.assign
                            "lim_A"
                            (.binop
                              "+"
                              (.lit (.str "A"))
                              (.binop
                                "-"
                                (.call "v8.internal.StringToIntHelper.radix:int()" [])
                                (.lit (.int 10)))))
                          (.seq
                            .skip
                            (.seq
                              (.assign "done" (.lit (.bool false)))
                              (.seq
                                (.loop
                                  (.hole "expr:BLOCK-impure")
                                  (.expr (.unop "!" (.name "done"))))
                                (.seq
                                  (.ifte
                                    (.binop
                                      "&&"
                                      (.unop
                                        "!"
                                        (.call
                                        "v8.internal.StringToIntHelper.allow_trailing_junk:bool()"
                                        []))
                                      (.call
                                        "AdvanceToNonspace"
                                        [(.hole "op:addressOf:local:pointer"), (.name "end")]))
                                    (.ret
                                      (.mcall
                                        (.name "State")
                                        "kJunk"
                                        [(.field (.name "State") "kJunk")]))
                                    .skip)
                                  (.ret
                                    (.mcall
                                      (.name "State")
                                      "kDone"
                                      [(.field (.name "State") "kDone")])))))))))))))) }

/-- `v8.internal.InternalStringToDouble:double(Char*,Char*,v8.internal.ConversionFlag,double)`  (from `conversions.cc`) -/
def f_v8_internal_InternalStringToDouble_double_Char__Char__v8_internal_ConversionFlag_double_ : Func :=
  { name := "v8.internal.InternalStringToDouble:double(Char*,Char*,v8.internal.ConversionFlag,double)"
  , params := ["current", "end", "flag", "empty_string_val"]
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
                          (.unop
                            "!"
                            (.call
                              "AdvanceToNonspace"
                              [(.hole "op:addressOf:local:pointer"), (.name "end")]))
                          (.ret (.name "empty_string_val"))
                          .skip)
                        (.seq
                          (.ifte
                            (.binop "==" (.name "flag") (.name "ALLOW_NON_DECIMAL_PREFIX"))
                            (.seq
                              .skip
                              (.seq
                                (.assign "prefixed" (.name "current"))
                                (.ifte
                                  (.binop "==" (.hole "op:indirection:pointer") (.lit (.int 0)))
                                  (.seq
                                    (.hole "op:preIncrement:pointer")
                                    (.seq
                                      (.ifte
                                        (.binop "==" (.name "prefixed") (.name "end"))
                                        (.ret (.lit (.int 0)))
                                        .skip)
                                      (.ifte
                                        (.binop
                                        "||"
                                        (.binop
                                        "=="
                                        (.hole "op:indirection:pointer")
                                        (.lit (.str "x")))
                                        (.binop
                                        "=="
                                        (.hole "op:indirection:pointer")
                                        (.lit (.str "X"))))
                                        (.seq
                                        (.hole "op:preIncrement:pointer")
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.name "prefixed") (.name "end"))
                                        (.ret (.call "v8.internal.JunkStringValue:double()" []))
                                        .skip)
                                        (.ret
                                        (.call
                                        "InternalStringToIntDouble<4>"
                                        [ (.name "prefixed")
                                        , (.name "end")
                                        , (.lit (.bool false))
                                        , (.lit (.bool false)) ]))))
                                        (.ifte
                                        (.binop
                                        "||"
                                        (.binop
                                        "=="
                                        (.hole "op:indirection:pointer")
                                        (.lit (.str "o")))
                                        (.binop
                                        "=="
                                        (.hole "op:indirection:pointer")
                                        (.lit (.str "O"))))
                                        (.seq
                                        (.hole "op:preIncrement:pointer")
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.name "prefixed") (.name "end"))
                                        (.ret (.call "v8.internal.JunkStringValue:double()" []))
                                        .skip)
                                        (.ret
                                        (.call
                                        "InternalStringToIntDouble<3>"
                                        [ (.name "prefixed")
                                        , (.name "end")
                                        , (.lit (.bool false))
                                        , (.lit (.bool false)) ]))))
                                        (.ifte
                                        (.binop
                                        "||"
                                        (.binop
                                        "=="
                                        (.hole "op:indirection:pointer")
                                        (.lit (.str "b")))
                                        (.binop
                                        "=="
                                        (.hole "op:indirection:pointer")
                                        (.lit (.str "B"))))
                                        (.seq
                                        (.hole "op:preIncrement:pointer")
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.name "prefixed") (.name "end"))
                                        (.ret (.call "v8.internal.JunkStringValue:double()" []))
                                        .skip)
                                        (.ret
                                        (.call
                                        "InternalStringToIntDouble<1>"
                                        [ (.name "prefixed")
                                        , (.name "end")
                                        , (.lit (.bool false))
                                        , (.lit (.bool false)) ]))))
                                        .skip)))))
                                  .skip)))
                            .skip)
                          (.seq
                            .skip
                            (.seq
                              (.assign
                                "allow_trailing_junk"
                                (.binop "==" (.name "flag") (.name "ALLOW_TRAILING_JUNK")))
                              (.seq
                                .skip
                                (.seq
                                  (.hole "stmt:TYPE_DECL")
                                  (.seq
                                    (.expr (.lit .unit))
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign "current_uc" (.hole "op:cast:pointer"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "end_uc" (.hole "op:cast:pointer"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "ret"
                                        (.call
                                        "from_chars"
                                        [ (.name "current_uc")
                                        , (.name "end_uc")
                                        , (.name "value")
                                        , (.hole "op:cast:opaque-type") ]))
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.field (.name "ret") "ptr") (.name "end_uc"))
                                        (.ret (.name "value"))
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.binop
                                        ">"
                                        (.field (.name "ret") "ptr")
                                        (.name "current_uc"))
                                        (.seq
                                        (.assign "current" (.hole "op:cast:pointer"))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.unop "!" (.name "allow_trailing_junk"))
                                        (.call
                                        "AdvanceToNonspace"
                                        [(.hole "op:addressOf:local:pointer"), (.name "end")]))
                                        (.ret (.call "v8.internal.JunkStringValue:double()" []))
                                        .skip)
                                        (.ret (.name "value"))))
                                        .skip)
                                        (.seq
                                        (.expr
                                        (.mcall
                                        (.name "ret")
                                        "ptr"
                                        [(.field (.name "ret") "ptr"), (.name "current_uc")]))
                                        (.seq
                                        (.expr
                                        (.call "DCHECK_NE" [(.name "current"), (.name "end")]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "kInfinityString" (.lit (.str "Infinity")))
                                        (.hole "control:SWITCH")))))))))))))))))))))))))) }

/-- `v8.internal.StringToDouble:double(char*,v8.internal.ConversionFlag,double)`  (from `conversions.cc`) -/
def f_v8_internal_StringToDouble_double_char__v8_internal_ConversionFlag_double_ : Func :=
  { name := "v8.internal.StringToDouble:double(char*,v8.internal.ConversionFlag,double)"
  , params := ["str", "flags", "empty_string_val"]
  , body := (.ret
            (.call
              "StringToDouble"
              [(.call "OneByteVector" [(.name "str")]), (.name "flags"), (.name "empty_string_val")])) }

/-- `v8.internal.StringToDouble:double(base.Vector,v8.internal.ConversionFlag,double)`  (from `conversions.cc`) -/
def f_v8_internal_StringToDouble_double_base_Vector_v8_internal_ConversionFlag_double_ : Func :=
  { name := "v8.internal.StringToDouble:double(base.Vector,v8.internal.ConversionFlag,double)"
  , params := ["str", "flags", "empty_string_val"]
  , body := (.ret
            (.call
              "InternalStringToDouble"
              [(.call "begin" []), (.call "end" []), (.name "flags"), (.name "empty_string_val")])) }

/-- `StringToDouble:double(base.Vector,v8.internal.ConversionFlag,double)`  (from `conversions.cc`) -/
def f_StringToDouble_double_base_Vector_v8_internal_ConversionFlag_double_ : Func :=
  { name := "StringToDouble:double(base.Vector,v8.internal.ConversionFlag,double)"
  , params := ["str", "flags", "empty_string_val"]
  , body := (.ret
            (.call
              "InternalStringToDouble"
              [(.call "begin" []), (.call "end" []), (.name "flags"), (.name "empty_string_val")])) }

/-- `v8.internal.BinaryStringToDouble:double(base.Vector)`  (from `conversions.cc`) -/
def f_v8_internal_BinaryStringToDouble_double_base_Vector_ : Func :=
  { name := "v8.internal.BinaryStringToDouble:double(base.Vector)"
  , params := ["str"]
  , body := (.seq
            (.expr (.call "DCHECK_EQ" [(.index (.name "str") (.lit (.int 0))), (.lit (.int 0))]))
            (.seq
              (.expr
                (.call
                  "DCHECK_EQ"
                  [(.call "tolower" [(.index (.name "str") (.lit (.int 1)))]), (.lit (.str "b"))]))
              (.ret
                (.call
                  "InternalStringToIntDouble"
                  [ (.binop "+" (.call "begin" []) (.lit (.int 2)))
                  , (.call "end" [])
                  , (.lit (.bool false))
                  , (.lit (.bool false)) ])))) }

/-- `v8.internal.OctalStringToDouble:double(base.Vector)`  (from `conversions.cc`) -/
def f_v8_internal_OctalStringToDouble_double_base_Vector_ : Func :=
  { name := "v8.internal.OctalStringToDouble:double(base.Vector)"
  , params := ["str"]
  , body := (.seq
            (.expr (.call "DCHECK_EQ" [(.index (.name "str") (.lit (.int 0))), (.lit (.int 0))]))
            (.seq
              (.expr
                (.call
                  "DCHECK_EQ"
                  [(.call "tolower" [(.index (.name "str") (.lit (.int 1)))]), (.lit (.str "o"))]))
              (.ret
                (.call
                  "InternalStringToIntDouble"
                  [ (.binop "+" (.call "begin" []) (.lit (.int 2)))
                  , (.call "end" [])
                  , (.lit (.bool false))
                  , (.lit (.bool false)) ])))) }

/-- `v8.internal.HexStringToDouble:double(base.Vector)`  (from `conversions.cc`) -/
def f_v8_internal_HexStringToDouble_double_base_Vector_ : Func :=
  { name := "v8.internal.HexStringToDouble:double(base.Vector)"
  , params := ["str"]
  , body := (.seq
            (.expr (.call "DCHECK_EQ" [(.index (.name "str") (.lit (.int 0))), (.lit (.int 0))]))
            (.seq
              (.expr
                (.call
                  "DCHECK_EQ"
                  [(.call "tolower" [(.index (.name "str") (.lit (.int 1)))]), (.lit (.str "x"))]))
              (.ret
                (.call
                  "InternalStringToIntDouble"
                  [ (.binop "+" (.call "begin" []) (.lit (.int 2)))
                  , (.call "end" [])
                  , (.lit (.bool false))
                  , (.lit (.bool false)) ])))) }

/-- `v8.internal.ImplicitOctalStringToDouble:double(base.Vector)`  (from `conversions.cc`) -/
def f_v8_internal_ImplicitOctalStringToDouble_double_base_Vector_ : Func :=
  { name := "v8.internal.ImplicitOctalStringToDouble:double(base.Vector)"
  , params := ["str"]
  , body := (.ret
            (.call
              "InternalStringToIntDouble"
              [(.call "begin" []), (.call "end" []), (.lit (.bool false)), (.lit (.bool false))])) }

/-- `v8.internal.StringToInt:double(Isolate*,DirectHandle,int)`  (from `conversions.cc`) -/
def f_v8_internal_StringToInt_double_Isolate__DirectHandle_int_ : Func :=
  { name := "v8.internal.StringToInt:double(Isolate*,DirectHandle,int)"
  , params := ["isolate", "string", "radix"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign
                  "helper"
                  (.alloc "NumberParseIntHelper" [(.name "string"), (.name "radix")]))
                (.ret (.call "v8.internal.NumberParseIntHelper.GetResult:double()" []))))) }

/-- `v8.internal.StringToBigIntHelper.__init__`  (from `conversions.cc`) -/
def f_v8_internal_StringToBigIntHelper___init__ : Func :=
  { name := "v8.internal.StringToBigIntHelper.__init__"
  , params := ["isolate", "string"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.expr
                  (.call
                    "v8.internal.StringToIntHelper.set_allow_binary_and_octal_prefixes:void()"
                    []))
                (.seq
                  (.expr
                    (.call "v8.internal.StringToIntHelper.set_disallow_trailing_junk:void()" []))
                  (.seq
                    (.setField (.name "self") "StringToIntHelper" (.name "string"))
                    (.seq
                      (.setField (.name "self") "isolate_" (.name "isolate"))
                      (.seq
                        (.setField
                          (.name "self")
                          "accumulator_"
                          (.field (.name "BigInt") "kMaxLength"))
                        (.setField
                          (.name "self")
                          "behavior_"
                          (.field (.name "Behavior") "kStringToBigInt"))))))))) }

/-- `v8.internal.StringToBigIntHelper.__init__`  (from `conversions.cc`) -/
def f_v8_internal_StringToBigIntHelper___init__' : Func :=
  { name := "v8.internal.StringToBigIntHelper.__init__"
  , params := ["isolate", "string", "length"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.expr
                  (.call
                    "v8.internal.StringToIntHelper.set_allow_binary_and_octal_prefixes:void()"
                    []))
                (.seq
                  (.setField (.name "self") "StringToIntHelper" (.name "string"))
                  (.seq
                    (.setField (.name "self") "isolate_" (.name "isolate"))
                    (.seq
                      (.setField
                        (.name "self")
                        "accumulator_"
                        (.field (.name "BigInt") "kMaxLength"))
                      (.setField (.name "self") "behavior_" (.field (.name "Behavior") "kLiteral")))))))) }

/-- `v8.internal.StringToBigIntHelper.ParseOneByte:void(uint8_t*)`  (from `conversions.cc`) -/
def f_v8_internal_StringToBigIntHelper_ParseOneByte_void_uint8_t__ : Func :=
  { name := "v8.internal.StringToBigIntHelper.ParseOneByte:void(uint8_t*)"
  , params := ["start"]
  , body := (.ret (.call "ParseInternal" [(.name "start")])) }

/-- `v8.internal.StringToBigIntHelper.ParseTwoByte:void(base.uc16*)`  (from `conversions.cc`) -/
def f_v8_internal_StringToBigIntHelper_ParseTwoByte_void_base_uc16__ : Func :=
  { name := "v8.internal.StringToBigIntHelper.ParseTwoByte:void(base.uc16*)"
  , params := ["start"]
  , body := (.ret (.call "ParseInternal" [(.name "start")])) }

/-- `v8.internal.StringToBigIntHelper.GetResult:MaybeHandle()`  (from `conversions.cc`) -/
def f_v8_internal_StringToBigIntHelper_GetResult_MaybeHandle__ : Func :=
  { name := "v8.internal.StringToBigIntHelper.GetResult:MaybeHandle()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.expr (.call "v8.internal.StringToIntHelper.ParseInt:void()" []))
                  (.seq
                    (.ifte
                      (.binop
                        "&&"
                        (.binop
                          "&&"
                          (.binop
                            "=="
                            (.field (.name "self") "behavior_")
                            (.field (.name "Behavior") "kStringToBigInt"))
                          (.binop
                            "!="
                            (.call "v8.internal.StringToIntHelper.sign:v8.internal..Sign()" [])
                            (.field (.name "Sign") "kNone")))
                        (.binop
                          "!="
                          (.call "v8.internal.StringToIntHelper.radix:int()" [])
                          (.lit (.int 10))))
                      (.ret (.call "MaybeHandle" []))
                      .skip)
                    (.seq
                      (.ifte
                        (.binop
                          "=="
                          (.call "v8.internal.StringToIntHelper.state:v8.internal..State()" [])
                          (.field (.name "State") "kEmpty"))
                        (.ifte
                          (.binop
                            "=="
                            (.field (.name "self") "behavior_")
                            (.field (.name "Behavior") "kStringToBigInt"))
                          (.expr
                            (.mcall (.name "State") "kZero" [(.field (.name "State") "kZero")]))
                          (.expr (.call "UNREACHABLE" [])))
                        .skip)
                      (.seq (.hole "control:SWITCH") (.expr (.call "UNREACHABLE" []))))))))) }

/-- `v8.internal.StringToBigIntHelper.DecimalString:pair(bigint.Processor*)`  (from `conversions.cc`) -/
def f_v8_internal_StringToBigIntHelper_DecimalString_pair_bigint_Processor__ : Func :=
  { name := "v8.internal.StringToBigIntHelper.DecimalString:pair(bigint.Processor*)"
  , params := ["processor"]
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
                              (.expr
                                (.mcall
                                  (.name "self")
                                  "behavior_"
                                  [ (.field (.name "self") "behavior_")
                                  , (.field (.name "Behavior") "kLiteral") ]))
                              (.seq
                                (.expr (.call "v8.internal.StringToIntHelper.ParseInt:void()" []))
                                (.seq
                                  (.ifte
                                    (.binop
                                      "=="
                                      (.call
                                        "v8.internal.StringToIntHelper.state:v8.internal..State()"
                                        [])
                                      (.field (.name "State") "kZero"))
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign
                                        "out"
                                        (.alloc
                                        "SandboxChars"
                                        [ (.binop
                                        ">"
                                        (.binop "<" (.name "SandboxAllocArray") (.name "uint8_t"))
                                        (.lit (.int 1))) ]))
                                        (.seq (.hole "assign:lhs:indirection") (.ret (.lit .unit)))))
                                    .skip)
                                  (.seq
                                    (.expr
                                      (.call
                                        "DCHECK_EQ"
                                        [ (.call
                                        "v8.internal.StringToIntHelper.state:v8.internal..State()"
                                        [])
                                        , (.field (.name "State") "kDone") ]))
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign
                                        "num_digits"
                                        (.mcall (.name "self") "accumulator_" []))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "kStackStorageSize"
                                        (.field
                                        (.field (.name "bigint") "FromStringAccumulator")
                                        "kStackParts"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "stack_storage" (.hole "op:alloc:array-decl"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "sandbox_storage"
                                        (.alloc
                                        "unique_ptr"
                                        [(.lit .unit), (.call "Deleter" [(.call "platform" [])])]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "<="
                                        (.name "num_digits")
                                        (.name "kStackStorageSize"))
                                        (.assign "digit_storage" (.name "stack_storage"))
                                        (.seq
                                        (.expr
                                        (.call "reset" [(.call "Allocate" [(.name "num_digits")])]))
                                        (.assign "digit_storage" (.call "get" []))))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "digits"
                                        (.alloc
                                        "RWDigits"
                                        [(.name "digit_storage"), (.name "num_digits")]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "FromString"
                                        [(.name "digits"), (.hole "op:addressOf:field:opaque-type")]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "num_chars"
                                        (.call
                                        "ToStringResultLength"
                                        [(.name "digits"), (.lit (.int 10)), (.lit (.bool false))]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "out"
                                        (.alloc
                                        "SandboxChars"
                                        [ (.binop
                                        ">"
                                        (.binop "<" (.name "SandboxAllocArray") (.name "uint8_t"))
                                        (.name "num_chars")) ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "chars" (.hole "op:cast:pointer"))
                                        (.seq
                                        (.expr
                                        (.call
                                        "ToString"
                                        [ (.name "chars")
                                        , (.hole "op:addressOf:local:scalar")
                                        , (.name "digits")
                                        , (.lit (.int 10))
                                        , (.lit (.bool false)) ]))
                                        (.ret (.lit .unit))))))))))))))))))))))))))))))))))) }

/-- `v8.internal.StringToBigIntHelper.isolate:ANY()`  (from `conversions.cc`) -/
def f_v8_internal_StringToBigIntHelper_isolate_ANY__ : Func :=
  { name := "v8.internal.StringToBigIntHelper.isolate:ANY()"
  , params := []
  , body := (.ret (.field (.name "self") "isolate_")) }

/-- `v8.internal.StringToBigIntHelper.ParseInternal:void(Char*)`  (from `conversions.cc`) -/
def f_v8_internal_StringToBigIntHelper_ParseInternal_void_Char__ : Func :=
  { name := "v8.internal.StringToBigIntHelper.ParseInternal:void(Char*)"
  , params := ["start"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.hole "stmt:TYPE_DECL")
                  (.seq
                    .skip
                    (.seq
                      (.assign "current" (.binop "+" (.name "start") (.call "cursor" [])))
                      (.seq
                        .skip
                        (.seq
                          (.assign "end" (.binop "+" (.name "start") (.call "length" [])))
                          (.seq
                            (.assign
                              "current"
                              (.call
                                "Parse"
                                [ (.name "current")
                                , (.name "end")
                                , (.call "v8.internal.StringToIntHelper.radix:int()" []) ]))
                            (.seq
                              .skip
                              (.seq
                                (.assign "result" (.call "result" []))
                                (.seq
                                  (.ifte
                                    (.binop
                                      "=="
                                      (.name "result")
                                      (.field (.name "Result") "kMaxSizeExceeded"))
                                    (.ret
                                      (.mcall
                                        (.name "State")
                                        "kError"
                                        [(.field (.name "State") "kError")]))
                                    .skip)
                                  (.seq
                                    (.ifte
                                      (.binop
                                        "&&"
                                        (.unop
                                        "!"
                                        (.call
                                        "v8.internal.StringToIntHelper.allow_trailing_junk:bool()"
                                        []))
                                        (.call
                                        "AdvanceToNonspace"
                                        [(.hole "op:addressOf:local:pointer"), (.name "end")]))
                                      (.ret
                                        (.mcall
                                        (.name "State")
                                        "kJunk"
                                        [(.field (.name "State") "kJunk")]))
                                      .skip)
                                    (.ret
                                      (.mcall
                                        (.name "State")
                                        "kDone"
                                        [(.field (.name "State") "kDone")]))))))))))))))) }

/-- `v8.internal.StringToBigIntHelper.allocation_type:AllocationType()`  (from `conversions.cc`) -/
def f_v8_internal_StringToBigIntHelper_allocation_type_AllocationType__ : Func :=
  { name := "v8.internal.StringToBigIntHelper.allocation_type:AllocationType()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              .skip
              (.ret
                (.cond
                  (.binop
                    "=="
                    (.field (.name "self") "behavior_")
                    (.field (.name "Behavior") "kLiteral"))
                  (.field (.name "AllocationType") "kOld")
                  (.field (.name "AllocationType") "kYoung"))))) }

/-- `v8.internal.StringToBigInt:MaybeHandle(Isolate*,DirectHandle)`  (from `conversions.cc`) -/
def f_v8_internal_StringToBigInt_MaybeHandle_Isolate__DirectHandle_ : Func :=
  { name := "v8.internal.StringToBigInt:MaybeHandle(Isolate*,DirectHandle)"
  , params := ["isolate", "string"]
  , body := (.seq
            .skip
            (.seq
              (.assign "string" (.call "Flatten" [(.name "isolate"), (.name "string")]))
              (.seq
                .skip
                (.seq
                  (.assign
                    "helper"
                    (.alloc "StringToBigIntHelper" [(.name "isolate"), (.name "string")]))
                  (.ret (.call "GetResult" [])))))) }

/-- `v8.internal.BigIntLiteral:MaybeHandle(IsolateT*,char*)`  (from `conversions.cc`) -/
def f_v8_internal_BigIntLiteral_MaybeHandle_IsolateT__char__ : Func :=
  { name := "v8.internal.BigIntLiteral:MaybeHandle(IsolateT*,char*)"
  , params := ["isolate", "string"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign
                  "helper"
                  (.alloc
                    "StringToBigIntHelper"
                    [ (.name "isolate")
                    , (.hole "op:cast:pointer")
                    , (.call "strlen" [(.name "string")]) ]))
                (.ret (.call "GetResult" []))))) }

/-- `v8.internal.BigIntLiteralToDecimal:pair(LocalIsolate*,base.Vector)`  (from `conversions.cc`) -/
def f_v8_internal_BigIntLiteralToDecimal_pair_LocalIsolate__base_Vector_ : Func :=
  { name := "v8.internal.BigIntLiteralToDecimal:pair(LocalIsolate*,base.Vector)"
  , params := ["isolate", "literal"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign
                  "helper"
                  (.alloc
                    "StringToBigIntHelper"
                    [(.name "isolate"), (.call "begin" []), (.call "size" [])]))
                (.ret (.call "DecimalString" [(.call "bigint_processor" [])]))))) }

/-- `v8.internal.DoubleToStringView:string_view(double,base.Vector)`  (from `conversions.cc`) -/
def f_v8_internal_DoubleToStringView_string_view_double_base_Vector_ : Func :=
  { name := "v8.internal.DoubleToStringView:string_view(double,base.Vector)"
  , params := ["v", "buffer"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq .skip (.seq .skip (.seq .skip (.seq .skip (.hole "control:SWITCH"))))))) }

/-- `v8.internal.IntToStringView:string_view(int,base.Vector)`  (from `conversions.cc`) -/
def f_v8_internal_IntToStringView_string_view_int_base_Vector_ : Func :=
  { name := "v8.internal.IntToStringView:string_view(int,base.Vector)"
  , params := ["n", "buffer"]
  , body := (.seq
            .skip
            (.seq
              (.assign "negative" (.lit (.bool true)))
              (.seq
                (.ifte
                  (.binop ">=" (.name "n") (.lit (.int 0)))
                  (.seq
                    (.assign "n" (.unop "-" (.name "n")))
                    (.assign "negative" (.lit (.bool false))))
                  .skip)
                (.seq
                  .skip
                  (.seq
                    (.assign "i" (.call "size" []))
                    (.seq
                      (.loop
                        (.hole "expr:BLOCK-prelude")
                        (.expr (.binop "!=" (.name "n") (.lit (.int 0)))))
                      (.seq
                        (.ifte
                          (.binop "!=" (.name "negative") (.lit (.int 0)))
                          (.setIndex
                            (.name "buffer")
                            (.hole "op:preDecrement:value")
                            (.lit (.str "-")))
                          .skip)
                        (.ret (.lit .unit))))))))) }

/-- `v8.internal.DoubleToFixedStringView:string_view(double,int,base.Vector)`  (from `conversions.cc`) -/
def f_v8_internal_DoubleToFixedStringView_string_view_double_int_base_Vector_ : Func :=
  { name := "v8.internal.DoubleToFixedStringView:string_view(double,int,base.Vector)"
  , params := ["value", "f", "buffer"]
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
                        (.assign "kFirstNonFixed" (.hole "lit:float"))
                        (.seq
                          (.expr (.call "DCHECK_GE" [(.name "f"), (.lit (.int 0))]))
                          (.seq
                            (.expr (.call "DCHECK_LE" [(.name "f"), (.name "kMaxFractionDigits")]))
                            (.seq
                              .skip
                              (.seq
                                (.assign "negative" (.lit (.bool false)))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "abs_value" (.name "value"))
                                    (.seq
                                      (.ifte
                                        (.binop "<" (.name "value") (.lit (.int 0)))
                                        (.seq
                                        (.assign "abs_value" (.unop "-" (.name "value")))
                                        (.assign "negative" (.lit (.bool true))))
                                        .skip)
                                      (.seq
                                        (.ifte
                                        (.binop ">=" (.name "abs_value") (.name "kFirstNonFixed"))
                                        (.ret
                                        (.call
                                        "DoubleToStringView"
                                        [(.name "value"), (.name "buffer")]))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "kDecimalRepCapacity"
                                        (.binop
                                        "+"
                                        (.binop
                                        "+"
                                        (.name "kDoubleToFixedMaxDigitsBeforePoint")
                                        (.name "kMaxFractionDigits"))
                                        (.lit (.int 1))))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "decimal_rep" (.hole "op:alloc:array-decl"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.expr
                                        (.call
                                        "DoubleToAscii"
                                        [ (.name "value")
                                        , (.field (.name "base") "DTOA_FIXED")
                                        , (.name "f")
                                        , (.call
                                        "Vector"
                                        [(.name "decimal_rep"), (.name "kDecimalRepCapacity")])
                                        , (.hole "op:addressOf:local:scalar")
                                        , (.hole "op:addressOf:local:scalar")
                                        , (.hole "op:addressOf:local:scalar") ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "zero_prefix_length" (.lit (.int 0)))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "zero_postfix_length" (.lit (.int 0)))
                                        (.seq
                                        (.ifte
                                        (.binop "<=" (.name "decimal_point") (.lit (.int 0)))
                                        (.seq
                                        (.assign
                                        "zero_prefix_length"
                                        (.binop
                                        "+"
                                        (.unop "-" (.name "decimal_point"))
                                        (.lit (.int 1))))
                                        (.assign "decimal_point" (.lit (.int 1))))
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "<"
                                        (.binop
                                        "+"
                                        (.name "zero_prefix_length")
                                        (.name "decimal_rep_length"))
                                        (.binop "+" (.name "decimal_point") (.name "f")))
                                        (.assign
                                        "zero_postfix_length"
                                        (.binop
                                        "-"
                                        (.binop
                                        "-"
                                        (.binop "+" (.name "decimal_point") (.name "f"))
                                        (.name "decimal_rep_length"))
                                        (.name "zero_prefix_length")))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "rep_length"
                                        (.binop
                                        "+"
                                        (.binop
                                        "+"
                                        (.name "zero_prefix_length")
                                        (.name "decimal_rep_length"))
                                        (.name "zero_postfix_length")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "rep_buffer"
                                        (.call
                                        "New"
                                        [(.binop "+" (.name "rep_length") (.lit (.int 1)))]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "rep_builder"
                                        (.alloc
                                        "SimpleStringBuilder"
                                        [(.call "begin" []), (.call "size" [])]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "v8.internal.SimpleStringBuilder.AddPadding:void(char,int)"
                                        [(.lit (.int 0)), (.name "zero_prefix_length")]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "AddString"
                                        [(.name "decimal_rep"), (.name "decimal_rep_length")]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "v8.internal.SimpleStringBuilder.AddPadding:void(char,int)"
                                        [(.lit (.int 0)), (.name "zero_postfix_length")]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "rep_end"
                                        (.call
                                        "v8.internal.SimpleStringBuilder.Finalize:char*()"
                                        []))
                                        (.seq
                                        (.hole "assign:lhs:indirection")
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "builder"
                                        (.alloc
                                        "SimpleStringBuilder"
                                        [(.call "begin" []), (.call "size" [])]))
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.name "negative") (.lit (.int 0)))
                                        (.expr
                                        (.call
                                        "v8.internal.SimpleStringBuilder.AddCharacter:void(char)"
                                        [(.lit (.str "-"))]))
                                        .skip)
                                        (.seq
                                        (.expr
                                        (.call
                                        "AddSubstring"
                                        [(.call "begin" []), (.name "decimal_point")]))
                                        (.seq
                                        (.ifte
                                        (.binop ">" (.name "f") (.lit (.int 0)))
                                        (.seq
                                        (.expr
                                        (.call
                                        "v8.internal.SimpleStringBuilder.AddCharacter:void(char)"
                                        [(.lit (.str "."))]))
                                        (.expr
                                        (.call
                                        "AddSubstring"
                                        [ (.binop "+" (.call "begin" []) (.name "decimal_point"))
                                        , (.name "f") ])))
                                        .skip)
                                        (.seq
                                        (.expr (.call "DeleteArray" [(.call "begin" [])]))
                                        (.ret (.lit .unit))))))))))))))))))))))))))))))))))))))))))))))))) }

/-- `v8.internal.CreateExponentialRepresentation:string_view(char*,int,int,bool,int,base.Vector)`  (from `conversions.cc`) -/
def f_v8_internal_CreateExponentialRepresentation_string_view_char__int_int_bool_int_base_Vector_ : Func :=
  { name := "v8.internal.CreateExponentialRepresentation:string_view(char*,int,int,bool,int,base.Vector)"
  , params := ["decimal_rep", "rep_length", "exponent", "negative", "significant_digits", "buffer"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.assign "negative_exponent" (.lit (.bool false)))
                (.seq
                  (.ifte
                    (.binop "<" (.name "exponent") (.lit (.int 0)))
                    (.seq
                      (.assign "negative_exponent" (.lit (.bool true)))
                      (.assign "exponent" (.unop "-" (.name "exponent"))))
                    .skip)
                  (.seq
                    .skip
                    (.seq
                      (.assign
                        "builder"
                        (.alloc "SimpleStringBuilder" [(.call "begin" []), (.call "size" [])]))
                      (.seq
                        (.ifte
                          (.binop "!=" (.name "negative") (.lit (.int 0)))
                          (.expr
                            (.call
                              "v8.internal.SimpleStringBuilder.AddCharacter:void(char)"
                              [(.lit (.str "-"))]))
                          .skip)
                        (.seq
                          (.expr
                            (.call
                              "v8.internal.SimpleStringBuilder.AddCharacter:void(char)"
                              [(.index (.name "decimal_rep") (.lit (.int 0)))]))
                          (.seq
                            (.ifte
                              (.binop "!=" (.name "significant_digits") (.lit (.int 1)))
                              (.seq
                                (.expr
                                  (.call
                                    "v8.internal.SimpleStringBuilder.AddCharacter:void(char)"
                                    [(.lit (.str "."))]))
                                (.seq
                                  (.expr
                                    (.call
                                      "DCHECK_EQ"
                                      [ (.name "rep_length")
                                      , (.call "strlen" [(.name "decimal_rep")]) ]))
                                  (.seq
                                    (.expr
                                      (.call
                                        "DCHECK_GE"
                                        [(.name "significant_digits"), (.name "rep_length")]))
                                    (.seq
                                      (.expr
                                        (.call
                                        "AddString"
                                        [ (.hole "cstr:pointer-arith")
                                        , (.binop "-" (.name "rep_length") (.lit (.int 1))) ]))
                                      (.expr
                                        (.call
                                        "v8.internal.SimpleStringBuilder.AddPadding:void(char,int)"
                                        [ (.lit (.int 0))
                                        , (.binop
                                        "-"
                                        (.name "significant_digits")
                                        (.name "rep_length")) ]))))))
                              .skip)
                            (.seq
                              (.expr
                                (.call
                                  "v8.internal.SimpleStringBuilder.AddCharacter:void(char)"
                                  [(.lit (.str "e"))]))
                              (.seq
                                (.expr
                                  (.call
                                    "v8.internal.SimpleStringBuilder.AddCharacter:void(char)"
                                    [ (.cond
                                        (.name "negative_exponent")
                                        (.lit (.str "-"))
                                        (.lit (.str "+"))) ]))
                                (.seq
                                  (.expr
                                    (.call
                                      "v8.internal.SimpleStringBuilder.AddExponent:void(int)"
                                      [(.name "exponent")]))
                                  (.ret (.lit .unit)))))))))))))) }

/-- `v8.internal.DoubleToExponentialStringView:string_view(double,int,base.Vector)`  (from `conversions.cc`) -/
def f_v8_internal_DoubleToExponentialStringView_string_view_double_int_base_Vector_ : Func :=
  { name := "v8.internal.DoubleToExponentialStringView:string_view(double,int,base.Vector)"
  , params := ["value", "f", "buffer"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.expr
                  (.call
                    "DCHECK"
                    [ (.binop
                        "&&"
                        (.binop ">=" (.name "f") (.unop "-" (.lit (.int 1))))
                        (.binop "<=" (.name "f") (.name "kMaxFractionDigits"))) ]))
                (.seq
                  .skip
                  (.seq
                    (.assign "negative" (.lit (.bool false)))
                    (.seq
                      (.ifte
                        (.binop "<" (.name "value") (.lit (.int 0)))
                        (.seq
                          (.assign "value" (.unop "-" (.name "value")))
                          (.assign "negative" (.lit (.bool true))))
                        .skip)
                      (.seq
                        .skip
                        (.seq
                          .skip
                          (.seq
                            .skip
                            (.seq
                              (.assign
                                "kV8DtoaBufferCapacity"
                                (.binop
                                  "+"
                                  (.binop "+" (.name "kMaxFractionDigits") (.lit (.int 1)))
                                  (.lit (.int 1))))
                              (.seq
                                (.expr
                                  (.mcall
                                    (.name "base")
                                    "kBase10MaximalLength"
                                    [ (.field (.name "base") "kBase10MaximalLength")
                                    , (.binop "+" (.name "kMaxFractionDigits") (.lit (.int 1))) ]))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "decimal_rep" (.hole "op:alloc:array-decl"))
                                    (.seq
                                      .skip
                                      (.seq
                                        (.ifte
                                        (.binop "==" (.name "f") (.unop "-" (.lit (.int 1))))
                                        (.seq
                                        (.expr
                                        (.call
                                        "DoubleToAscii"
                                        [ (.name "value")
                                        , (.field (.name "base") "DTOA_SHORTEST")
                                        , (.lit (.int 0))
                                        , (.call
                                        "Vector"
                                        [(.name "decimal_rep"), (.name "kV8DtoaBufferCapacity")])
                                        , (.hole "op:addressOf:local:scalar")
                                        , (.hole "op:addressOf:local:scalar")
                                        , (.hole "op:addressOf:local:scalar") ]))
                                        (.assign
                                        "f"
                                        (.binop "-" (.name "decimal_rep_length") (.lit (.int 1)))))
                                        (.expr
                                        (.call
                                        "DoubleToAscii"
                                        [ (.name "value")
                                        , (.field (.name "base") "DTOA_PRECISION")
                                        , (.binop "+" (.name "f") (.lit (.int 1)))
                                        , (.call
                                        "Vector"
                                        [(.name "decimal_rep"), (.name "kV8DtoaBufferCapacity")])
                                        , (.hole "op:addressOf:local:scalar")
                                        , (.hole "op:addressOf:local:scalar")
                                        , (.hole "op:addressOf:local:scalar") ])))
                                        (.seq
                                        (.expr
                                        (.call
                                        "DCHECK_GT"
                                        [(.name "decimal_rep_length"), (.lit (.int 0))]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "DCHECK"
                                        [ (.binop
                                        "<="
                                        (.name "decimal_rep_length")
                                        (.binop "+" (.name "f") (.lit (.int 1)))) ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "exponent"
                                        (.binop "-" (.name "decimal_point") (.lit (.int 1))))
                                        (.ret
                                        (.call
                                        "CreateExponentialRepresentation"
                                        [ (.name "decimal_rep")
                                        , (.name "decimal_rep_length")
                                        , (.name "exponent")
                                        , (.name "negative")
                                        , (.binop "+" (.name "f") (.lit (.int 1)))
                                        , (.name "buffer") ]))))))))))))))))))))) }

/-- `v8.internal.DoubleToPrecisionStringView:string_view(double,int,base.Vector)`  (from `conversions.cc`) -/
def f_v8_internal_DoubleToPrecisionStringView_string_view_double_int_base_Vector_ : Func :=
  { name := "v8.internal.DoubleToPrecisionStringView:string_view(double,int,base.Vector)"
  , params := ["value", "p", "buffer"]
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
                      (.assign "kMinimalDigits" (.lit (.int 1)))
                      (.seq
                        (.expr
                          (.call
                            "DCHECK"
                            [ (.binop
                                "&&"
                                (.binop ">=" (.name "p") (.name "kMinimalDigits"))
                                (.binop "<=" (.name "p") (.name "kMaxFractionDigits"))) ]))
                        (.seq
                          (.expr (.call "USE" [(.name "kMinimalDigits")]))
                          (.seq
                            .skip
                            (.seq
                              (.assign "negative" (.lit (.bool false)))
                              (.seq
                                (.ifte
                                  (.binop "<" (.name "value") (.lit (.int 0)))
                                  (.seq
                                    (.assign "value" (.unop "-" (.name "value")))
                                    (.assign "negative" (.lit (.bool true))))
                                  .skip)
                                (.seq
                                  .skip
                                  (.seq
                                    .skip
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign
                                        "kV8DtoaBufferCapacity"
                                        (.binop "+" (.name "kMaxFractionDigits") (.lit (.int 1))))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "decimal_rep" (.hole "op:alloc:array-decl"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.expr
                                        (.call
                                        "DoubleToAscii"
                                        [ (.name "value")
                                        , (.field (.name "base") "DTOA_PRECISION")
                                        , (.name "p")
                                        , (.call
                                        "Vector"
                                        [(.name "decimal_rep"), (.name "kV8DtoaBufferCapacity")])
                                        , (.hole "op:addressOf:local:scalar")
                                        , (.hole "op:addressOf:local:scalar")
                                        , (.hole "op:addressOf:local:scalar") ]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "DCHECK"
                                        [(.binop "<=" (.name "decimal_rep_length") (.name "p"))]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "exponent"
                                        (.binop "-" (.name "decimal_point") (.lit (.int 1))))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "||"
                                        (.binop "<" (.name "exponent") (.unop "-" (.lit (.int 6))))
                                        (.binop ">=" (.name "exponent") (.name "p")))
                                        (.assign
                                        "result"
                                        (.call
                                        "CreateExponentialRepresentation"
                                        [ (.name "decimal_rep")
                                        , (.name "decimal_rep_length")
                                        , (.name "exponent")
                                        , (.name "negative")
                                        , (.name "p")
                                        , (.name "buffer") ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "builder"
                                        (.alloc
                                        "SimpleStringBuilder"
                                        [(.call "begin" []), (.call "size" [])]))
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.name "negative") (.lit (.int 0)))
                                        (.expr
                                        (.call
                                        "v8.internal.SimpleStringBuilder.AddCharacter:void(char)"
                                        [(.lit (.str "-"))]))
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.binop "<=" (.name "decimal_point") (.lit (.int 0)))
                                        (.seq
                                        (.expr (.call "AddStringLiteral" [(.lit (.str "0."))]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "v8.internal.SimpleStringBuilder.AddPadding:void(char,int)"
                                        [(.lit (.int 0)), (.unop "-" (.name "decimal_point"))]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "AddString"
                                        [(.name "decimal_rep"), (.name "decimal_rep_length")]))
                                        (.expr
                                        (.call
                                        "v8.internal.SimpleStringBuilder.AddPadding:void(char,int)"
                                        [ (.lit (.int 0))
                                        , (.binop "-" (.name "p") (.name "decimal_rep_length")) ])))))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "m"
                                        (.call
                                        "min"
                                        [(.name "decimal_rep_length"), (.name "decimal_point")]))
                                        (.seq
                                        (.expr
                                        (.call "AddSubstring" [(.name "decimal_rep"), (.name "m")]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "v8.internal.SimpleStringBuilder.AddPadding:void(char,int)"
                                        [ (.lit (.int 0))
                                        , (.binop
                                        "-"
                                        (.name "decimal_point")
                                        (.name "decimal_rep_length")) ]))
                                        (.ifte
                                        (.binop "<" (.name "decimal_point") (.name "p"))
                                        (.seq
                                        (.expr
                                        (.call
                                        "v8.internal.SimpleStringBuilder.AddCharacter:void(char)"
                                        [(.lit (.str "."))]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "extra"
                                        (.cond (.name "negative") (.lit (.int 2)) (.lit (.int 1))))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        ">"
                                        (.name "decimal_rep_length")
                                        (.name "decimal_point"))
                                        (.seq
                                        (.expr
                                        (.call
                                        "DCHECK_EQ"
                                        [ (.binop
                                        "-"
                                        (.name "decimal_rep_length")
                                        (.name "decimal_point"))
                                        , (.call "strlen" [(.hole "cstr:pointer-arith")]) ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "len"
                                        (.binop
                                        "-"
                                        (.name "decimal_rep_length")
                                        (.name "decimal_point")))
                                        (.seq
                                        (.expr
                                        (.call
                                        "DCHECK_LE"
                                        [(.call "position" []), (.name "kMaxInt")]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "n"
                                        (.call
                                        "min"
                                        [ (.name "len")
                                        , (.binop
                                        "-"
                                        (.name "p")
                                        (.unop
                                        "cast:i32"
                                        (.binop "-" (.call "position" []) (.name "extra")))) ]))
                                        (.expr
                                        (.call
                                        "AddSubstring"
                                        [(.hole "cstr:pointer-arith"), (.name "n")]))))))))
                                        .skip)
                                        (.expr
                                        (.call
                                        "v8.internal.SimpleStringBuilder.AddPadding:void(char,int)"
                                        [ (.lit (.int 0))
                                        , (.binop
                                        "+"
                                        (.name "extra")
                                        (.binop
                                        "-"
                                        (.name "p")
                                        (.unop "cast:i32" (.call "position" [])))) ]))))))
                                        .skip))))))
                                        (.hole "assign:arity"))))))
                                        (.ret (.name "result")))))))))))))))))))))))))) }

/-- `v8.internal.DoubleToRadixStringView:string_view(double,int,base.Vector)`  (from `conversions.cc`) -/
def f_v8_internal_DoubleToRadixStringView_string_view_double_int_base_Vector_ : Func :=
  { name := "v8.internal.DoubleToRadixStringView:string_view(double,int,base.Vector)"
  , params := ["value", "radix", "buffer"]
  , body := (.seq
            (.expr (.call "DCHECK_NE" [(.hole "lit:float"), (.name "value")]))
            (.seq
              (.expr
                (.call
                  "CHECK"
                  [ (.binop
                      "&&"
                      (.binop ">=" (.name "radix") (.lit (.int 2)))
                      (.binop "<=" (.name "radix") (.lit (.int 36)))) ]))
              (.seq
                (.expr (.call "CHECK" [(.call "isfinite" [(.name "value")])]))
                (.seq
                  .skip
                  (.seq
                    (.assign "chars" (.lit (.str "0123456789abcdefghijklmnopqrstuvwxyz")))
                    (.seq
                      .skip
                      (.seq
                        (.assign "integer_cursor" (.binop "/" (.call "size" []) (.lit (.int 2))))
                        (.seq
                          .skip
                          (.seq
                            (.assign "fraction_cursor" (.name "integer_cursor"))
                            (.seq
                              .skip
                              (.seq
                                (.assign "negative" (.binop "<" (.name "value") (.lit (.int 0))))
                                (.seq
                                  (.ifte
                                    (.binop "!=" (.name "negative") (.lit (.int 0)))
                                    (.assign "value" (.unop "-" (.name "value")))
                                    .skip)
                                  (.seq
                                    .skip
                                    (.seq
                                      (.assign "integer" (.call "floor" [(.name "value")]))
                                      (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "fraction"
                                        (.binop "-" (.name "value") (.name "integer")))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "delta"
                                        (.binop
                                        "*"
                                        (.hole "lit:float")
                                        (.binop "-" (.call "NextDouble" []) (.name "value"))))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "delta_is_positive" (.lit (.bool true)))
                                        (.seq
                                        (.ifte
                                        (.binop "<=" (.name "delta") (.lit (.int 0)))
                                        (.ifte
                                        (.call "GetFlushDenormals" [])
                                        (.assign "delta_is_positive" (.lit (.bool false)))
                                        (.seq
                                        (.expr (.lit .unit))
                                        (.assign "delta" (.call "NextDouble" []))))
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.name "delta_is_positive")
                                        (.binop ">=" (.name "fraction") (.name "delta")))
                                        (.seq
                                        (.setIndex
                                        (.name "buffer")
                                        (.hole "op:postIncrement:value")
                                        (.lit (.str ".")))
                                        (.loop
                                        (.hole "expr:BLOCK-prelude")
                                        (.expr (.binop ">=" (.name "fraction") (.name "delta")))))
                                        .skip)
                                        (.seq
                                        (.loop
                                        (.binop ">" (.call "Exponent" []) (.lit (.int 0)))
                                        (.seq
                                        (.expr (.hole "op:assignmentDivision"))
                                        (.setIndex
                                        (.name "buffer")
                                        (.hole "op:preDecrement:value")
                                        (.lit (.int 0)))))
                                        (.seq
                                        (.loop
                                        (.hole "expr:BLOCK-impure")
                                        (.expr (.binop ">" (.name "integer") (.lit (.int 0)))))
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.name "negative") (.lit (.int 0)))
                                        (.setIndex
                                        (.name "buffer")
                                        (.hole "op:preDecrement:value")
                                        (.lit (.str "-")))
                                        .skip)
                                        (.seq
                                        (.expr
                                        (.call
                                        "DCHECK_LE"
                                        [(.name "integer_cursor"), (.hole "op:shiftLeft")]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "DCHECK_GT"
                                        [(.name "fraction_cursor"), (.name "integer_cursor")]))
                                        (.ret (.lit .unit))))))))))))))))))))))))))))) }

/-- `v8.internal.StringToDouble:double(Isolate*,DirectHandle,v8.internal.ConversionFlag,double)`  (from `conversions.cc`) -/
def f_v8_internal_StringToDouble_double_Isolate__DirectHandle_v8_internal_ConversionFlag_double_ : Func :=
  { name := "v8.internal.StringToDouble:double(Isolate*,DirectHandle,v8.internal.ConversionFlag,double)"
  , params := ["isolate", "string", "flag", "empty_string_val"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.hole "assign:lhs:greaterThan")
                  (.ret
                    (.call
                      "FlatStringToDouble"
                      [ (.hole "op:indirection:unknown-type")
                      , (.name "flag")
                      , (.name "empty_string_val") ])))))) }

/-- `v8.internal.FlatStringToDouble:double(Tagged,v8.internal.ConversionFlag,double)`  (from `conversions.cc`) -/
def f_v8_internal_FlatStringToDouble_double_Tagged_v8_internal_ConversionFlag_double_ : Func :=
  { name := "v8.internal.FlatStringToDouble:double(Tagged,v8.internal.ConversionFlag,double)"
  , params := ["string", "flag", "empty_string_val"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.call "DCHECK" [(.call "IsFlat" [])]))
              (.seq
                .skip
                (.seq
                  (.assign "flat" (.call "GetFlatContent" [(.name "no_gc")]))
                  (.seq
                    (.expr (.call "DCHECK" [(.call "IsFlat" [])]))
                    (.ifte
                      (.call "IsOneByte" [])
                      (.ret
                        (.call
                          "StringToDouble"
                          [(.call "ToOneByteVector" []), (.name "flag"), (.name "empty_string_val")]))
                      (.ret
                        (.call
                          "StringToDouble"
                          [(.call "ToUC16Vector" []), (.name "flag"), (.name "empty_string_val")])))))))) }

/-- `v8.internal.TryStringToDouble:optional(LocalIsolate*,DirectHandle,uint32_t)`  (from `conversions.cc`) -/
def f_v8_internal_TryStringToDouble_optional_LocalIsolate__DirectHandle_uint32_t_ : Func :=
  { name := "v8.internal.TryStringToDouble:optional(LocalIsolate*,DirectHandle,uint32_t)"
  , params := ["isolate", "object", "max_length_for_conversion"]
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
                        (.assign "length" (.call "length" []))
                        (.seq
                          (.ifte
                            (.binop ">" (.name "length") (.name "max_length_for_conversion"))
                            (.ret (.field (.name "std") "nullopt"))
                            .skip)
                          (.seq
                            .skip
                            (.seq
                              (.assign
                                "buffer"
                                (.call "make_unique" [(.name "max_length_for_conversion")]))
                              (.seq
                                .skip
                                (.seq
                                  (.assign
                                    "access_guard"
                                    (.alloc "SharedStringAccessGuardIfNeeded" [(.name "isolate")]))
                                  (.seq
                                    (.expr
                                      (.call
                                        "WriteToFlat"
                                        [ (.hole "op:indirection:opaque-type")
                                        , (.call "get" [])
                                        , (.lit (.int 0))
                                        , (.name "length")
                                        , (.name "access_guard") ]))
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign
                                        "v"
                                        (.alloc "Vector" [(.call "get" []), (.name "length")]))
                                        (.ret
                                        (.call
                                        "StringToDouble"
                                        [(.name "v"), (.name "ALLOW_NON_DECIMAL_PREFIX")]))))))))))))))))) }

/-- `v8.internal.TryStringToInt:optional(LocalIsolate*,DirectHandle,int)`  (from `conversions.cc`) -/
def f_v8_internal_TryStringToInt_optional_LocalIsolate__DirectHandle_int_ : Func :=
  { name := "v8.internal.TryStringToInt:optional(LocalIsolate*,DirectHandle,int)"
  , params := ["isolate", "object", "radix"]
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
                          (.assign "kMaxLengthForConversion" (.lit (.int 20)))
                          (.seq
                            .skip
                            (.seq
                              (.assign "length" (.call "length" []))
                              (.seq
                                (.ifte
                                  (.binop ">" (.name "length") (.name "kMaxLengthForConversion"))
                                  (.ret (.field (.name "std") "nullopt"))
                                  .skip)
                                (.ifte
                                  (.call
                                    "IsOneByteRepresentationUnderneath"
                                    [(.hole "op:indirection:opaque-type")])
                                  (.seq
                                    .skip
                                    (.seq
                                      (.assign "buffer" (.hole "op:alloc:array-decl"))
                                      (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "access_guard"
                                        (.alloc
                                        "SharedStringAccessGuardIfNeeded"
                                        [(.name "isolate")]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "WriteToFlat"
                                        [ (.hole "op:indirection:opaque-type")
                                        , (.name "buffer")
                                        , (.lit (.int 0))
                                        , (.name "length")
                                        , (.name "access_guard") ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "helper"
                                        (.alloc
                                        "NumberParseIntHelper"
                                        [(.name "buffer"), (.name "radix"), (.name "length")]))
                                        (.ret
                                        (.call
                                        "v8.internal.NumberParseIntHelper.GetResult:double()"
                                        [])))))))))
                                  (.seq
                                    .skip
                                    (.seq
                                      (.assign "buffer" (.hole "op:alloc:array-decl"))
                                      (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "access_guard"
                                        (.alloc
                                        "SharedStringAccessGuardIfNeeded"
                                        [(.name "isolate")]))
                                        (.seq
                                        (.expr
                                        (.call
                                        "WriteToFlat"
                                        [ (.hole "op:indirection:opaque-type")
                                        , (.name "buffer")
                                        , (.lit (.int 0))
                                        , (.name "length")
                                        , (.name "access_guard") ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "helper"
                                        (.alloc
                                        "NumberParseIntHelper"
                                        [(.name "buffer"), (.name "radix"), (.name "length")]))
                                        (.ret
                                        (.call
                                        "v8.internal.NumberParseIntHelper.GetResult:double()"
                                        []))))))))))))))))))))) }

/-- `v8.internal.IsSpecialIndex:bool(Tagged)`  (from `conversions.cc`) -/
def f_v8_internal_IsSpecialIndex_bool_Tagged_ : Func :=
  { name := "v8.internal.IsSpecialIndex:bool(Tagged)"
  , params := ["string"]
  , body := (.seq
            (.expr (.call "DCHECK" [(.unop "!" (.call "IsNeeded" [(.name "string")]))]))
            (.seq
              .skip
              (.seq
                (.assign "access_guard" (.call "NotNeeded" []))
                (.ret (.call "IsSpecialIndex" [(.name "string"), (.name "access_guard")]))))) }

/-- `v8.internal.IsSpecialIndex:bool(Tagged,v8.internal.SharedStringAccessGuardIfNeeded&)`  (from `conversions.cc`) -/
def f_v8_internal_IsSpecialIndex_bool_Tagged_v8_internal_SharedStringAccessGuardIfNeeded__ : Func :=
  { name := "v8.internal.IsSpecialIndex:bool(Tagged,v8.internal.SharedStringAccessGuardIfNeeded&)"
  , params := ["string", "access_guard"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  .skip
                  (.seq
                    (.assign "kBufferSize" (.lit (.int 24)))
                    (.seq
                      .skip
                      (.seq
                        (.assign "length" (.call "length" []))
                        (.seq
                          (.ifte
                            (.binop
                              "||"
                              (.binop "==" (.name "length") (.lit (.int 0)))
                              (.binop ">" (.name "length") (.name "kBufferSize")))
                            (.ret (.lit (.bool false)))
                            .skip)
                          (.seq
                            .skip
                            (.seq
                              (.assign "buffer" (.hole "op:alloc:array-decl"))
                              (.seq
                                (.expr
                                  (.call
                                    "WriteToFlat"
                                    [ (.name "string")
                                    , (.name "buffer")
                                    , (.lit (.int 0))
                                    , (.name "length")
                                    , (.name "access_guard") ]))
                                (.seq
                                  .skip
                                  (.seq
                                    (.assign "offset" (.lit (.int 0)))
                                    (.seq
                                      (.ifte
                                        (.unop
                                        "!"
                                        (.call
                                        "IsDecimalDigit"
                                        [(.index (.name "buffer") (.lit (.int 0)))]))
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.index (.name "buffer") (.lit (.int 0)))
                                        (.lit (.str "-")))
                                        (.seq
                                        (.ifte
                                        (.binop "==" (.name "length") (.lit (.int 1)))
                                        (.ret (.lit (.bool false)))
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.unop
                                        "!"
                                        (.call
                                        "IsDecimalDigit"
                                        [(.index (.name "buffer") (.lit (.int 1)))]))
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.binop
                                        "=="
                                        (.index (.name "buffer") (.lit (.int 1)))
                                        (.lit (.str "I")))
                                        (.binop "==" (.name "length") (.lit (.int 9))))
                                        .skip
                                        (.ret (.lit (.bool false))))
                                        .skip)
                                        (.assign
                                        "offset"
                                        (.binop "+" (.name "offset") (.lit (.int 1))))))
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.binop
                                        "=="
                                        (.index (.name "buffer") (.lit (.int 0)))
                                        (.lit (.str "I")))
                                        (.binop "==" (.name "length") (.lit (.int 8))))
                                        .skip
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.binop
                                        "=="
                                        (.index (.name "buffer") (.lit (.int 0)))
                                        (.lit (.str "N")))
                                        (.binop "==" (.name "length") (.lit (.int 3))))
                                        (.ret
                                        (.binop
                                        "&&"
                                        (.binop
                                        "=="
                                        (.index (.name "buffer") (.lit (.int 1)))
                                        (.lit (.str "a")))
                                        (.binop
                                        "=="
                                        (.index (.name "buffer") (.lit (.int 2)))
                                        (.lit (.str "N")))))
                                        (.ret (.lit (.bool false))))))
                                        .skip)
                                      (.seq
                                        .skip
                                        (.seq
                                        (.assign "kRepresentableIntegerLength" (.lit (.int 15)))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "<="
                                        (.binop "-" (.name "length") (.name "offset"))
                                        (.name "kRepresentableIntegerLength"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "initial_offset" (.name "offset"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "matches" (.lit (.bool true)))
                                        (.seq
                                        (.hole "control:FOR")
                                        (.ifte
                                        (.binop "!=" (.name "matches") (.lit (.int 0)))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "=="
                                        (.index (.name "buffer") (.name "initial_offset"))
                                        (.lit (.int 0)))
                                        (.ret
                                        (.binop
                                        "=="
                                        (.name "initial_offset")
                                        (.binop "-" (.name "length") (.lit (.int 1)))))
                                        .skip)
                                        (.ret (.lit (.bool true))))
                                        .skip))))))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "vector"
                                        (.alloc "Vector" [(.name "buffer"), (.name "length")]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "d"
                                        (.call
                                        "StringToDouble"
                                        [(.name "vector"), (.name "NO_CONVERSION_FLAG")]))
                                        (.seq
                                        (.ifte
                                        (.call "isnan" [(.name "d")])
                                        (.ret (.lit (.bool false)))
                                        .skip)
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "reverse_buffer" (.hole "op:alloc:array-decl"))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "reverse_vector"
                                        (.alloc
                                        "Vector"
                                        [ (.name "reverse_buffer")
                                        , (.call "arraysize" [(.name "reverse_buffer")]) ]))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign
                                        "reverse_string"
                                        (.call
                                        "DoubleToStringView"
                                        [(.name "d"), (.name "reverse_vector")]))
                                        (.seq
                                        (.ifte
                                        (.binop "!=" (.call "length" []) (.name "length"))
                                        (.ret (.lit (.bool false)))
                                        .skip)
                                        (.seq (.hole "control:FOR") (.ret (.lit (.bool true))))))))))))))))))))))))))))))))) }

/-- `v8.internal.DoubleToFloat32_NoInline:float(double)`  (from `conversions.cc`) -/
def f_v8_internal_DoubleToFloat32_NoInline_float_double_ : Func :=
  { name := "v8.internal.DoubleToFloat32_NoInline:float(double)"
  , params := ["x"]
  , body := (.ret (.call "v8.internal.DoubleToFloat32:float(double)" [(.name "x")])) }

/-- `v8.internal.DoubleToInt32_NoInline:int32_t(double)`  (from `conversions.cc`) -/
def f_v8_internal_DoubleToInt32_NoInline_int32_t_double_ : Func :=
  { name := "v8.internal.DoubleToInt32_NoInline:int32_t(double)"
  , params := ["x"]
  , body := (.ret (.call "v8.internal.DoubleToInt32:ANY(double)" [(.name "x")])) }

/-- `HashSeed.InitializeRoots:void(Isolate*)`  (from `hash-seed.cc`) -/
def f_HashSeed_InitializeRoots_void_Isolate__ : Func :=
  { name := "HashSeed.InitializeRoots:void(Isolate*)"
  , params := ["isolate"]
  , body := (.seq
            .skip
            (.seq
              (.expr (.call "DCHECK" [(.unop "!" (.call "deserialization_complete" []))]))
              (.seq
                .skip
                (.seq
                  (.ifte
                    (.binop "==" (.field (.name "v8_flags") "hash_seed") (.lit (.int 0)))
                    (.seq
                      .skip
                      (.seq
                        (.assign "rnd" (.call "NextInt64" []))
                        (.assign "seed" (.unop "cast:u64" (.name "rnd")))))
                    (.assign "seed" (.unop "cast:u64" (.field (.name "v8_flags") "hash_seed"))))
                  (.seq
                    .skip
                    (.seq
                      (.assign "data" (.mcall (.call "hash_seed" []) "data_" []))
                      (.seq
                        (.setField (.name "data") "seed" (.name "seed"))
                        (.expr
                          (.call
                            "rapidhash_make_secret"
                            [(.name "seed"), (.field (.name "data") "secrets")]))))))))) }

/-- `v8.internal.math.pow:double(double,double)`  (from `ieee754.cc`) -/
def f_v8_internal_math_pow_double_double_double_ : Func :=
  { name := "v8.internal.math.pow:double(double,double)"
  , params := ["x", "y"]
  , body := (.seq
            .skip
            (.seq
              (.ifte (.call "isnan" [(.name "y")]) (.ret (.call "quiet_NaN" [])) .skip)
              (.seq
                (.ifte
                  (.binop
                    "&&"
                    (.call "isinf" [(.name "y")])
                    (.binop
                      "||"
                      (.binop "==" (.name "x") (.lit (.int 1)))
                      (.binop "==" (.name "x") (.unop "-" (.lit (.int 1))))))
                  (.ret (.call "quiet_NaN" []))
                  .skip)
                (.seq
                  (.ifte (.call "isnan" [(.name "x")]) (.assign "x" (.call "quiet_NaN" [])) .skip)
                  (.seq
                    (.ifte
                      (.binop "==" (.name "y") (.lit (.int 2)))
                      (.ret (.binop "*" (.name "x") (.name "x")))
                      (.ifte
                        (.binop "==" (.name "y") (.hole "lit:float"))
                        (.ifte
                          (.call "isinf" [(.name "x")])
                          (.ret (.call "infinity" []))
                          (.ret (.call "sqrt" [(.binop "+" (.name "x") (.lit (.int 0)))])))
                        .skip))
                    (.seq
                      (.ifte
                        (.field (.name "v8_flags") "use_std_math_pow")
                        (.ret (.call "pow" [(.name "x"), (.name "y")]))
                        .skip)
                      (.ret (.call "pow" [(.name "x"), (.name "y")])))))))) }

/-- `v8.internal.MathRandom.InitializeContext:void(Isolate*,DirectHandle)`  (from `math-random.cc`) -/
def f_v8_internal_MathRandom_InitializeContext_void_Isolate__DirectHandle_ : Func :=
  { name := "v8.internal.MathRandom.InitializeContext:void(Isolate*,DirectHandle)"
  , params := ["isolate", "native_context"]
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
                              (.hole "assign:lhs:lessThan")
                              (.seq
                                (.expr
                                  (.call
                                    "set_math_random_state"
                                    [(.hole "op:indirection:unknown-type")]))
                                (.seq
                                  (.expr
                                    (.call "ResetContext" [(.hole "op:indirection:opaque-type")]))
                                  (.ifte
                                    (.binop "!=" (.name "kUseRefillCache") (.lit (.int 0)))
                                    (.seq
                                      .skip
                                      (.seq
                                        (.assign
                                        "cache"
                                        (.binop
                                        ">"
                                        (.binop "<" (.name "Cast") (.name "FixedDoubleArray"))
                                        (.call "NewFixedDoubleArray" [(.name "kCacheSize")])))
                                        (.seq
                                        (.hole "control:FOR")
                                        (.expr
                                        (.call
                                        "set_math_random_cache"
                                        [(.hole "op:indirection:scalar")])))))
                                    (.expr
                                      (.call "set_math_random_cache" [(.call "undefined_value" [])]))))))))))))))) }

/-- `v8.internal.MathRandom.ResetContext:void(Tagged)`  (from `math-random.cc`) -/
def f_v8_internal_MathRandom_ResetContext_void_Tagged_ : Func :=
  { name := "v8.internal.MathRandom.ResetContext:void(Tagged)"
  , params := ["native_context"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.expr (.call "set_math_random_index" [(.call "zero" [])]))
                  (.seq
                    .skip
                    (.seq
                      (.assign "state" (.hole "op:arrayInitializer"))
                      (.expr
                        (.binop
                          "<"
                          (.binop "<" (.name "Cast") (.name "PodArray"))
                          (.hole "op:arithmeticShiftRight"))))))))) }

/-- `v8.internal.MathRandom.InitializeAndMaybeRefillCache:Address(Isolate*,Address)`  (from `math-random.cc`) -/
def f_v8_internal_MathRandom_InitializeAndMaybeRefillCache_Address_Isolate__Address_ : Func :=
  { name := "v8.internal.MathRandom.InitializeAndMaybeRefillCache:Address(Isolate*,Address)"
  , params := ["isolate", "raw_native_context"]
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
                                        (.hole "assign:lhs:greaterThan")
                                        (.seq
                                        .skip
                                        (.seq
                                        (.hole "assign:lhs:lessThan")
                                        (.seq
                                        .skip
                                        (.seq
                                        (.assign "state" (.call "get" [(.lit (.int 0))]))
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "&&"
                                        (.binop "==" (.field (.name "state") "s0") (.lit (.int 0)))
                                        (.binop "==" (.field (.name "state") "s1") (.lit (.int 0))))
                                        (.seq
                                        .skip
                                        (.seq
                                        (.ifte
                                        (.binop
                                        "!="
                                        (.field (.name "v8_flags") "random_seed")
                                        (.lit (.int 0)))
                                        (.assign "seed" (.field (.name "v8_flags") "random_seed"))
                                        (.expr
                                        (.call
                                        "NextBytes"
                                        [(.hole "op:addressOf:local:scalar"), (.hole "op:sizeOf")])))
                                        (.seq
                                        (.setField
                                        (.name "state")
                                        "s0"
                                        (.call "MurmurHash3" [(.name "seed")]))
                                        (.seq
                                        (.setField
                                        (.name "state")
                                        "s1"
                                        (.call "MurmurHash3" [(.unop "!" (.name "seed"))]))
                                        (.expr
                                        (.call
                                        "CHECK"
                                        [ (.binop
                                        "||"
                                        (.binop "!=" (.field (.name "state") "s0") (.lit (.int 0)))
                                        (.binop "!=" (.field (.name "state") "s1") (.lit (.int 0)))) ]))))))
                                        .skip)
                                        (.seq
                                        (.ifte
                                        (.unop "!" (.name "kUseRefillCache"))
                                        (.seq
                                        (.expr (.call "set" [(.lit (.int 0)), (.name "state")]))
                                        (.ret (.call "ptr" [])))
                                        .skip)
                                        (.seq
                                        (.hole "assign:lhs:greaterThan")
                                        (.seq
                                        (.hole "control:FOR")
                                        (.seq
                                        (.expr (.call "set" [(.lit (.int 0)), (.name "state")]))
                                        (.seq
                                        (.hole "assign:lhs:greaterThan")
                                        (.seq
                                        (.expr
                                        (.call "set_math_random_index" [(.name "new_index")]))
                                        (.ret (.call "ptr" []))))))))))))))))))))))))))))) }

/-- `v8.internal.FastD2IChecked:int(double)`  (from `conversions.h`) -/
def f_v8_internal_FastD2IChecked_int_double_ : Func :=
  { name := "v8.internal.FastD2IChecked:int(double)"
  , params := ["x"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.ifte
                  (.unop "!" (.binop ">=" (.name "x") (.name "INT_MIN")))
                  (.ret (.name "INT_MIN"))
                  .skip)
                (.seq
                  (.ifte (.binop ">" (.name "x") (.name "INT_MAX")) (.ret (.name "INT_MAX")) .skip)
                  (.ret (.unop "cast:i32" (.name "x"))))))) }

/-- `v8.internal.FastD2I:int(double)`  (from `conversions.h`) -/
def f_v8_internal_FastD2I_int_double_ : Func :=
  { name := "v8.internal.FastD2I:int(double)"
  , params := ["x"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.expr (.call "DCHECK" [(.binop "<=" (.name "x") (.name "INT_MAX"))]))
                (.seq
                  (.expr (.call "DCHECK" [(.binop ">=" (.name "x") (.name "INT_MIN"))]))
                  (.ret (.unop "cast:i32" (.name "x"))))))) }

/-- `v8.internal.FastI2D:double(int)`  (from `conversions.h`) -/
def f_v8_internal_FastI2D_double_int_ : Func :=
  { name := "v8.internal.FastI2D:double(int)"
  , params := ["x"]
  , body := (.ret (.hole "op:cast:scalar")) }

/-- `v8.internal.FastUI2D:double(unsigned)`  (from `conversions.h`) -/
def f_v8_internal_FastUI2D_double_unsigned_ : Func :=
  { name := "v8.internal.FastUI2D:double(unsigned)"
  , params := ["x"]
  , body := (.ret (.hole "op:cast:scalar")) }

/-- `v8.internal.IsMinusZero:bool(double)`  (from `conversions.h`) -/
def f_v8_internal_IsMinusZero_bool_double_ : Func :=
  { name := "v8.internal.IsMinusZero:bool(double)"
  , params := ["value"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.ret
                (.binop
                  "=="
                  (.binop
                    ">"
                    (.binop "<" (.field (.name "base") "bit_cast") (.name "int64_t"))
                    (.name "value"))
                  (.binop
                    ">"
                    (.binop "<" (.field (.name "base") "bit_cast") (.name "int64_t"))
                    (.unop "-" (.hole "lit:float"))))))) }

/-- `HashSeed.__init__`  (from `hash-seed-inl.h`) -/
def f_HashSeed___init__ : Func :=
  { name := "HashSeed.__init__"
  , params := ["isolate"]
  , body := (.setField (.name "self") "HashSeed" (.call "ReadOnlyRoots" [(.name "isolate")])) }

/-- `HashSeed.__init__`  (from `hash-seed-inl.h`) -/
def f_HashSeed___init__' : Func :=
  { name := "HashSeed.__init__"
  , params := ["isolate"]
  , body := (.setField (.name "self") "HashSeed" (.call "ReadOnlyRoots" [(.name "isolate")])) }

/-- `HashSeed.__init__`  (from `hash-seed-inl.h`) -/
def f_HashSeed___init__'' : Func :=
  { name := "HashSeed.__init__"
  , params := ["roots"]
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                (.expr
                  (.call
                    "DCHECK_EQ"
                    [ (.lit (.int 0))
                    , (.binop "%" (.unop "cast:u64" (.name "data_")) (.hole "op:sizeOf")) ]))
                (.setField (.name "self") "data_" (.hole "op:addressOf:call:unknown-type"))))) }

/-- `HashSeed.Default:HashSeed()`  (from `hash-seed-inl.h`) -/
def f_HashSeed_Default_HashSeed__ : Func :=
  { name := "HashSeed.Default:HashSeed()"
  , params := []
  , body := (.seq .skip (.ret (.call "HashSeed" [(.name "kDefaultData")]))) }

/-- `HashSeed.seed:uint64_t()<const>`  (from `hash-seed-inl.h`) -/
def f_HashSeed_seed_uint64_t___const_ : Func :=
  { name := "HashSeed.seed:uint64_t()<const>"
  , params := []
  , body := (.seq .skip (.ret (.field (.name "data_") "seed"))) }

/-- `HashSeed.secret:uint64_t()<const>`  (from `hash-seed-inl.h`) -/
def f_HashSeed_secret_uint64_t___const_ : Func :=
  { name := "HashSeed.secret:uint64_t()<const>"
  , params := []
  , body := (.seq .skip (.ret (.field (.name "data_") "secrets"))) }

/-- `v8.internal.MathRandom.<clinit>:v8.internal.MathRandom()`  (from `math-random.h`) -/
def f_v8_internal_MathRandom__clinit__v8_internal_MathRandom__ : Func :=
  { name := "v8.internal.MathRandom.<clinit>:v8.internal.MathRandom()"
  , params := []
  , body := (.seq
            .skip
            (.seq
              .skip
              (.seq
                .skip
                (.seq
                  (.assign "kCacheSize" (.lit (.int 64)))
                  (.assign "kStateSize" (.binop "*" (.lit (.int 2)) (.name "kInt64Size"))))))) }

/-- `v8.internal.FastD2UI:unsigned int(double)`  (from `conversions.h`) -/
def f_v8_internal_FastD2UI_unsigned_int_double_ : Func :=
  { name := "v8.internal.FastD2UI:unsigned int(double)"
  , params := ["x"]
  , body := .skip }

/-- `v8.internal.DoubleToFloat32:float(double)`  (from `conversions.h`) -/
def f_v8_internal_DoubleToFloat32_float_double_ : Func :=
  { name := "v8.internal.DoubleToFloat32:float(double)"
  , params := ["x"]
  , body := .skip }

/-- `v8.internal.DoubleToFloat16:ANY(double)`  (from `conversions.h`) -/
def f_v8_internal_DoubleToFloat16_ANY_double_ : Func :=
  { name := "v8.internal.DoubleToFloat16:ANY(double)"
  , params := ["x"]
  , body := .skip }

/-- `v8.internal.DoubleToInteger:double(double)`  (from `conversions.h`) -/
def f_v8_internal_DoubleToInteger_double_double_ : Func :=
  { name := "v8.internal.DoubleToInteger:double(double)"
  , params := ["x"]
  , body := .skip }

/-- `v8.internal.DoubleToInt32:ANY(double)`  (from `conversions.h`) -/
def f_v8_internal_DoubleToInt32_ANY_double_ : Func :=
  { name := "v8.internal.DoubleToInt32:ANY(double)"
  , params := ["x"]
  , body := .skip }

/-- `v8.internal.DoubleToInt32_NoInline:ANY(double)`  (from `conversions.h`) -/
def f_v8_internal_DoubleToInt32_NoInline_ANY_double_ : Func :=
  { name := "v8.internal.DoubleToInt32_NoInline:ANY(double)"
  , params := ["x"]
  , body := .skip }

/-- `v8.internal.DoubleToUint32:ANY(double)`  (from `conversions.h`) -/
def f_v8_internal_DoubleToUint32_ANY_double_ : Func :=
  { name := "v8.internal.DoubleToUint32:ANY(double)"
  , params := ["x"]
  , body := .skip }

/-- `v8.internal.DoubleToInt64:ANY(double)`  (from `conversions.h`) -/
def f_v8_internal_DoubleToInt64_ANY_double_ : Func :=
  { name := "v8.internal.DoubleToInt64:ANY(double)"
  , params := ["x"]
  , body := .skip }

/-- `v8.internal.DoubleToUint64:ANY(double)`  (from `conversions.h`) -/
def f_v8_internal_DoubleToUint64_ANY_double_ : Func :=
  { name := "v8.internal.DoubleToUint64:ANY(double)"
  , params := ["x"]
  , body := .skip }

/-- `v8.internal.StringToBigInt:ANY(Isolate*,DirectHandle)`  (from `conversions.h`) -/
def f_v8_internal_StringToBigInt_ANY_Isolate__DirectHandle_ : Func :=
  { name := "v8.internal.StringToBigInt:ANY(Isolate*,DirectHandle)"
  , params := ["isolate", "string"]
  , body := .skip }

/-- `v8.internal.BigIntLiteral:ANY(IsolateT*,char*)`  (from `conversions.h`) -/
def f_v8_internal_BigIntLiteral_ANY_IsolateT__char__ : Func :=
  { name := "v8.internal.BigIntLiteral:ANY(IsolateT*,char*)"
  , params := ["isolate", "string"]
  , body := .skip }

/-- `v8.internal.DoubleToStringView:ANY(double,base.Vector)`  (from `conversions.h`) -/
def f_v8_internal_DoubleToStringView_ANY_double_base_Vector_ : Func :=
  { name := "v8.internal.DoubleToStringView:ANY(double,base.Vector)"
  , params := ["value", "buffer"]
  , body := .skip }

/-- `v8.internal.BigIntLiteralToDecimal:ANY(LocalIsolate*,base.Vector)`  (from `conversions.h`) -/
def f_v8_internal_BigIntLiteralToDecimal_ANY_LocalIsolate__base_Vector_ : Func :=
  { name := "v8.internal.BigIntLiteralToDecimal:ANY(LocalIsolate*,base.Vector)"
  , params := ["isolate", "literal"]
  , body := .skip }

/-- `v8.internal.IntToStringView:ANY(int,base.Vector)`  (from `conversions.h`) -/
def f_v8_internal_IntToStringView_ANY_int_base_Vector_ : Func :=
  { name := "v8.internal.IntToStringView:ANY(int,base.Vector)"
  , params := ["n", "buffer"]
  , body := .skip }

/-- `v8.internal.DoubleToFixedStringView:ANY(double,int,base.Vector)`  (from `conversions.h`) -/
def f_v8_internal_DoubleToFixedStringView_ANY_double_int_base_Vector_ : Func :=
  { name := "v8.internal.DoubleToFixedStringView:ANY(double,int,base.Vector)"
  , params := ["value", "f", "buffer"]
  , body := .skip }

/-- `v8.internal.DoubleToExponentialStringView:ANY(double,int,base.Vector)`  (from `conversions.h`) -/
def f_v8_internal_DoubleToExponentialStringView_ANY_double_int_base_Vector_ : Func :=
  { name := "v8.internal.DoubleToExponentialStringView:ANY(double,int,base.Vector)"
  , params := ["value", "f", "buffer"]
  , body := .skip }

/-- `v8.internal.DoubleToPrecisionStringView:ANY(double,int,base.Vector)`  (from `conversions.h`) -/
def f_v8_internal_DoubleToPrecisionStringView_ANY_double_int_base_Vector_ : Func :=
  { name := "v8.internal.DoubleToPrecisionStringView:ANY(double,int,base.Vector)"
  , params := ["value", "f", "buffer"]
  , body := .skip }

/-- `v8.internal.DoubleToRadixStringView:ANY(double,int,base.Vector)`  (from `conversions.h`) -/
def f_v8_internal_DoubleToRadixStringView_ANY_double_int_base_Vector_ : Func :=
  { name := "v8.internal.DoubleToRadixStringView:ANY(double,int,base.Vector)"
  , params := ["value", "radix", "buffer"]
  , body := .skip }

/-- `v8.internal.DoubleToSmiInteger:bool(double,int*)`  (from `conversions.h`) -/
def f_v8_internal_DoubleToSmiInteger_bool_double_int__ : Func :=
  { name := "v8.internal.DoubleToSmiInteger:bool(double,int*)"
  , params := ["value", "smi_int_value"]
  , body := .skip }

/-- `v8.internal.IsSmiDouble:bool(double)`  (from `conversions.h`) -/
def f_v8_internal_IsSmiDouble_bool_double_ : Func :=
  { name := "v8.internal.IsSmiDouble:bool(double)"
  , params := ["value"]
  , body := .skip }

/-- `v8.internal.IsInt32Double:bool(double)`  (from `conversions.h`) -/
def f_v8_internal_IsInt32Double_bool_double_ : Func :=
  { name := "v8.internal.IsInt32Double:bool(double)"
  , params := ["value"]
  , body := .skip }

/-- `v8.internal.IsUint32Double:bool(double)`  (from `conversions.h`) -/
def f_v8_internal_IsUint32Double_bool_double_ : Func :=
  { name := "v8.internal.IsUint32Double:bool(double)"
  , params := ["value"]
  , body := .skip }

/-- `v8.internal.DoubleToUint32IfEqualToSelf:bool(double,uint32_t*)`  (from `conversions.h`) -/
def f_v8_internal_DoubleToUint32IfEqualToSelf_bool_double_uint32_t__ : Func :=
  { name := "v8.internal.DoubleToUint32IfEqualToSelf:bool(double,uint32_t*)"
  , params := ["value", "uint32_value"]
  , body := .skip }

/-- `v8.internal.PositiveNumberToUint32:ANY(Tagged)`  (from `conversions.h`) -/
def f_v8_internal_PositiveNumberToUint32_ANY_Tagged_ : Func :=
  { name := "v8.internal.PositiveNumberToUint32:ANY(Tagged)"
  , params := ["number"]
  , body := .skip }

/-- `v8.internal.NumberToInt32:ANY(Tagged)`  (from `conversions.h`) -/
def f_v8_internal_NumberToInt32_ANY_Tagged_ : Func :=
  { name := "v8.internal.NumberToInt32:ANY(Tagged)"
  , params := ["number"]
  , body := .skip }

/-- `v8.internal.NumberToUint32:ANY(Tagged)`  (from `conversions.h`) -/
def f_v8_internal_NumberToUint32_ANY_Tagged_ : Func :=
  { name := "v8.internal.NumberToUint32:ANY(Tagged)"
  , params := ["number"]
  , body := .skip }

/-- `v8.internal.NumberToInt64:ANY(Tagged)`  (from `conversions.h`) -/
def f_v8_internal_NumberToInt64_ANY_Tagged_ : Func :=
  { name := "v8.internal.NumberToInt64:ANY(Tagged)"
  , params := ["number"]
  , body := .skip }

/-- `v8.internal.PositiveNumberToUint64:ANY(Tagged)`  (from `conversions.h`) -/
def f_v8_internal_PositiveNumberToUint64_ANY_Tagged_ : Func :=
  { name := "v8.internal.PositiveNumberToUint64:ANY(Tagged)"
  , params := ["number"]
  , body := .skip }

/-- `v8.internal.TryStringToDouble:ANY(LocalIsolate*,DirectHandle,uint32_t)`  (from `conversions.h`) -/
def f_v8_internal_TryStringToDouble_ANY_LocalIsolate__DirectHandle_uint32_t_ : Func :=
  { name := "v8.internal.TryStringToDouble:ANY(LocalIsolate*,DirectHandle,uint32_t)"
  , params := ["isolate", "object", "max_length_for_conversion"]
  , body := .skip }

/-- `v8.internal.TryStringToInt:ANY(LocalIsolate*,DirectHandle,int)`  (from `conversions.h`) -/
def f_v8_internal_TryStringToInt_ANY_LocalIsolate__DirectHandle_int_ : Func :=
  { name := "v8.internal.TryStringToInt:ANY(LocalIsolate*,DirectHandle,int)"
  , params := ["isolate", "object", "radix"]
  , body := .skip }

/-- `v8.internal.TryNumberToSize:bool(Tagged,size_t*)`  (from `conversions.h`) -/
def f_v8_internal_TryNumberToSize_bool_Tagged_size_t__ : Func :=
  { name := "v8.internal.TryNumberToSize:bool(Tagged,size_t*)"
  , params := ["number", "result"]
  , body := .skip }

/-- `v8.internal.NumberToSize:ANY(Tagged)`  (from `conversions.h`) -/
def f_v8_internal_NumberToSize_ANY_Tagged_ : Func :=
  { name := "v8.internal.NumberToSize:ANY(Tagged)"
  , params := ["number"]
  , body := .skip }

/-- `v8.internal.MathRandom.InitializeAndMaybeRefillCache:ANY(Isolate*,Address)`  (from `math-random.h`) -/
def f_v8_internal_MathRandom_InitializeAndMaybeRefillCache_ANY_Isolate__Address_ : Func :=
  { name := "v8.internal.MathRandom.InitializeAndMaybeRefillCache:ANY(Isolate*,Address)"
  , params := ["isolate", "raw_native_context"]
  , body := .skip }

/-- `v8.internal.StringToIntHelper.ParseOneByte:void(uint8_t*)`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper_ParseOneByte_void_uint8_t__ : Func :=
  { name := "v8.internal.StringToIntHelper.ParseOneByte:void(uint8_t*)"
  , params := ["start"]
  , body := .skip }

/-- `v8.internal.StringToIntHelper.ParseTwoByte:void(base.uc16*)`  (from `conversions.cc`) -/
def f_v8_internal_StringToIntHelper_ParseTwoByte_void_base_uc16__ : Func :=
  { name := "v8.internal.StringToIntHelper.ParseTwoByte:void(base.uc16*)"
  , params := ["start"]
  , body := .skip }

/-- `v8.internal.BigIntLiteral:ANY(Isolate*,char*)`  (from `conversions.cc`) -/
def f_v8_internal_BigIntLiteral_ANY_Isolate__char__ : Func :=
  { name := "v8.internal.BigIntLiteral:ANY(Isolate*,char*)"
  , params := ["isolate", "string"]
  , body := .skip }

/-- `v8.internal.BigIntLiteral:ANY(LocalIsolate*,char*)`  (from `conversions.cc`) -/
def f_v8_internal_BigIntLiteral_ANY_LocalIsolate__char__ : Func :=
  { name := "v8.internal.BigIntLiteral:ANY(LocalIsolate*,char*)"
  , params := ["isolate", "string"]
  , body := .skip }

/-- `conversions-inl.h:<global>`  (from `conversions-inl.h`) -/
def f_conversions_inl_h__global_ : Func :=
  { name := "conversions-inl.h:<global>"
  , params := []
  , body := (.hole "stmt:UNKNOWN:namespace") }

/-- `conversions.cc:<global>`  (from `conversions.cc`) -/
def f_conversions_cc__global_ : Func :=
  { name := "conversions.cc:<global>"
  , params := []
  , body := .skip }

/-- `conversions.h:<global><cpp>`  (from `conversions.h`) -/
def f_conversions_h__global__cpp_ : Func :=
  { name := "conversions.h:<global><cpp>"
  , params := []
  , body := .skip }

/-- `hash-seed-inl.h:<global><cpp>`  (from `hash-seed-inl.h`) -/
def f_hash_seed_inl_h__global__cpp_ : Func :=
  { name := "hash-seed-inl.h:<global><cpp>"
  , params := []
  , body := .skip }

/-- `hash-seed.cc:<global>`  (from `hash-seed.cc`) -/
def f_hash_seed_cc__global_ : Func :=
  { name := "hash-seed.cc:<global>"
  , params := []
  , body := .skip }

/-- `hash-seed.h:<global><cpp>`  (from `hash-seed.h`) -/
def f_hash_seed_h__global__cpp_ : Func :=
  { name := "hash-seed.h:<global><cpp>"
  , params := []
  , body := .skip }

/-- `ieee754.cc:<global>`  (from `ieee754.cc`) -/
def f_ieee754_cc__global_ : Func :=
  { name := "ieee754.cc:<global>"
  , params := []
  , body := .skip }

/-- `ieee754.h:<global><cpp>`  (from `ieee754.h`) -/
def f_ieee754_h__global__cpp_ : Func :=
  { name := "ieee754.h:<global><cpp>"
  , params := []
  , body := .skip }

/-- `integer-literal-inl.h:<global>`  (from `integer-literal-inl.h`) -/
def f_integer_literal_inl_h__global_ : Func :=
  { name := "integer-literal-inl.h:<global>"
  , params := []
  , body := (.hole "stmt:UNKNOWN:namespace") }

/-- `integer-literal.h:<global>`  (from `integer-literal.h`) -/
def f_integer_literal_h__global_ : Func :=
  { name := "integer-literal.h:<global>"
  , params := []
  , body := (.hole "stmt:UNKNOWN:namespace") }

/-- `math-random.cc:<global>`  (from `math-random.cc`) -/
def f_math_random_cc__global_ : Func :=
  { name := "math-random.cc:<global>"
  , params := []
  , body := .skip }

/-- `math-random.h:<global><cpp>`  (from `math-random.h`) -/
def f_math_random_h__global__cpp_ : Func :=
  { name := "math-random.h:<global><cpp>"
  , params := []
  , body := .skip }

/-- Module-level initializers: run these to populate the globals frame
before calling any entry point. -/
def moduleInits : List Func := [f_conversions_inl_h__global_, f_conversions_cc__global_, f_hash_seed_cc__global_, f_ieee754_cc__global_, f_integer_literal_inl_h__global_, f_integer_literal_h__global_, f_math_random_cc__global_]

/-- Source dialect: `.cLike` (integer division/modulo convention). -/
def program : Program := { dialect := .cLike, funcs := [
  f_v8_internal_Convert2Digits_void_uint8_t_char__,
  f_v8_internal_ConvertHeadDigits_uint8_t_uint8_t_char__,
  f_v8_internal_Convert8Digits_void_uint32_t_char__,
  f_v8_internal_ConvertUpTo9Digits_uint8_t_uint32_t_char__,
  f_v8_internal_SignificandToChars_uint8_t_uint64_t_char__,
  f_v8_internal_SimpleStringBuilder__clinit__v8_internal_SimpleStringBuilder__,
  f_v8_internal_SimpleStringBuilder___init__,
  f_v8_internal_SimpleStringBuilder___init__',
  f_v8_internal_SimpleStringBuilder__SimpleStringBuilder_ANY__,
  f_v8_internal_SimpleStringBuilder_position_size_t___const_,
  f_v8_internal_SimpleStringBuilder_AddCharacter_void_char_,
  f_v8_internal_SimpleStringBuilder_AddString_void_char__size_t_,
  f_v8_internal_SimpleStringBuilder_AddSubstring_void_char__size_t_,
  f_v8_internal_SimpleStringBuilder_AddPadding_void_char_int_,
  f_v8_internal_SimpleStringBuilder_AddExponent_void_int_,
  f_v8_internal_SimpleStringBuilder_Finalize_char___,
  f_v8_internal_SimpleStringBuilder_is_finalized_bool___const_,
  f_v8_internal_JunkStringValue_double__,
  f_v8_internal_SignedZero_double_bool_,
  f_v8_internal_isDigit_bool_int_int_,
  f_v8_internal_isBinaryDigit_bool_int_,
  f_v8_internal_SubStringEquals_bool_Char___Char__char__,
  f_v8_internal_AdvanceToNonspace_bool_Char___Char__,
  f_v8_internal_InternalStringToIntDouble_double_Char__Char__bool_bool_,
  f_v8_internal_StringToIntHelper__clinit__v8_internal_StringToIntHelper__,
  f_v8_internal_StringToIntHelper___init__,
  f_v8_internal_StringToIntHelper___init__',
  f_v8_internal_StringToIntHelper___init__'',
  f_v8_internal_StringToIntHelper___init__''',
  f_v8_internal_StringToIntHelper___init__'''',
  f_v8_internal_StringToIntHelper__StringToIntHelper_ANY__,
  f_v8_internal_StringToIntHelper_set_allow_binary_and_octal_prefixes_void__,
  f_v8_internal_StringToIntHelper_set_disallow_trailing_junk_void__,
  f_v8_internal_StringToIntHelper_allow_trailing_junk_bool__,
  f_v8_internal_StringToIntHelper_IsOneByte_bool___const_,
  f_v8_internal_StringToIntHelper_radix_int__,
  f_v8_internal_StringToIntHelper_cursor_size_t__,
  f_v8_internal_StringToIntHelper_length_size_t__,
  f_v8_internal_StringToIntHelper_negative_bool__,
  f_v8_internal_StringToIntHelper_sign_v8_internal__Sign__,
  f_v8_internal_StringToIntHelper_state_v8_internal__State__,
  f_v8_internal_StringToIntHelper_set_state_void_v8_internal_State_,
  f_v8_internal_StringToIntHelper_ParseInt_void__,
  f_v8_internal_StringToIntHelper_DetectRadixInternal_void_Char__size_t_,
  f_v8_internal_NumberParseIntHelper__clinit__v8_internal_NumberParseIntHelper__,
  f_v8_internal_NumberParseIntHelper___init__,
  f_v8_internal_NumberParseIntHelper___init__',
  f_v8_internal_NumberParseIntHelper___init__'',
  f_v8_internal_NumberParseIntHelper_ParseInternal_void_Char__,
  f_v8_internal_NumberParseIntHelper_ParseOneByte_void_uint8_t__,
  f_v8_internal_NumberParseIntHelper_ParseTwoByte_void_base_uc16__,
  f_v8_internal_NumberParseIntHelper_GetResult_double__,
  f_v8_internal_NumberParseIntHelper_HandlePowerOfTwoCase_double_Char__Char__,
  f_v8_internal_NumberParseIntHelper_HandleBaseTenCase_void_Char__Char__,
  f_v8_internal_NumberParseIntHelper_HandleGenericCase_void_Char__Char__,
  f_v8_internal_InternalStringToDouble_double_Char__Char__v8_internal_ConversionFlag_double_,
  f_v8_internal_StringToDouble_double_char__v8_internal_ConversionFlag_double_,
  f_v8_internal_StringToDouble_double_base_Vector_v8_internal_ConversionFlag_double_,
  f_StringToDouble_double_base_Vector_v8_internal_ConversionFlag_double_,
  f_v8_internal_BinaryStringToDouble_double_base_Vector_,
  f_v8_internal_OctalStringToDouble_double_base_Vector_,
  f_v8_internal_HexStringToDouble_double_base_Vector_,
  f_v8_internal_ImplicitOctalStringToDouble_double_base_Vector_,
  f_v8_internal_StringToInt_double_Isolate__DirectHandle_int_,
  f_v8_internal_StringToBigIntHelper___init__,
  f_v8_internal_StringToBigIntHelper___init__',
  f_v8_internal_StringToBigIntHelper_ParseOneByte_void_uint8_t__,
  f_v8_internal_StringToBigIntHelper_ParseTwoByte_void_base_uc16__,
  f_v8_internal_StringToBigIntHelper_GetResult_MaybeHandle__,
  f_v8_internal_StringToBigIntHelper_DecimalString_pair_bigint_Processor__,
  f_v8_internal_StringToBigIntHelper_isolate_ANY__,
  f_v8_internal_StringToBigIntHelper_ParseInternal_void_Char__,
  f_v8_internal_StringToBigIntHelper_allocation_type_AllocationType__,
  f_v8_internal_StringToBigInt_MaybeHandle_Isolate__DirectHandle_,
  f_v8_internal_BigIntLiteral_MaybeHandle_IsolateT__char__,
  f_v8_internal_BigIntLiteralToDecimal_pair_LocalIsolate__base_Vector_,
  f_v8_internal_DoubleToStringView_string_view_double_base_Vector_,
  f_v8_internal_IntToStringView_string_view_int_base_Vector_,
  f_v8_internal_DoubleToFixedStringView_string_view_double_int_base_Vector_,
  f_v8_internal_CreateExponentialRepresentation_string_view_char__int_int_bool_int_base_Vector_,
  f_v8_internal_DoubleToExponentialStringView_string_view_double_int_base_Vector_,
  f_v8_internal_DoubleToPrecisionStringView_string_view_double_int_base_Vector_,
  f_v8_internal_DoubleToRadixStringView_string_view_double_int_base_Vector_,
  f_v8_internal_StringToDouble_double_Isolate__DirectHandle_v8_internal_ConversionFlag_double_,
  f_v8_internal_FlatStringToDouble_double_Tagged_v8_internal_ConversionFlag_double_,
  f_v8_internal_TryStringToDouble_optional_LocalIsolate__DirectHandle_uint32_t_,
  f_v8_internal_TryStringToInt_optional_LocalIsolate__DirectHandle_int_,
  f_v8_internal_IsSpecialIndex_bool_Tagged_,
  f_v8_internal_IsSpecialIndex_bool_Tagged_v8_internal_SharedStringAccessGuardIfNeeded__,
  f_v8_internal_DoubleToFloat32_NoInline_float_double_,
  f_v8_internal_DoubleToInt32_NoInline_int32_t_double_,
  f_HashSeed_InitializeRoots_void_Isolate__,
  f_v8_internal_math_pow_double_double_double_,
  f_v8_internal_MathRandom_InitializeContext_void_Isolate__DirectHandle_,
  f_v8_internal_MathRandom_ResetContext_void_Tagged_,
  f_v8_internal_MathRandom_InitializeAndMaybeRefillCache_Address_Isolate__Address_,
  f_v8_internal_FastD2IChecked_int_double_,
  f_v8_internal_FastD2I_int_double_,
  f_v8_internal_FastI2D_double_int_,
  f_v8_internal_FastUI2D_double_unsigned_,
  f_v8_internal_IsMinusZero_bool_double_,
  f_HashSeed___init__,
  f_HashSeed___init__',
  f_HashSeed___init__'',
  f_HashSeed_Default_HashSeed__,
  f_HashSeed_seed_uint64_t___const_,
  f_HashSeed_secret_uint64_t___const_,
  f_v8_internal_MathRandom__clinit__v8_internal_MathRandom__,
  f_v8_internal_FastD2UI_unsigned_int_double_,
  f_v8_internal_DoubleToFloat32_float_double_,
  f_v8_internal_DoubleToFloat16_ANY_double_,
  f_v8_internal_DoubleToInteger_double_double_,
  f_v8_internal_DoubleToInt32_ANY_double_,
  f_v8_internal_DoubleToInt32_NoInline_ANY_double_,
  f_v8_internal_DoubleToUint32_ANY_double_,
  f_v8_internal_DoubleToInt64_ANY_double_,
  f_v8_internal_DoubleToUint64_ANY_double_,
  f_v8_internal_StringToBigInt_ANY_Isolate__DirectHandle_,
  f_v8_internal_BigIntLiteral_ANY_IsolateT__char__,
  f_v8_internal_DoubleToStringView_ANY_double_base_Vector_,
  f_v8_internal_BigIntLiteralToDecimal_ANY_LocalIsolate__base_Vector_,
  f_v8_internal_IntToStringView_ANY_int_base_Vector_,
  f_v8_internal_DoubleToFixedStringView_ANY_double_int_base_Vector_,
  f_v8_internal_DoubleToExponentialStringView_ANY_double_int_base_Vector_,
  f_v8_internal_DoubleToPrecisionStringView_ANY_double_int_base_Vector_,
  f_v8_internal_DoubleToRadixStringView_ANY_double_int_base_Vector_,
  f_v8_internal_DoubleToSmiInteger_bool_double_int__,
  f_v8_internal_IsSmiDouble_bool_double_,
  f_v8_internal_IsInt32Double_bool_double_,
  f_v8_internal_IsUint32Double_bool_double_,
  f_v8_internal_DoubleToUint32IfEqualToSelf_bool_double_uint32_t__,
  f_v8_internal_PositiveNumberToUint32_ANY_Tagged_,
  f_v8_internal_NumberToInt32_ANY_Tagged_,
  f_v8_internal_NumberToUint32_ANY_Tagged_,
  f_v8_internal_NumberToInt64_ANY_Tagged_,
  f_v8_internal_PositiveNumberToUint64_ANY_Tagged_,
  f_v8_internal_TryStringToDouble_ANY_LocalIsolate__DirectHandle_uint32_t_,
  f_v8_internal_TryStringToInt_ANY_LocalIsolate__DirectHandle_int_,
  f_v8_internal_TryNumberToSize_bool_Tagged_size_t__,
  f_v8_internal_NumberToSize_ANY_Tagged_,
  f_v8_internal_MathRandom_InitializeAndMaybeRefillCache_ANY_Isolate__Address_,
  f_v8_internal_StringToIntHelper_ParseOneByte_void_uint8_t__,
  f_v8_internal_StringToIntHelper_ParseTwoByte_void_base_uc16__,
  f_v8_internal_BigIntLiteral_ANY_Isolate__char__,
  f_v8_internal_BigIntLiteral_ANY_LocalIsolate__char__,
  f_conversions_inl_h__global_,
  f_conversions_cc__global_,
  f_conversions_h__global__cpp_,
  f_hash_seed_inl_h__global__cpp_,
  f_hash_seed_cc__global_,
  f_hash_seed_h__global__cpp_,
  f_ieee754_cc__global_,
  f_ieee754_h__global__cpp_,
  f_integer_literal_inl_h__global_,
  f_integer_literal_h__global_,
  f_math_random_cc__global_,
  f_math_random_h__global__cpp_
] }

end Autoform.Generated